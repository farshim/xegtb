// verify.cpp -- independent check of the finished table.
//
// Every live entry is recomputed from its successors with the ordinary
// (forward) move generator and the generic probe path, which shares no code
// with the retrograde inner loop.  A table that satisfies
//
//   white to move : value = 1 + min { value(child) : child is a loss }, else draw
//   black to move : value = 1 + max { value(child) } when every child is a win,
//                   else draw; and 0 / draw for mate / stalemate
//
// everywhere, with finite depths, is the unique correct depth-to-mate table.
#include "table.hpp"

#include <atomic>
#include <cstdio>
#include <mutex>

namespace kqk {

U64 Table::verify(int threads, U64 stride, bool progress) const {
    const Geometry& g = geo;
    const U32 npc = idx.npc;
    if (stride < 1) stride = 1;

    std::atomic<U64> bad{0}, checked{0};
    std::mutex reportMtx;
    int reported = 0;

    auto describe = [&](const Pos& p) {
        std::string s = "wK=" + g.name(p.wk) + " bK=" + g.name(p.bk);
        for (int i = 0; i < mat.np; ++i) s += " " + mat.label(i) + "=" + g.name(p.wp[i]);
        return s;
    };
    auto report = [&](const char* what, const Pos& p, bool wtm, int got, int want) {
        std::lock_guard<std::mutex> lk(reportMtx);
        if (reported++ < 12)
            std::fprintf(stderr, "  MISMATCH %s  %s %s: table=%d expected=%d\n",
                         what, describe(p).c_str(), wtm ? "wtm" : "btm", got, want);
    };

    parallelFor(idx.nkk, 32, threads, [&](U64 lo, U64 hi, int) {
        U64 localBad = 0, localChecked = 0;
        for (U64 kk = lo; kk < hi; ++kk) {
            Pos p;
            p.wk = idx.kkWk[kk];
            p.bk = idx.kkBk[kk];
            U64 base = kk * npc;
            for (U32 pc = 0; pc < npc; ++pc) {
                U64 slot = base + pc;
                if (stride > 1 && slot % stride) continue;
                U8 vw = w[slot], vb = b[slot];
                idx.decode(pc, p.wp);

                bool live = idx.cfgLive(p.wp, p.wk, p.bk) &&
                            idx.cfgIsCanonical((int32_t)kk, p.wp);
                if (!live) {
                    if (vw != V_DEAD || vb != V_DEAD) {
                        ++localBad;
                        report("dead-slot", p, true, vw, V_DEAD);
                    }
                    continue;
                }
                ++localChecked;

                // ---- white to move ---------------------------------------
                bool inCheck = blackInCheck(g, mat, p);
                if (inCheck) {
                    if (vw != V_DEAD) { ++localBad; report("wtm-illegal", p, true, vw, V_DEAD); }
                } else {
                    int best = -1, moves = 0;
                    genWhite(g, mat, p, [&](const Pos& q) {
                        ++moves;
                        U8 c = valueAt(q, false);
                        if (c == V_DEAD) { best = -2; return; }
                        if (best == -2) return;
                        if (isDtm(c) && (best < 0 || c + 1 < best)) best = c + 1;
                    });
                    int want = (best == -2) ? -2 : (best >= 0 ? best : (int)V_DRAW);
                    if (want != (int)vw) { ++localBad; report("wtm", p, true, vw, want); }
                    if (isDtm(vw) && (vw % 2) == 0) {
                        ++localBad; report("wtm-parity", p, true, vw, -1);
                    }
                    (void)moves;
                }

                // ---- black to move ---------------------------------------
                {
                    int moves = 0, worst = 0;
                    bool allWin = true, broken = false;
                    genBlack(g, mat, p, [&](Sq t, int cap) {
                        ++moves;
                        if (cap >= 0) {
                            // A capture leaves material that cannot mate, and
                            // is a draw -- except in KNNNK, where two knights
                            // can mate and the answer comes from the KNNK
                            // table this one is attached to.
                            U8 cv = V_DRAW;
                            if (sub) {
                                Pos r;
                                r.wk = p.wk;
                                r.bk = t;
                                int k = 0;
                                for (int i = 0; i < mat.np; ++i)
                                    if (i != cap) r.wp[k++] = p.wp[i];
                                cv = sub->valueAt(r, true);
                            }
                            if (!isDtm(cv)) { allWin = false; return; }
                            if (cv > worst) worst = cv;
                            return;
                        }
                        Pos q = p;
                        q.bk = t;
                        U8 c = valueAt(q, true);
                        if (c == V_DEAD) { broken = true; return; }
                        if (!isDtm(c)) allWin = false;
                        else if (c > worst) worst = c;
                    });
                    int want;
                    if (broken)        want = -2;
                    else if (!moves)   want = (inCheck || stalemateLoss) ? 0 : (int)V_DRAW;
                    else               want = allWin ? worst + 1 : (int)V_DRAW;
                    if (want != (int)vb) { ++localBad; report("btm", p, false, vb, want); }
                    if (isDtm(vb) && (vb % 2) != 0) {
                        ++localBad; report("btm-parity", p, false, vb, -1);
                    }
                }
            }
        }
        bad.fetch_add(localBad, std::memory_order_relaxed);
        checked.fetch_add(localChecked, std::memory_order_relaxed);
    });

    if (progress)
        std::fprintf(stderr, "  verified %llu positions (stride %llu), %llu mismatches\n",
                     (unsigned long long)checked.load(), (unsigned long long)stride,
                     (unsigned long long)bad.load());
    return bad.load();
}

} // namespace kqk
