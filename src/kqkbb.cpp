// kqkbb.cpp -- king and queen against king and two bishops.
//
// Why this needs its own solver
// -----------------------------
// It is the first endgame here with five men, and the first in which the
// *armed* side is the one with two like pieces.  Both facts break something.
//
// The index breaks because the configuration is a queen square and an
// unordered bishop pair at once, which index.hpp has no shape for; see
// indexbb.hpp.  The solver breaks because Black is armed, so the table is
// signed and it converts -- and unlike KQKR it converts into a table that is
// not a bare-king endgame:
//
//   * White's QxB or KxB leaves king and queen against king and bishop, which
//     is KQKB, solved by kqkr.cpp.  There is no shortcut for its value: a
//     queen against a bishop is usually a win, sometimes a draw, and nothing
//     here may assume which.
//   * Black's ...BxQ or ...KxQ leaves a bare white king against king and two
//     bishops, which is the KBBK table read with the colours swapped -- a
//     black win when the bishops are on opposite colours and the king is not
//     stalemated, a draw when they are on the same colour.
//
// Neither conversion can be reached backwards from inside this table, a
// predecessor of a capture having six men, so both are read forwards out of
// tables already built and enter the induction as ordinary successors.
//
// One thing KQKR could assume and this endgame cannot
// ---------------------------------------------------
// kqkr.cpp rests on "no capture is ever bad for the side making it": QxR
// leaves KQK, which White never loses, and ...RxQ leaves KRK reversed, which
// Black never loses.  Half of that survives here -- ...BxQ leaves Black two
// bishops against a bare king, and Black cannot lose that -- but the other
// half does not.  KQKB contains mates of White, so White taking a bishop can
// in principle walk into one.
//
// A losing conversion is not merely a seeding detail.  A position whose
// longest defence is a capture has no successor inside this table at that
// depth, so the retrograde pass can never propose it as a candidate and it
// would be scored a draw.  Two things close that hole, both in the
// initialisation below: a position whose every move is a capture is settled
// outright from the conversions, and a position that has any *losing*
// conversion is put on a watch list that is re-tested forwards at every ply.
// The list is tiny -- it needs a hanging bishop whose capture loses -- so the
// cost is nil, and with it the solver no longer depends on the assumption at
// all.  (On the boards tested so far KQKB holds no mate of White whatever, so
// the list comes out empty; it is there because "empty at n <= 9" is not a
// theorem.)
#include "table.hpp"

#include <atomic>
#include <map>
#include <random>
#include <set>
#include <chrono>
#include <cstdio>
#include <thread>

namespace kqk {
namespace {

// ---------------------------------------------------------------------------
// Entry encoding, from White's point of view throughout, exactly as kqkr.cpp:
//     v > 0   White mates in v-1 plies
//     v < 0   Black mates in -v-1 plies
//     v == 0  drawn
// ---------------------------------------------------------------------------
inline int16_t wMate(int plies) { return (int16_t)(plies + 1); }
inline int16_t bMate(int plies) { return (int16_t)(-(plies + 1)); }
inline bool isWin (int16_t v) { return v > 0 && v < VK_UNKNOWN && v != VK_DEAD; }
inline bool isLoss(int16_t v) { return v < 0; }
inline int  winPly (int16_t v) { return v - 1; }
inline int  lossPly(int16_t v) { return -v - 1; }

inline int16_t aload(const int16_t* a, U64 i) {
    return std::atomic_ref<int16_t>(const_cast<int16_t&>(a[i])).load(std::memory_order_relaxed);
}
inline void astore(int16_t* a, U64 i, int16_t v) {
    std::atomic_ref<int16_t>(a[i]).store(v, std::memory_order_relaxed);
}

struct Timer {
    std::chrono::steady_clock::time_point t0 = std::chrono::steady_clock::now();
    double s() const {
        return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    }
};

// ---------------------------------------------------------------------------
// Attack tests.  A captured man is passed as -1, and both Geometry::attacks
// and the blocker test treat a negative square as absent, so the same call
// serves before and after a capture.  Five men means three candidate blockers
// on any ray, which is what the three-blocker form of attacks() is for.
// ---------------------------------------------------------------------------
inline bool blackChecked(const Geometry& g, Sq wk, Sq bk, Sq wq, Sq b1, Sq b2) {
    return wq >= 0 && g.attacks(Piece::Queen, wq, bk, wk, b1, b2);
}
inline bool whiteChecked(const Geometry& g, Sq wk, Sq bk, Sq wq, Sq b1, Sq b2) {
    return (b1 >= 0 && g.attacks(Piece::Bishop, b1, wk, bk, wq, b2)) ||
           (b2 >= 0 && g.attacks(Piece::Bishop, b2, wk, bk, wq, b1));
}

// ---------------------------------------------------------------------------
// Forward move generation.  fn(wk, bk, wq, b1, b2, captured) receives the
// position after the move; `captured` is true when the move took a man, in
// which case that man's square is -1.  Only legal moves are produced.
// ---------------------------------------------------------------------------
template <class F>
inline void genWhite(const Geometry& g, Sq wk, Sq bk, Sq wq, Sq b1, Sq b2, F&& fn) {
    // king
    const int f0 = g.file(wk), r0 = g.rank(wk);
    for (int df = -1; df <= 1; ++df)
        for (int dr = -1; dr <= 1; ++dr) {
            if (!df && !dr) continue;
            int f = f0 + df, r = r0 + dr;
            if (!g.onBoard(f, r)) continue;
            Sq t = g.sq(f, r);
            if (t == wq) continue;                       // own queen
            if (g.kingsTouch(t, bk)) continue;           // into the black king
            Sq n1 = (t == b1) ? -1 : b1, n2 = (t == b2) ? -1 : b2;
            if (whiteChecked(g, t, bk, wq, n1, n2)) continue;
            fn(t, bk, wq, n1, n2, n1 < 0 || n2 < 0);
        }
    // queen
    const int qf = g.file(wq), qr = g.rank(wq);
    for (int d = 0; d < 8; ++d) {
        int f = qf + DIR_F[d], r = qr + DIR_R[d];
        while (g.onBoard(f, r)) {
            Sq t = g.sq(f, r);
            if (t == wk || t == bk) break;               // blocked (bk unreachable: illegal)
            const bool cap = (t == b1 || t == b2);
            Sq n1 = (t == b1) ? -1 : b1, n2 = (t == b2) ? -1 : b2;
            if (!whiteChecked(g, wk, bk, t, n1, n2)) fn(wk, bk, t, n1, n2, cap);
            if (cap) break;
            f += DIR_F[d]; r += DIR_R[d];
        }
    }
}

template <class F>
inline void genBlack(const Geometry& g, Sq wk, Sq bk, Sq wq, Sq b1, Sq b2, F&& fn) {
    // king
    const int f0 = g.file(bk), r0 = g.rank(bk);
    for (int df = -1; df <= 1; ++df)
        for (int dr = -1; dr <= 1; ++dr) {
            if (!df && !dr) continue;
            int f = f0 + df, r = r0 + dr;
            if (!g.onBoard(f, r)) continue;
            Sq t = g.sq(f, r);
            if (t == b1 || t == b2) continue;            // own bishop
            if (g.kingsTouch(wk, t)) continue;
            Sq nq = (t == wq) ? -1 : wq;
            if (blackChecked(g, wk, t, nq, b1, b2)) continue;
            fn(wk, t, nq, b1, b2, nq < 0);
        }
    // the two bishops -- the diagonal rays are the odd entries of the
    // direction table.  A bishop may be pinned against its own king, which is
    // why every move is tested for check afterwards rather than before.
    for (int which = 0; which < 2; ++which) {
        const Sq from  = which ? b2 : b1;
        const Sq other = which ? b1 : b2;
        const int bf = g.file(from), br = g.rank(from);
        for (int d = 1; d < 8; d += 2) {
            int f = bf + DIR_F[d], r = br + DIR_R[d];
            while (g.onBoard(f, r)) {
                Sq t = g.sq(f, r);
                if (t == wk || t == bk || t == other) break;   // blocked
                const bool cap = (t == wq);
                Sq nq = cap ? -1 : wq;
                Sq n1 = which ? other : t, n2 = which ? t : other;
                if (!blackChecked(g, wk, bk, nq, n1, n2)) fn(wk, bk, nq, n1, n2, cap);
                if (cap) break;
                f += DIR_F[d]; r += DIR_R[d];
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Un-move generation.  Only non-capturing moves are retracted: a predecessor
// under a capture would have six men and is not in this table.  `fn(wk, bk,
// wq, b1, b2)` receives a legal predecessor with the other side to move.
// ---------------------------------------------------------------------------
template <class F>
inline void retractWhite(const Geometry& g, Sq wk, Sq bk, Sq wq, Sq b1, Sq b2, F&& fn) {
    // the white king came from an adjacent empty square
    const int f0 = g.file(wk), r0 = g.rank(wk);
    for (int df = -1; df <= 1; ++df)
        for (int dr = -1; dr <= 1; ++dr) {
            if (!df && !dr) continue;
            int f = f0 + df, r = r0 + dr;
            if (!g.onBoard(f, r)) continue;
            Sq t = g.sq(f, r);
            if (t == wq || t == b1 || t == b2 || t == bk) continue;
            if (g.kingsTouch(t, bk)) continue;
            if (blackChecked(g, t, bk, wq, b1, b2)) continue;  // black in check, white to move
            fn(t, bk, wq, b1, b2);
        }
    // the queen came from any square she could have travelled from
    forEachMove<Piece::Queen>(g, wq, wk, bk, b1, b2, [&](Sq t) {
        if (!blackChecked(g, wk, bk, t, b1, b2)) fn(wk, bk, t, b1, b2);
        return true;
    });
}

template <class F>
inline void retractBlack(const Geometry& g, Sq wk, Sq bk, Sq wq, Sq b1, Sq b2, F&& fn) {
    const int f0 = g.file(bk), r0 = g.rank(bk);
    for (int df = -1; df <= 1; ++df)
        for (int dr = -1; dr <= 1; ++dr) {
            if (!df && !dr) continue;
            int f = f0 + df, r = r0 + dr;
            if (!g.onBoard(f, r)) continue;
            Sq t = g.sq(f, r);
            if (t == wq || t == b1 || t == b2 || t == wk) continue;
            if (g.kingsTouch(wk, t)) continue;
            if (whiteChecked(g, wk, t, wq, b1, b2)) continue;  // white in check, black to move
            fn(wk, t, wq, b1, b2);
        }
    for (int which = 0; which < 2; ++which) {
        const Sq from  = which ? b2 : b1;
        const Sq other = which ? b1 : b2;
        forEachMove<Piece::Bishop>(g, from, wk, bk, wq, other, [&](Sq t) {
            Sq n1 = which ? other : t, n2 = which ? t : other;
            if (!whiteChecked(g, wk, bk, wq, n1, n2)) fn(wk, bk, wq, n1, n2);
            return true;
        });
    }
}

// ---------------------------------------------------------------------------
// The two conversions, read forwards out of tables this program already has.
// Both return the value of the position *after* the capture, in the encoding
// above.
// ---------------------------------------------------------------------------
struct Conv {
    const TableKQKR& kqkb;   // king and queen against king and bishop
    const Table&     kbbk;   // two bishops and the bare side; colours swapped here

    // White has just taken a bishop: KQKB with Black to move.  That table is
    // signed and White-relative already, so its value carries over unchanged.
    // It is never dead: the capture left five distinct men, kings apart, and
    // the mover is not in check, which is exactly what that table calls legal.
    int16_t afterWhiteTakes(Sq wk, Sq bk, Sq wq, Sq surv) const {
        Pos p; p.wk = wk; p.bk = bk; p.wp[0] = wq; p.wp[1] = surv;
        return kqkb.valueAt(p, false);
    }
    // Black has just taken the queen: a bare white king against king and two
    // bishops, White to move.  In KBBK terms the bishops' owner is "White", so
    // the two kings swap roles and it is the bare side -- "Black" -- to move.
    int16_t afterBlackTakes(Sq wk, Sq bk, Sq b1, Sq b2) const {
        Pos p; p.wk = bk; p.bk = wk; p.wp[0] = b1; p.wp[1] = b2;
        U8 v = kbbk.valueAt(p, false);
        return isDtm(v) ? bMate((int)v) : (int16_t)VK_DRAW;
    }
};

// The value of a capturing move, whichever side made it.
inline int16_t convValue(const Conv& c, bool white, Sq wk, Sq bk, Sq wq, Sq b1, Sq b2) {
    if (white) return c.afterWhiteTakes(wk, bk, wq, b1 < 0 ? b2 : b1);
    return c.afterBlackTakes(wk, bk, b1, b2);
}

} // namespace

// Exposed for the differential move-generator test in tests/.
void kqkbbGenWhiteRaw(const Geometry& g, Sq wk, Sq bk, Sq wq, Sq b1, Sq b2,
                      const std::function<void(Sq, Sq, Sq, Sq, Sq, bool)>& fn) {
    genWhite(g, wk, bk, wq, b1, b2, fn);
}
void kqkbbGenBlackRaw(const Geometry& g, Sq wk, Sq bk, Sq wq, Sq b1, Sq b2,
                      const std::function<void(Sq, Sq, Sq, Sq, Sq, bool)>& fn) {
    genBlack(g, wk, bk, wq, b1, b2, fn);
}

// ---------------------------------------------------------------------------
int16_t TableKQKBB::valueAt(const PosBB& p, bool whiteToMove) const {
    if (!idx.cfgLive(p.wk, p.bk, p.wq, p.b1, p.b2)) return VK_DEAD;
    if (p.b1 == p.b2) return VK_DEAD;
    U64 s;
    if (idx.slotOf(p, s) < 0) return VK_DEAD;
    return whiteToMove ? w[s] : b[s];
}

void TableKQKBB::buildSubTables(int threads, bool progress) const {
    if (kqkb && kbbk) return;
    Timer clock;
    kqkb = std::make_unique<TableKQKR>(n, Endgame::KQKB);
    kqkb->generate(threads, false);
    kbbk = std::make_unique<Table>(n, Endgame::KBBK);
    kbbk->generate(threads, false);
    if (progress)
        std::fprintf(stderr, "  sub-tables KQKB and KBBK built, %.2fs\n", clock.s());
}

void TableKQKBB::generate(int threads, bool progress) {
    const Geometry& g = geo;
    const int  nsq   = g.nsq;
    const U32  npc   = idx.npc;
    const U64  nkk   = idx.nkk;
    const U64  npair = idx.npair;
    Timer clock;

    w.assign(idx.nslots, VK_DEAD);
    b.assign(idx.nslots, VK_DEAD);

    buildSubTables(threads, progress);
    const Conv conv{*kqkb, *kbbk};

    // ---- initialisation ---------------------------------------------------
    // Dead slots, mates, stalemates, the conversion seeds, and the two devices
    // that make a losing conversion safe: a position with no non-capturing
    // move is settled here outright, and a position with a losing conversion
    // joins the watch list re-tested at every ply.
    std::atomic<U64> nMateW{0}, nMateB{0};
    std::atomic<int> seedMax{0};
    std::vector<std::vector<U64>> watchW(threads > 0 ? threads : 1),
                                  watchB(threads > 0 ? threads : 1);
    parallelFor(nkk, 8, threads, [&](U64 lo, U64 hi, int tid) {
        U64 lw = 0, lb = 0; int lseed = 0;
        auto& wW = watchW[tid];
        auto& wB = watchB[tid];
        for (U64 kk = lo; kk < hi; ++kk) {
            const Sq wk = idx.kkWk[kk], bk = idx.kkBk[kk];
            const U64 base = kk * npc;
            for (Sq wq = 0; wq < nsq; ++wq) {
                if (wq == wk || wq == bk) continue;
                const U64 qbase = base + (U64)wq * npair;
                for (U32 pid = 0; pid < npair; ++pid) {
                    const Sq b1 = idx.pairA[pid], b2 = idx.pairB[pid];
                    if (b1 == wk || b1 == bk || b1 == wq) continue;
                    if (b2 == wk || b2 == bk || b2 == wq) continue;
                    if (!idx.cfgIsCanonical((int32_t)kk, wq, b1, b2)) continue;
                    const U64 s = qbase + pid;

                    // White to move: legal unless Black stands in check.
                    if (!blackChecked(g, wk, bk, wq, b1, b2)) {
                        int moves = 0, quiet = 0;
                        int16_t best = VK_UNKNOWN;     // shortest winning capture
                        int worstBad = -1;             // longest losing capture
                        bool allBad = true;
                        genWhite(g, wk, bk, wq, b1, b2,
                                 [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2, bool cap) {
                            ++moves;
                            if (!cap) { ++quiet; allBad = false; return; }
                            int16_t v = conv.afterWhiteTakes(a, bb, q, c1 < 0 ? c2 : c1);
                            if (isWin(v) && (best == VK_UNKNOWN || v < best)) best = v;
                            if (isLoss(v)) { if (lossPly(v) > worstBad) worstBad = lossPly(v); }
                            else allBad = false;
                        });
                        if (moves == 0) {
                            const bool chk = whiteChecked(g, wk, bk, wq, b1, b2);
                            w[s] = chk ? bMate(0) : (int16_t)VK_DRAW;
                            if (chk) ++lw;
                        } else if (best != VK_UNKNOWN) {
                            int16_t seed = wMate(winPly(best) + 1);
                            w[s] = seed;
                            if (winPly(seed) > lseed) lseed = winPly(seed);
                        } else if (quiet == 0) {
                            // Every move is a capture, so the conversions say
                            // everything there is to say about this position.
                            w[s] = allBad ? bMate(worstBad + 1) : (int16_t)VK_DRAW;
                            if (allBad && worstBad + 1 > lseed) lseed = worstBad + 1;
                        } else {
                            w[s] = VK_UNKNOWN;
                            if (worstBad >= 0) wW.push_back(s);
                        }
                    }
                    // Black to move: legal unless White stands in check.
                    if (!whiteChecked(g, wk, bk, wq, b1, b2)) {
                        int moves = 0, quiet = 0;
                        int16_t best = VK_UNKNOWN;     // shortest capture winning for Black
                        int worstBad = -1;
                        bool allBad = true;
                        genBlack(g, wk, bk, wq, b1, b2,
                                 [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2, bool cap) {
                            ++moves;
                            if (!cap) { ++quiet; allBad = false; return; }
                            int16_t v = conv.afterBlackTakes(a, bb, c1, c2);
                            (void)q;
                            if (isLoss(v) && (best == VK_UNKNOWN || v > best)) best = v;
                            if (isWin(v)) { if (winPly(v) > worstBad) worstBad = winPly(v); }
                            else allBad = false;
                        });
                        if (moves == 0) {
                            const bool chk = blackChecked(g, wk, bk, wq, b1, b2);
                            b[s] = chk ? wMate(0) : (int16_t)VK_DRAW;
                            if (chk) ++lb;
                        } else if (best != VK_UNKNOWN) {
                            int16_t seed = bMate(lossPly(best) + 1);
                            b[s] = seed;
                            if (lossPly(seed) > lseed) lseed = lossPly(seed);
                        } else if (quiet == 0) {
                            b[s] = allBad ? wMate(worstBad + 1) : (int16_t)VK_DRAW;
                            if (allBad && worstBad + 1 > lseed) lseed = worstBad + 1;
                        } else {
                            b[s] = VK_UNKNOWN;
                            if (worstBad >= 0) wB.push_back(s);
                        }
                    }
                }
            }
        }
        nMateW.fetch_add(lb, std::memory_order_relaxed);   // black mated: White wins
        nMateB.fetch_add(lw, std::memory_order_relaxed);   // white mated: Black wins
        int cur = seedMax.load(std::memory_order_relaxed);
        while (lseed > cur && !seedMax.compare_exchange_weak(cur, lseed)) {}
    });

    std::vector<U64> watchWhite, watchBlack;
    for (auto& v : watchW) watchWhite.insert(watchWhite.end(), v.begin(), v.end());
    for (auto& v : watchB) watchBlack.insert(watchBlack.end(), v.begin(), v.end());
    st.watched = watchWhite.size() + watchBlack.size();

    if (progress)
        std::fprintf(stderr, "  init: %llu king pairs, %llu mates of Black, %llu of White,"
                             " deepest conversion %d plies, %llu watched, %.2fs\n",
                     (unsigned long long)nkk, (unsigned long long)nMateW.load(),
                     (unsigned long long)nMateB.load(), seedMax.load(),
                     (unsigned long long)st.watched, clock.s());

    // ---- backward induction ----------------------------------------------
    int16_t* W = w.data();
    int16_t* B = b.data();
    const int seedCeil = seedMax.load();

    // One slot of the watch list, re-tested forwards.  Run at the *start* of a
    // ply, so that every value it reads was settled at an earlier one: a
    // position resolves at ply d exactly when all of its moves lose for the
    // mover and the most stubborn of them takes d-1 plies.
    auto retest = [&](U64 s, bool wtm, int d) -> bool {
        int16_t* self = wtm ? W : B;
        if (aload(self, s) != VK_UNKNOWN) return false;
        const U64 kk = s / npc;
        const U32 pc = (U32)(s % npc);
        const Sq wk = idx.kkWk[kk], bk = idx.kkBk[kk];
        Sq wq, b1, b2;
        idx.decode(pc, wq, b1, b2);
        int worst = -1; bool all = true;
        auto see = [&](int16_t v) {
            if (!all) return;
            const bool bad = wtm ? isLoss(v) : isWin(v);
            if (!bad) { all = false; return; }
            int pl = wtm ? lossPly(v) : winPly(v);
            if (pl > worst) worst = pl;
        };
        auto step = [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2, bool cap) {
            if (!all) return;
            if (cap) { see(convValue(conv, wtm, a, bb, q, c1, c2)); return; }
            PosBB u{a, q, bb, c1, c2};
            U64 s2;
            if (idx.slotOf(u, s2) < 0) { all = false; return; }
            see(aload(wtm ? B : W, s2));
        };
        if (wtm) genWhite(g, wk, bk, wq, b1, b2, step);
        else     genBlack(g, wk, bk, wq, b1, b2, step);
        if (!all || worst != d - 1) return false;
        astore(self, s, wtm ? bMate(d) : wMate(d));
        return true;
    };

    for (int d = 1;; ++d) {
        if (d > 30000) { std::fprintf(stderr, "error: depth overflow\n"); std::exit(2); }
        std::atomic<U64> made{0};
        if (!(d & 1)) {
            U64 local = 0;
            for (U64 s : watchWhite) local += retest(s, true,  d) ? 1 : 0;
            for (U64 s : watchBlack) local += retest(s, false, d) ? 1 : 0;
            made.fetch_add(local, std::memory_order_relaxed);
        }
        if (d & 1) {
            // Winner to move: retract, and claim any entry not already at
            // least this good.  A conversion seed is an upper bound and may
            // legitimately be improved here.
            parallelFor(nkk, 8, threads, [&](U64 lo, U64 hi, int) {
                U64 local = 0;
                for (U64 kk = lo; kk < hi; ++kk) {
                    const Sq wk = idx.kkWk[kk], bk = idx.kkBk[kk];
                    const U64 base = kk * npc;
                    for (Sq wq = 0; wq < nsq; ++wq) {
                        const U64 qbase = base + (U64)wq * npair;
                        for (U32 pid = 0; pid < npair; ++pid) {
                            const U64 s = qbase + pid;
                            const int16_t vb = B[s], vw = W[s];
                            const bool srcW = isWin(vb)  && winPly(vb)  == d - 1;
                            const bool srcB = isLoss(vw) && lossPly(vw) == d - 1;
                            if (!srcW && !srcB) continue;
                            Sq b1, b2;
                            idx.decodePair(pid, b1, b2);
                            if (srcW) {   // White mates in d-1 with Black to move
                                retractWhite(g, wk, bk, wq, b1, b2,
                                             [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2) {
                                    PosBB t{a, q, bb, c1, c2};
                                    U64 s2;
                                    if (idx.slotOf(t, s2) < 0) return;
                                    int16_t cur = aload(W, s2);
                                    if (cur == VK_DEAD) return;
                                    if (cur == VK_UNKNOWN || (isWin(cur) && winPly(cur) > d)) {
                                        astore(W, s2, wMate(d)); ++local;
                                    }
                                });
                            }
                            if (srcB) {   // Black mates in d-1 with White to move
                                retractBlack(g, wk, bk, wq, b1, b2,
                                             [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2) {
                                    PosBB t{a, q, bb, c1, c2};
                                    U64 s2;
                                    if (idx.slotOf(t, s2) < 0) return;
                                    int16_t cur = aload(B, s2);
                                    if (cur == VK_DEAD) return;
                                    if (cur == VK_UNKNOWN || (isLoss(cur) && lossPly(cur) > d)) {
                                        astore(B, s2, bMate(d)); ++local;
                                    }
                                });
                            }
                        }
                    }
                }
                made.fetch_add(local, std::memory_order_relaxed);
            });
        } else {
            // Loser to move: retraction only proposes candidates, which are
            // then re-tested forwards.  A candidate resolves at ply d exactly
            // when every one of its moves is a win for the opponent and the
            // most stubborn of them takes d-1 plies.
            parallelFor(nkk, 8, threads, [&](U64 lo, U64 hi, int) {
                U64 local = 0;
                for (U64 kk = lo; kk < hi; ++kk) {
                    const Sq wk = idx.kkWk[kk], bk = idx.kkBk[kk];
                    const U64 base = kk * npc;
                    for (Sq wq = 0; wq < nsq; ++wq) {
                        const U64 qbase = base + (U64)wq * npair;
                        for (U32 pid = 0; pid < npair; ++pid) {
                            const U64 s = qbase + pid;
                            const int16_t vw = W[s], vb = B[s];
                            const bool srcW = isWin(vw)  && winPly(vw)  == d - 1;
                            const bool srcB = isLoss(vb) && lossPly(vb) == d - 1;
                            if (!srcW && !srcB) continue;
                            Sq b1, b2;
                            idx.decodePair(pid, b1, b2);
                            if (srcW) {   // candidates: black-to-move losses at ply d
                                retractBlack(g, wk, bk, wq, b1, b2,
                                             [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2) {
                                    PosBB t{a, q, bb, c1, c2};
                                    U64 s2;
                                    if (idx.slotOf(t, s2) < 0) return;
                                    if (aload(B, s2) != VK_UNKNOWN) return;
                                    int worst = -1; bool all = true;
                                    genBlack(g, a, bb, q, c1, c2,
                                             [&](Sq a2, Sq b2k, Sq q2, Sq d1, Sq d2, bool cap) {
                                        if (!all) return;
                                        int16_t v;
                                        if (cap) v = conv.afterBlackTakes(a2, b2k, d1, d2);
                                        else {
                                            PosBB u{a2, q2, b2k, d1, d2};
                                            U64 s3;
                                            if (idx.slotOf(u, s3) < 0) { all = false; return; }
                                            v = aload(W, s3);
                                        }
                                        if (!isWin(v)) { all = false; return; }
                                        if (winPly(v) > worst) worst = winPly(v);
                                    });
                                    if (all && worst == d - 1) { astore(B, s2, wMate(d)); ++local; }
                                });
                            }
                            if (srcB) {   // candidates: white-to-move losses at ply d
                                retractWhite(g, wk, bk, wq, b1, b2,
                                             [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2) {
                                    PosBB t{a, q, bb, c1, c2};
                                    U64 s2;
                                    if (idx.slotOf(t, s2) < 0) return;
                                    if (aload(W, s2) != VK_UNKNOWN) return;
                                    int worst = -1; bool all = true;
                                    genWhite(g, a, bb, q, c1, c2,
                                             [&](Sq a2, Sq b2k, Sq q2, Sq d1, Sq d2, bool cap) {
                                        if (!all) return;
                                        int16_t v;
                                        if (cap) v = conv.afterWhiteTakes(a2, b2k, q2,
                                                                          d1 < 0 ? d2 : d1);
                                        else {
                                            PosBB u{a2, q2, b2k, d1, d2};
                                            U64 s3;
                                            if (idx.slotOf(u, s3) < 0) { all = false; return; }
                                            v = aload(B, s3);
                                        }
                                        if (!isLoss(v)) { all = false; return; }
                                        if (lossPly(v) > worst) worst = lossPly(v);
                                    });
                                    if (all && worst == d - 1) { astore(W, s2, bMate(d)); ++local; }
                                });
                            }
                        }
                    }
                }
                made.fetch_add(local, std::memory_order_relaxed);
            });
        }
        if (progress && made.load())
            std::fprintf(stderr, "  ply %3d: %10llu entries, %.2fs\n",
                         d, (unsigned long long)made.load(), clock.s());
        // Conversion seeds already sit in the arrays, so a ply that changes
        // nothing may still be followed by one that has seeded sources.
        if (!made.load() && d > seedCeil + 1) break;
    }

    // ---- everything still unresolved is a draw, and the census -----------
    st.slots = idx.nslots;
    std::atomic<U64> wWin{0}, wLoss{0}, wDraw{0}, wLegal{0};
    std::atomic<U64> bWin{0}, bLoss{0}, bDraw{0}, bLegal{0};
    std::atomic<int> deepW{-1}, deepB{-1};
    parallelFor(nkk, 8, threads, [&](U64 lo, U64 hi, int) {
        U64 aw = 0, al = 0, ad = 0, an = 0, bw = 0, bl = 0, bd = 0, bn = 0;
        int lw = -1, lb = -1;
        for (U64 kk = lo; kk < hi; ++kk) {
            const U64 base = kk * npc;
            for (U32 pc = 0; pc < npc; ++pc) {
                int16_t& vw = w[base + pc];
                if (vw != VK_DEAD) {
                    if (vw == VK_UNKNOWN) vw = VK_DRAW;
                    ++an;
                    if (isWin(vw))       { ++aw; if (winPly(vw)  > lw) lw = winPly(vw); }
                    else if (isLoss(vw)) { ++al; if (lossPly(vw) > lb) lb = lossPly(vw); }
                    else ++ad;
                }
                int16_t& vb = b[base + pc];
                if (vb != VK_DEAD) {
                    if (vb == VK_UNKNOWN) vb = VK_DRAW;
                    ++bn;
                    if (isWin(vb)) ++bw; else if (isLoss(vb)) ++bl; else ++bd;
                }
            }
        }
        wWin += aw; wLoss += al; wDraw += ad; wLegal += an;
        bWin += bw; bLoss += bl; bDraw += bd; bLegal += bn;
        int cur = deepW.load(std::memory_order_relaxed);
        while (lw > cur && !deepW.compare_exchange_weak(cur, lw)) {}
        cur = deepB.load(std::memory_order_relaxed);
        while (lb > cur && !deepB.compare_exchange_weak(cur, lb)) {}
    });
    st.wLegal = wLegal; st.wWin = wWin; st.wLoss = wLoss; st.wDraw = wDraw;
    st.bLegal = bLegal; st.bWin = bWin; st.bLoss = bLoss; st.bDraw = bDraw;
    st.maxWinPly  = deepW.load() < 0 ? 0 : deepW.load();
    st.maxLossPly = deepB.load() < 0 ? 0 : deepB.load();

    // Recover a position realising each extreme, deterministically: the lowest
    // slot at that depth, so repeated runs name the same one.
    auto findDeepest = [&](bool win, int ply, PosBB& out) {
        for (U64 kk = 0; kk < nkk; ++kk) {
            const U64 base = kk * npc;
            for (U32 pc = 0; pc < npc; ++pc) {
                int16_t v = w[base + pc];
                bool hit = win ? (isWin(v) && winPly(v) == ply)
                               : (isLoss(v) && lossPly(v) == ply);
                if (!hit) continue;
                out.wk = idx.kkWk[kk]; out.bk = idx.kkBk[kk];
                idx.decode(pc, out.wq, out.b1, out.b2);
                return;
            }
        }
    };
    st.histW.assign((size_t)st.maxWinPly + 1, 0);
    for (U64 kk = 0; kk < nkk; ++kk) {
        const U64 base = kk * npc;
        for (U32 pc = 0; pc < npc; ++pc) {
            int16_t v = w[base + pc];
            if (isWin(v)) ++st.histW[(size_t)winPly(v)];
        }
    }
    if (st.wWin)  findDeepest(true,  st.maxWinPly,  st.deepest);
    if (st.wLoss) findDeepest(false, st.maxLossPly, st.deepestLoss);
    st.seconds = clock.s();
}

void kqkbbMoves(const TableKQKBB& t, const PosBB& p, bool whiteToMove,
                const std::function<void(const PosBB&, bool, int16_t)>& fn) {
    t.buildSubTables(1, false);
    const Geometry& g = t.geo;
    const Conv conv{*t.kqkb, *t.kbbk};
    auto emit = [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2, bool cap, bool white) {
        PosBB u{a, q, bb, c1, c2};
        int16_t v = cap ? convValue(conv, white, a, bb, q, c1, c2)
                        : t.valueAt(u, !white);
        fn(u, cap, v);
    };
    if (whiteToMove)
        genWhite(g, p.wk, p.bk, p.wq, p.b1, p.b2,
                 [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2, bool cap) {
            emit(a, bb, q, c1, c2, cap, true); });
    else
        genBlack(g, p.wk, p.bk, p.wq, p.b1, p.b2,
                 [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2, bool cap) {
            emit(a, bb, q, c1, c2, cap, false); });
}

// ---------------------------------------------------------------------------
// Bellman re-derivation: recompute every entry from its successors with the
// forward move generator alone, and compare.  Returns the mismatch count.
// ---------------------------------------------------------------------------
U64 TableKQKBB::verify(int threads, bool progress) const {
    buildSubTables(threads, false);
    const Geometry& g = geo;
    const int nsq   = g.nsq;
    const U32 npc   = idx.npc;
    const U64 nkk   = idx.nkk;
    const U64 npair = idx.npair;
    const Conv conv{*kqkb, *kbbk};
    std::atomic<U64> bad{0};

    parallelFor(nkk, 8, threads, [&](U64 lo, U64 hi, int) {
        U64 local = 0;
        for (U64 kk = lo; kk < hi; ++kk) {
            const Sq wk = idx.kkWk[kk], bk = idx.kkBk[kk];
            const U64 base = kk * npc;
            for (Sq wq = 0; wq < nsq; ++wq) {
                if (wq == wk || wq == bk) continue;
                const U64 qbase = base + (U64)wq * npair;
                for (U32 pid = 0; pid < npair; ++pid) {
                    const Sq b1 = idx.pairA[pid], b2 = idx.pairB[pid];
                    if (b1 == wk || b1 == bk || b1 == wq) continue;
                    if (b2 == wk || b2 == bk || b2 == wq) continue;
                    if (!idx.cfgIsCanonical((int32_t)kk, wq, b1, b2)) continue;
                    const U64 s = qbase + pid;

                    for (int side = 0; side < 2; ++side) {
                        const bool wtm = (side == 0);
                        const int16_t stored = wtm ? w[s] : b[s];
                        const bool legal = wtm ? !blackChecked(g, wk, bk, wq, b1, b2)
                                               : !whiteChecked(g, wk, bk, wq, b1, b2);
                        if (!legal) { if (stored != VK_DEAD) ++local; continue; }

                        int best = -1, worst = -1, moves = 0;
                        bool anyWin = false, allLose = true;
                        auto see = [&](int16_t v) {
                            ++moves;
                            const bool goodForMover = wtm ? isWin(v) : isLoss(v);
                            const bool badForMover  = wtm ? isLoss(v) : isWin(v);
                            if (goodForMover) {
                                int pl = wtm ? winPly(v) : lossPly(v);
                                if (!anyWin || pl < best) best = pl;
                                anyWin = true;
                            }
                            if (!badForMover) allLose = false;
                            else {
                                int pl = wtm ? lossPly(v) : winPly(v);
                                if (pl > worst) worst = pl;
                            }
                        };
                        auto step = [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2, bool cap) {
                            if (cap) { see(convValue(conv, wtm, a, bb, q, c1, c2)); return; }
                            PosBB u{a, q, bb, c1, c2};
                            U64 s2;
                            if (idx.slotOf(u, s2) < 0) { ++moves; allLose = false; return; }
                            see(wtm ? b[s2] : w[s2]);
                        };
                        if (wtm) genWhite(g, wk, bk, wq, b1, b2, step);
                        else     genBlack(g, wk, bk, wq, b1, b2, step);

                        int16_t want;
                        if (moves == 0) {
                            const bool inCheck = wtm ? whiteChecked(g, wk, bk, wq, b1, b2)
                                                     : blackChecked(g, wk, bk, wq, b1, b2);
                            want = inCheck ? (wtm ? bMate(0) : wMate(0)) : (int16_t)VK_DRAW;
                        } else if (anyWin) {
                            want = wtm ? wMate(best + 1) : bMate(best + 1);
                        } else if (allLose) {
                            want = wtm ? bMate(worst + 1) : wMate(worst + 1);
                        } else {
                            want = VK_DRAW;
                        }
                        if (want != stored) ++local;
                    }
                }
            }
        }
        bad.fetch_add(local, std::memory_order_relaxed);
    });
    if (progress)
        std::fprintf(stderr, "  verify: %llu mismatches\n", (unsigned long long)bad.load());
    return bad.load();
}

// ---------------------------------------------------------------------------
// The reference implementation: the same endgame with no symmetry at all, one
// entry per ordered placement, and a different algorithm -- repeated forward
// relaxation to a fixpoint rather than backward induction by ply.  n^10
// entries, so only the smallest boards, but it is what catches indexing bugs,
// which a self-consistency check structurally cannot.
// ---------------------------------------------------------------------------
U64 kqkbbBruteForceCheck(const TableKQKBB& t, bool progress) {
    t.buildSubTables(1, false);
    const Geometry& g = t.geo;
    const int nsq = g.nsq;
    const U64 N = (U64)nsq * nsq * nsq * nsq * nsq;
    std::vector<int16_t> W(N, VK_DEAD), B(N, VK_DEAD);
    auto ix = [&](Sq wk, Sq bk, Sq wq, Sq b1, Sq b2) {
        return ((((U64)wk * nsq + bk) * nsq + wq) * nsq + b1) * nsq + b2;
    };
    const Conv conv{*t.kqkb, *t.kbbk};

    // Every placement, in both sides-to-move.  Both orders of the two bishops
    // are enumerated and stored, so that the comparison at the end tests the
    // index's claim that they name the same position.
    auto forEachPlacement = [&](auto&& body) {
        for (Sq wk = 0; wk < nsq; ++wk)
        for (Sq bk = 0; bk < nsq; ++bk) {
            if (g.kingsTouch(wk, bk)) continue;
            for (Sq wq = 0; wq < nsq; ++wq) {
                if (wq == wk || wq == bk) continue;
                for (Sq b1 = 0; b1 < nsq; ++b1) {
                    if (b1 == wk || b1 == bk || b1 == wq) continue;
                    for (Sq b2 = 0; b2 < nsq; ++b2) {
                        if (b2 == wk || b2 == bk || b2 == wq || b2 == b1) continue;
                        body(wk, bk, wq, b1, b2);
                    }
                }
            }
        }
    };

    // ---- terminals, and how deep a conversion can reach -------------------
    int convCeil = 0;
    forEachPlacement([&](Sq wk, Sq bk, Sq wq, Sq b1, Sq b2) {
        U64 i = ix(wk, bk, wq, b1, b2);
        if (!blackChecked(g, wk, bk, wq, b1, b2)) {
            int mv = 0;
            genWhite(g, wk, bk, wq, b1, b2, [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2, bool cap) {
                ++mv;
                if (!cap) return;
                int16_t v = conv.afterWhiteTakes(a, bb, q, c1 < 0 ? c2 : c1);
                if (isWin(v)  && winPly(v)  + 1 > convCeil) convCeil = winPly(v)  + 1;
                if (isLoss(v) && lossPly(v) + 1 > convCeil) convCeil = lossPly(v) + 1;
            });
            W[i] = mv ? VK_UNKNOWN
                      : (whiteChecked(g, wk, bk, wq, b1, b2) ? bMate(0) : (int16_t)VK_DRAW);
        }
        if (!whiteChecked(g, wk, bk, wq, b1, b2)) {
            int mv = 0;
            genBlack(g, wk, bk, wq, b1, b2, [&](Sq a, Sq bb, Sq, Sq c1, Sq c2, bool cap) {
                ++mv;
                if (!cap) return;
                int16_t v = conv.afterBlackTakes(a, bb, c1, c2);
                if (isLoss(v) && lossPly(v) + 1 > convCeil) convCeil = lossPly(v) + 1;
                if (isWin(v)  && winPly(v)  + 1 > convCeil) convCeil = winPly(v)  + 1;
            });
            B[i] = mv ? VK_UNKNOWN
                      : (blackChecked(g, wk, bk, wq, b1, b2) ? wMate(0) : (int16_t)VK_DRAW);
        }
    });

    // ---- one forward sweep per ply ----------------------------------------
    // Deliberately not the algorithm in generate(): no un-moves, no candidate
    // sets, no symmetry, and no watch list -- a position is settled at ply d
    // purely by looking at what its own moves lead to.
    for (int d = 1;; ++d) {
        U64 made = 0;
        forEachPlacement([&](Sq wk, Sq bk, Sq wq, Sq b1, Sq b2) {
            U64 i = ix(wk, bk, wq, b1, b2);
            for (int side = 0; side < 2; ++side) {
                const bool wtm = (side == 0);
                int16_t cur = wtm ? W[i] : B[i];
                if (cur != VK_UNKNOWN) continue;
                bool wins = false, allLose = true;
                int worst = -1;
                auto see = [&](int16_t v) {
                    const bool moverWins = wtm ? (isWin(v)  && winPly(v)  == d - 1)
                                               : (isLoss(v) && lossPly(v) == d - 1);
                    if (moverWins) wins = true;
                    const bool moverLoses = wtm ? isLoss(v) : isWin(v);
                    if (!moverLoses) allLose = false;
                    else {
                        int pl = wtm ? lossPly(v) : winPly(v);
                        if (pl > worst) worst = pl;
                    }
                };
                auto step = [&](Sq a, Sq bb, Sq q, Sq c1, Sq c2, bool cap) {
                    see(cap ? convValue(conv, wtm, a, bb, q, c1, c2)
                            : (wtm ? B[ix(a, bb, q, c1, c2)] : W[ix(a, bb, q, c1, c2)]));
                };
                if (wtm) genWhite(g, wk, bk, wq, b1, b2, step);
                else     genBlack(g, wk, bk, wq, b1, b2, step);
                if (wins) {
                    (wtm ? W[i] : B[i]) = wtm ? wMate(d) : bMate(d);
                    ++made;
                } else if (allLose && worst == d - 1) {
                    (wtm ? W[i] : B[i]) = wtm ? bMate(d) : wMate(d);
                    ++made;
                }
            }
        });
        if (progress && made)
            std::fprintf(stderr, "  brute ply %d: %llu\n", d, (unsigned long long)made);
        if (!made && d > convCeil + 1) break;
    }
    for (U64 i = 0; i < N; ++i) {
        if (W[i] == VK_UNKNOWN) W[i] = VK_DRAW;
        if (B[i] == VK_UNKNOWN) B[i] = VK_DRAW;
    }

    // ---- compare, placement by placement ----------------------------------
    U64 bad = 0;
    forEachPlacement([&](Sq wk, Sq bk, Sq wq, Sq b1, Sq b2) {
        PosBB p{wk, wq, bk, b1, b2};
        U64 i = ix(wk, bk, wq, b1, b2);
        if (t.valueAt(p, true)  != W[i]) ++bad;
        if (t.valueAt(p, false) != B[i]) ++bad;
    });
    if (progress)
        std::fprintf(stderr, "  brute force: %llu disagreements over %llu placements\n",
                     (unsigned long long)bad, (unsigned long long)N);
    return bad;
}

// ---------------------------------------------------------------------------
// Self-checks for the two components the brute force cannot reach on a large
// board: the move generator and the index.  The brute force stops at n = 5 or
// 6 because it needs n^10 entries, and the Bellman check shares this file's
// move generator, so without these two nothing would test either one at n = 12.
// ---------------------------------------------------------------------------
namespace {

// A deliberately naive legal-move generator: an occupancy board, rays walked
// one square at a time, check detected by scanning.  Shares nothing with the
// generators above beyond board arithmetic.
struct Naive {
    const Geometry& g;
    static constexpr int DIAG[8] = {1,1, -1,1, -1,-1, 1,-1};
    static constexpr int ALL8[16] = {1,0, 1,1, 0,1, -1,1, -1,0, -1,-1, 0,-1, 1,-1};
    explicit Naive(const Geometry& geo) : g(geo) {}

    std::vector<char> board(Sq wk, Sq bk, Sq wq, Sq b1, Sq b2) const {
        std::vector<char> occ(g.nsq, 0);
        for (Sq s : { wk, bk, wq, b1, b2 }) if (s >= 0) occ[s] = 1;
        return occ;
    }
    bool rayHits(Sq from, Sq to, const std::vector<char>& occ,
                 const int* dirs, int ndir) const {
        for (int d = 0; d < ndir; ++d) {
            int f = g.file(from) + dirs[2*d], r = g.rank(from) + dirs[2*d+1];
            while (g.onBoard(f, r)) {
                Sq u = g.sq(f, r);
                if (u == to) return true;
                if (occ[u]) break;
                f += dirs[2*d]; r += dirs[2*d+1];
            }
        }
        return false;
    }
    bool wCheck(Sq wk, Sq bk, Sq wq, Sq b1, Sq b2) const {
        if (g.kingsTouch(wk, bk)) return true;
        auto occ = board(wk, bk, wq, b1, b2);
        return (b1 >= 0 && rayHits(b1, wk, occ, DIAG, 4)) ||
               (b2 >= 0 && rayHits(b2, wk, occ, DIAG, 4));
    }
    bool bCheck(Sq wk, Sq bk, Sq wq, Sq b1, Sq b2) const {
        if (g.kingsTouch(wk, bk)) return true;
        if (wq < 0) return false;
        return rayHits(wq, bk, board(wk, bk, wq, b1, b2), ALL8, 8);
    }
    static U64 key(Sq a, Sq b, Sq c, Sq d, Sq e) {
        // The two bishops are interchangeable, so the key sorts them: a
        // generator that reports the same position twice under two names must
        // not look different from one that reports it once.
        if (d > e) { Sq t = d; d = e; e = t; }
        return ((((U64)(a+1) * 4096 + (b+1)) * 4096 + (c+1)) * 4096 + (d+1)) * 4096 + (e+1);
    }
    void white(Sq wk, Sq bk, Sq wq, Sq b1, Sq b2, std::set<U64>& out) const {
        auto add = [&](Sq a, Sq b, Sq q, Sq c1, Sq c2) {
            if (wCheck(a, b, q, c1, c2)) return;
            out.insert(key(a, b, q, c1, c2));
        };
        for (Sq t = 0; t < g.nsq; ++t) {
            if (t == wk || !g.kingsTouch(wk, t) || t == wq) continue;
            add(t, bk, wq, t == b1 ? -1 : b1, t == b2 ? -1 : b2);
        }
        for (int d = 0; d < 8; ++d) {
            int f = g.file(wq) + ALL8[2*d], r = g.rank(wq) + ALL8[2*d+1];
            while (g.onBoard(f, r)) {
                Sq t = g.sq(f, r);
                if (t == wk || t == bk) break;
                add(wk, bk, t, t == b1 ? -1 : b1, t == b2 ? -1 : b2);
                if (t == b1 || t == b2) break;
                f += ALL8[2*d]; r += ALL8[2*d+1];
            }
        }
    }
    void black(Sq wk, Sq bk, Sq wq, Sq b1, Sq b2, std::set<U64>& out) const {
        auto add = [&](Sq a, Sq b, Sq q, Sq c1, Sq c2) {
            if (bCheck(a, b, q, c1, c2)) return;
            out.insert(key(a, b, q, c1, c2));
        };
        for (Sq t = 0; t < g.nsq; ++t) {
            if (t == bk || !g.kingsTouch(bk, t) || t == b1 || t == b2) continue;
            add(wk, t, t == wq ? -1 : wq, b1, b2);
        }
        for (int which = 0; which < 2; ++which) {
            const Sq from = which ? b2 : b1, other = which ? b1 : b2;
            for (int d = 0; d < 4; ++d) {
                int f = g.file(from) + DIAG[2*d], r = g.rank(from) + DIAG[2*d+1];
                while (g.onBoard(f, r)) {
                    Sq t = g.sq(f, r);
                    if (t == bk || t == wk || t == other) break;
                    add(wk, bk, t == wq ? -1 : wq, which ? other : t, which ? t : other);
                    if (t == wq) break;
                    f += DIAG[2*d]; r += DIAG[2*d+1];
                }
            }
        }
    }
};

} // namespace

U64 kqkbbSelfCheck(int lo, int hi, U64 trials, bool progress) {
    U64 bad = 0;
    for (int n = lo; n <= hi; ++n) {
        Geometry g(n);
        Naive nv(g);
        IndexKQKBB idx(g);
        std::mt19937_64 rng(20260913u + n);
        std::uniform_int_distribution<int> pick(0, g.nsq - 1);
        U64 mgBad = 0, ixBad = 0, tested = 0;
        std::map<U64, U64> slotOwner;      // slot -> the orbit it was first seen from
        for (U64 i = 0; i < trials; ++i) {
            PosBB p;
            p.wk = pick(rng); p.bk = pick(rng); p.wq = pick(rng);
            p.b1 = pick(rng); p.b2 = pick(rng);
            if (!idx.cfgLive(p.wk, p.bk, p.wq, p.b1, p.b2)) continue;
            if (p.wk == p.bk || p.b1 == p.b2) continue;
            if (g.kingsTouch(p.wk, p.bk)) continue;
            ++tested;

            // (a) the index: every D4 image, and both namings of the bishop
            //     pair, must land on the same slot, and no two distinct orbits
            //     may share one.
            U64 s0;
            if (idx.slotOf(p, s0) < 0) { ++ixBad; continue; }
            U64 orbit = ~0ull;
            for (int sym = 0; sym < NSYM; ++sym) {
                for (int swap = 0; swap < 2; ++swap) {
                    PosBB q;
                    q.wk = g.image(sym, p.wk); q.bk = g.image(sym, p.bk);
                    q.wq = g.image(sym, p.wq);
                    q.b1 = g.image(sym, swap ? p.b2 : p.b1);
                    q.b2 = g.image(sym, swap ? p.b1 : p.b2);
                    U64 s;
                    if (idx.slotOf(q, s) < 0 || s != s0) { ++ixBad; break; }
                    Sq a = q.b1, b = q.b2;
                    if (a > b) { Sq t = a; a = b; b = t; }
                    U64 k = Naive::key(q.wk, q.bk, q.wq, a, b);
                    if (k < orbit) orbit = k;
                }
            }
            auto it = slotOwner.find(s0);
            if (it == slotOwner.end()) slotOwner.emplace(s0, orbit);
            else if (it->second != orbit) ++ixBad;

            // (b) the move generators, against the naive ones
            for (int side = 0; side < 2; ++side) {
                const bool wtm = (side == 0);
                if (wtm ? nv.bCheck(p.wk, p.bk, p.wq, p.b1, p.b2)
                        : nv.wCheck(p.wk, p.bk, p.wq, p.b1, p.b2)) continue;
                std::set<U64> mine, theirs;
                auto rec = [&](Sq a, Sq b, Sq q, Sq c1, Sq c2, bool) {
                    mine.insert(Naive::key(a, b, q, c1, c2));
                };
                if (wtm) { kqkbbGenWhiteRaw(g, p.wk, p.bk, p.wq, p.b1, p.b2, rec);
                           nv.white(p.wk, p.bk, p.wq, p.b1, p.b2, theirs); }
                else     { kqkbbGenBlackRaw(g, p.wk, p.bk, p.wq, p.b1, p.b2, rec);
                           nv.black(p.wk, p.bk, p.wq, p.b1, p.b2, theirs); }
                if (mine != theirs) ++mgBad;
            }
        }
        if (progress)
            std::fprintf(stderr, "  n=%2d: %llu placements, %llu move-generator, "
                                 "%llu index disagreements\n", n,
                         (unsigned long long)tested, (unsigned long long)mgBad,
                         (unsigned long long)ixBad);
        bad += mgBad + ixBad;
    }
    return bad;
}

} // namespace kqk
