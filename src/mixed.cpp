// mixed.cpp -- two UNLIKE white men against one black man, capture rules.
//
// Every other capture table in this program has one kind of man a side, which
// is what lets kings.cpp rank the white men as an unordered combination and
// key the conversion lattice on how MANY are left.  Neither holds here.  The
// two white men are told apart, so the white placement is an ordered pair; and
// when Black takes one of them it matters WHICH, because K + Q vs N converts
// into K vs N or into Q vs N and those are different endgames.  The lattice is
// therefore keyed on the surviving man, not on a count:
//
//     {0,1} vs b  ->  {1} vs b   (Black took white man 0)
//                 ->  {0} vs b   (Black took white man 1)
//
// Both destinations are terminal: with one man a side the next capture ends it.
//
// The index is the plain ordered one -- (w0, w1, b) at m^3 slots -- with no D4
// reduction at all.  That costs a factor of eight in memory that this material
// can afford (n = 20 is 256 MB) and buys an implementation that shares no
// index, no move generator and no induction with kings.cpp, so running it on
// two LIKE men and comparing against the reduced solver checks both.
//
// Values are relative to the side to move, as everywhere else here:
//   v > 0  the side to move wins in v plies
//   v < 0  the side to move loses in -v plies
//   v == 0 drawn
#include "table.hpp"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

namespace kqk {
namespace {

using S16 = int16_t;
static const S16 UNK = VC_UNKNOWN;
static const S16 ILL = VC_DEAD;

static const int DF[8] = {  1,  1,  0, -1, -1, -1,  0,  1 };
static const int DR[8] = {  0,  1,  1,  1,  0, -1, -1, -1 };
static const int KF[8] = {  1,  2,  2,  1, -1, -2, -2, -1 };
static const int KR[8] = {  2,  1, -1, -2, -2, -1,  1,  2 };

static const int MAXD = 256;

struct Bd {
    Geometry gm;
    int n, m;
    explicit Bd(int nn) : gm(nn), n(nn), m(nn * nn) {}
};

// Destinations of the man of kind `pc` standing on `s`.  Written independently
// of kings.cpp's genDst, which is the point of the file.
static int gen(const Bd& B, int pc, int s, const int* mine, int nm,
               const int* theirs, int nt, int* dst, int* capOf) {
    int c = 0;
    const int n = B.n, f0 = s % n, r0 = s / n;
    if (pc == CP_KING || pc == CP_KNIGHT) {
        const int* af = pc == CP_KING ? DF : KF;
        const int* ar = pc == CP_KING ? DR : KR;
        for (int d = 0; d < 8; ++d) {
            const int f = f0 + af[d], r = r0 + ar[d];
            if (f < 0 || f >= n || r < 0 || r >= n) continue;
            const int t = r * n + f;
            bool own = false;
            for (int q = 0; q < nm; ++q) if (mine[q] == t) { own = true; break; }
            if (own) continue;
            int cap = -1;
            for (int q = 0; q < nt; ++q) if (theirs[q] == t) { cap = q; break; }
            dst[c] = t; capOf[c] = cap; ++c;
        }
        return c;
    }
    const int d0 = (pc == CP_BISHOP) ? 1 : 0, ds = (pc == CP_QUEEN) ? 1 : 2;
    for (int d = d0; d < 8; d += ds) {
        int f = f0 + DF[d], r = r0 + DR[d];
        for (; f >= 0 && f < n && r >= 0 && r < n; f += DF[d], r += DR[d]) {
            const int t = r * n + f;
            bool own = false;
            for (int q = 0; q < nm; ++q) if (mine[q] == t) { own = true; break; }
            if (own) break;
            int cap = -1;
            for (int q = 0; q < nt; ++q) if (theirs[q] == t) { cap = q; break; }
            dst[c] = t; capOf[c] = cap; ++c;
            if (cap >= 0) break;
        }
    }
    return c;
}

// Whether Black taking White's man `j` ends the game there and then.
//
// The rule these tables are meant to obey (kqkkcap.cpp, rule 3, stated "in
// full, for any number of kings a side"): a side that HAS kings is beaten when
// its LAST king is captured, and a side with none when its last man is.  This
// file originally converted every capture into the surviving man's table,
// which is the kingless reading applied to both, and it made ...KxK merely a
// won piece.
//
// The first repair read the captured man alone -- "was it a king?" -- on the
// reasoning that a mixed pair is two UNLIKE men, so at most one of them can be
// a king.  That premise is false, and the header of this very file says why:
// the solver is deliberately run on two ALIKE men, because that is how it
// cross-checks kings.cpp.  KK is a side with two kings, and the predicate
// ended the game on the first one taken.  What ends it is the LAST king, so
// the SURVIVOR has to be looked at too: with two men, the survivor is all that
// is left, and White is only beaten if he is not himself a king.
static inline bool takingEndsIt(int taken, int survivor) {
    return taken == CP_KING && survivor != CP_KING;
}

struct Acc {
    int best = 0, worst = 0, moves = 0;
    bool anyDraw = false, anyUnknown = false;
    inline void add(S16 x) {
        ++moves;
        if (x == UNK) { anyUnknown = true; return; }
        if (x < 0) { int q = -x + 1; if (!best || q < best) best = q; }
        else if (x > 0) { if (x + 1 > worst) worst = x + 1; }
        else anyDraw = true;
    }
    inline void winNow() { ++moves; if (!best || best > 1) best = 1; }
};

static inline S16 settle(const Acc& a, int k, int& pend) {
    if (a.best && a.best <= k) return (S16)a.best;
    if (a.best) { if (a.best > pend) pend = a.best; return UNK; }
    if (a.anyUnknown) return UNK;
    if (!a.moves || a.anyDraw) return 0;
    return (S16)-a.worst;
}

// One white man against one black man.  Self-contained: the next capture on
// either side ends the game, so nothing is read and nothing converts.
struct T1 {
    int m = 0, pw = 0, pb = 0, maxAbs = 0;
    std::vector<S16> v[2];
    inline S16 at(int w, int b, int stm) const { return v[stm][(size_t)w * m + b]; }
};

static void solve1(const Bd& B, int pw, int pb, T1& t) {
    const int m = B.m;
    t.m = m; t.pw = pw; t.pb = pb;
    t.v[0].assign((size_t)m * m, UNK);
    t.v[1].assign((size_t)m * m, UNK);
    for (int w = 0; w < m; ++w) t.v[0][(size_t)w * m + w] = t.v[1][(size_t)w * m + w] = ILL;

    int dst[MAXD], cap[MAXD];
    for (int k = 1;; ++k) {
        int ch = 0, pend = 0;
        for (int w = 0; w < m; ++w)
            for (int b = 0; b < m; ++b) {
                if (w == b) continue;
                const size_t i = (size_t)w * m + b;
                for (int stm = 0; stm < 2; ++stm) {
                    if (t.v[stm][i] != UNK) continue;
                    const int me = stm == 0 ? w : b, him = stm == 0 ? b : w;
                    const int pc = stm == 0 ? pw : pb;
                    Acc a;
                    const int nd = gen(B, pc, me, &me, 1, &him, 1, dst, cap);
                    for (int d = 0; d < nd; ++d) {
                        if (cap[d] >= 0) { a.winNow(); continue; }   // his last man
                        a.add(stm == 0 ? t.v[1][(size_t)dst[d] * m + b]
                                       : t.v[0][(size_t)w * m + dst[d]]);
                    }
                    S16 nv = settle(a, k, pend);
                    if (nv != UNK) { t.v[stm][i] = nv; ++ch; }
                }
            }
        if (!ch && pend <= k) break;
    }
    for (int stm = 0; stm < 2; ++stm)
        for (auto& x : t.v[stm]) if (x == UNK) x = 0;
    t.maxAbs = 0;
    for (int stm = 0; stm < 2; ++stm)
        for (S16 x : t.v[stm]) { if (x == ILL) continue; int q = x < 0 ? -x : x; if (q > t.maxAbs) t.maxAbs = q; }
}

// Two unlike white men against one black man.
struct T2 {
    int m = 0, p0 = 0, p1 = 0, pb = 0, maxAbs = 0;
    std::vector<S16> v[2];
    inline size_t ix(int w0, int w1, int b) const { return ((size_t)w0 * m + w1) * m + b; }
    inline S16 at(int w0, int w1, int b, int stm) const { return v[stm][ix(w0, w1, b)]; }
};

static void solve2(const Bd& B, T2& t, const T1& keep0, const T1& keep1, int nthr) {
    const int m = B.m;
    const size_t N = (size_t)m * m * m;
    t.m = m;
    t.v[0].assign(N, UNK); t.v[1].assign(N, UNK);
    for (int a = 0; a < m; ++a)
        for (int c = 0; c < m; ++c)
            for (int e = 0; e < m; ++e)
                if (a == c || a == e || c == e) {
                    t.v[0][t.ix(a, c, e)] = ILL; t.v[1][t.ix(a, c, e)] = ILL;
                }

    const int subMax = std::max(keep0.maxAbs, keep1.maxAbs);
    for (int k = 1;; ++k) {
        std::atomic<int> ch{0}, pendA{0};
        auto worker = [&](int lo, int hi) {
            int dst[MAXD], cap[MAXD];
            int loc = 0, pend = 0;
            for (int w0 = lo; w0 < hi; ++w0)
                for (int w1 = 0; w1 < m; ++w1) {
                    if (w1 == w0) continue;
                    for (int b = 0; b < m; ++b) {
                        if (b == w0 || b == w1) continue;
                        const size_t i = t.ix(w0, w1, b);
                        for (int stm = 0; stm < 2; ++stm) {
                            if (t.v[stm][i] != UNK) continue;
                            Acc a;
                            if (stm == 0) {
                                const int mine[2] = { w0, w1 };
                                for (int j = 0; j < 2; ++j) {
                                    const int pc = j == 0 ? t.p0 : t.p1;
                                    const int nd = gen(B, pc, mine[j], mine, 2, &b, 1, dst, cap);
                                    for (int d = 0; d < nd; ++d) {
                                        if (cap[d] >= 0) { a.winNow(); continue; }  // his last man
                                        a.add(j == 0 ? t.v[1][t.ix(dst[d], w1, b)]
                                                     : t.v[1][t.ix(w0, dst[d], b)]);
                                    }
                                }
                            } else {
                                const int theirs[2] = { w0, w1 };
                                const int nd = gen(B, t.pb, b, &b, 1, theirs, 2, dst, cap);
                                for (int d = 0; d < nd; ++d) {
                                    if (cap[d] == 0) {                               // took white man 0
                                        if (takingEndsIt(t.p0, t.p1)) a.winNow();
                                        else a.add(keep1.v[0][(size_t)w1 * m + dst[d]]);
                                    } else if (cap[d] == 1) {                        // took white man 1
                                        if (takingEndsIt(t.p1, t.p0)) a.winNow();
                                        else a.add(keep0.v[0][(size_t)w0 * m + dst[d]]);
                                    } else
                                        a.add(t.v[0][t.ix(w0, w1, dst[d])]);
                                }
                            }
                            S16 nv = settle(a, k, pend);
                            if (nv != UNK) { t.v[stm][i] = nv; ++loc; }
                        }
                    }
                }
            ch += loc;
            int cur = pendA.load();
            while (pend > cur && !pendA.compare_exchange_weak(cur, pend)) {}
        };
        std::vector<std::thread> th;
        const int chunk = (m + nthr - 1) / nthr;
        for (int q = 0; q < nthr; ++q) {
            int lo = std::min(q * chunk, m), hi = std::min(lo + chunk, m);
            if (lo < hi) th.emplace_back(worker, lo, hi);
        }
        for (auto& x : th) x.join();
        if (!ch.load() && pendA.load() <= k && k > subMax) break;
        if (k > 40000) { std::printf("      RUNAWAY\n"); break; }
    }
    for (int stm = 0; stm < 2; ++stm)
        for (auto& x : t.v[stm]) if (x == UNK) x = 0;
    t.maxAbs = 0;
    for (int stm = 0; stm < 2; ++stm)
        for (S16 x : t.v[stm]) { if (x == ILL) continue; int q = x < 0 ? -x : x; if (q > t.maxAbs) t.maxAbs = q; }
}

// --------------------------------------------------------------------------
// Out-counting (frontier) solver for the two-man table.
// --------------------------------------------------------------------------
// The sweep solver above rescans the array once per ply, so every entry is
// evaluated O(D) times -- measured on this project's tables at 17 to 95 times.
// Out-counting evaluates each entry once and thereafter touches it only
// through its predecessors: O(b) work per entry, independent of D.
//
// Two properties make it EXACT here, and both are worth stating because
// neither holds for the D4-reduced solver in kings.cpp:
//
//   * No move inside T2 is a capture.  White taking the black man ends the
//     game, and Black taking a white man leaves T2 for a T1 table.  So the
//     in-table successor graph is exactly the non-capture move graph.
//   * This index is unreduced, so the reverse of a non-capture move is the
//     same generator run backwards, and each (predecessor, successor) pair
//     arises from exactly one move.  The counter is therefore exact, with no
//     symmetry multiplicity to correct.
//
// `outs[p]` counts the successors of p NOT yet known to be wins for the
// opponent.  When it reaches zero every move walks into a win, so p is lost,
// and the loss depth is one more than the SLOWEST of those wins -- which is
// what `mw[p]` tracks.  A terminal win, a drawn conversion and a losing
// conversion all count toward `outs`, precisely so that it can never reach
// zero for a position that is not lost.  Events are processed in increasing
// depth, so the first one to reach a position carries its true distance and
// later ones are discarded.
struct Ev { int d; uint32_t key; bool win; };

// Predecessors of (w0,w1,b,stm) inside T2: the previous mover is the other
// side and it arrived by a non-capture, so run its generator backwards from
// the square it now stands on and keep the empty destinations.
template <class F>
static inline void forEachPred(const Bd& B, const T2& t, int w0, int w1, int b, int stm,
                               int* dst, int* cap, F fn) {
    if (stm == 0) {                        // Black moved last, into b
        const int theirs[2] = { w0, w1 };
        const int nd = gen(B, t.pb, b, &b, 1, theirs, 2, dst, cap);
        for (int d = 0; d < nd; ++d)
            if (cap[d] < 0) fn(t.ix(w0, w1, dst[d]), 1);
    } else {                               // White moved last, into w0 or w1
        const int mine[2] = { w0, w1 };
        for (int j = 0; j < 2; ++j) {
            const int pc = j == 0 ? t.p0 : t.p1;
            const int nd = gen(B, pc, mine[j], mine, 2, &b, 1, dst, cap);
            for (int d = 0; d < nd; ++d) {
                if (cap[d] >= 0) continue;
                fn(j == 0 ? t.ix(dst[d], w1, b) : t.ix(w0, dst[d], b), 0);
            }
        }
    }
}

static bool frontier2(const Bd& B, T2& t, const T1& keep0, const T1& keep1, int nthr) {
    const int m = B.m;
    const size_t N = (size_t)m * m * m;
    if ((N << 1) >> 32) return false;                  // bucket keys are 32-bit

    t.m = m;
    t.v[0].assign(N, UNK); t.v[1].assign(N, UNK);
    std::vector<uint8_t>  outs[2];
    std::vector<uint16_t> mw[2];
    for (int s = 0; s < 2; ++s) { outs[s].assign(N, 0); mw[s].assign(N, 0); }

    for (int a = 0; a < m; ++a)
        for (int c = 0; c < m; ++c)
            for (int e = 0; e < m; ++e)
                if (a == c || a == e || c == e) {
                    t.v[0][t.ix(a, c, e)] = ILL; t.v[1][t.ix(a, c, e)] = ILL;
                }

    // ---- init: one forward evaluation per entry, in parallel ----------
    std::vector<std::vector<Ev>> tev(nthr);
    std::atomic<bool> tooWide{false};
    auto initer = [&](int q, int lo, int hi) {
        int dst[MAXD], cap[MAXD];
        std::vector<Ev>& ev = tev[q];
        for (int w0 = lo; w0 < hi; ++w0)
            for (int w1 = 0; w1 < m; ++w1) {
                if (w1 == w0) continue;
                for (int b = 0; b < m; ++b) {
                    if (b == w0 || b == w1) continue;
                    const size_t i = t.ix(w0, w1, b);
                    const int mine[2] = { w0, w1 };
                    // White to move: every move is in-table or ends the game.
                    {
                        int nm = 0; bool term = false;
                        for (int j = 0; j < 2; ++j) {
                            const int pc = j == 0 ? t.p0 : t.p1;
                            const int nd = gen(B, pc, mine[j], mine, 2, &b, 1, dst, cap);
                            nm += nd;
                            for (int d = 0; d < nd; ++d) if (cap[d] >= 0) term = true;
                        }
                        if (nm > 255) { tooWide = true; return; }
                        if (term)          ev.push_back({ 1, (uint32_t)(i << 1), true });
                        else if (nm == 0)  t.v[0][i] = 0;                 // stalemate
                        else               outs[0][i] = (uint8_t)nm;
                    }
                    // Black to move: a capture converts into a T1 table.
                    {
                        const int theirs[2] = { w0, w1 };
                        const int nd = gen(B, t.pb, b, &b, 1, theirs, 2, dst, cap);
                        if (nd > 255) { tooWide = true; return; }
                        int o = 0, best = 0, mx = 0;
                        for (int d = 0; d < nd; ++d) {
                            if (cap[d] < 0) { ++o; continue; }
                            const bool tookW0 = (theirs[cap[d]] == w0);
                            if (takingEndsIt(tookW0 ? t.p0 : t.p1, tookW0 ? t.p1 : t.p0)) {
                                if (!best || best > 1) best = 1;   // Black wins on the spot
                                ++o;
                                continue;
                            }
                            const S16 sv = tookW0
                                ? keep1.v[0][(size_t)w1 * m + dst[d]]
                                : keep0.v[0][(size_t)w0 * m + dst[d]];
                            if (sv < 0) { const int qd = -sv + 1; if (!best || qd < best) best = qd; ++o; }
                            else if (sv > 0) { if (sv > mx) mx = sv; }
                            else ++o;
                        }
                        if (nd == 0) t.v[1][i] = 0;                       // stalemate
                        else if (best) ev.push_back({ best, (uint32_t)((i << 1) | 1), true });
                        else if (o == 0) ev.push_back({ mx + 1, (uint32_t)((i << 1) | 1), false });
                        else { outs[1][i] = (uint8_t)o; mw[1][i] = (uint16_t)mx; }
                    }
                }
            }
    };
    {
        std::vector<std::thread> th;
        const int chunk = (m + nthr - 1) / nthr;
        for (int q = 0; q < nthr; ++q) {
            int lo = std::min(q * chunk, m), hi = std::min(lo + chunk, m);
            if (lo < hi) th.emplace_back(initer, q, lo, hi);
        }
        for (auto& x : th) x.join();
    }
    if (tooWide.load()) return false;                  // fan-out will not fit a byte

    std::vector<std::vector<uint32_t>> bwin(2), blos(2);
    int maxSched = 0;
    auto push = [&](bool win, int d, uint32_t key) {
        auto& bk = win ? bwin : blos;
        if ((int)bk.size() <= d) bk.resize(d + 1);
        bk[d].push_back(key);
        if (d > maxSched) maxSched = d;
    };
    for (auto& ev : tev) {
        for (const Ev& e : ev) push(e.win, e.d, e.key);
        ev.clear(); ev.shrink_to_fit();
    }

    // ---- propagate, strictly in increasing depth ----------------------
    int dst[MAXD], cap[MAXD];
    for (int d = 1; d <= maxSched; ++d) {
        if (d > 40000) { std::printf("      RUNAWAY\n"); break; }
        if (d < (int)bwin.size())
            for (size_t z = 0; z < bwin[d].size(); ++z) {
                const uint32_t key = bwin[d][z];
                const size_t i = key >> 1; const int stm = key & 1;
                if (t.v[stm][i] != UNK) continue;
                t.v[stm][i] = (S16)d;
                const int w0 = (int)(i / ((size_t)m * m)), w1 = (int)((i / m) % m), b = (int)(i % m);
                forEachPred(B, t, w0, w1, b, stm, dst, cap, [&](size_t pi, int ps) {
                    if (t.v[ps][pi] != UNK) return;
                    uint8_t& oo = outs[ps][pi];
                    if (!oo) return;
                    if ((uint16_t)d > mw[ps][pi]) mw[ps][pi] = (uint16_t)d;
                    if (--oo == 0) push(false, (int)mw[ps][pi] + 1, (uint32_t)((pi << 1) | (size_t)ps));
                });
            }
        if (d < (int)blos.size())
            for (size_t z = 0; z < blos[d].size(); ++z) {
                const uint32_t key = blos[d][z];
                const size_t i = key >> 1; const int stm = key & 1;
                if (t.v[stm][i] != UNK) continue;
                t.v[stm][i] = (S16)(-d);
                const int w0 = (int)(i / ((size_t)m * m)), w1 = (int)((i / m) % m), b = (int)(i % m);
                forEachPred(B, t, w0, w1, b, stm, dst, cap, [&](size_t pi, int ps) {
                    if (t.v[ps][pi] != UNK) return;
                    push(true, d + 1, (uint32_t)((pi << 1) | (size_t)ps));
                });
            }
        if (d < (int)bwin.size()) { bwin[d].clear(); bwin[d].shrink_to_fit(); }
        if (d < (int)blos.size()) { blos[d].clear(); blos[d].shrink_to_fit(); }
    }

    for (int stm = 0; stm < 2; ++stm)
        for (auto& x : t.v[stm]) if (x == UNK) x = 0;
    t.maxAbs = 0;
    for (int stm = 0; stm < 2; ++stm)
        for (S16 x : t.v[stm]) { if (x == ILL) continue; int q = x < 0 ? -x : x; if (q > t.maxAbs) t.maxAbs = q; }
    return true;
}

}  // namespace

// ---------------------------------------------------------------------------
// The whole lattice, solved: the two one-man tables Black's capture converts
// into, and the pair against the man.  Written once and called from both the
// command below and TableMixed, so the two can never disagree about which
// induction ran or under what conditions.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The table store.
// ---------------------------------------------------------------------------
// `mixed` is UNREDUCED -- no D4, every placement its own entry -- so a
// configuration is m*m*m entries a side for the two-man table and m*m for each
// of the one-man tables a capture converts into.  That is small: 2.9 M
// placements at n = 12, 11 MB the lot.  Small enough that the file is read
// rather than mapped, and that all three tables of a configuration live in one
// file: they are solved together and are useless apart.
//
// The name cannot be the kings lattice's.  Two LIKE white men spell the same
// material there -- `mixed --w1 king --w2 king` is KKvK, and so is `kings
// --white 2` -- but the two index it differently, so they must never be handed
// each other's files.  Hence the .mx extension AND an identity in the header,
// the same belt and braces the kings store uses.
struct MxHeader {
    char    magic[8];          // "MIXEDTB"
    U32     version;
    U32     n;
    U32     p0, p1, pb;
    U32     pad;               // explicit: the layout is not the compiler's choice
    U64     m;
    U64     n1, n2;            // entries a side: m*m for a T1, m*m*m for the T2
    int64_t maxAbs0, maxAbs1, maxAbs2;
    U64     hash;              // over the payload, to catch a truncated file
};
static_assert(sizeof(MxHeader) == 88, "the on-disk mixed header is fixed at 88 bytes");
// Version 2: a white pair holding a king means something different from what
// it meant in version 1.  A file records values, not rules, and mxLoad checks
// the magic, the board, the piece kinds and a payload hash -- none of which
// can tell a table solved under "a side dies with its last man" from one
// solved under "a side dies with its last king".  A version 1 file would have
// passed every one of those checks and been served as if it were right, so the
// version is the only thing that can retire it.  Bumping it turns every file
// on disk into a miss, which re-solves and rewrites it; no file has to be
// found and deleted by hand, and none can survive by being overlooked.
//
// Version 3: version 2 read the captured man alone and so ended the game on
// the first of TWO kings, which is a side that is not beaten at all.  It is
// wrong for exactly the five KK shapes and right for the other seventy, and a
// version 2 file of one of those five has to be retired for the same reason a
// version 1 file did.  Measured against the version 1 files still on disk, the
// payload of all five is byte-identical to version 1 again, and the twenty
// shapes whose white pair holds exactly ONE king are the only ones that differ
// from version 1 at all.
static const U32 MX_VERSION = 3;

static U64 mxHash(const void* p, size_t nbytes) {
    const unsigned char* q = (const unsigned char*)p;
    U64 h = 1469598103934665603ull;
    for (size_t i = 0; i < nbytes; ++i) { h ^= q[i]; h *= 0x100000001b3ull; }
    return h;
}

static std::string mxName(int p0, int p1, int pb, int n) {
    char b[64];
    std::snprintf(b, sizeof b, "%c%cv%c-n%d.mx", capPieceLetter(p0), capPieceLetter(p1),
                  capPieceLetter(pb), n);
    return b;
}

// Written to .part and renamed, so an interrupted run leaves nothing a later
// one will read: the loader only ever opens the final name.
static bool mxSave(const std::string& path, int n, const T1& k0, const T1& k1, const T2& t) {
    MxHeader h{};
    std::memcpy(h.magic, "MIXEDTB", 8);
    h.version = MX_VERSION; h.n = (U32)n; h.m = (U64)t.m;
    h.p0 = (U32)t.p0; h.p1 = (U32)t.p1; h.pb = (U32)t.pb;
    h.n1 = (U64)k0.v[0].size(); h.n2 = (U64)t.v[0].size();
    h.maxAbs0 = k0.maxAbs; h.maxAbs1 = k1.maxAbs; h.maxAbs2 = t.maxAbs;

    std::vector<S16> pay;
    pay.reserve(h.n1 * 4 + h.n2 * 2);
    for (int s = 0; s < 2; ++s) pay.insert(pay.end(), k0.v[s].begin(), k0.v[s].end());
    for (int s = 0; s < 2; ++s) pay.insert(pay.end(), k1.v[s].begin(), k1.v[s].end());
    for (int s = 0; s < 2; ++s) pay.insert(pay.end(), t.v[s].begin(), t.v[s].end());
    h.hash = mxHash(pay.data(), pay.size() * sizeof(S16));

    const std::string tmp = path + ".part";
    std::FILE* f = std::fopen(tmp.c_str(), "wb");
    if (!f) { std::fprintf(stderr, "mixed: cannot write %s\n", tmp.c_str()); return false; }
    bool ok = std::fwrite(&h, sizeof h, 1, f) == 1 &&
              std::fwrite(pay.data(), sizeof(S16), pay.size(), f) == pay.size();
    if (std::fclose(f) != 0) ok = false;
    if (!ok) { std::remove(tmp.c_str()); std::fprintf(stderr, "mixed: short write %s\n", tmp.c_str()); return false; }
    if (std::rename(tmp.c_str(), path.c_str()) != 0) {
        std::remove(tmp.c_str());
        std::fprintf(stderr, "mixed: cannot rename %s into place\n", tmp.c_str());
        return false;
    }
    return true;
}

// A file that does not match what was asked for is a MISS, not an error: the
// caller solves instead, exactly as if it had not been there.
static bool mxLoad(const std::string& path, int m, int p0, int p1, int pb,
                   T1& k0, T1& k1, T2& t) {
    std::FILE* f = std::fopen(path.c_str(), "rb");
    if (!f) return false;
    MxHeader h{};
    if (std::fread(&h, sizeof h, 1, f) != 1) { std::fclose(f); return false; }
    const U64 n1 = (U64)m * m, n2 = (U64)m * m * m;
    if (std::memcmp(h.magic, "MIXEDTB", 8) != 0 || h.version != MX_VERSION ||
        h.m != (U64)m || h.p0 != (U32)p0 || h.p1 != (U32)p1 || h.pb != (U32)pb ||
        h.n1 != n1 || h.n2 != n2) { std::fclose(f); return false; }
    std::vector<S16> pay(n1 * 4 + n2 * 2);
    if (std::fread(pay.data(), sizeof(S16), pay.size(), f) != pay.size()) { std::fclose(f); return false; }
    std::fclose(f);
    if (mxHash(pay.data(), pay.size() * sizeof(S16)) != h.hash) {
        std::fprintf(stderr, "mixed: %s fails its payload hash -- solving instead\n", path.c_str());
        return false;
    }
    size_t o = 0;
    auto take1 = [&](T1& x, int64_t mx) {
        x.m = m; x.pw = 0; x.pb = pb; x.maxAbs = (int)mx;
        for (int s = 0; s < 2; ++s) { x.v[s].assign(pay.begin() + o, pay.begin() + o + n1); o += n1; }
    };
    take1(k0, h.maxAbs0); take1(k1, h.maxAbs1);
    t.m = m; t.p0 = p0; t.p1 = p1; t.pb = pb; t.maxAbs = (int)h.maxAbs2;
    for (int s = 0; s < 2; ++s) { t.v[s].assign(pay.begin() + o, pay.begin() + o + n2); o += n2; }
    return true;
}

static void solveMixed(const Bd& B, int p0, int p1, int pb, int nthr,
                       T1& keep0, T1& keep1, T2& t, const std::string& store = "",
                       bool* loaded = nullptr) {
    if (loaded) *loaded = false;
    // A configuration already on disk is used as it stands, all three of its
    // tables together.  Same bargain as the kings store: solved once, read
    // thereafter, and a file that does not match is a miss rather than an error.
    if (!store.empty()) {
        const std::string path = store + "/" + mxName(p0, p1, pb, B.n);
        if (mxLoad(path, B.m, p0, p1, pb, keep0, keep1, t)) {
            if (loaded) *loaded = true;
            return;
        }
    }
    solve1(B, p0, pb, keep0);
    solve1(B, p1, pb, keep1);
    t.p0 = p0; t.p1 = p1; t.pb = pb;
    // EGTB_SWEEP forces the old full-sweep induction; EGTB_CHECKFRONTIER runs
    // BOTH and compares every entry, which is the correctness gate for the
    // frontier solver.  The frontier declines (returns false) when the index
    // or the fan-out will not fit its 32-bit keys and one-byte counters, and
    // the sweep solver then runs instead.
    const bool forceSweep = getenv("EGTB_SWEEP") != nullptr;
    const bool crossCheck = getenv("EGTB_CHECKFRONTIER") != nullptr;
    bool usedFrontier = false;
    if (!forceSweep) usedFrontier = frontier2(B, t, keep0, keep1, nthr);
    if (!usedFrontier) solve2(B, t, keep0, keep1, nthr);
    if (crossCheck && usedFrontier) {
        T2 r; r.p0 = p0; r.p1 = p1; r.pb = pb;
        solve2(B, r, keep0, keep1, nthr);
        U64 bad = 0; int firstStm = -1; size_t firstIx = 0;
        for (int stm = 0; stm < 2; ++stm)
            for (size_t q = 0; q < r.v[stm].size(); ++q)
                if (r.v[stm][q] != t.v[stm][q]) {
                    if (!bad) { firstStm = stm; firstIx = q; }
                    ++bad;
                }
        if (bad)
            std::fprintf(stderr, "  [frontier] n=%d MISMATCH %llu entries; first stm=%d ix=%llu "
                                 "sweep=%d frontier=%d\n", B.n, (unsigned long long)bad, firstStm,
                         (unsigned long long)firstIx, (int)r.v[firstStm][firstIx],
                         (int)t.v[firstStm][firstIx]);
        else
            std::fprintf(stderr, "  [frontier] n=%d identical to the sweep solver "
                                 "(%llu entries, maxAbs %d)\n",
                         B.n, (unsigned long long)(2 * r.v[0].size()), r.maxAbs);
    }
    // Written only once the whole configuration is solved, so a file on disk
    // is always a complete one.
    if (!store.empty()) mxSave(store + "/" + mxName(p0, p1, pb, B.n), B.n, keep0, keep1, t);
}

// --------------------------------------------------------------------------
// The object the browser explorer probes: the same three tables, kept.
// --------------------------------------------------------------------------
struct TableMixed::Impl {
    Bd  B;
    int p0, p1, pb;
    T1  keep0, keep1;
    T2  t;
    bool loaded = false;      // came out of a .mx file rather than solved here
    Impl(int n, int a, int b, int c) : B(n), p0(a), p1(b), pb(c) {}

    // Which table a placement lives in, and its value there.  A white man
    // Black has taken comes in as -1, which is exactly the lattice key: both
    // men on is the pair table, one man on is that man's own table, and no
    // man on is not a position at all -- Black has already won.
    S16 value(int w0, int w1, int b, int stm) const {
        if (b < 0) return 0;
        if (w0 >= 0 && w1 >= 0) {
            if (w0 == w1 || w0 == b || w1 == b) return ILL;
            return t.at(w0, w1, b, stm);
        }
        // One man down.  That is a position only when the man Black took was
        // not White's king; if it was, White is already beaten and there is no
        // table to answer from.
        if (w0 >= 0) {
            if (w0 == b) return ILL;
            if (takingEndsIt(p1, p0)) return ILL;  // the missing man was the last king
            return keep0.at(w0, b, stm);
        }
        if (w1 >= 0) {
            if (w1 == b) return ILL;
            if (takingEndsIt(p0, p1)) return ILL;
            return keep1.at(w1, b, stm);
        }
        return ILL;
    }
};

TableMixed::TableMixed(int edge, int a, int b, int c) : p(new Impl(edge, a, b, c)) {}
TableMixed::~TableMixed() = default;

void TableMixed::generate(int threads, const std::string& store) {
    solveMixed(p->B, p->p0, p->p1, p->pb, threads, p->keep0, p->keep1, p->t, store,
               &p->loaded);
}

bool TableMixed::fromStore() const { return p->loaded; }

int16_t TableMixed::probe(Sq w0, Sq w1, Sq b, bool wtm) const {
    return p->value(w0, w1, b, wtm ? 0 : 1);
}

std::vector<MixedMove> TableMixed::moves(Sq w0, Sq w1, Sq b, bool wtm) const {
    std::vector<MixedMove> out;
    int dst[MAXD], cap[MAXD];
    const Bd& B = p->B;
    if (b < 0 || (w0 < 0 && w1 < 0)) return out;          // the game is over
    if (wtm) {
        const int live[2] = { w0, w1 };
        int mine[2], nm = 0, which[2];
        for (int j = 0; j < 2; ++j) if (live[j] >= 0) { which[nm] = j; mine[nm++] = live[j]; }
        for (int q = 0; q < nm; ++q) {
            const int j  = which[q];
            const int pc = j == 0 ? p->p0 : p->p1;
            const int nd = gen(B, pc, mine[q], mine, nm, &b, 1, dst, cap);
            for (int d = 0; d < nd; ++d) {
                MixedMove M;
                M.from = (Sq)mine[q]; M.to = (Sq)dst[d]; M.mover = j;
                M.capture = cap[d] >= 0;
                M.ends    = cap[d] >= 0;                   // Black's only man
                M.w0 = j == 0 ? (Sq)dst[d] : w0;
                M.w1 = j == 1 ? (Sq)dst[d] : w1;
                M.b  = M.ends ? (Sq)-1 : b;
                M.value = M.ends ? 0 : p->value(M.w0, M.w1, M.b, 1);
                out.push_back(M);
            }
        }
    } else {
        int theirs[2], nt = 0, which[2];
        if (w0 >= 0) { which[nt] = 0; theirs[nt++] = w0; }
        if (w1 >= 0) { which[nt] = 1; theirs[nt++] = w1; }
        const int nd = gen(B, p->pb, b, &b, 1, theirs, nt, dst, cap);
        for (int d = 0; d < nd; ++d) {
            MixedMove M;
            M.from = (Sq)b; M.to = (Sq)dst[d]; M.mover = 0;
            M.capture = cap[d] >= 0;
            M.w0 = w0; M.w1 = w1; M.b = (Sq)dst[d];
            if (cap[d] >= 0) {
                const int took = which[cap[d]];
                if (took == 0) M.w0 = -1; else M.w1 = -1;
                // Taking White's last king ends it even though the other man
                // is still standing, so the board this move leads to is a
                // finished game and not a position to walk on from.
                M.ends = (M.w0 < 0 && M.w1 < 0) ||
                         takingEndsIt(took == 0 ? p->p0 : p->p1,
                                      took == 0 ? p->p1 : p->p0);
            }
            M.value = M.ends ? 0 : p->value(M.w0, M.w1, M.b, 0);
            out.push_back(M);
        }
    }
    return out;
}

bool TableMixed::quiet(Sq w0, Sq w1, Sq b) const {
    if (b < 0 || (w0 < 0 && w1 < 0)) return false;
    for (int stm = 0; stm < 2; ++stm)
        for (const MixedMove& M : moves(w0, w1, b, stm == 0))
            if (M.capture) return false;
    return true;
}

bool TableMixed::deepestQuiet(Sq& w0, Sq& w1, Sq& b, int& plies) const {
    const int m = p->B.m;
    int best = 0;
    plies = 0;
    for (int a = 0; a < m; ++a)
        for (int c = 0; c < m; ++c) {
            if (c == a) continue;
            for (int e = 0; e < m; ++e) {
                if (e == a || e == c) continue;
                const S16 v = p->t.at(a, c, e, 0);
                if (v <= best) continue;                  // monotone: rare
                if (!quiet((Sq)a, (Sq)c, (Sq)e)) continue;
                best = v; w0 = (Sq)a; w1 = (Sq)c; b = (Sq)e;
            }
        }
    plies = best;
    return best > 0;
}

bool TableMixed::deepestAny(Sq& w0, Sq& w1, Sq& b, int& plies) const {
    const int m = p->B.m;
    int best = 0;
    plies = 0;
    for (int a = 0; a < m; ++a)
        for (int c = 0; c < m; ++c) {
            if (c == a) continue;
            for (int e = 0; e < m; ++e) {
                if (e == a || e == c) continue;
                const S16 v = p->t.at(a, c, e, 0);
                if (v <= best) continue;
                best = v; w0 = (Sq)a; w1 = (Sq)c; b = (Sq)e;
            }
        }
    plies = best;
    return best > 0;
}

// ---------------------------------------------------------------------------
// The command.
// ---------------------------------------------------------------------------
int runMixed(int n, int p0, int p1, int pb, int nthr, bool wantLine, bool wantQuiet,
             MixedStats& out, const std::string& store) {
    Bd B(n);
    T1 keep0, keep1;                 // the man that survives when Black takes the other
    T2 t;
    solveMixed(B, p0, p1, pb, nthr, keep0, keep1, t, store);
    const int m = B.m;
    out.n = n; out.deepestWhite = 0; out.deepestBlack = 0;
    out.positions = 0;
    out.wWin = out.wDraw = out.wLoss = out.bWin = out.bDraw = out.bLoss = 0;
    out.quiet = out.quietWinW = out.quietWinB = 0;
    out.qwWin = out.qwDraw = out.qwLoss = 0;
    out.qbWin = out.qbDraw = out.qbLoss = 0;
    out.deepestWhiteQuiet = 0; out.posWhiteQuiet.clear();
    out.sub0Win = out.sub0Draw = out.sub0Loss = 0;
    out.sub1Win = out.sub1Draw = out.sub1Loss = 0;
    out.sub0Deep = keep0.maxAbs; out.sub1Deep = keep1.maxAbs;

    int dst[MAXD], cap[MAXD];
    for (int w0 = 0; w0 < m; ++w0)
        for (int w1 = 0; w1 < m; ++w1) {
            if (w1 == w0) continue;
            for (int b = 0; b < m; ++b) {
                if (b == w0 || b == w1) continue;
                ++out.positions;
                const S16 vw = t.at(w0, w1, b, 0), vb = t.at(w0, w1, b, 1);
                if (vw > 0) ++out.wWin; else if (vw < 0) ++out.wLoss; else ++out.wDraw;
                if (vb < 0) ++out.bWin; else if (vb > 0) ++out.bLoss; else ++out.bDraw;
                if (vw > out.deepestWhite) {
                    out.deepestWhite = vw;
                    out.posWhite = { (Sq)w0, (Sq)w1, (Sq)b };
                }
                if (vb > out.deepestBlack) {
                    out.deepestBlack = vb;
                    out.posBlack = { (Sq)w0, (Sq)w1, (Sq)b };
                }
                // Quiet: no capture available to either side on the move.
                bool hang = false;
                const int mine[2] = { w0, w1 };
                for (int j = 0; j < 2 && !hang; ++j) {
                    const int nd = gen(B, j == 0 ? p0 : p1, mine[j], mine, 2, &b, 1, dst, cap);
                    for (int d = 0; d < nd; ++d) if (cap[d] >= 0) { hang = true; break; }
                }
                if (!hang) {
                    const int nd = gen(B, pb, b, &b, 1, mine, 2, dst, cap);
                    for (int d = 0; d < nd; ++d) if (cap[d] >= 0) { hang = true; break; }
                }
                if (!hang) {
                    ++out.quiet;
                    if (vw > 0) ++out.quietWinW;
                    if (vb < 0) ++out.quietWinB;
                    // The same split as the whole-board rows: White-relative,
                    // so with Black to move a Black win reads as a White loss.
                    if (vw > 0) ++out.qwWin; else if (vw < 0) ++out.qwLoss; else ++out.qwDraw;
                    if (vb < 0) ++out.qbWin; else if (vb > 0) ++out.qbLoss; else ++out.qbDraw;
                    if (vw > out.deepestWhiteQuiet) {
                        out.deepestWhiteQuiet = vw;
                        out.posWhiteQuiet = { (Sq)w0, (Sq)w1, (Sq)b };
                    }
                }
            }
        }
    for (int w = 0; w < m; ++w)
        for (int b = 0; b < m; ++b) {
            if (w == b) continue;
            S16 a0 = keep0.at(w, b, 0), a1 = keep1.at(w, b, 0);
            if (a0 > 0) ++out.sub0Win; else if (a0 < 0) ++out.sub0Loss; else ++out.sub0Draw;
            if (a1 > 0) ++out.sub1Win; else if (a1 < 0) ++out.sub1Loss; else ++out.sub1Draw;
        }

    if (wantLine && out.deepestWhite) {
        std::string s;
        int w0 = out.posWhite[0], w1 = out.posWhite[1], b = out.posWhite[2];
        int stm = 0, mno = 1, alive = 3;          // bit 0/1: white men, always both here
        for (int ply = 0; ply < 400; ++ply) {
            S16 cur = alive == 3 ? t.at(w0, w1, b, stm)
                    : alive == 1 ? keep0.at(w0, b, stm) : keep1.at(w1, b, stm);
            if (cur == 0) break;
            out.trace.push_back(cur);
            int bj = -1, bd = -1, bval = 0;
            const int mine[2] = { w0, w1 };
            if (stm == 0) {
                for (int j = 0; j < 2; ++j) {
                    if (!(alive & (1 << j))) continue;
                    const int pc = j == 0 ? p0 : p1;
                    const int* mm = alive == 3 ? mine : &mine[j];
                    const int nm = alive == 3 ? 2 : 1;
                    const int nd = gen(B, pc, mine[j], mm, nm, &b, 1, dst, cap);
                    for (int d = 0; d < nd; ++d) {
                        int worth;
                        if (cap[d] >= 0) worth = 1;
                        else {
                            S16 sv = alive == 3 ? (j == 0 ? t.at(dst[d], w1, b, 1) : t.at(w0, dst[d], b, 1))
                                   : (j == 0 ? keep0.at(dst[d], b, 1) : keep1.at(dst[d], b, 1));
                            worth = sv < 0 ? -sv + 1 : sv > 0 ? -(sv + 1) : 0;
                        }
                        bool better = bj < 0 || (cur > 0 ? (worth > 0 && (bval <= 0 || worth < bval))
                                                         : worth < bval);
                        if (better) { bj = j; bd = dst[d]; bval = worth; }
                    }
                }
            } else {
                const int* tt = alive == 3 ? mine : (alive == 1 ? &mine[0] : &mine[1]);
                const int nt = alive == 3 ? 2 : 1;
                const int nd = gen(B, pb, b, &b, 1, tt, nt, dst, cap);
                for (int d = 0; d < nd; ++d) {
                    int worth;
                    if (cap[d] >= 0 && alive != 3) worth = 1;          // white's last man
                    else if (cap[d] >= 0) {
                        int took = (tt[cap[d]] == w0) ? 0 : 1;
                        if (takingEndsIt(took == 0 ? p0 : p1,
                                         took == 0 ? p1 : p0)) worth = 1;   // last king
                        else {
                            S16 sv = took == 0 ? keep1.at(w1, dst[d], 0) : keep0.at(w0, dst[d], 0);
                            worth = sv < 0 ? -sv + 1 : sv > 0 ? -(sv + 1) : 0;
                        }
                    } else {
                        S16 sv = alive == 3 ? t.at(w0, w1, dst[d], 0)
                               : alive == 1 ? keep0.at(w0, dst[d], 0) : keep1.at(w1, dst[d], 0);
                        worth = sv < 0 ? -sv + 1 : sv > 0 ? -(sv + 1) : 0;
                    }
                    bool better = bj < 0 || (cur > 0 ? (worth > 0 && (bval <= 0 || worth < bval))
                                                     : worth < bval);
                    if (better) { bj = 0; bd = dst[d]; bval = worth; }
                }
            }
            if (bd < 0) break;
            if (stm == 0) s += std::to_string(mno) + ". ";
            const char L = stm == 0 ? capPieceLetter(bj == 0 ? p0 : p1)
                                    : (char)(capPieceLetter(pb) | 32);
            int from = stm == 0 ? (bj == 0 ? w0 : w1) : b;
            bool isCap = (stm == 0) ? (bd == b) : (bd == w0 || bd == w1);
            s += L; s += B.gm.name(from); s += isCap ? "x" : "-"; s += B.gm.name(bd);
            if (stm == 0) {
                if (bd == b) { s += "#"; break; }
                if (bj == 0) w0 = bd; else w1 = bd;
            } else {
                if (bd == w0) { alive &= ~1; }
                else if (bd == w1) { alive &= ~2; }
                if (!alive) { s += "#"; break; }
                b = bd;
                ++mno;
            }
            s += " ";
            if (s.size() % 72 < 12 && stm == 1) s += "\n      ";
            stm ^= 1;
        }
        out.line = s;
    }
    return 0;
}

}  // namespace kqk
