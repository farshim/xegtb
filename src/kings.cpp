// kings.cpp -- w white kings against b black kings, under CAPTURE rules.
//
// The rules are kqkkcap.cpp's with the queen deleted, so nothing here is a new
// rule; this is that rule set carried to its limit, where *every* man on the
// board is royal:
//
//   1. every king moves and captures as in chess, one square in any direction;
//   2. a king is an ordinary man -- no check, no mate, no pin -- and may be
//      taken by anything, another king included;
//   3. a player wins the instant the opponent's LAST king is taken;
//   4. a player with a king and no legal move is stalemated, and it is a draw.
//
// Rule 4 cannot fire for this material.  Immobility needs every square beside
// every one of a side's kings to hold one of its own men, and a corner king
// alone has three such squares, so a side needs four men to be immobile and no
// side here has more than three.  This is the same argument README section 5
// makes for the four-man capture tables, one man further along.
//
// What is new is that material now falls on BOTH sides.  Every other endgame
// in this program converts downwards in one direction only: Black takes a white
// piece and the game is over or drawn.  Here either side may take, so (w, b)
// converts into (w, b-1) when White takes and (w-1, b) when Black does, and the
// tables have to be built up the lattice
//
//     (1,1) -> (2,1), (1,2) -> (3,1), (2,2) -> (3,2)
//
// each one reading the two below it as seeds.  A conversion is not a draw here
// and not the end of the game: it is a smaller endgame with a value of its own,
// which is why this file solves six tables and not one.
//
// Values are relative to the side to move, as in kqkkcap.cpp:
//   v > 0   the side to move wins in v plies
//   v < 0   the side to move loses in -v plies
//   v == 0  drawn
//
// The index is not index.hpp's and not indexkk.hpp's.  Neither fits: there is
// no white king to put in the fundamental triangle and no piece to put in the
// configuration, only two unordered sets of like men that both move.  So a
// position is ranked as a pair of combinations -- colex rank of the white set
// times the number of black sets, plus colex rank of the black set -- and D4 is
// applied to the white set alone.  See `Sym` below for why that is enough.
#include "table.hpp"

#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <memory>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

namespace kqk {
namespace {

using S16 = int16_t;
using S8  = int8_t;
using I64 = int64_t;

// The same sentinels kqkkcap.cpp uses, and for the same reason.  These are the
// values the whole file reasons in; they are WIDE, and the narrow storage below
// translates to and from them so that no logic has to know the width.
static const S16 UNK = VC_UNKNOWN;   // not yet resolved
static const S16 ILL = VC_DEAD;      // slot is not a position: two men on one square

// Entries are stored in ONE byte while that is enough, and the table widens to
// two in place when it is not.  A byte holds the sentinels plus depths to 126;
// the deepest table in this project is 125 plies (K+K vs K+K at 14x14, and
// K+K+K vs K+K at 11x11), so one ply of headroom is not a margin worth
// trusting -- hence the widening rather than a cap.
static const S8 N_UNK = 127;         // narrow form of UNK
static const S8 N_ILL = -128;        // narrow form of ILL
static const int N_MAX = 126;        // largest magnitude a byte can hold

static const int DF[8] = {  1,  1,  0, -1, -1, -1,  0,  1 };
static const int DR[8] = {  0,  1,  1,  1,  0, -1, -1, -1 };

static inline S16 ld16(const S16* p, U64 i) {
    return std::atomic_ref<S16>(const_cast<S16&>(p[i])).load(std::memory_order_relaxed);
}
static inline void st16(S16* p, U64 i, S16 v) {
    std::atomic_ref<S16>(p[i]).store(v, std::memory_order_relaxed);
}
static inline S8 ld8(const S8* p, U64 i) {
    return std::atomic_ref<S8>(const_cast<S8&>(p[i])).load(std::memory_order_relaxed);
}
static inline void st8(S8* p, U64 i, S8 v) {
    std::atomic_ref<S8>(p[i]).store(v, std::memory_order_relaxed);
}

static std::atomic<U64> gEvals{0}, gSucc{0}, gSweeps{0};

struct Timer {
    std::chrono::steady_clock::time_point t0 = std::chrono::steady_clock::now();
    double s() const { return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(); }
};

// --------------------------------------------------------------------------
// Board.
// --------------------------------------------------------------------------
// The project's Geometry supplies the board, the square names and the D4
// tables; all this adds is a neighbour list, since a king's move is the one
// move geometry.hpp does not already generate.
struct Geo {
    Geometry gm;
    int n = 0, m = 0;
    int pc[2] = { CP_KING, CP_KING };   // [0] White's men, [1] Black's
    std::vector<int8_t>  ncnt;    // king neighbours of each square
    std::vector<int32_t> nbr;     // 8 slots per square
    std::vector<int8_t>  kcnt;    // knight jumps from each square
    std::vector<int32_t> knbr;    // 8 slots per square

    inline Sq img(int g, Sq s) const { return gm.image(g, s); }

    explicit Geo(int nn, int pw = CP_KING, int pb = CP_KING)
        : gm(nn), n(nn), m(nn * nn), ncnt(nn * nn), nbr((size_t)nn * nn * 8, -1),
          kcnt(nn * nn), knbr((size_t)nn * nn * 8, -1) {
        pc[0] = pw; pc[1] = pb;
        for (int r = 0; r < n; ++r)
            for (int f = 0; f < n; ++f) {
                int s = r * n + f, c = 0;
                for (int d = 0; d < 8; ++d) {
                    int ff = f + DF[d], rr = r + DR[d];
                    if (ff >= 0 && ff < n && rr >= 0 && rr < n) nbr[(size_t)s * 8 + c++] = rr * n + ff;
                }
                ncnt[s] = (int8_t)c;
                c = 0;
                for (int d = 0; d < 8; ++d) {
                    int ff = f + NF[d], rr = r + NR[d];
                    if (ff >= 0 && ff < n && rr >= 0 && rr < n) knbr[(size_t)s * 8 + c++] = rr * n + ff;
                }
                kcnt[s] = (int8_t)c;
            }
    }
    std::string name(int s) const { return gm.name(s); }
    int         parse(const std::string& t) const { return gm.parse(t); }
};

// --------------------------------------------------------------------------
// Destinations of the man standing on `s`.
// --------------------------------------------------------------------------
// The one place the piece enters the solver.  A king takes the eight
// neighbours and a knight its eight jumps -- for both, a square is a
// destination unless one of our own men stands on it, and nothing in between
// matters.  A rook walks the four orthogonal rays instead, and each ray stops
// at the first man on it, which is a destination when it is an enemy and not
// when it is one of ours: the rook is the only one of the three that can be
// blocked.  `mine` may contain `s` itself -- no destination is ever `s`, so it
// never matches.  Returns the count and fills `dst` with the squares and
// `capOf` with the index into `opp` of the man taken there, or -1.
//
// MAXDST bounds the fan-out: eight for a king or a knight, 4(n-1) for a rook
// or a bishop and 8(n-1) for a queen, so a slider board is capped at
// n <= MAXDST/capMaxRays(piece) + 1.
static const int MAXDST = 256;

static inline int genDst(const Geo& g, int pc, int s, const int* mine, int km,
                         const int* opp, int ko, int* dst, int* capOf) {
    int c = 0;
    if (!capIsSlider(pc)) {
        const bool kn = pc == CP_KNIGHT;
        const int32_t* nb = kn ? &g.knbr[(size_t)s * 8] : &g.nbr[(size_t)s * 8];
        const int nd = kn ? g.kcnt[s] : g.ncnt[s];
        for (int d = 0; d < nd; ++d) {
            const int t = nb[d];
            bool own = false;
            for (int q = 0; q < km; ++q) if (mine[q] == t) { own = true; break; }
            if (own) continue;
            int cap = -1;
            for (int q = 0; q < ko; ++q) if (opp[q] == t) { cap = q; break; }
            dst[c] = t; capOf[c] = cap; ++c;
        }
        return c;
    }
    const int n = g.n, f0 = s % n, r0 = s / n;
    // The even directions are the orthogonals and the odd ones the diagonals,
    // so all three sliders are the same walk off a different offset and stride.
    for (int d = capRayStart(pc), ds = capRayStride(pc); d < 8; d += ds) {
        int f = f0 + DF[d], r = r0 + DR[d];
        for (; f >= 0 && f < n && r >= 0 && r < n; f += DF[d], r += DR[d]) {
            const int t = r * n + f;
            bool own = false;
            for (int q = 0; q < km; ++q) if (mine[q] == t) { own = true; break; }
            if (own) break;                     // our own man: the ray stops short of it
            int cap = -1;
            for (int q = 0; q < ko; ++q) if (opp[q] == t) { cap = q; break; }
            dst[c] = t; capOf[c] = cap; ++c;
            if (cap >= 0) break;                // his man: take it, and the ray stops on it
        }
    }
    return c;
}

// --------------------------------------------------------------------------
// Colex ranking of unordered k-subsets of {0..m-1}.
// --------------------------------------------------------------------------
static inline I64 Ck(I64 x, int k) {
    if (x < k) return 0;
    if (k == 1) return x;
    if (k == 2) return x * (x - 1) / 2;
    if (k == 3) return x * (x - 1) * (x - 2) / 6;
    return x * (x - 1) * (x - 2) * (x - 3) / 24;
}
static inline U64 rk(const int* a, int k) {            // a sorted ascending
    U64 r = (U64)a[0];
    if (k > 1) r += (U64)((I64)a[1] * (a[1] - 1) / 2);
    if (k > 2) r += (U64)((I64)a[2] * (a[2] - 1) * (a[2] - 2) / 6);
    if (k > 3) r += (U64)((I64)a[3] * (a[3] - 1) * (a[3] - 2) * (a[3] - 3) / 24);
    return r;
}
static inline bool nextCombo(int* a, int k, int m) {   // colex successor
    for (int i = 0; i < k; ++i) {
        int lim = (i + 1 < k) ? a[i + 1] : m;
        if (a[i] + 1 < lim) { ++a[i]; for (int j = 0; j < i; ++j) a[j] = j; return true; }
    }
    return false;
}
static inline void sortk(int* a, int k) {
    for (int i = 1; i < k; ++i) { int x = a[i], j = i - 1; while (j >= 0 && a[j] > x) { a[j + 1] = a[j]; --j; } a[j + 1] = x; }
}


// --------------------------------------------------------------------------
// D4 reduction.  Only the WHITE set is canonicalised: a position is stored
// under (orbit of the white set, black set carried by the same group element).
// Positions whose white set has a nontrivial stabiliser therefore occupy more
// than one slot, which costs a little memory on the O(n^2) symmetric sets and
// buys a scheme with no stabiliser arithmetic anywhere in the hot path.  Each
// slot of a block stands for exactly |orbit| = 8 / |stab| real positions, which
// is what the census weights by.
// --------------------------------------------------------------------------
struct Sym {
    int w = 0;
    U64 nw = 0, nblk = 0;
    std::vector<int32_t> blockOf;   // white rank -> block
    std::vector<uint8_t> gTo;       // white rank -> element carrying it to the block
    std::vector<int32_t> blkSq;     // w squares per block
    std::vector<uint8_t> wt;        // orbit size of the block's white set: 8, 4, 2 or 1
};

static void buildSym(const Geo& g, int w, Sym& S) {
    S.w = w; S.nw = (U64)Ck(g.m, w);
    S.blockOf.assign(S.nw, -1); S.gTo.assign(S.nw, 0);
    S.nblk = 0;
    int a[4], t[4];
    for (int q = 0; q < w; ++q) a[q] = q;
    for (U64 r = 0; r < S.nw; ++r) {
        U64 best = r; int bg = 0, fix = 1;
        for (int gg = 1; gg < 8; ++gg) {
            for (int q = 0; q < w; ++q) t[q] = g.img(gg, a[q]);
            sortk(t, w);
            U64 rr = rk(t, w);
            if (rr < best) { best = rr; bg = gg; }
            if (rr == r) ++fix;
        }
        if (best == r) {
            S.blockOf[r] = (int32_t)S.nblk++;
            S.gTo[r] = 0;
            for (int q = 0; q < w; ++q) S.blkSq.push_back(a[q]);
            S.wt.push_back((uint8_t)(8 / fix));
        } else {
            S.blockOf[r] = S.blockOf[best];   // best < r, so already assigned
            S.gTo[r] = (uint8_t)bg;
        }
        nextCombo(a, w, g.m);
    }
}

// --------------------------------------------------------------------------
// One table: w white kings against b black kings.
// --------------------------------------------------------------------------
struct Tbl {
    int n = 0, m = 0, w = 0, b = 0;
    U64 nb = 0, nblk = 0, N = 0;
    const Sym* sym = nullptr;
    const Geo* geo = nullptr;
    // One of these two is live; `wide` says which.  Access goes through
    // get()/put(), which speak the wide convention either way.
    std::vector<S8>  v8[2];
    std::vector<S16> v16[2];
    bool wide = false;
    U64 legal = 0;                // real positions, orbit weighted
    int maxAbs = 0;

    void alloc(U64 n) {
        wide = false;
        for (int s = 0; s < 2; ++s) { v16[s].clear(); v16[s].shrink_to_fit(); v8[s].assign(n, N_UNK); }
    }
    // Promote to two bytes, carrying every value already computed.  Called
    // between sweeps, single-threaded, so there is nothing to race with.
    void widen() {
        if (wide) return;
        for (int s = 0; s < 2; ++s) {
            v16[s].resize(v8[s].size());
            for (U64 i = 0; i < (U64)v8[s].size(); ++i) {
                const S8 b = v8[s][i];
                v16[s][i] = (b == N_UNK) ? UNK : (b == N_ILL) ? ILL : (S16)b;
            }
            v8[s].clear(); v8[s].shrink_to_fit();
        }
        wide = true;
    }
    inline S16 get(int stm, U64 i) const {
        if (wide) return ld16(v16[stm].data(), i);
        const S8 b = ld8(v8[stm].data(), i);
        return (b == N_UNK) ? UNK : (b == N_ILL) ? ILL : (S16)b;
    }
    inline void put(int stm, U64 i, S16 x) {
        if (wide) { st16(v16[stm].data(), i, x); return; }
        S8 b;
        if      (x == UNK) b = N_UNK;
        else if (x == ILL) b = N_ILL;
        else {
            // Never reachable: solve() widens before a sweep that could
            // produce this.  Loud rather than silent if that ever changes.
            if (x > N_MAX || x < -N_MAX) { std::fprintf(stderr, "kings: narrow overflow %d\n", (int)x); std::abort(); }
            b = (S8)x;
        }
        st8(v8[stm].data(), i, b);
    }

    // The index splits cleanly in two, and the halves cost wildly different
    // amounts.  The WHITE half ranks the white set and then gathers twice out
    // of sym->blockOf and sym->gTo -- tables of C(m,w) entries, 245 MB at
    // w = 4, n = 14 -- so it is a random miss into a quarter-gigabyte array.
    // The BLACK half is a couple of table lookups and a rank.  Splitting them
    // lets a caller that moves only Black lift the expensive half out of its
    // loop; see evalPos.
    inline void whiteFrame(const int* W, int& blk, int& g0) const {
        const U64 wr = rk(W, w);
        blk = sym->blockOf[wr];
        g0  = sym->gTo[wr];
    }
    inline U64 slotIn(int blk, int g0, const int* B) const {
        int t[4];
        for (int q = 0; q < b; ++q) t[q] = geo->img(g0, B[q]);
        sortk(t, b);
        return (U64)blk * nb + rk(t, b);
    }
    inline U64 slot(const int* W, const int* B) const {
        int blk, g0;
        whiteFrame(W, blk, g0);
        return slotIn(blk, g0, B);
    }
    S16 at(const int* W, const int* B, int stm) const { return get(stm, slot(W, B)); }
};

// The value of a move is what it does to the opponent: leave them lost in k and
// I win in k+1; if every move leaves them winning, I lose by the slowest.
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

// Accumulate every move of `stm` from (W,B).  capW is the table entered when
// White takes a black king, capB the one entered when Black takes a white king;
// either is null when that capture ends the game instead.
static inline void evalPos(const Geo& g, const Tbl& t, const Tbl* capW, const Tbl* capB,
                           const int* W, const int* B, int stm, Acc& acc,
                           int blk, const int32_t* fblk, const uint8_t* fg0) {
    const int* mv = stm == 0 ? W : B;
    const int* op = stm == 0 ? B : W;
    const int  km = stm == 0 ? t.w : t.b;
    const int  ko = stm == 0 ? t.b : t.w;
    const Tbl* sub = stm == 0 ? capW : capB;
    int tm[4], to[4];

    const int myPc = g.pc[stm];
    int dsq[MAXDST], dcap[MAXDST];
    for (int j = 0; j < km; ++j) {
        const int nd = genDst(g, myPc, mv[j], mv, km, op, ko, dsq, dcap);
        for (int d = 0; d < nd; ++d) {
            const int dst = dsq[d];
            const int cap = dcap[d];

            for (int q = 0; q < km; ++q) tm[q] = mv[q];
            tm[j] = dst; sortk(tm, km);

            if (stm == 0) {
                // White moved, so the white set changed -- but it changed into
                // one of the perturbations this block already has a frame for,
                // and the frame is what costs money.  Both branches reuse it:
                // a conversion keeps the same white men and the same Sym, only
                // `nb` differs, so slotIn on the sub-table is the right call.
                const size_t f = (size_t)j * (size_t)g.m + (size_t)dst;
                const int fb = fblk[f], fg = fg0[f];
                if (cap >= 0) {
                    if (ko == 1) { acc.winNow(); continue; }  // his last man: over
                    int c = 0;
                    for (int q = 0; q < ko; ++q) if (q != cap) to[c++] = op[q];
                    acc.add(sub->get(1, sub->slotIn(fb, fg, to)));
                } else {
                    acc.add(t.get(1, t.slotIn(fb, fg, op)));
                }
            } else {
                if (cap >= 0) {
                    if (ko == 1) { acc.winNow(); continue; }
                    int c = 0;
                    for (int q = 0; q < ko; ++q) if (q != cap) to[c++] = op[q];
                    // Black took a white man: fewer white men, a different
                    // Sym, so this one has to be ranked the long way.
                    acc.add(sub->get(0, sub->slot(to, tm)));
                } else {
                    // Black moved, so the white set is this block's canonical
                    // representative: its frame is (blk, identity) by
                    // construction.  No gather at all.
                    acc.add(t.get(0, t.slotIn(blk, 0, tm)));
                }
            }
        }
    }
}

// --------------------------------------------------------------------------
// Per-block memo of the white half of the index.
// --------------------------------------------------------------------------
// The sweep holds one white set fixed while it runs through every black set in
// the block -- C(m, b) of them, 196 at b = 1, n = 14.  White's successors are
// the same perturbations of that one white set every time, so their frames are
// the same too, and computing them once a block instead of once a black set
// removes almost all of the random gathering into sym->blockOf.
//
// Built with no enemy man on the board, which yields a SUPERSET of the
// destinations any real position in the block offers: a black man can only
// block a ray or be captured on it, never open one.  So every (j, dst) the
// sweep actually asks for is present.
static void buildFrames(const Geo& g, const Tbl& t, const int* W,
                        std::vector<int32_t>& fblk, std::vector<uint8_t>& fg0) {
    int dsq[MAXDST], dcap[MAXDST], tm[4];
    for (int j = 0; j < t.w; ++j) {
        int32_t* pb = &fblk[(size_t)j * g.m];
        std::fill(pb, pb + g.m, -1);
        const int nd = genDst(g, g.pc[0], W[j], W, t.w, nullptr, 0, dsq, dcap);
        for (int d = 0; d < nd; ++d) {
            const int dst = dsq[d];
            for (int q = 0; q < t.w; ++q) tm[q] = W[q];
            tm[j] = dst; sortk(tm, t.w);
            int b2, g2; t.whiteFrame(tm, b2, g2);
            pb[dst] = (int32_t)b2;
            fg0[(size_t)j * g.m + dst] = (uint8_t)g2;
        }
    }
}

// --------------------------------------------------------------------------
// The induction.  Sweep by ply; at sweep k commit every position whose value
// is settled, which is a win of depth <= k, or any position all of whose
// successors are already known.  A win offered only by a conversion deeper
// than k stays pending until sweep k reaches it, so the depth stored is always
// the shortest route and never the first one found.
// --------------------------------------------------------------------------
static void solve(const Geo& g, Tbl& t, const Sym& sy, const Tbl* capW, const Tbl* capB,
                  int nthr, bool progress) {
    t.n = g.n; t.m = g.m; t.geo = &g; t.sym = &sy;
    t.nb = (U64)Ck(g.m, t.b); t.nblk = sy.nblk; t.N = t.nblk * t.nb;
    t.alloc(t.N);

    // Slots whose two sets overlap are not positions.
    {
        int B[4];
        t.legal = 0;
        for (U64 blk = 0; blk < t.nblk; ++blk) {
            const int* W = (const int*)&sy.blkSq[(size_t)blk * t.w];
            for (int q = 0; q < t.b; ++q) B[q] = q;
            for (U64 br = 0; br < t.nb; ++br) {
                bool bad = false;
                for (int p = 0; p < t.w && !bad; ++p)
                    for (int q = 0; q < t.b; ++q) if (W[p] == B[q]) { bad = true; break; }
                if (bad) { U64 i = blk * t.nb + br; t.put(0, i, ILL); t.put(1, i, ILL); }
                else t.legal += sy.wt[blk];
                nextCombo(B, t.b, g.m);
            }
        }
    }

    // Once every slot of one white triple is settled it can never come back,
    // so the sweep skips the whole row.  Most of the tail is skipped rows.
    std::vector<uint8_t> live(t.nblk, 1);

    int subMax = 0;
    if (capW) subMax = std::max(subMax, capW->maxAbs);
    if (capB) subMax = std::max(subMax, capB->maxAbs);

    for (int k = 1;; ++k) {
        // A value of magnitude M can first appear at sweep k = M - 1 (a loss
        // one ply slower than a successor settled last sweep), so the byte
        // form is safe only while k < N_MAX.  Widen just before that, between
        // sweeps, where no worker is running.
        // EGTB_WIDEN_AT lowers the threshold so the widening path can be
        // exercised on shallow tables: forcing it early must not change a
        // single entry.  Test hook only.
        static const int widenAt = getenv("EGTB_WIDEN_AT") ? std::atoi(getenv("EGTB_WIDEN_AT")) : N_MAX;
        if (k >= widenAt && !t.wide) t.widen();
        std::atomic<U64> changed{0};
        std::atomic<int> pend{0};

        auto worker = [&](U64 lo, U64 hi) {
            int B[4];
            U64 loc = 0; int locPend = 0;
            U64 locEval = 0, locSucc = 0;
            std::vector<int32_t> fblk((size_t)t.w * g.m, -1);
            std::vector<uint8_t> fg0((size_t)t.w * g.m, 0);
            for (U64 blk = lo; blk < hi; ++blk) {
                if (!live[blk]) continue;
                const int* W = (const int*)&sy.blkSq[(size_t)blk * t.w];
                buildFrames(g, t, W, fblk, fg0);
                bool anyLeft = false;
                for (int q = 0; q < t.b; ++q) B[q] = q;
                for (U64 br = 0; br < t.nb; ++br) {
                    const U64 i = blk * t.nb + br;
                    for (int stm = 0; stm < 2; ++stm) {
                        if (t.get(stm, i) != UNK) continue;
                        Acc a;
                        evalPos(g, t, capW, capB, W, B, stm, a, (int)blk, fblk.data(), fg0.data());
                        ++locEval; locSucc += (U64)a.moves;
                        S16 nv;
                        if (a.best && a.best <= k)          nv = (S16)a.best;
                        else if (a.best)                    { if (a.best > locPend) locPend = a.best; nv = UNK; }
                        else if (a.anyUnknown)              nv = UNK;
                        else if (!a.moves || a.anyDraw)     nv = 0;
                        else                                nv = (S16)-a.worst;
                        if (nv != UNK) { t.put(stm, i, nv); ++loc; } else anyLeft = true;
                    }
                    nextCombo(B, t.b, g.m);
                }
                live[blk] = anyLeft;
            }
            changed += loc; gEvals += locEval; gSucc += locSucc;
            int cur = pend.load();
            while (locPend > cur && !pend.compare_exchange_weak(cur, locPend)) {}
        };

        std::vector<std::thread> th;
        U64 chunk = (t.nblk + nthr - 1) / nthr;
        for (int q = 0; q < nthr; ++q) {
            U64 lo = std::min<U64>((U64)q * chunk, t.nblk), hi = std::min<U64>(lo + chunk, t.nblk);
            if (lo < hi) th.emplace_back(worker, lo, hi);
        }
        for (auto& x : th) x.join();

        if (progress && changed)
            std::printf("      ply %3d  settled %llu\n", k, (unsigned long long)changed.load());
        gSweeps = (U64)k;
        if (!changed.load() && pend.load() <= k && k > subMax) break;
        if (k > 40000) { std::printf("      RUNAWAY\n"); break; }
    }

    for (int stm = 0; stm < 2; ++stm)
        for (U64 i = 0; i < t.N; ++i) if (t.get(stm, i) == UNK) t.put(stm, i, 0);

    t.maxAbs = 0;
    U64 deep = 0, live8 = 0;
    for (int stm = 0; stm < 2; ++stm)
        for (U64 i = 0; i < t.N; ++i) {
            S16 x = t.get(stm, i);
            if (x == ILL) continue;
            int a = x < 0 ? -x : x;
            ++live8;
            if (a > 126) ++deep;
            if (a > t.maxAbs) t.maxAbs = a;
        }
    if (getenv("EGTB_DEEP"))
        std::fprintf(stderr, "  [deep] K%dvK%d n=%d  maxAbs=%d  |v|>126: %llu of %llu (%.6f%%)\n",
                     t.w, t.b, t.n, t.maxAbs, (unsigned long long)deep,
                     (unsigned long long)live8, 100.0 * (double)deep / (double)std::max<U64>(1, live8));
    if (getenv("EGTB_COUNT")) {
        const U64 entries = 2 * t.N;
        std::fprintf(stderr,
            "  [count] K%dvK%d n=%d  entries=%llu sweeps=%llu  evals=%llu (%.2f/entry)"
            "  succ-reads=%llu (%.1f/eval)  naive N*D=%llu (%.1fx saved)\n",
            t.w, t.b, t.n, (unsigned long long)entries, (unsigned long long)gSweeps.load(),
            (unsigned long long)gEvals.load(), (double)gEvals.load() / (double)entries,
            (unsigned long long)gSucc.load(), (double)gSucc.load() / (double)std::max<U64>(1, gEvals.load()),
            (unsigned long long)(entries * gSweeps.load()),
            (double)(entries * gSweeps.load()) / (double)std::max<U64>(1, gEvals.load()));
        gEvals = 0; gSucc = 0; gSweeps = 0;
    }
}

// --------------------------------------------------------------------------
// The suite of tables for W white kings against B black kings.
// --------------------------------------------------------------------------
struct Suite {
    Geo g;
    Tbl t[5][3];
    Sym sym[5];
    bool have[5][3] = {};
    int W = 0, B = 0;

    Suite(int n, int w, int b, int pw, int pb) : g(n, pw, pb), W(w), B(b) {
        for (int k = 1; k <= W; ++k) buildSym(g, k, sym[k]);
    }

    const Tbl* capWof(int w, int b) const { return b > 1 ? &t[w][b - 1] : nullptr; }
    const Tbl* capBof(int w, int b) const { return w > 1 ? &t[w - 1][b] : nullptr; }

    void build(int nthr, bool progress) {
        for (int tot = 2; tot <= W + B; ++tot)
            for (int w = 1; w <= W; ++w) {
                int b = tot - w;
                if (b < 1 || b > B) continue;
                t[w][b].w = w; t[w][b].b = b;
                Timer tm;
                solve(g, t[w][b], sym[w], capWof(w, b), capBof(w, b), nthr, progress);
                have[w][b] = true;
                if (progress)
                    std::printf("   built K%d vs K%d: %llu slots/side (%llu positions), deepest %d ply, %.2f s\n",
                                w, b, (unsigned long long)t[w][b].N,
                                (unsigned long long)t[w][b].legal, t[w][b].maxAbs, tm.s());
            }
    }
    S16 look(const std::vector<int>& Wq, const std::vector<int>& Bq, int stm) const {
        const Tbl& q = t[(int)Wq.size()][(int)Bq.size()];
        int a[4], c[4];
        for (size_t i = 0; i < Wq.size(); ++i) a[i] = Wq[i];
        for (size_t i = 0; i < Bq.size(); ++i) c[i] = Bq[i];
        sortk(a, (int)Wq.size()); sortk(c, (int)Bq.size());
        return q.at(a, c, stm);
    }
};

// --------------------------------------------------------------------------
// Concrete moves, for the census, the check and the play-out.
// --------------------------------------------------------------------------
struct Mv {
    int from = -1, to = -1;
    bool cap = false, ends = false;          // `ends` = took his last king
    std::vector<int> W, B;
};

static void genMoves(const Geo& g, const std::vector<int>& W, const std::vector<int>& B,
                     int stm, std::vector<Mv>& out) {
    out.clear();
    const std::vector<int>& mv = stm == 0 ? W : B;
    const std::vector<int>& op = stm == 0 ? B : W;
    int dsq[MAXDST], dcap[MAXDST];
    for (size_t j = 0; j < mv.size(); ++j) {
        int s = mv[j];
        const int nd = genDst(g, g.pc[stm], s, mv.data(), (int)mv.size(),
                              op.data(), (int)op.size(), dsq, dcap);
        for (int d = 0; d < nd; ++d) {
            int dst = dsq[d];
            int cap = dcap[d];
            Mv M; M.from = s; M.to = dst; M.cap = cap >= 0;
            std::vector<int> nm = mv, no = op;
            nm[j] = dst; std::sort(nm.begin(), nm.end());
            if (cap >= 0) { no.erase(no.begin() + cap); M.ends = no.empty(); }
            M.W = stm == 0 ? nm : no;
            M.B = stm == 0 ? no : nm;
            out.push_back(std::move(M));
        }
    }
}

// Second forward generator, written independently of evalPos: it picks the
// successor table by counting men rather than by a precomputed pointer, and it
// ranks through Tbl::at rather than inline.  This is what --verify runs.
static S16 rederiveFast(const Suite& S, const Tbl& t, const int* W, const int* B, int stm) {
    const Geo& g = S.g;
    int mv[4], op[4], km, ko;
    if (stm == 0) { km = t.w; ko = t.b; for (int i = 0; i < km; ++i) mv[i] = W[i]; for (int i = 0; i < ko; ++i) op[i] = B[i]; }
    else          { km = t.b; ko = t.w; for (int i = 0; i < km; ++i) mv[i] = B[i]; for (int i = 0; i < ko; ++i) op[i] = W[i]; }

    Acc a;
    int nm[4], no[4];
    int dsq[MAXDST], dcap[MAXDST];
    for (int j = 0; j < km; ++j) {
        const int nd = genDst(g, g.pc[stm], mv[j], mv, km, op, ko, dsq, dcap);
        for (int d = 0; d < nd; ++d) {
            const int dst = dsq[d];
            const int cap = dcap[d];
            for (int q = 0; q < km; ++q) nm[q] = mv[q];
            nm[j] = dst; sortk(nm, km);
            int ns = ko, c = 0;
            if (cap >= 0) {
                if (ko == 1) { a.winNow(); continue; }
                for (int q = 0; q < ko; ++q) if (q != cap) no[c++] = op[q];
                ns = ko - 1;
            } else for (int q = 0; q < ko; ++q) no[q] = op[q];
            const int* SW = stm == 0 ? nm : no;
            const int* SB = stm == 0 ? no : nm;
            const int   cw = stm == 0 ? km : ns;
            const int   cb = stm == 0 ? ns : km;
            a.add(S.t[cw][cb].at(SW, SB, 1 - stm));
        }
    }
    if (a.best) return (S16)a.best;
    if (!a.moves || a.anyDraw) return 0;
    return (S16)-a.worst;
}

struct Census { U64 win[2] = {0, 0}, draw[2] = {0, 0}, loss[2] = {0, 0}; };

// Walk one table: census, deepest win each way, and (if asked) the Bellman check.
static U64 walk(const Suite& S, const Tbl& t, int nthr, bool verify,
                Census& cen, int deepW[6], int deepB[6], int& dW, int& dB) {
    std::atomic<U64> bad{0};
    std::vector<Census>            cs(nthr);
    std::vector<std::array<int, 6>> bw(nthr), bb(nthr);
    std::vector<int>               vw(nthr, 0), vb(nthr, 0);

    const Sym& sy = *t.sym;
    auto worker = [&](int id, U64 lo, U64 hi) {
        int B[4]; Census c; U64 nbad = 0;
        int bestW = 0, bestB = 0; std::array<int, 6> pw{}, pb{};
        for (U64 blk = lo; blk < hi; ++blk) {
            const int* W = (const int*)&sy.blkSq[(size_t)blk * t.w];
            const U64 wgt = sy.wt[blk];          // real positions this slot stands for
            for (int q = 0; q < t.b; ++q) B[q] = q;
            for (U64 br = 0; br < t.nb; ++br) {
                const U64 i = blk * t.nb + br;
                for (int stm = 0; stm < 2; ++stm) {
                    S16 x = t.get(stm, i);
                    if (x == ILL) continue;
                    if (verify && rederiveFast(S, t, W, B, stm) != x) ++nbad;
                    // Translate mover-relative to White-relative for the census.
                    int wrel = (stm == 0) ? x : -x;
                    if (wrel > 0) c.win[stm] += wgt; else if (wrel < 0) c.loss[stm] += wgt; else c.draw[stm] += wgt;
                    if (stm == 0 && x > bestW) {
                        bestW = x; int k = 0;
                        for (int q = 0; q < t.w; ++q) pw[k++] = W[q];
                        for (int q = 0; q < t.b; ++q) pw[k++] = B[q];
                    }
                    if (stm == 1 && x > bestB) {
                        bestB = x; int k = 0;
                        for (int q = 0; q < t.w; ++q) pb[k++] = W[q];
                        for (int q = 0; q < t.b; ++q) pb[k++] = B[q];
                    }
                }
                nextCombo(B, t.b, S.g.m);
            }
        }
        cs[id] = c; bw[id] = pw; bb[id] = pb; vw[id] = bestW; vb[id] = bestB;
        bad += nbad;
    };

    std::vector<std::thread> th;
    U64 chunk = (t.nblk + nthr - 1) / nthr;
    for (int q = 0; q < nthr; ++q) {
        U64 lo = std::min<U64>((U64)q * chunk, t.nblk), hi = std::min<U64>(lo + chunk, t.nblk);
        if (lo < hi) th.emplace_back(worker, q, lo, hi);
    }
    for (auto& x : th) x.join();

    dW = dB = 0;
    for (int q = 0; q < nthr; ++q) {
        for (int s = 0; s < 2; ++s) { cen.win[s] += cs[q].win[s]; cen.draw[s] += cs[q].draw[s]; cen.loss[s] += cs[q].loss[s]; }
        if (vw[q] > dW) { dW = vw[q]; for (int i = 0; i < 6; ++i) deepW[i] = bw[q][i]; }
        if (vb[q] > dB) { dB = vb[q]; for (int i = 0; i < 6; ++i) deepB[i] = bb[q][i]; }
    }
    return bad.load();
}

// --------------------------------------------------------------------------
// Play out the value: shortest win for the winner, longest resistance for the
// loser.  Material falls as kings are taken, so the line walks down the tables.
// --------------------------------------------------------------------------
static std::string playOut(const Suite& S, std::vector<int> W, std::vector<int> B, int stm, int cap) {
    std::string out;
    std::vector<Mv> mvs;
    int mno = 1;
    size_t lastBreak = 0;
    // A line that opens with Black needs the move number all the same, so that
    // the pairs that follow are numbered as they would be over the board.
    if (stm == 1) out += "1... ";
    for (int ply = 0; ply < cap; ++ply) {
        S16 cur = S.look(W, B, stm);
        if (cur == 0) break;
        genMoves(S.g, W, B, stm, mvs);
        // What playing M is worth to the mover: > 0 win in that many plies,
        // < 0 loss in that many, 0 a draw.
        auto worth = [&](const Mv& M) -> int {
            if (M.ends) return 1;
            S16 sv = S.look(M.W, M.B, 1 - stm);
            if (sv < 0) return -sv + 1;
            if (sv > 0) return -(sv + 1);
            return 0;
        };
        const Mv* pick = nullptr; int pv = 0;
        for (const Mv& M : mvs) {
            int mine = worth(M);
            if (!pick) { pick = &M; pv = mine; continue; }
            // Winning: the quickest.  Losing: the slowest, which is the most
            // negative, since every move loses.
            bool better = (cur > 0) ? (mine > 0 && (pv <= 0 || mine < pv)) : (mine < pv);
            if (better) { pick = &M; pv = mine; }
        }
        if (!pick) break;
        if (stm == 0) { out += std::to_string(mno) + ". "; }
        {
            const char L = capPieceLetter(S.g.pc[stm]);
            out += (stm == 0 ? L : (char)(L | 32));
        }
        out += S.g.name(pick->from);
        out += pick->cap ? "x" : "-";
        out += S.g.name(pick->to);
        if (pick->ends) { out += "#"; break; }
        out += " ";
        if (stm == 1) {
            ++mno;
            if (out.size() - lastBreak > 66) { out += "\n      "; lastBreak = out.size(); }
        }
        W = pick->W; B = pick->B; stm = 1 - stm;
    }
    return out;
}

// --------------------------------------------------------------------------
// Brute force: the same game solved with no index and no material split -- one
// hash table over every state of every material, value-iterated to a fixpoint.
// --------------------------------------------------------------------------
static U64 bruteCheck(const Suite& S, int W, int B) {
    const Geo& g = S.g;
    std::vector<std::pair<std::vector<int>, std::vector<int>>> st;
    std::vector<U64> key;
    if (g.m > 160) throw std::runtime_error("kings: --brute needs n <= 12");
    const U64 base = (U64)g.m + 1;
    auto enc = [&](const std::vector<int>& a, const std::vector<int>& b, int stm) {
        U64 k = (U64)stm;
        k = k * 8 + a.size(); k = k * 8 + b.size();
        for (int x : a) k = k * base + (U64)(x + 1);
        for (int i = (int)a.size(); i < 4; ++i) k = k * base;
        for (int x : b) k = k * base + (U64)(x + 1);
        for (int i = (int)b.size(); i < 4; ++i) k = k * base;
        return k;
    };
    std::vector<U64> allKeys;
    std::vector<std::pair<std::vector<int>, std::vector<int>>> allPos;
    std::vector<int> stms;
    for (int w = 1; w <= W; ++w)
        for (int b = 1; b <= B; ++b) {
            std::vector<int> A(w), C(b);
            for (int i = 0; i < w; ++i) A[i] = i;
            do {
                for (int i = 0; i < b; ++i) C[i] = i;
                do {
                    bool bad = false;
                    for (int x : A) for (int y : C) if (x == y) bad = true;
                    if (!bad) for (int s = 0; s < 2; ++s) { allPos.push_back({A, C}); stms.push_back(s); allKeys.push_back(enc(A, C, s)); }
                } while (nextCombo(C.data(), b, g.m));
            } while (nextCombo(A.data(), w, g.m));
        }
    std::vector<U64> sorted = allKeys;
    std::sort(sorted.begin(), sorted.end());
    auto find = [&](U64 k) { return (size_t)(std::lower_bound(sorted.begin(), sorted.end(), k) - sorted.begin()); };
    std::vector<S16> val(sorted.size(), UNK);

    std::vector<Mv> mvs;
    for (int k = 1;; ++k) {
        U64 ch = 0; int pend = 0;
        for (size_t i = 0; i < allPos.size(); ++i) {
            size_t at = find(allKeys[i]);
            if (val[at] != UNK) continue;
            genMoves(g, allPos[i].first, allPos[i].second, stms[i], mvs);
            Acc a;
            for (const Mv& M : mvs) {
                if (M.ends) { a.winNow(); continue; }
                a.add(val[find(enc(M.W, M.B, 1 - stms[i]))]);
            }
            S16 nv;
            if (a.best && a.best <= k)      nv = (S16)a.best;
            else if (a.best)                { if (a.best > pend) pend = a.best; nv = UNK; }
            else if (a.anyUnknown)          nv = UNK;
            else if (!a.moves || a.anyDraw) nv = 0;
            else                            nv = (S16)-a.worst;
            if (nv != UNK) { val[at] = nv; ++ch; }
        }
        if (!ch && pend <= k) break;
    }
    for (auto& x : val) if (x == UNK) x = 0;

    U64 bad = 0;
    for (size_t i = 0; i < allPos.size(); ++i) {
        S16 mine = val[find(allKeys[i])];
        S16 theirs = S.look(allPos[i].first, allPos[i].second, stms[i]);
        if (mine != theirs) ++bad;
    }
    return bad;
}

}  // namespace

// ---------------------------------------------------------------------------
// The public face of the file.
// ---------------------------------------------------------------------------
struct TableKings::Impl {
    Suite s;
    KingsStats st;
    KingsStats sub[5][3];
    Impl(int n, int w, int b, int pw, int pb) : s(n, w, b, pw, pb) {}
};

TableKings::TableKings(int edge, int whiteMen, int blackMen, int whitePiece, int blackPiece)
    : p(new Impl(edge, whiteMen, blackMen, whitePiece, blackPiece)) {
    if (whiteMen < 1 || whiteMen > 4 || blackMen < 1 || blackMen > 2)
        throw std::runtime_error("capture: white 1..4, black 1..2");
    for (int q : { whitePiece, blackPiece })
        if (capIsSlider(q) && capMaxRays(q) * (edge - 1) > MAXDST)
            throw std::runtime_error("capture: n is too large for the move buffer");
}
TableKings::~TableKings() = default;

void TableKings::generate(int threads, bool progress) {
    Timer tm;
    p->s.build(threads, progress);
    p->st.seconds = tm.s();
}

// Fill one stats block from a walk of one table.
static void fill(const Suite& S, const Tbl& t, int nthr, bool verify, KingsStats& out) {
    Census c; int dW = 0, dB = 0, pw[6] = {}, pb[6] = {};
    out.mismatches = walk(S, t, nthr, verify, c, pw, pb, dW, dB);
    out.verified   = verify;
    out.n = t.n; out.w = t.w; out.b = t.b;
    out.slots = t.N; out.positions = t.legal;
    out.wWin = c.win[0]; out.wDraw = c.draw[0]; out.wLoss = c.loss[0];
    out.bWin = c.win[1]; out.bDraw = c.draw[1]; out.bLoss = c.loss[1];
    out.deepestWhite = dW; out.deepestBlack = dB;
    out.posWhite.assign(pw, pw + t.w + t.b);
    out.posBlack.assign(pb, pb + t.w + t.b);
}

void TableKings::census(int threads, bool verify) {
    const int W = p->s.W, B = p->s.B;
    double keep = p->st.seconds;
    fill(p->s, p->s.t[W][B], threads, verify, p->st);
    p->st.seconds = keep;
    for (int w = 1; w <= W; ++w)
        for (int b = 1; b <= B; ++b)
            if (w != W || b != B) fill(p->s, p->s.t[w][b], threads, false, p->sub[w][b]);
}

const KingsStats& TableKings::stats() const { return p->st; }
const KingsStats& TableKings::subStats(int w, int b) const { return p->sub[w][b]; }

int16_t TableKings::probe(const std::vector<Sq>& W, const std::vector<Sq>& B, bool wtm) const {
    std::vector<int> a(W.begin(), W.end()), c(B.begin(), B.end());
    return p->s.look(a, c, wtm ? 0 : 1);
}

std::string TableKings::line(const std::vector<Sq>& W, const std::vector<Sq>& B,
                             bool wtm, int cap) const {
    std::vector<int> a(W.begin(), W.end()), c(B.begin(), B.end());
    std::sort(a.begin(), a.end()); std::sort(c.begin(), c.end());
    return playOut(p->s, a, c, wtm ? 0 : 1, cap);
}

std::string TableKings::square(Sq s) const { return p->s.g.name(s); }
Sq          TableKings::parse(const std::string& t) const { return p->s.g.parse(t); }

U64 kingsBruteForceCheck(const TableKings& t) {
    return bruteCheck(t.p->s, t.p->s.W, t.p->s.B);
}

}  // namespace kqk
