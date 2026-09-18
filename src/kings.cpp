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
#include <map>
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

// --------------------------------------------------------------------------
// Parallel for, with the work handed out dynamically.
// --------------------------------------------------------------------------
// Equal shares are wrong on an asymmetric machine.  This one has four
// performance and four efficiency cores, and every parallel phase here ends
// at a barrier, so equal shares leave the fast cores idling while the slow
// ones finish their identical portion.  Measured on KKKK v K n = 12: 3.02x on
// four threads, only 3.43x on eight, and six threads slower in wall time than
// four -- while total CPU time nearly doubled, 154s to 298s, which is the
// efficiency cores burning time on work a performance core would have taken.
//
// So: a shared counter, and each thread claims a chunk at a time and comes
// back for more.  `work(q, claim)` runs once per thread; it sets up whatever
// per-thread state it needs, then calls claim(lo, hi) until that returns
// false.  The grain has to be big enough to bury the atomic and small enough
// that the tail is short.
template <class F>
static void parDyn(int nthr, U64 n, U64 grain, F work) {
    std::atomic<U64> next{0};
    auto claim = [&](U64& lo, U64& hi) {
        lo = next.fetch_add(grain, std::memory_order_relaxed);
        if (lo >= n) return false;
        hi = std::min(lo + grain, n);
        return true;
    };
    if (nthr < 2) { work(0, claim); return; }
    std::vector<std::thread> th;
    th.reserve((size_t)nthr);
    for (int q = 0; q < nthr; ++q) th.emplace_back([&, q] { work(q, claim); });
    for (auto& x : th) x.join();
}

static std::atomic<U64> gEvals{0}, gSucc{0}, gSweeps{0};
// Frontier queue accounting, printed under EGTB_QUEUE.
static std::atomic<U64> gWake{0}, gAfterUniq{0}, gBuckets{0}, gBackwards{0};
static double gTsort = 0, gTmerge = 0, gTpar = 0;

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

// Every man-set in here is an int[4] holding k = 1..4 squares.  Saying so out
// loud matters: with k a runtime variable clang lowers `for (q<k) d[q]=s[q]`
// into a call to memcpy, and the profile showed _platform_memmove taking ~6%
// of the solve to move four words at a time.  With the range pinned it
// unrolls into stores.
#define KSET_BOUND(k) do { if ((k) < 1 || (k) > 4) __builtin_unreachable(); } while (0)

// Occupancy tests over a man-set of one to four squares.  Written without the
// early exit on purpose: the scan is short and the position of the hit is
// effectively random, so `break` bought a skipped comparison at the price of a
// branch mispredict.  Fixing the trip count instead lets these fold into a
// handful of compares and conditional selects.  capturedAt returns the index
// of the man standing on t, or -1; the squares in a set are distinct, so
// taking the last match is the same as taking the first.
static inline bool occupies(const int* set, int k, int t) {
    if (k == 0) return false;
    KSET_BOUND(k);
    int hit = 0;
    for (int q = 0; q < k; ++q) hit |= (set[q] == t);
    return hit != 0;
}
static inline int capturedAt(const int* set, int k, int t) {
    if (k == 0) return -1;
    KSET_BOUND(k);
    int at = -1;
    for (int q = 0; q < k; ++q) at = (set[q] == t) ? q : at;
    return at;
}

static inline int genDst(const Geo& g, int pc, int s, const int* mine, int km,
                         const int* opp, int ko, int* dst, int* capOf) {
    int c = 0;
    if (!capIsSlider(pc)) {
        const bool kn = pc == CP_KNIGHT;
        const int32_t* nb = kn ? &g.knbr[(size_t)s * 8] : &g.nbr[(size_t)s * 8];
        const int nd = kn ? g.kcnt[s] : g.ncnt[s];
        for (int d = 0; d < nd; ++d) {
            const int t = nb[d];
            if (occupies(mine, km, t)) continue;
            const int cap = capturedAt(opp, ko, t);
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
            if (occupies(mine, km, t)) break;   // our own man: the ray stops short of it
            const int cap = capturedAt(opp, ko, t);
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
static inline void cpk(int* d, const int* s, int k) {
    KSET_BOUND(k);
    for (int q = 0; q < k; ++q) d[q] = s[q];
}

// Sorting networks, not an insertion sort.  These sets are sorted once per
// successor -- tens of millions of times a second -- and an insertion sort's
// inner loop runs a data-dependent number of times on effectively random
// input, so it mispredicted on nearly every call.  The comparators below
// lower to conditional selects, so the only branch left is the dispatch on k,
// which is constant for the whole solve and so predicts perfectly.
#define KSW(i, j) do { const int x = a[i], y = a[j];                  \
                       a[i] = x < y ? x : y; a[j] = x < y ? y : x; } while (0)
static inline void sortk(int* a, int k) {
    KSET_BOUND(k);
    if (k == 1) return;
    if (k == 2) { KSW(0, 1); return; }
    if (k == 3) { KSW(0, 1); KSW(1, 2); KSW(0, 1); return; }
    KSW(0, 1); KSW(2, 3); KSW(0, 2); KSW(1, 3); KSW(1, 2);
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
    // The identity group element, for a set the caller already has sorted:
    // neither the image nor the sort has anything to do.  This is the whole
    // of Black's non-capture successor, since a black move leaves the white
    // set at its block's canonical representative.
    inline U64 slotIn0(int blk, const int* B) const {
        return (U64)blk * nb + rk(B, b);
    }
    // Rank the black set under each of the eight group elements.  White's
    // successors all carry the SAME black set, and differ only in which
    // element carries it, so this replaces one image-sort-rank per successor
    // with one array read.
    inline void rankAll(const int* B, U64* out) const {
        int t[4];
        for (int e = 0; e < 8; ++e) {
            for (int q = 0; q < b; ++q) t[q] = geo->img(e, B[q]);
            sortk(t, b);
            out[e] = rk(t, b);
        }
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
    // Successors NOT known to be wins for the opponent.  The frontier's
    // counter is this, counted down; it can only reach zero when every move
    // walks into a win, which is exactly when the mover is lost.  A draw, an
    // unresolved successor, a losing successor and a game-ending capture all
    // count, so it never reaches zero for a position that is not lost.
    int notWin = 0;
    bool anyDraw = false, anyUnknown = false;
    inline void add(S16 x) {
        ++moves;
        if (x == UNK) { anyUnknown = true; ++notWin; return; }
        if (x < 0) { int q = -x + 1; if (!best || q < best) best = q; ++notWin; }
        else if (x > 0) { if (x + 1 > worst) worst = x + 1; }
        else { anyDraw = true; ++notWin; }
    }
    inline void winNow() { ++moves; ++notWin; if (!best || best > 1) best = 1; }
};

// --------------------------------------------------------------------------
// Per-block memo of everything that does not depend on where Black stands.
// --------------------------------------------------------------------------
// The sweep holds one white set fixed while it runs through every black set
// in the block -- C(m, b) of them, 196 at b = 1, n = 14.  White's successors
// are the same perturbations of that one white set every time, so their
// frames are the same too, and computing them once a block instead of once a
// black set removes almost all of the random gathering into sym->blockOf.
//
// Built with no enemy man on the board, which yields a SUPERSET of the
// destinations any real position in the block offers: a black man can only
// block a ray or be captured on it, never open one.  So every (j, dst) the
// sweep actually asks for is present.
//
// For a king or a knight that superset is exact, since a black man can stand
// on the target square but cannot open or close a jump.  So the memo also
// keeps a FLAT list of White's successors -- destination square, and the
// frame of the white set it produces -- and evalPos walks that instead of
// regenerating the moves and re-deriving the frames.  All that is left per
// successor is the one test of whether Black stands on the destination.  A
// slider gets no flat list: a black man blocks the ray beyond it, so the
// superset is not exact and the moves must be generated against the real
// position.
struct Frames {
    std::vector<int32_t> blk;         // [j * m + dst] -> block of the moved set
    std::vector<uint8_t> g0;          // [j * m + dst] -> element carrying it
    std::vector<int32_t> fdst, ffb;   // flat list: destination, its block
    std::vector<uint8_t> ffg;         // flat list: its group element
    int nflat = 0;
    bool flat = false;                // is the flat list exact?

    void alloc(const Geo& g, const Tbl& t) {
        flat = !capIsSlider(g.pc[0]);
        if (flat) {
            // The square-indexed map is read only where the flat list cannot
            // be used, so when there is a flat list it is not built at all --
            // and is left empty, so that a stray read faults rather than
            // quietly returning -1.
            const size_t cap = (size_t)t.w * 8;   // a king or a knight: at most 8
            fdst.resize(cap); ffb.resize(cap); ffg.resize(cap);
            return;
        }
        blk.assign((size_t)t.w * g.m, -1);
        g0.assign((size_t)t.w * g.m, 0);
    }

    void build(const Geo& g, const Tbl& t, const int* W) {
        int dsq[MAXDST], dcap[MAXDST], tm[4];
        nflat = 0;
        for (int j = 0; j < t.w; ++j) {
            int32_t* pb = nullptr;
            if (!flat) { pb = &blk[(size_t)j * g.m]; std::fill(pb, pb + g.m, -1); }
            const int nd = genDst(g, g.pc[0], W[j], W, t.w, nullptr, 0, dsq, dcap);
            for (int d = 0; d < nd; ++d) {
                const int dst = dsq[d];
                cpk(tm, W, t.w);
                tm[j] = dst; sortk(tm, t.w);
                int b2, g2; t.whiteFrame(tm, b2, g2);
                if (flat) {
                    fdst[(size_t)nflat] = dst;
                    ffb[(size_t)nflat] = (int32_t)b2;
                    ffg[(size_t)nflat] = (uint8_t)g2;
                    ++nflat;
                } else {
                    pb[dst] = (int32_t)b2;
                    g0[(size_t)j * g.m + dst] = (uint8_t)g2;
                }
            }
        }
    }
};

// Accumulate every move of `stm` from (W,B).  capW is the table entered when
// White takes a black king, capB the one entered when Black takes a white king;
// either is null when that capture ends the game instead.
static inline void evalPos(const Geo& g, const Tbl& t, const Tbl* capW, const Tbl* capB,
                           const int* W, const int* B, int stm, Acc& acc,
                           int blk, const Frames& fr) {
    const int32_t* fblk = fr.blk.data();
    const uint8_t* fg0  = fr.g0.data();
    const int* mv = stm == 0 ? W : B;
    const int* op = stm == 0 ? B : W;
    const int  km = stm == 0 ? t.w : t.b;
    const int  ko = stm == 0 ? t.b : t.w;
    const Tbl* sub = stm == 0 ? capW : capB;
    int tm[4], to[4];

    const int myPc = g.pc[stm];
    int dsq[MAXDST], dcap[MAXDST];
    U64 brk[8];
    if (stm == 0) {
        t.rankAll(op, brk);
        if (fr.flat) {
            // White's whole successor list is a property of the block: the
            // destination square and the frame of the white set it produces.
            // All that is left per successor is whether Black stands on the
            // destination, which makes it a capture into the sub-table.
            for (int k = 0; k < fr.nflat; ++k) {
                const int dst = fr.fdst[(size_t)k];
                const int fb = fr.ffb[(size_t)k], fg = fr.ffg[(size_t)k];
                const int cap = capturedAt(op, ko, dst);
                if (cap < 0) { acc.add(t.get(1, (U64)fb * t.nb + brk[fg])); continue; }
                if (ko == 1) { acc.winNow(); continue; }   // his last man: over
                int c = 0;
                for (int q = 0; q < ko; ++q) if (q != cap) to[c++] = op[q];
                acc.add(sub->get(1, sub->slotIn(fb, fg, to)));
            }
            return;
        }
    }
    for (int j = 0; j < km; ++j) {
        const int nd = genDst(g, myPc, mv[j], mv, km, op, ko, dsq, dcap);
        for (int d = 0; d < nd; ++d) {
            const int dst = dsq[d];
            const int cap = dcap[d];

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
                    acc.add(t.get(1, (U64)fb * t.nb + brk[fg]));
                }
            } else {
                // Only this branch reads the moved set: White's successor is
                // named by its precomputed frame instead, so building and
                // sorting `tm` for White was dead work -- once per successor,
                // on half of all evaluations.
                cpk(tm, mv, km);
                tm[j] = dst; sortk(tm, km);
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
                    acc.add(t.get(0, t.slotIn0(blk, tm)));
                }
            }
        }
    }
}

// --------------------------------------------------------------------------
// Out-counting frontier for the reduced tables.
// --------------------------------------------------------------------------
// The sweep re-evaluates each entry O(D) times -- measured at 17 to 95 on
// these tables.  Out-counting evaluates each entry about twice and otherwise
// only decrements a counter, which is O(b) cheap work per entry.
//
// THE COUNTER IS A TRIGGER, NEVER AN ORACLE.  A fired event re-runs the
// ordinary forward evaluation, so every value written is the sweep's own
// answer.  That is what makes the D4 stabiliser slack harmless here.  A white
// set with a nontrivial stabiliser occupies several slots of one orbit, and a
// reverse move can attribute a predecessor to the wrong one of them, so a
// counter may be decremented too often or not often enough.  Too often costs
// a wasted evaluation, which sees an unresolved successor and declines.  Not
// often enough loses a wake-up, and the closing sweep-to-fixpoint collects
// those.  Neither can write a wrong value.
//
// Every in-table move is a non-capture: White taking a black man converts to
// (w, b-1) and Black taking a white man to (w-1, b), both other tables.  So
// the in-table successor graph is the non-capture move graph and its reverse
// is the same generator run backwards.
static const int FR_FANOUT = 255;    // outs is a byte

// A white set with a nontrivial stabiliser has its orbit spread over several
// slots, and t.slot() names only one of them.  A wake-up must reach all of
// them or the frontier writes values out of order and records wins longer than
// the shortest.  wt[blk] == 8 means the stabiliser is trivial -- one byte to
// check, and it is the overwhelmingly common case.
// The slack case only: walk the stabiliser of this block's representative and
// emit the black set under each element that fixes it.  Split out because it
// is rare -- wt[blk] == 8 means the stabiliser is trivial -- and keeping it
// out of line leaves the common path to the two entry points below.
template <class F>
static void emitOrbitSlack(const Geo& g, const Tbl& t, const Sym& sy,
                           int blk, const int* im, int ps, F fn) {
    const int* Wc = (const int*)&sy.blkSq[(size_t)blk * t.w];
    int tw[4], tb[4];
    for (int e = 1; e < 8; ++e) {
        for (int q = 0; q < t.w; ++q) tw[q] = g.img(e, Wc[q]);
        sortk(tw, t.w);
        bool fix = true;
        for (int q = 0; q < t.w; ++q) if (tw[q] != Wc[q]) { fix = false; break; }
        if (!fix) continue;
        for (int q = 0; q < t.b; ++q) tb[q] = g.img(e, im[q]);
        sortk(tb, t.b);
        fn((U64)blk * t.nb + rk(tb, t.b), ps);
    }
}

// Rewinding a BLACK man leaves the white set alone, so its rank and the two
// random gathers off it -- into blockOf and gTo, tens of megabytes at w = 4 --
// are the same for every predecessor.  The caller lifts them and passes the
// frame in.
template <class F>
static inline void emitOrbitAt(const Geo& g, const Tbl& t, const Sym& sy,
                               int blk, int g0, const int* Bp, int ps, F fn) {
    int im[4];
    for (int q = 0; q < t.b; ++q) im[q] = g.img(g0, Bp[q]);
    sortk(im, t.b);
    fn((U64)blk * t.nb + rk(im, t.b), ps);
    if (sy.wt[blk] == 8) return;
    emitOrbitSlack(g, t, sy, blk, im, ps, fn);
}

// Rewinding a WHITE man leaves the black set alone, so its eight images are
// the same for every predecessor and the caller ranks them once.  Only the
// slack case still needs the squares themselves.
template <class F>
static inline void emitOrbitRanked(const Geo& g, const Tbl& t, const Sym& sy,
                                   const int* Wp, const int* Bp, const U64* brk,
                                   int ps, F fn) {
    const U64 wr = rk(Wp, t.w);
    const int blk = sy.blockOf[wr], g0 = sy.gTo[wr];
    fn((U64)blk * t.nb + brk[g0], ps);
    if (sy.wt[blk] == 8) return;
    int im[4];
    for (int q = 0; q < t.b; ++q) im[q] = g.img(g0, Bp[q]);
    sortk(im, t.b);
    emitOrbitSlack(g, t, sy, blk, im, ps, fn);
}

template <class F>
static void forEachPredSlot(const Geo& g, const Tbl& t, const Sym& sy,
                            const int* W, const int* B, int stm, const Frames* fr, F fn) {
    int dsq[MAXDST], dcap[MAXDST], tm[4];
    if (stm == 0) {                          // Black moved last; rewind a black man
        const U64 wr = rk(W, t.w);           // white set fixed: lift its frame
        const int wblk = sy.blockOf[wr], wg0 = sy.gTo[wr];
        for (int j = 0; j < t.b; ++j) {
            const int nd = genDst(g, g.pc[1], B[j], B, t.b, W, t.w, dsq, dcap);
            for (int d = 0; d < nd; ++d) {
                if (dcap[d] >= 0) continue;  // would be an un-capture: another table
                cpk(tm, B, t.b);
                tm[j] = dsq[d]; sortk(tm, t.b);
                emitOrbitAt(g, t, sy, wblk, wg0, tm, 1, fn);
            }
        }
    } else {                                 // White moved last; rewind a white man
        U64 brk[8];                          // black set fixed: rank its images
        t.rankAll(B, brk);
        if (fr && fr->flat) {
            // A king's and a knight's move relation is its own reverse, so the
            // squares a white man could have come from are the same flat list
            // evalPos walks forward -- and the list carries the frame of the
            // rewound set, so the rank and the two gathers off it are gone
            // too.  A destination Black occupies would be an un-capture, which
            // belongs to another table.
            for (int k = 0; k < fr->nflat; ++k) {
                const int dst = fr->fdst[(size_t)k];
                if (occupies(B, t.b, dst)) continue;
                const int fb = fr->ffb[(size_t)k], fg = fr->ffg[(size_t)k];
                fn((U64)fb * t.nb + brk[fg], 0);
                if (sy.wt[fb] == 8) continue;
                int im[4];
                for (int q = 0; q < t.b; ++q) im[q] = g.img(fg, B[q]);
                sortk(im, t.b);
                emitOrbitSlack(g, t, sy, fb, im, 0, fn);
            }
            return;
        }
        for (int j = 0; j < t.w; ++j) {
            const int nd = genDst(g, g.pc[0], W[j], W, t.w, B, t.b, dsq, dcap);
            for (int d = 0; d < nd; ++d) {
                if (dcap[d] >= 0) continue;
                cpk(tm, W, t.w);
                tm[j] = dsq[d]; sortk(tm, t.w);
                emitOrbitRanked(g, t, sy, tm, B, brk, 0, fn);
            }
        }
    }
}

static bool solveFrontier(const Geo& g, Tbl& t, const Sym& sy, const Tbl* capW,
                          const Tbl* capB, int nthr, bool progress) {
    t.n = g.n; t.m = g.m; t.geo = &g; t.sym = &sy;
    t.nb = (U64)Ck(g.m, t.b); t.nblk = sy.nblk; t.N = t.nblk * t.nb;

    // Ranking a black set by walking colex from zero is O(nb); the sweep gets
    // it for free by iterating, the frontier does not.  Precompute the black
    // sets once -- nb is n^2 for one black man, C(n^2,2) for two.
    std::vector<int32_t> bset((size_t)t.nb * t.b);
    {
        int B[4];
        for (int q = 0; q < t.b; ++q) B[q] = q;
        for (U64 br = 0; br < t.nb; ++br) {
            for (int q = 0; q < t.b; ++q) bset[(size_t)br * t.b + q] = B[q];
            nextCombo(B, t.b, g.m);
        }
    }

    t.alloc(t.N);
    std::vector<uint8_t> outs[2];
    for (int s = 0; s < 2; ++s) outs[s].assign(t.N, 0);

    // Illegal slots, and the orbit-weighted population count.
    {
        t.legal = 0;
        for (U64 blk = 0; blk < t.nblk; ++blk) {
            const int* W = (const int*)&sy.blkSq[(size_t)blk * t.w];
            for (U64 br = 0; br < t.nb; ++br) {
                const int32_t* B = &bset[(size_t)br * t.b];
                bool bad = false;
                for (int p = 0; p < t.w && !bad; ++p)
                    for (int q = 0; q < t.b; ++q) if (W[p] == B[q]) { bad = true; break; }
                const U64 i = blk * t.nb + br;
                if (bad) { t.put(0, i, ILL); t.put(1, i, ILL); }
                else t.legal += sy.wt[blk];
            }
        }
    }

    // ---- init: one forward evaluation per entry ------------------------
    struct Ev { U64 key; int d; };
    std::vector<std::vector<Ev>> tev(nthr);
    std::atomic<bool> tooWide{false};
    {
        auto initer = [&](int q, auto& claim) {
            int B[4];
            Frames fr; fr.alloc(g, t);
            U64 lo, hi;
            std::vector<Ev>& ev = tev[q];
            while (claim(lo, hi)) {
                for (U64 blk = lo; blk < hi; ++blk) {
                    const int* W = (const int*)&sy.blkSq[(size_t)blk * t.w];
                    fr.build(g, t, W);
                    for (U64 br = 0; br < t.nb; ++br) {
                        const U64 i = blk * t.nb + br;
                        if (t.get(0, i) == ILL) continue;
                        for (int z = 0; z < t.b; ++z) B[z] = bset[(size_t)br * t.b + z];
                        for (int stm = 0; stm < 2; ++stm) {
                            Acc a;
                            evalPos(g, t, capW, capB, W, B, stm, a, (int)blk, fr);
                            if (a.notWin > FR_FANOUT) { tooWide = true; return; }
                            outs[stm][i] = (uint8_t)a.notWin;
                            // Exactly the sweep's precedence.  `best` first: a
                            // drawn conversion in hand does NOT settle a position
                            // that also has a win, and an unresolved successor
                            // does not settle one at all.
                            if (a.best)                      ev.push_back({ (i << 1) | (U64)stm, a.best });
                            else if (a.anyUnknown)           { }            // wait for a wake-up
                            else if (!a.moves || a.anyDraw)  t.put(stm, i, 0);
                            else                             ev.push_back({ (i << 1) | (U64)stm, a.worst });
                        }
                    }
                }
            }
        };
        // A block is C(m, b) positions, so a few dozen of them is already a
        // substantial chunk.
        parDyn(nthr, t.nblk, 32, initer);
    }
    if (tooWide.load()) return false;

    // ---- propagate ------------------------------------------------------
    // De-duplication is per depth and MUST NOT be wider than that.  A single
    // "already queued" bit spanning all depths is tempting and is WRONG: a
    // wake-up arriving later with a SHORTER depth would be dropped, the
    // position would fire at its older, longer bucket, and it would record a
    // win two plies too long.  That was an observed bug, uniform +2 across
    // the b = 2 tables.  Within one depth there is nothing to lose, since
    // every event in a bucket carries that bucket's depth; the bitmap below
    // collapses those, and a duplicate that survives is harmless anyway -- it
    // fires, finds the entry already resolved, and costs one comparison.
    std::map<int, std::vector<uint64_t>> bucket;
    auto sched = [&](U64 key, int d) { bucket[d].push_back(key); };
    for (auto& ev : tev) { for (const Ev& e : ev) sched(e.key, e.d); ev.clear(); ev.shrink_to_fit(); }

    // A bucket's wake-ups all land on the very next depth.  A value is
    // written only at the bucket equal to its own magnitude, so a predecessor
    // woken by it is a win in exactly d + 1 -- which means the queue for the
    // next depth needs one bit per slot, not a list of slots.  That removes
    // the serial sort whose only jobs were to group the list by block and
    // collapse its duplicates: scanning a bitmap yields slots in increasing
    // order, which IS block order, and a bit cannot be set twice.  Measured
    // on KKKK v K n = 10, the sort was 4.85s and merging the per-thread lists
    // another 0.77s, against 10.40s of parallel evaluation -- a 35% serial
    // tail on 236 million queued keys.  Collapsing the duplicates on the way
    // in rather than afterwards also cut the traffic itself, 224M pushes down
    // to 83M bits.
    //
    // Each bitmap stands for exactly one depth and is cleared when that depth
    // runs, which is what keeps the dedupe inside a depth.  Two bitmaps, so
    // the depth being consumed and the depth being filled do not collide.
    //
    // Two things still need the list.  A re-evaluation that turns out to
    // belong to a later depth carries its own depth, and so does an init
    // event; those were 5% of the traffic.  And a re-evaluation can name a
    // depth BELOW the bitmap's -- a wake-up delayed by the stabiliser slack,
    // finding a win shorter than the bucket it fired in -- which runs from
    // the map the old way, leaving the bitmap alone for its own depth.

    // Small buckets are not worth eight thread launches.  EGTB_PAR_MIN lowers
    // the threshold so a sanitiser run can be forced down the parallel paths
    // -- both the bitmap drain and the propagation -- on a board small enough
    // to run under one.
    static const size_t kParMin =
        getenv("EGTB_PAR_MIN") ? (size_t)std::atol(getenv("EGTB_PAR_MIN")) : 8192;

    const U64 nkey = 2 * t.N;
    std::vector<U64> bits[2];
    bits[0].assign((size_t)((nkey + 63) / 64), 0);
    bits[1].assign((size_t)((nkey + 63) / 64), 0);
    int cur = 0, bitsD = -1;
    U64 nsetCur = 0;
    std::vector<U64> nsetT((size_t)nthr, 0);

    // Materialise one depth's queue from its bitmap, in increasing key order,
    // and clear the bitmap as it goes.  Two streaming passes: popcount each
    // thread's word range to find where its output starts, then fill.
    auto drainBits = [&](std::vector<U64>& bm, U64 count, std::vector<uint64_t>& out) {
        out.resize((size_t)count);
        if (!count) { std::fill(bm.begin(), bm.end(), 0); return; }
        const size_t nw = bm.size();
        const int P = (count < (U64)kParMin || nthr < 2) ? 1 : nthr;
        const size_t chunk = (nw + P - 1) / P;
        std::vector<U64> off((size_t)P + 1, 0);
        auto pass1 = [&](int q) {
            const size_t lo = std::min((size_t)q * chunk, nw), hi = std::min(lo + chunk, nw);
            U64 c = 0;
            for (size_t z = lo; z < hi; ++z) c += (U64)__builtin_popcountll(bm[z]);
            off[(size_t)q + 1] = c;
        };
        auto pass2 = [&](int q) {
            const size_t lo = std::min((size_t)q * chunk, nw), hi = std::min(lo + chunk, nw);
            U64 at = off[(size_t)q];
            for (size_t z = lo; z < hi; ++z) {
                U64 wv = bm[z];
                if (!wv) continue;
                bm[z] = 0;
                do { const int b = __builtin_ctzll(wv); wv &= wv - 1;
                     out[(size_t)at++] = ((U64)z << 6) | (U64)b; } while (wv);
            }
        };
        if (P == 1) pass1(0);
        else {
            std::vector<std::thread> th;
            for (int q = 0; q < P; ++q) th.emplace_back(pass1, q);
            for (auto& x : th) x.join();
        }
        for (int q = 0; q < P; ++q) off[(size_t)q + 1] += off[(size_t)q];
        // `count` is carried along as bits are set, one increment per 0 -> 1
        // transition, rather than recounted here; this is where the two meet.
        // Getting it wrong would size `out` wrongly, so say so rather than
        // write past it or leave a stale key in the tail.
        if (off[(size_t)P] != count) {
            std::fprintf(stderr, "kings: frontier bitmap holds %llu bits, expected %llu\n",
                         (unsigned long long)off[(size_t)P], (unsigned long long)count);
            std::abort();
        }
        if (P == 1) { pass2(0); return; }
        {
            std::vector<std::thread> th;
            for (int q = 0; q < P; ++q) th.emplace_back(pass2, q);
            for (auto& x : th) x.join();
        }
    };

    // ---- propagate, buckets in increasing depth ------------------------
    // Events inside one bucket are independent: they all carry depth d, and a
    // win at d only reads losses at d-1, which were written in an earlier
    // bucket and are separated from this one by the join.  So a bucket can be
    // split across threads.  What is shared:
    //   * the value array, through the same relaxed atomics the sweep uses;
    //   * `outs`, decremented with a compare-exchange so it can never run
    //     below zero;
    //   * the wake-up queue, which each thread writes locally and which is
    //     merged into the bucket map after the join.
    // A thread can overwrite another's decrement when it self-heals `outs`
    // from its own evaluation.  That can only leave the counter too HIGH, so
    // the position is never wrongly declared lost -- it is left unresolved
    // instead, and the closing fixpoint collects it.
    static const bool kQueueCount = getenv("EGTB_QUEUE") != nullptr;
    static const bool kNoBits = getenv("EGTB_NOBITS") != nullptr;
    struct Wake { int d; uint64_t key; };
    std::vector<std::vector<Wake>> wk(nthr);
    std::atomic<U64> evalsA{0};
    auto decOuts = [&](int ps, U64 pi) -> bool {          // true iff it just hit zero
        std::atomic_ref<uint8_t> r(outs[ps][pi]);
        uint8_t v = r.load(std::memory_order_relaxed);
        while (v) {
            if (r.compare_exchange_weak(v, (uint8_t)(v - 1), std::memory_order_relaxed))
                return v == 1;
        }
        return false;
    };

    std::vector<uint64_t> work;
    for (;;) {
        // The live bitmap stands for depth bitsD; the map holds everything
        // that carries a depth of its own.  Run the smaller of the two, and
        // adopt an empty bitmap for whatever depth comes next so the common
        // case stays on the bitmap.
        const int mapD = bucket.empty() ? (1 << 30) : bucket.begin()->first;
        int d;
        bool useBits;
        if (kNoBits) {
            // EGTB_NOBITS forces every bucket down the list path, which is the
            // queue this file had before the bitmap.  It is how the two are
            // A/B'd against each other, and it is the only way to exercise the
            // list path on a table whose wake-ups all land on d + 1 -- which,
            // measured, is all of them.
            if (mapD == (1 << 30)) break;
            d = mapD; useBits = false;
        } else if (nsetCur == 0) {
            if (mapD == (1 << 30)) break;
            d = mapD; bitsD = d; useBits = true;
        } else if (mapD < bitsD) {
            d = mapD; useBits = false;          // rare: a depth below the bitmap's
        } else {
            d = bitsD; useBits = true;
        }

        Timer tS;
        if (useBits) {
            // Fold this depth's listed events into the bitmap, then drain it:
            // one sorted, de-duplicated queue out of both sources.
            auto it = bucket.find(d);
            if (it != bucket.end()) {
                for (const uint64_t k : it->second) {
                    U64& wd = bits[cur][(size_t)(k >> 6)];
                    const U64 mk = (U64)1 << (k & 63);
                    if (!(wd & mk)) { wd |= mk; ++nsetCur; }
                }
                bucket.erase(it);
            }
            drainBits(bits[cur], nsetCur, work);
            nsetCur = 0;
        } else {
            auto it = bucket.find(d);
            work = std::move(it->second);
            bucket.erase(it);
            std::sort(work.begin(), work.end());
            work.erase(std::unique(work.begin(), work.end()), work.end());
            if (kQueueCount) ++gBackwards;
        }
        if (kQueueCount) { gTsort += tS.s(); gAfterUniq += work.size(); ++gBuckets; }
        if (work.empty()) continue;
        for (auto& v : wk) v.clear();
        std::fill(nsetT.begin(), nsetT.end(), 0);
        const int nxt = 1 - cur;

        auto run = [&](int q, auto& claim) {
            int B0[4];
            Frames fr; fr.alloc(g, t);
            std::vector<Wake>& out = wk[q];
            U64 lastBlk = (U64)-1, loc = 0, newb = 0;
            // Set a bit in the next depth's map; true if this call is what put
            // it there.  Relaxed is enough: the bit only has to be visible by
            // the join, which orders it.
            U64* const nb_ = bits[nxt].data();
            auto setNext = [&](U64 k) -> bool {
                std::atomic_ref<U64> r(nb_[k >> 6]);
                const U64 mk = (U64)1 << (k & 63);
                return !(r.fetch_or(mk, std::memory_order_relaxed) & mk);
            };
            U64 lo, hi;
            while (claim(lo, hi)) {
                for (U64 z = lo; z < hi; ++z) {
                    const U64 key = work[(size_t)z], i = key >> 1;
                    const int stm = (int)(key & 1);
                    if (t.get(stm, i) != UNK) continue;
                    const U64 blk = i / t.nb, br = i % t.nb;
                    const int* W = (const int*)&sy.blkSq[(size_t)blk * t.w];
                    for (int z2 = 0; z2 < t.b; ++z2) B0[z2] = bset[(size_t)br * t.b + z2];
                    if (blk != lastBlk) { fr.build(g, t, W); lastBlk = blk; }
                    Acc a;
                    evalPos(g, t, capW, capB, W, B0, stm, a, (int)blk, fr);
                    ++loc;
                    // Write ONLY at the bucket equal to the value's own magnitude,
                    // which keeps every write in increasing-depth order and is what
                    // makes `a.best` the true shortest win when it is taken.
                    S16 nv;
                    if (a.best) {
                        if (a.best != d) { out.push_back({ a.best, key }); continue; }
                        nv = (S16)a.best;
                    } else if (a.anyUnknown) {
                        std::atomic_ref<uint8_t>(outs[stm][i])
                            .store((uint8_t)a.notWin, std::memory_order_relaxed);
                        continue;
                    } else if (!a.moves || a.anyDraw) {
                        nv = 0;
                    } else {
                        if (a.worst != d) { out.push_back({ a.worst, key }); continue; }
                        nv = (S16)-a.worst;
                    }
                    t.put(stm, i, nv);
                    if (nv == 0) continue;
                    const int mag = nv < 0 ? -nv : nv;
                    forEachPredSlot(g, t, sy, W, B0, stm, &fr, [&](U64 pi, int ps) {
                        if (t.get(ps, pi) != UNK) return;
                        const U64 pk = (pi << 1) | (U64)ps;
                        // mag == d here, so a predecessor woken by this value is a
                        // win in exactly d + 1: the bitmap's depth.  Outside the
                        // bitmap path the list still carries the depth.
                        if (nv >= 0 && !decOuts(ps, pi)) return;
                        if (useBits) { if (setNext(pk)) ++newb; }
                        else         out.push_back({ mag + 1, (uint64_t)pk });
                    });
                }
            }
            evalsA += loc;
            nsetT[(size_t)q] = newb;
            if (kQueueCount) gWake += newb;
        };

        Timer tP;
        // The keys are in slot order, so a chunk of them mostly shares a block
        // and reuses the frame memo; a thousand is enough to bury the atomic
        // and still leaves a short tail.
        parDyn(work.size() < kParMin ? 1 : nthr, work.size(), 1024, run);
        if (kQueueCount) gTpar += tP.s();
        Timer tM;
        for (auto& v : wk) for (const Wake& e : v) bucket[e.d].push_back(e.key);
        if (useBits) {
            U64 tot = 0;
            for (const U64 c : nsetT) tot += c;
            cur = nxt; bitsD = d + 1; nsetCur = tot;
        }
        if (kQueueCount) gTmerge += tM.s();
    }
    const U64 evals = evalsA.load();

    if (kQueueCount) {
        const U64 wk_ = gWake.load(), un = gAfterUniq.load();
        const U64 bu = gBuckets.load(), bk = gBackwards.load();
        std::fprintf(stderr,
            "      queue: %llu wake-ups, %llu keys drained over %llu buckets (%llu from the "
            "list), %llu entries\n",
            (unsigned long long)wk_, (unsigned long long)un, (unsigned long long)bu,
            (unsigned long long)bk, (unsigned long long)(2 * t.N));
        std::fprintf(stderr,
            "      queue: %.2fs drain, %.2fs serial merge, %.2fs parallel eval "
            "(serial tail %.0f%% of propagation)\n",
            gTsort, gTmerge, gTpar,
            100.0 * (gTsort + gTmerge) / std::max(1e-9, gTsort + gTmerge + gTpar));
        gTsort = gTmerge = gTpar = 0;
        gWake = 0; gAfterUniq = 0; gBuckets = 0; gBackwards = 0;
    }
    if (progress) std::printf("      frontier: %llu evaluations (%.2f per entry)\n",
                              (unsigned long long)evals, (double)evals / (double)(2 * t.N));
    return true;
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
            Frames fr; fr.alloc(g, t);
            for (U64 blk = lo; blk < hi; ++blk) {
                if (!live[blk]) continue;
                const int* W = (const int*)&sy.blkSq[(size_t)blk * t.w];
                fr.build(g, t, W);
                bool anyLeft = false;
                for (int q = 0; q < t.b; ++q) B[q] = q;
                for (U64 br = 0; br < t.nb; ++br) {
                    const U64 i = blk * t.nb + br;
                    for (int stm = 0; stm < 2; ++stm) {
                        if (t.get(stm, i) != UNK) continue;
                        Acc a;
                        evalPos(g, t, capW, capB, W, B, stm, a, (int)blk, fr);
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

// The frontier's safety net.  Its counter can miss a wake-up on the slots of a
// symmetric white orbit, so whatever is still unresolved gets the ordinary
// per-ply treatment here -- and it must be PER PLY, with the `best <= k` gate.
// Taking a win as soon as it is computable records the first one found rather
// than the shortest, which is the bug README section 5 reports the reference
// solver hitting; it shows up as depths a few plies too long.
static void fixpoint(const Geo& g, Tbl& t, const Sym& sy, const Tbl* capW,
                     const Tbl* capB, int nthr, int subMax) {
    std::vector<U64> todo;
    for (U64 i = 0; i < t.N; ++i)
        for (int stm = 0; stm < 2; ++stm)
            if (t.get(stm, i) == UNK) todo.push_back((i << 1) | (U64)stm);
    if (todo.empty()) return;

    std::vector<int32_t> bs((size_t)t.nb * t.b);
    {
        int B[4];
        for (int q = 0; q < t.b; ++q) B[q] = q;
        for (U64 br = 0; br < t.nb; ++br) {
            for (int q = 0; q < t.b; ++q) bs[(size_t)br * t.b + q] = B[q];
            nextCombo(B, t.b, g.m);
        }
    }

    for (int k = 1;; ++k) {
        std::atomic<U64> changed{0};
        std::atomic<int> pend{0};
        auto worker = [&](size_t lo, size_t hi) {
            int B[4];
            Frames fr; fr.alloc(g, t);
            U64 last = (U64)-1, loc = 0; int locPend = 0;
            for (size_t z = lo; z < hi; ++z) {
                const U64 key = todo[z], i = key >> 1;
                const int stm = (int)(key & 1);
                if (t.get(stm, i) != UNK) continue;
                const U64 blk = i / t.nb, br = i % t.nb;
                const int* W = (const int*)&sy.blkSq[(size_t)blk * t.w];
                if (blk != last) { fr.build(g, t, W); last = blk; }
                for (int q = 0; q < t.b; ++q) B[q] = bs[(size_t)br * t.b + q];
                Acc a;
                evalPos(g, t, capW, capB, W, B, stm, a, (int)blk, fr);
                S16 nv;
                if (a.best && a.best <= k)      nv = (S16)a.best;
                else if (a.best)                { if (a.best > locPend) locPend = a.best; continue; }
                else if (a.anyUnknown)          continue;
                else if (!a.moves || a.anyDraw) nv = 0;
                else                            nv = (S16)-a.worst;
                t.put(stm, i, nv); ++loc;
            }
            changed += loc;
            int cur = pend.load();
            while (locPend > cur && !pend.compare_exchange_weak(cur, locPend)) {}
        };
        std::vector<std::thread> th;
        const size_t chunk = (todo.size() + nthr - 1) / nthr;
        for (int q = 0; q < nthr; ++q) {
            size_t lo = std::min(q * chunk, todo.size()), hi = std::min(lo + chunk, todo.size());
            if (lo < hi) th.emplace_back(worker, lo, hi);
        }
        for (auto& x : th) x.join();
        if (!changed.load() && pend.load() <= k && k > subMax) break;
        if (k > 40000) break;
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
                Tbl& T = t[w][b];
                const Tbl* cW = capWof(w, b);
                const Tbl* cB = capBof(w, b);
                int sm2 = 0;
                if (cW) sm2 = std::max(sm2, cW->maxAbs);
                if (cB) sm2 = std::max(sm2, cB->maxAbs);

                auto finish = [&]() {
                    for (int sm = 0; sm < 2; ++sm)
                        for (U64 z = 0; z < T.N; ++z)
                            if (T.get(sm, z) == UNK) T.put(sm, z, 0);
                    T.maxAbs = 0;
                    for (int sm = 0; sm < 2; ++sm)
                        for (U64 z = 0; z < T.N; ++z) {
                            S16 x = T.get(sm, z);
                            if (x == ILL) continue;
                            int q2 = x < 0 ? -x : x;
                            if (q2 > T.maxAbs) T.maxAbs = q2;
                        }
                };
                auto runFrontier = [&]() -> bool {
                    if (!solveFrontier(g, T, sym[w], cW, cB, nthr, progress)) return false;
                    U64 before = 0;
                    for (U64 z = 0; z < T.N; ++z)
                        for (int sm = 0; sm < 2; ++sm) if (T.get(sm, z) == UNK) ++before;
                    fixpoint(g, T, sym[w], cW, cB, nthr, sm2);
                    U64 after = 0;
                    for (U64 z = 0; z < T.N; ++z)
                        for (int sm = 0; sm < 2; ++sm) if (T.get(sm, z) == UNK) ++after;
                    if (getenv("EGTB_CHECKFRONTIER"))
                        std::fprintf(stderr, "  [fixpoint] K%dvK%d n=%d: %llu unresolved after the "
                                     "frontier, %llu settled by the closing sweep\n",
                                     w, b, g.n, (unsigned long long)before,
                                     (unsigned long long)(before - after));
                    finish();
                    return true;
                };

                if (getenv("EGTB_CHECKFRONTIER")) {
                    std::vector<S16> snap[2];
                    bool ok = runFrontier();
                    if (ok) {
                        for (int sm = 0; sm < 2; ++sm) {
                            snap[sm].resize(T.N);
                            for (U64 z = 0; z < T.N; ++z) snap[sm][z] = T.get(sm, z);
                        }
                    }
                    solve(g, T, sym[w], cW, cB, nthr, progress);
                    if (ok) {
                        U64 bad = 0; U64 fi = 0; int fs = -1;
                        for (int sm = 0; sm < 2; ++sm)
                            for (U64 z = 0; z < T.N; ++z)
                                if (snap[sm][z] != T.get(sm, z)) {
                                    if (!bad) { fi = z; fs = sm; }
                                    ++bad;
                                }
                        if (bad) {
                            const U64 blk = fi / T.nb, br = fi % T.nb;
                            const int* WW = (const int*)&sym[w].blkSq[(size_t)blk * T.w];
                            int BB[4]; for (int q = 0; q < T.b; ++q) BB[q] = q;
                            for (U64 z = 0; z < br; ++z) nextCombo(BB, T.b, g.m);
                            std::string sq;
                            for (int q = 0; q < T.w; ++q) sq += " W" + g.name(WW[q]);
                            for (int q = 0; q < T.b; ++q) sq += " b" + g.name(BB[q]);
                            std::fprintf(stderr, "  [frontier] K%dvK%d n=%d MISMATCH %llu of %llu entries;"
                                         " first stm=%d slot=%llu (%s) frontier=%d sweep=%d\n",
                                         w, b, g.n, (unsigned long long)bad,
                                         (unsigned long long)(2 * T.N), fs,
                                         (unsigned long long)fi, sq.c_str(),
                                         (int)snap[fs][fi], (int)T.get(fs, fi));
                        } else
                            std::fprintf(stderr, "  [frontier] K%dvK%d n=%d identical to the sweep"
                                         " (%llu entries, maxAbs %d)\n", w, b, g.n,
                                         (unsigned long long)(2 * T.N), T.maxAbs);
                    }
                } else if (!(!getenv("EGTB_SWEEP") && runFrontier())) {
                    // The frontier is the default; EGTB_SWEEP forces the old
                    // per-ply induction, and runFrontier() declines by itself
                    // when a fan-out will not fit the one-byte counter.
                    solve(g, T, sym[w], cW, cB, nthr, progress);
                }
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

    // A state's own row never moves, so look it up once rather than once per
    // sweep.  Successors still go through the binary search, which is what
    // keeps this free of the index it is meant to be checking.
    std::vector<uint32_t> slotOf(allPos.size());
    for (size_t i = 0; i < allPos.size(); ++i) slotOf[i] = (uint32_t)find(allKeys[i]);

    const int nthr = std::max(1, (int)std::thread::hardware_concurrency());
    for (int k = 1;; ++k) {
        std::atomic<U64> ch{0};
        std::atomic<int> pend{0};
        auto worker = [&](size_t lo, size_t hi) {
            std::vector<Mv> mvs;
            U64 loc = 0; int locPend = 0;
            for (size_t i = lo; i < hi; ++i) {
                const size_t at = slotOf[i];
                if (ld16(val.data(), at) != UNK) continue;
                genMoves(g, allPos[i].first, allPos[i].second, stms[i], mvs);
                Acc a;
                for (const Mv& M : mvs) {
                    if (M.ends) { a.winNow(); continue; }
                    a.add(ld16(val.data(), find(enc(M.W, M.B, 1 - stms[i]))));
                }
                S16 nv;
                if (a.best && a.best <= k)      nv = (S16)a.best;
                else if (a.best)                { if (a.best > locPend) locPend = a.best; nv = UNK; }
                else if (a.anyUnknown)          nv = UNK;
                else if (!a.moves || a.anyDraw) nv = 0;
                else                            nv = (S16)-a.worst;
                if (nv != UNK) { st16(val.data(), at, nv); ++loc; }
            }
            ch += loc;
            int cur = pend.load();
            while (locPend > cur && !pend.compare_exchange_weak(cur, locPend)) {}
        };
        std::vector<std::thread> th;
        const size_t chunk = (allPos.size() + nthr - 1) / nthr;
        for (int q = 0; q < nthr; ++q) {
            size_t lo = std::min(q * chunk, allPos.size()), hi = std::min(lo + chunk, allPos.size());
            if (lo < hi) th.emplace_back(worker, lo, hi);
        }
        for (auto& x : th) x.join();
        if (!ch.load() && pend.load() <= k) break;
    }
    for (auto& x : val) if (x == UNK) x = 0;

    U64 bad = 0;
    for (size_t i = 0; i < allPos.size(); ++i) {
        S16 mine = val[slotOf[i]];
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
