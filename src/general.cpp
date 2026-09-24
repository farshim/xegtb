// general.cpp -- the solver for an arbitrary material.  See general.hpp for
// what this is for and why the index is unreduced.
//
// THE VALUE ENCODING, which differs from mixed.cpp on purpose.
//
// Every other signed table here reads "v plies" straight out of the value and
// uses 0 for a draw.  That works only while no position is lost in ZERO plies.
// Here they abound: a checkmate under the ordinary rules, and under capture
// rules every stalemate as well, are positions whose mover has already lost
// with nothing left to play.  Writing those as 0 would make them drawn.  So a
// value carries one more than the distance:
//
//     v = +(plies + 1)   the side to move wins in `plies`
//     v = -(plies + 1)   the side to move loses in `plies`
//     v = 0              drawn
//     v = VC_DEAD        not a position at all
//
// which leaves checkmate as -1 and mate-in-one as +2, and keeps 0 free.  The
// arithmetic stays as short as before: a successor worth u to the opponent is
// worth 1 - u to the mover when u < 0, and -(u + 1) when u > 0.
//
// HOW IT IS SOLVED.  Out-counting, the scheme mixed.cpp sets out: `outs[p]`
// holds the number of p's moves not yet known to walk into a win for the
// opponent, so p is lost the moment it reaches zero, and the loss is as slow
// as the slowest of those wins.  It is exact here for the two reasons that
// file gives and that still hold for any material: no move inside the table is
// a capture -- every capture changes the material and so leaves for another
// table -- and the index is unreduced, so a move and its retraction are the
// same generator run in the two directions and each predecessor-successor pair
// arises exactly once.  Under a reduced index neither holds and the counter
// would be wrong, which is why kings.cpp does not use one.
#include "general.hpp"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cinttypes>
#include <climits>
#include <cstdio>
#include <cstring>
#include <atomic>
#include <mutex>
#include <queue>
#include <thread>

namespace kqk {
namespace {

constexpr int GEN_MAXMEN = 6;
constexpr int16_t GUNK = VC_UNKNOWN;
constexpr int16_t GILL = VC_DEAD;

const int DF[8] = {  1,  1,  0, -1, -1, -1,  0,  1 };
const int DR[8] = {  0,  1,  1,  1,  0, -1, -1, -1 };
const int KF[8] = {  1,  2,  2,  1, -1, -2, -2, -1 };
const int KR[8] = {  2,  1, -1, -2, -2, -1,  1,  2 };

// ---------------------------------------------------------------------------
// The board, precomputed.
//
// The first version of this file worked the geometry out afresh for every
// destination of every man of every slot: a file and rank from a square, an
// increment, four bounds tests, and -- worst -- a linear scan over the men to
// see what stood there.  For a queen on a 11 x 11 board that is forty-odd
// destinations each costing a scan.  None of it depends on the position, so
// none of it belongs in the inner loop.
//
//   step[d * nsq + s]  the square one step in direction d from s, or -1
//   jump[8 * s + i]    a knight's destinations from s, -1 padded
//
// Occupancy is then a single array lookup rather than a scan.  `at` is kept at
// -1 everywhere between positions and only the k squares in use are written
// and cleared, so setting it up costs k stores rather than nsq.
// ---------------------------------------------------------------------------
struct GenGeo {
    int n = 0, nsq = 0;
    std::vector<int16_t> step;     // 8 * nsq
    std::vector<int16_t> jump;     // 8 * nsq
    explicit GenGeo(int edge) : n(edge), nsq(edge * edge) {
        step.assign((size_t)8 * nsq, -1);
        jump.assign((size_t)8 * nsq, -1);
        for (int s = 0; s < nsq; ++s) {
            const int f0 = s % n, r0 = s / n;
            for (int d = 0; d < 8; ++d) {
                const int f = f0 + DF[d], r = r0 + DR[d];
                if (f >= 0 && f < n && r >= 0 && r < n)
                    step[(size_t)d * nsq + s] = (int16_t)(r * n + f);
            }
            int c = 0;
            for (int d = 0; d < 8; ++d) {
                const int f = f0 + KF[d], r = r0 + KR[d];
                if (f >= 0 && f < n && r >= 0 && r < n)
                    jump[(size_t)8 * s + c++] = (int16_t)(r * n + f);
            }
        }
    }
};

// One per board edge, shared by every table of that size and by every thread.
// Built under a lock the first time and read-only thereafter.
const GenGeo& genGeoFor(int edge) {
    static std::mutex m;
    static std::vector<std::unique_ptr<GenGeo>> cache;
    std::lock_guard<std::mutex> lk(m);
    if ((int)cache.size() <= edge) cache.resize((size_t)edge + 1);
    if (!cache[(size_t)edge]) cache[(size_t)edge] = std::make_unique<GenGeo>(edge);
    return *cache[(size_t)edge];
}

// The occupancy map: square -> index of the man standing there, or -1.  One
// per thread, reused; see the comment above for why it is not cleared whole.
struct OccMap {
    std::vector<int8_t> at;
    explicit OccMap(int nsq) : at((size_t)nsq, (int8_t)-1) {}
    inline void set(const Sq* sq, int k)   { for (int i = 0; i < k; ++i) at[(size_t)sq[i]] = (int8_t)i; }
    inline void clear(const Sq* sq, int k) { for (int i = 0; i < k; ++i) at[(size_t)sq[i]] = (int8_t)-1; }
};

// Hand work out in chunks from a shared counter, as kings.cpp does.  Equal
// shares would do nearly as well here -- that commit measured dynamic at 0 to
// 6% over static -- but the slots of this index are not equal: a range where
// every placement has two men on a square costs almost nothing, and one in the
// middle of the board costs a full move generation for both sides.
template <class F>
void parDyn(int nthr, U64 n, U64 grain, F work) {
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

// A move: which man of the side to move, where it lands, and which man it
// takes (an index into the whole position, or -1).
struct GMove { int mover; Sq to; int cap; };

// Destinations of the man standing at `from`, of kind `pc`, on a board holding
// `sq[0..k-1]`.  `alive[i]` says whether man i is still on; a captured man is
// neither a blocker nor a target.  Written as one loop over both the stepping
// and the sliding kinds rather than specialised, because nothing here is in an
// inner loop that a branch would spoil -- the cost of this solver is the index,
// not the move generator.
template <class F>
void genFrom(const GenGeo& G, const OccMap& occ, int pc, Sq from,
             int firstOther, int lastOther, F fn) {
    const int nsq = G.nsq;
    if (pc == CP_KING || pc == CP_KNIGHT) {
        const int16_t* d = pc == CP_KING ? &G.step[0] : &G.jump[(size_t)8 * from];
        for (int i = 0; i < 8; ++i) {
            const int t = pc == CP_KING ? d[(size_t)i * nsq + from] : d[i];
            if (t < 0) continue;
            const int o = occ.at[(size_t)t];
            if (o >= firstOther && o <= lastOther) continue;      // own man
            fn((Sq)t, o);
        }
        return;
    }
    const int start = capRayStart(pc), stride = capRayStride(pc);
    const int rays = capMaxRays(pc);
    for (int q = 0, d = start; q < rays; ++q, d = (d + stride) & 7) {
        const int16_t* line = &G.step[(size_t)d * nsq];
        int t = line[from];
        while (t >= 0) {
            const int o = occ.at[(size_t)t];
            if (o < 0) { fn((Sq)t, -1); t = line[t]; continue; }
            if (!(o >= firstOther && o <= lastOther)) fn((Sq)t, o);   // a capture
            break;                                                   // blocked either way
        }
    }
}

// The men of `side` occupy a contiguous run of the position, which is what
// lets genFrom tell own from enemy with two comparisons.
struct Layout {
    int nw = 0, k = 0;
    int lo(int side) const { return side == 0 ? 0 : nw; }
    int hi(int side) const { return side == 0 ? nw - 1 : k - 1; }
};

// Is `s` attacked by a man of `side`?  Used only under the ordinary rules, to
// decide check; capture rules have no such notion.  `occ` is the board as it
// stands, which during the legality test below is the board AFTER the move --
// the mover blocks and the captured man does not.
bool attackedBy(const GenGeo& G, const OccMap& occ, const GenMat& m, const Layout& L,
                const Sq* sq, Sq s, int side) {
    const std::vector<U8>& men = side == 0 ? m.w : m.b;
    for (int i = L.lo(side); i <= L.hi(side); ++i) {
        if (occ.at[(size_t)sq[i]] != (int8_t)i) continue;      // taken, or moved away
        bool hit = false;
        genFrom(G, occ, men[i - L.lo(side)], sq[i], L.lo(side), L.hi(side),
                [&](Sq t, int) { if (t == s) hit = true; });
        if (hit) return true;
    }
    return false;
}

Sq kingOf(const GenMat& m, const Layout& L, const Sq* sq, const OccMap& occ, int side) {
    const std::vector<U8>& men = side == 0 ? m.w : m.b;
    for (int i = L.lo(side); i <= L.hi(side); ++i)
        if (men[i - L.lo(side)] == CP_KING && occ.at[(size_t)sq[i]] == (int8_t)i) return sq[i];
    return (Sq)-1;
}

// Every legal move for `side`.  Under capture rules that is every pseudo-legal
// move, kings included as targets; under the ordinary rules a king may not be
// taken and a move may not leave the mover's own king attacked.
//
// The legality test plays the move on the occupancy map and takes it back
// again, rather than copying the position: three stores out and three back.
template <class F>
void forEachMove(const GenGeo& G, OccMap& occ, const GenMat& m, const Layout& L,
                 const Sq* sq, int side, F fn) {
    const std::vector<U8>& men = side == 0 ? m.w : m.b;
    const std::vector<U8>& foe = side == 0 ? m.b : m.w;
    for (int i = L.lo(side); i <= L.hi(side); ++i) {
        const int pc = men[i - L.lo(side)];
        const Sq from = sq[i];
        genFrom(G, occ, pc, from, L.lo(side), L.hi(side), [&](Sq t, int cap) {
            if (!m.capture) {
                if (cap >= 0 && foe[cap - L.lo(1 - side)] == CP_KING) return;  // no king taking
                const int8_t hadT = occ.at[(size_t)t];
                occ.at[(size_t)from] = -1;
                occ.at[(size_t)t]    = (int8_t)i;
                const Sq myK = (pc == CP_KING) ? t : kingOf(m, L, sq, occ, side);
                const bool bad = myK >= 0 && attackedBy(G, occ, m, L, sq, myK, 1 - side);
                occ.at[(size_t)t]    = hadT;
                occ.at[(size_t)from] = (int8_t)i;
                if (bad) return;
            }
            fn(GMove{ i, t, cap });
        });
    }
}

// Is this placement a position at all?  Two men on one square never is; under
// the ordinary rules neither is one where the side NOT to move stands in
// check, because the move before it would have been illegal.
bool legalPlacement(const GenGeo& G, OccMap& occ, const GenMat& m, const Layout& L,
                    const Sq* sq, int stm) {
    if (m.capture) return true;
    const Sq idleK = kingOf(m, L, sq, occ, 1 - stm);
    return !(idleK >= 0 && attackedBy(G, occ, m, L, sq, idleK, stm));
}

// Distinctness, which is cheaper to ask of the occupancy map than pairwise:
// the map holds k entries only when the k squares differ.
inline bool distinct(const Sq* sq, int k) {
    for (int i = 0; i < k; ++i)
        for (int j = i + 1; j < k; ++j)
            if (sq[i] == sq[j]) return false;
    return true;
}

// What a capture is worth to the side that just made it, expressed the way a
// successor is: the value of the position reached, to the player to move
// there.  A capture that beats the opponent outright is "the opponent has lost
// in nought plies", which is -1 in this encoding.
int16_t convValue(const TableGen& t, const Layout& L, const Sq* sq,
                  const GMove& mv, int side) {
    const int capSide = 1 - side;
    const int capIdx  = mv.cap - L.lo(capSide);
    const TableGen* sub = capSide == 0 ? t.subW[capIdx] : t.subB[capIdx];
    if (!sub) return -1;                       // the opponent is beaten
    // The same men, minus the one taken, with the mover moved.
    Sq out[GEN_MAXMEN];
    int o = 0;
    for (int i = 0; i < L.k; ++i) {
        if (i == mv.cap) continue;
        out[o++] = (i == mv.mover) ? mv.to : sq[i];
    }
    U64 sl;
    if (!sub->rank(out, sl)) return 0;
    return sub->v[capSide][(size_t)sl];
}

} // namespace

bool genParseMen(const std::string& s, std::vector<U8>& out) {
    out.clear();
    for (char c : s) {
        switch (c) {
            case 'K': case 'k': out.push_back(CP_KING);   break;
            case 'Q': case 'q': out.push_back(CP_QUEEN);  break;
            case 'R': case 'r': out.push_back(CP_ROOK);   break;
            case 'B': case 'b': out.push_back(CP_BISHOP); break;
            case 'N': case 'n': out.push_back(CP_KNIGHT); break;
            case ' ': case '-': break;
            default: return false;
        }
    }
    return true;
}

// ---------------------------------------------------------------------------
// The solve itself.
// ---------------------------------------------------------------------------
namespace {

// An event, packed.  It was a struct of an int, a U64, an int and a bool --
// 24 bytes after padding -- and there is one per settled entry, so at 8 x 8 the
// init pass alone held 395 MB of them against a 64 MB value array.  The depth
// is implied by which bucket it sits in and the rest is a slot and two bits.
// This is the same accounting kings.cpp made in 99ee861, arrived at the same
// way: by printing what each array cost rather than assuming the values were
// the biggest thing in the program.
// The depth rides in the word too, so a thread can append to ONE buffer.
// Bucketing at the point of emission -- a vector per depth per thread -- keeps
// the same eight bytes but scatters every push across five thousand vectors,
// and measured 11.2 s of propagation against 6.0 s for the flat form.  The
// grouping by depth happens once, at the merge.
using Ev = U64;
constexpr int  EV_DBITS = 11;                       // depth, up to 2047
constexpr U64  EV_DMASK = (1ull << EV_DBITS) - 1;
inline Ev evPack(int d, U64 slot, int stm, bool win) {
    return (slot << (EV_DBITS + 2)) | ((U64)d << 2) | ((U64)stm << 1) | (U64)win;
}
inline U64 evSlot(Ev e) { return e >> (EV_DBITS + 2); }
inline int evDepth(Ev e) { return (int)((e >> 2) & EV_DMASK); }
inline int evStm (Ev e) { return (int)((e >> 1) & 1); }
inline bool evWin(Ev e) { return (e & 1) != 0; }

// Peak accounting, printed under EGTB_MEM.  kings.cpp learned the hard way
// that the value array is not always the biggest thing in the program; the
// only way to know is to count.
std::atomic<U64> gLossAtNext{0}, gLossDeeper{0}, gMerges{0}, gPeakQueued{0};

// ---------------------------------------------------------------------------
// The frontier queue, as a bitmap.
//
// Measured before it was written: at 8 x 8 the init pass held 132 MB of event
// records against a 64 MB value array, while the propagation's own queue never
// exceeded 68 MB.  So the list to remove is the one the INIT makes, which is
// what kings.cpp found in 99ee861 by the same method -- printing what each
// array cost rather than assuming the values were the biggest thing.
//
// One bit per (slot, side to move), in two maps: one for the entries claimed
// as wins at this depth and one for the losses.  A round runs `cur` and writes
// into `next`; a wake-up for d+1 can land on a word the scan has already
// passed, which is why there are two and not one.  A word belongs to exactly
// one thread for the whole round, so running it needs no atomic; writing into
// `next` does, and is a fetch_or.
struct BitQ {
    std::vector<U64> w;                 // win claims
    std::vector<U64> l;                 // loss claims
    U64 nbits = 0;
    void init(U64 slots) { nbits = slots * 2; w.assign((size_t)((nbits + 63) / 64), 0);
                           l.assign(w.size(), 0); }
    static inline U64 bitOf(U64 slot, int stm) { return slot * 2 + (U64)stm; }
    inline void setAtomic(U64 slot, int stm, bool win) {
        const U64 b = bitOf(slot, stm);
        std::vector<U64>& a = win ? w : l;
        std::atomic_ref<U64>(a[(size_t)(b >> 6)]).fetch_or(1ull << (b & 63),
                                                           std::memory_order_relaxed);
    }
    inline void setPlain(U64 slot, int stm, bool win) {
        const U64 b = bitOf(slot, stm);
        (win ? w : l)[(size_t)(b >> 6)] |= 1ull << (b & 63);
    }
    void clear() { std::fill(w.begin(), w.end(), 0ull); std::fill(l.begin(), l.end(), 0ull); }
    bool empty() const {
        for (U64 x : w) if (x) return false;
        for (U64 x : l) if (x) return false;
        return true;
    }
    U64 bytes() const { return (U64)w.size() * 8 * 2; }
};

// Read once.  getenv takes a lock and was being called on every loss-claim
// from every thread: it turned 6 s of propagation into 11.5 s with 50 s of
// system time, and it was measurement code, which is the worst thing for a
// measurement to be.
const bool gMemStats  = getenv("EGTB_MEM")  != nullptr;
const bool gTimeStats = getenv("EGTB_TIME") != nullptr;

struct MemStat {
    U64 initEvents = 0, peakQueued = 0, lossAtNext = 0, lossDeeper = 0;
};

// ---------------------------------------------------------------------------
// The solve on the D4-reduced ranking.
//
// Everything about the induction changes, and for one reason.  On the plain
// ranking a move and its retraction are the same generator run in the two
// directions, and each predecessor-successor pair arises exactly once, so a
// counter of "successors not yet known to be wins" is EXACT and a position can
// be settled by arithmetic on it.  Under reduction that is false: a placement
// whose pair lies on a symmetry axis shares its slot with its images, so
// retracting a move can land on a slot that is not the one the forward move
// came from, and the same relationship can be counted twice or not at all.
//
// kings.cpp met this and answered it in one sentence: the counter is a TRIGGER,
// never an oracle.  Here the trigger is dropped altogether and a woken slot is
// simply re-evaluated forward -- enumerate its moves, look up what they lead
// to, and settle only when that proves a value.  Waking too often costs time;
// waking too rarely would lose entries, so retraction wakes every slot an
// image of the predecessor ranks to.
//
// Every value written is therefore the forward evaluation's own answer, which
// is the same answer the unreduced solver computes.  That is what the check
// against it tests, position by position.
namespace {

// Evaluate one entry from its successors.  `settled` comes back false when
// some successor is still unknown and no win has been found.
int16_t evalEntry(const TableGen& t, const GenGeo& G, OccMap& occ, const Layout& L,
                  const Sq* sq, int stm, bool& settled) {
    const GenMat& m = t.mat;
    int nmoves = 0, bestWin = INT_MAX, worstLoss = 0;
    bool anyDraw = false, anyUnknown = false;
    forEachMove(G, occ, m, L, sq, stm, [&](const GMove& mv) {
        ++nmoves;
        int16_t u;
        if (mv.cap >= 0) u = convValue(t, L, sq, mv, stm);
        else {
            Sq out[GEN_MAXMEN];
            for (int q = 0; q < L.k; ++q) out[q] = sq[q];
            out[mv.mover] = mv.to;
            U64 sl;
            if (!t.rank(out, sl)) return;
            u = t.v[1 - stm][(size_t)sl];
        }
        if (u == GILL)      return;
        if (u == GUNK)      { anyUnknown = true; return; }
        if (u < 0)          bestWin   = std::min(bestWin, 1 - (int)u);
        else if (u > 0)     worstLoss = std::max(worstLoss, (int)u + 1);
        else                anyDraw = true;
    });
    settled = true;
    if (nmoves == 0) {
        bool lost = false;
        if (!m.capture) {
            const Sq myK = kingOf(m, L, sq, occ, stm);
            lost = myK >= 0 && attackedBy(G, occ, m, L, sq, myK, 1 - stm);
        }
        return lost ? (int16_t)-1 : (int16_t)0;
    }
    if (bestWin != INT_MAX) return (int16_t)bestWin;      // a win is final at once
    if (anyUnknown) { settled = false; return GUNK; }
    if (anyDraw) return 0;
    return (int16_t)-worstLoss;
}

} // namespace

void solveOne(TableGen& t, int threads, bool progress);

void solveOneD4(TableGen& t, int threads, bool progress) {
    const Geometry& g = t.g;
    const GenMat& m = t.mat;
    Layout L; L.nw = (int)m.w.size(); L.k = m.men();
    const U64 N = t.idx4.nslots;
    const GenGeo& G = genGeoFor(t.n);
    constexpr int MAXGD = 512;

    for (int s = 0; s < 2; ++s) t.v[s].assign((size_t)N, GUNK);

    BitQ cur, next;
    cur.init(N);
    next.init(N);
    std::vector<std::vector<Ev>> deep(4);
    auto pushDeep = [&](int d, U64 slot, int stm, bool win) {
        if ((size_t)d >= deep.size()) deep.resize((size_t)d + 1);
        deep[(size_t)d].push_back(evPack(d, slot, stm, win));
    };

    // ---- initialisation: one forward evaluation of every canonical entry ---
    std::vector<std::vector<Ev>> tev((size_t)std::max(1, threads));
    parDyn(threads, N, 2048, [&](int q, auto claim) {
        OccMap occ(g.nsq);
        Sq sq[GEN_MAXMEN];
        std::vector<Ev>& ev = tev[(size_t)q];
        U64 lo, hi;
        while (claim(lo, hi)) {
            for (U64 i = lo; i < hi; ++i) {
                t.idx4.decode(i, sq);
                if (!distinct(sq, L.k)) { t.v[0][(size_t)i] = GILL; t.v[1][(size_t)i] = GILL; continue; }
                // A slot whose remaining men are not canonical for their pair is
                // a duplicate of another slot; it holds no position of its own.
                if (!t.idx4.restCanonical(t.idx4.pairIdOf(i), sq + 2)) {
                    t.v[0][(size_t)i] = GILL; t.v[1][(size_t)i] = GILL; continue;
                }
                occ.set(sq, L.k);
                for (int stm = 0; stm < 2; ++stm) {
                    if (!legalPlacement(G, occ, m, L, sq, stm)) { t.v[stm][(size_t)i] = GILL; continue; }
                    bool settled = false;
                    const int16_t v = evalEntry(t, G, occ, L, sq, stm, settled);
                    if (!settled) continue;
                    const int d = v < 0 ? -v : v;
                    if (v == 0) { t.v[stm][(size_t)i] = 0; continue; }
                    if (d == 1)      cur.setAtomic(i, stm, v > 0);
                    else if (d == 2) next.setAtomic(i, stm, v > 0);
                    else             ev.push_back(evPack(d, i, stm, v > 0));
                }
                occ.clear(sq, L.k);
            }
        }
    });
    for (auto& ev : tev) {
        for (const Ev e : ev) pushDeep(evDepth(e), evSlot(e), evStm(e), evWin(e));
        ev.clear(); ev.shrink_to_fit();
    }

    // ---- propagation ------------------------------------------------------
    // Retracting a move gives the predecessor PLACEMENTS; each is ranked, and
    // the slot it ranks to is woken.  Over-waking is harmless -- the woken slot
    // is re-evaluated and settles only if that proves a value -- and is the
    // price of the reduction.
    auto wakePreds = [&](const Sq* pos, OccMap& po, int stm, BitQ& into) {
        const int mover = 1 - stm;
        const std::vector<U8>& men = mover == 0 ? m.w : m.b;
        for (int i = L.lo(mover); i <= L.hi(mover); ++i) {
            const int pc = men[i - L.lo(mover)];
            genFrom(G, po, pc, pos[i], L.lo(mover), L.hi(mover), [&](Sq from, int who) {
                if (who >= 0) return;
                Sq out[GEN_MAXMEN];
                for (int q = 0; q < L.k; ++q) out[q] = pos[q];
                out[i] = from;
                U64 sl;
                if (!t.rank(out, sl)) return;
                const int pstm = mover;
                if (t.v[pstm][(size_t)sl] != GUNK) return;
                into.setAtomic(sl, pstm, /*win=*/true);   // the map is "re-evaluate me"
            });
        }
    };

    const U64 nwords = (U64)cur.w.size();
    int maxDeep = (int)deep.size() - 1;
    for (int d = 1; d <= MAXGD; ++d) {
        if (d < (int)deep.size() && !deep[(size_t)d].empty()) {
            for (const Ev e : deep[(size_t)d]) cur.setPlain(evSlot(e), evStm(e), evWin(e));
            deep[(size_t)d].clear(); deep[(size_t)d].shrink_to_fit();
        }
        if (cur.empty() && d > maxDeep) break;

        std::vector<std::vector<Ev>> tdeep((size_t)std::max(1, threads));
        std::atomic<U64> deeper{0};
        parDyn(threads, nwords, 256, [&](int q, auto claim) {
            OccMap occ(g.nsq);
            Sq pos[GEN_MAXMEN];
            std::vector<Ev>& myDeep = tdeep[(size_t)q];
            U64 lo, hi;
            while (claim(lo, hi)) {
                for (U64 wi = lo; wi < hi; ++wi) {
                    for (int side = 0; side < 2; ++side) {
                        std::vector<U64>& arr = side == 0 ? cur.w : cur.l;
                        U64 word = arr[(size_t)wi];
                        if (!word) continue;
                        arr[(size_t)wi] = 0;
                        while (word) {
                            const int bit = __builtin_ctzll(word);
                            word &= word - 1;
                            const U64 b = wi * 64 + (U64)bit;
                            const U64 slot = b >> 1;
                            const int stm  = (int)(b & 1);
                            if (t.v[stm][(size_t)slot] != GUNK) continue;
                            t.idx4.decode(slot, pos);
                            occ.set(pos, L.k);
                            bool settled = false;
                            const int16_t v = evalEntry(t, G, occ, L, pos, stm, settled);
                            if (settled) {
                                const int vd = v < 0 ? -v : v;
                                if (v == 0) {
                                    t.v[stm][(size_t)slot] = 0;
                                } else if (vd <= d) {
                                    std::atomic_ref<int16_t> vr(t.v[stm][(size_t)slot]);
                                    int16_t expect = GUNK;
                                    if (vr.compare_exchange_strong(expect, v))
                                        wakePreds(pos, occ, stm, next);
                                } else {
                                    // Settled, but deeper than this round: it waits
                                    // for its own, so that a value is never written
                                    // before the round its distance names.
                                    myDeep.push_back(evPack(vd, slot, stm, v > 0));
                                    ++deeper;
                                }
                            }
                            occ.clear(pos, L.k);
                        }
                    }
                }
            }
        });
        if (deeper.load())
            for (auto& td : tdeep)
                for (const Ev e : td) {
                    const int nd = evDepth(e);
                    if (nd > maxDeep) maxDeep = nd;
                    pushDeep(nd, evSlot(e), evStm(e), evWin(e));
                }
        cur.w.swap(next.w);
        cur.l.swap(next.l);
        next.clear();
    }

    for (int s = 0; s < 2; ++s)
        for (auto& x : t.v[s]) if (x == GUNK) x = 0;
    t.maxAbs = 0;
    for (int s = 0; s < 2; ++s)
        for (int16_t x : t.v[s]) {
            if (x == GILL) continue;
            const int q = x < 0 ? -x : x;
            if (q > t.maxAbs) t.maxAbs = q;
        }
    if (progress)
        std::fprintf(stderr, "  %s %dx%d (D4): %llu slots, deepest %d\n", m.name().c_str(),
                     t.n, t.n, (unsigned long long)N, t.maxAbs ? t.maxAbs - 1 : 0);
}

void solveOne(TableGen& t, int threads, bool progress) {
    const Geometry& g = t.g;
    const GenMat& m = t.mat;
    Layout L; L.nw = (int)m.w.size(); L.k = m.men();
    const U64 N = t.idx.nslots;
    const GenGeo& G = genGeoFor(t.n);
    constexpr int MAXGD = 512;              // deepest bucket a wake-up can name

    for (int s = 0; s < 2; ++s) t.v[s].assign((size_t)N, GUNK);
    // One byte a side for the out-counter, NOT the nibble kings.cpp packs it
    // into.  That file can use four bits because a king has at most eight
    // moves; here a side may have sixty, so a nibble would have to saturate,
    // and a saturating counter needs a second array to hold the true count and
    // a handoff between the two when it crosses fifteen.  Two threads crossing
    // that boundary at once lose a decrement -- which showed up as exactly the
    // queen and rook materials differing -- and the fix is not worth it: the
    // counters measured 32 MB against 64 MB of values and 50 MB of init list,
    // so the nibble would save 8% of the peak for a racy design.
    std::vector<uint8_t> outs[2], mw[2];
    for (int s = 0; s < 2; ++s) { outs[s].assign((size_t)N, 0); mw[s].assign((size_t)N, 0); }

    // An event claims that a position can be settled at this depth.  It is a
    // claim and not a fact: a position may be claimed as a win at ten plies by
    // a conversion and again at three by a move inside the table, and only the
    // shallowest may stand.  Claims are therefore processed in increasing
    // depth and the first one to reach an unsettled position wins; later ones
    // find it settled and are dropped.  Committing a conversion's win straight
    // into the array at initialisation -- which is what this first did -- locks
    // in whichever depth happened to be found first, and that is not the same
    // number.
    // Depths 1 and 2 carry the bulk -- a mate, and a win in one ply -- and go
    // straight into the bitmap.  Everything deeper is sparse (measured: 35% of
    // the init events spread over fifteen depths) and stays a packed list until
    // its depth comes round, when it is merged into the map.
    BitQ cur, next;
    cur.init(N);
    next.init(N);
    std::vector<std::vector<Ev>> deep(4);          // init claims for d >= 3
    auto pushDeep = [&](int d, U64 slot, int stm, bool win) {
        if ((size_t)d >= deep.size()) deep.resize((size_t)d + 1);
        deep[(size_t)d].push_back(evPack(d, slot, stm, win));
    };

    // ---- initialisation ---------------------------------------------------
    // Nothing inside the table is known yet, so this pass must not read the
    // value array for a non-capture move -- not even the entries it has
    // already filled on its way through.  Doing so made `outs` mean different
    // things at different slots, and a successor counted as known here and
    // then delivered again during propagation decremented the counter twice,
    // which settled losses several plies too early.
    //
    // That same property is what lets the pass be split: a slot's answer
    // depends on the sub-tables and on nothing else in this array, so threads
    // never read each other's work.  Each keeps its own occupancy map and its
    // own event list, and the lists are merged once at the join.
    std::vector<std::vector<Ev>> tev((size_t)std::max(1, threads));
    const auto t0Phase = std::chrono::steady_clock::now();
    parDyn(threads, N, 4096, [&](int q, auto claim) {
        OccMap occ(g.nsq);
        Sq sq[GEN_MAXMEN];
        std::vector<Ev>& ev = tev[(size_t)q];
        auto emit = [&](int d, U64 slot, int stm, bool win) {
            if (d < 1) d = 1;
            // A bitmap carries no depth of its own: every bit in `cur` is
            // claimed at the round being run.  So depth 1 goes into `cur` and
            // depth 2 into `next`, which becomes `cur` when round 2 starts.
            // Putting both into `cur` -- which is what this first did -- stamps
            // the mate-in-one entries with the mate-in-nought depth, and every
            // table came out different because of it.
            if (d == 1)      cur.setAtomic(slot, stm, win);
            else if (d == 2) next.setAtomic(slot, stm, win);
            else             ev.push_back(evPack(d, slot, stm, win));
        };
        U64 lo, hi;
        while (claim(lo, hi)) {
            for (U64 i = lo; i < hi; ++i) {
                t.idx.decode(i, sq);
                if (!distinct(sq, L.k)) { t.v[0][(size_t)i] = GILL; t.v[1][(size_t)i] = GILL; continue; }
                occ.set(sq, L.k);
                for (int stm = 0; stm < 2; ++stm) {
                    if (!legalPlacement(G, occ, m, L, sq, stm)) { t.v[stm][(size_t)i] = GILL; continue; }
                    int nmoves = 0, quiet = 0;
                    int bestWin = INT_MAX, worstLoss = 0, open = 0;
                    bool anyDraw = false;
                    forEachMove(G, occ, m, L, sq, stm, [&](const GMove& mv) {
                        ++nmoves;
                        if (mv.cap < 0) { ++quiet; ++open; return; }   // stays in this table
                        const int16_t u = convValue(t, L, sq, mv, stm);
                        if (u < 0)      { bestWin = std::min(bestWin, 1 - (int)u); ++open; }
                        else if (u > 0) { worstLoss = std::max(worstLoss, (int)u + 1); }
                        else            { anyDraw = true; ++open; }
                    });
                    if (nmoves == 0) {
                        // Nothing to play.  Under the ordinary rules that is mate
                        // when the king is attacked and stalemate, a draw, when it
                        // is not.  Under capture rules it is always a draw --
                        // kings.cpp rule 4.  This is NOT the shared solver's
                        // `stalemateLoss`, which scores a CHESS stalemate as a
                        // loss because a bare king with no chess move must step
                        // into attack and be taken; here a king may legally step
                        // into attack, so having no move means being walled in by
                        // one's own men, and that is genuinely drawn.
                        bool lost = false;
                        if (!m.capture) {
                            const Sq myK = kingOf(m, L, sq, occ, stm);
                            lost = myK >= 0 && attackedBy(G, occ, m, L, sq, myK, 1 - stm);
                        }
                        if (lost) emit(1, i, stm, /*win=*/false);     // checkmate
                        else      t.v[stm][(size_t)i] = 0;            // stalemate, drawn
                        continue;
                    }
                    if (bestWin != INT_MAX) emit(bestWin, i, stm, /*win=*/true);
                    if (quiet == 0) {
                        // Every move leaves the table, so this entry is decided here.
                        if (bestWin == INT_MAX) {
                            if (anyDraw) t.v[stm][(size_t)i] = 0;
                            else         emit(worstLoss, i, stm, /*win=*/false);
                        }
                        continue;
                    }
                    // One byte each.  `open` is a move count -- a queen and a king on
                    // 12 x 12 cannot reach 255 squares between them -- and `mw` is a
                    // ply count, which this encoding caps at 254 anyway.  Both are
                    // checked rather than assumed: a silent wrap here would look
                    // exactly like a solved table.
                    if (open > 254 || worstLoss > 254) {
                        std::fprintf(stderr, "error: %s on %dx%d overflows a one-byte "
                                     "counter (open %d, worst %d)\n",
                                     m.name().c_str(), t.n, t.n, open, worstLoss);
                        std::exit(2);
                    }
                    outs[stm][(size_t)i] = (uint8_t)open;
                    mw[stm][(size_t)i]   = (uint8_t)worstLoss;
                }
                occ.clear(sq, L.k);
            }
        }
    });
    const double tInit = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - t0Phase).count();
    MemStat ms;
    for (auto& ev : tev) ms.initEvents += ev.size();
    for (auto& ev : tev) {
        for (const Ev e : ev) pushDeep(evDepth(e), evSlot(e), evStm(e), evWin(e));
        ev.clear(); ev.shrink_to_fit();
    }
    if (gMemStats) {
        U64 q = 0; for (const auto& b : deep) q += b.size();
        // where the init events land, which decides whether a bitmap can hold them
        std::map<int, U64> hist;
        for (size_t dd = 0; dd < deep.size(); ++dd) if (!deep[dd].empty()) hist[(int)dd] = deep[dd].size();
        std::string h; int shown = 0;
        for (auto& kv : hist) { if (shown++ < 8) h += " d" + std::to_string(kv.first) + ":" + std::to_string(kv.second); }
        std::fprintf(stderr, "  MEM init-depths(%zu distinct):%s%s\n", hist.size(), h.c_str(),
                     hist.size() > 8 ? " ..." : "");
        const double MB = 1.0 / 1048576.0;
        std::fprintf(stderr,
            "  MEM %s %dx%d: slots %llu | values %.0f MB | outs %.0f MB | mw %.0f MB | "
            "init list %llu = %.0f MB | bitmaps %.0f MB\n",
            m.name().c_str(), t.n, t.n, (unsigned long long)N,
            (double)N * 4 * MB, (double)N * 2 * MB, (double)N * 2 * MB,
            (unsigned long long)ms.initEvents, (double)ms.initEvents * sizeof(Ev) * MB,
            (double)(cur.bytes() + next.bytes()) * MB);
    }

    // ---- propagation, shallowest first ------------------------------------
    // Retracting a move gives the predecessors: the other side moved last, and
    // it was not a capture -- captures leave the table -- so run its generator
    // backwards from where it now stands and keep the empty squares.
    auto forEachPred = [&](const Sq* pos, OccMap& po, int stm, auto fn) {
        const int mover = 1 - stm;
        const std::vector<U8>& men = mover == 0 ? m.w : m.b;
        for (int i = L.lo(mover); i <= L.hi(mover); ++i) {
            const int pc = men[i - L.lo(mover)];
            genFrom(G, po, pc, pos[i], L.lo(mover), L.hi(mover),
                    [&](Sq from, int who) {
                if (who >= 0) return;                       // it came from an empty square
                Sq out[GEN_MAXMEN];
                for (int q = 0; q < L.k; ++q) out[q] = pos[q];
                out[i] = from;
                fn(t.idx.encode(out));
            });
        }
    };

    // A round can be split because its claims are independent: they all carry
    // depth d, and a win at d only reads losses at d-1, settled in an earlier
    // round and separated from this one by the join.  A thread owns whole
    // WORDS of `cur` for the round, so running them needs no atomic; what is
    // shared is the value array, claimed with a compare-exchange so two claims
    // on one slot cannot both go on to wake its predecessors; `outs`,
    // decremented the same way so it cannot run below zero; and `next`, which
    // is written with fetch_or.
    //
    // The values do not depend on the order any of this happens in -- a win is
    // settled at the round equal to its own depth, and a loss only once its
    // last successor is known -- so one thread and ten produce the same table,
    // which is what the repository's thread-count check demands.
    const auto t0Prop = std::chrono::steady_clock::now();
    const U64 nwords = (U64)cur.w.size();
    int maxDeep = (int)deep.size() - 1;
    for (int d = 1; d <= MAXGD; ++d) {
        // Bring in any init claims that were held back for this depth.
        if (d < (int)deep.size() && !deep[(size_t)d].empty()) {
            for (const Ev e : deep[(size_t)d]) cur.setPlain(evSlot(e), evStm(e), evWin(e));
            deep[(size_t)d].clear();
            deep[(size_t)d].shrink_to_fit();
        }
        if (cur.empty() && d > maxDeep) break;

        std::atomic<U64> deeperCount{0};
        std::vector<std::vector<Ev>> tdeep((size_t)std::max(1, threads));
        parDyn(threads, nwords, 256, [&](int q, auto claim) {
            OccMap occ(g.nsq);
            Sq pos[GEN_MAXMEN];
            std::vector<Ev>& myDeep = tdeep[(size_t)q];
            U64 lo, hi;
            while (claim(lo, hi)) {
                for (U64 wi = lo; wi < hi; ++wi) {
                    for (int side = 0; side < 2; ++side) {
                        std::vector<U64>& arr = side == 0 ? cur.w : cur.l;
                        U64 word = arr[(size_t)wi];
                        if (!word) continue;
                        arr[(size_t)wi] = 0;                 // consumed as it is read
                        const bool eWin = (side == 0);
                        while (word) {
                            const int bit = __builtin_ctzll(word);
                            word &= word - 1;
                            const U64 b = wi * 64 + (U64)bit;
                            const U64 eSlot = b >> 1;
                            const int eStm  = (int)(b & 1);
                            std::atomic_ref<int16_t> vr(t.v[eStm][(size_t)eSlot]);
                            int16_t expect = GUNK;
                            if (!vr.compare_exchange_strong(expect, (int16_t)(eWin ? d : -d)))
                                continue;      // a shallower claim, or a twin, got here
                            t.idx.decode(eSlot, pos);
                            occ.set(pos, L.k);
                            forEachPred(pos, occ, eStm, [&](U64 p) {
                                const int pstm = 1 - eStm;
                                std::atomic_ref<int16_t> pv(t.v[pstm][(size_t)p]);
                                if (pv.load(std::memory_order_relaxed) != GUNK) return;
                                if (eWin) {
                                    // Its mover walks into a win for us, so that
                                    // move is no use to it; when none are left it
                                    // is lost, as slowly as the slowest of them.
                                    std::atomic_ref<uint8_t> mr(mw[pstm][(size_t)p]);
                                    const uint8_t want = (uint8_t)(d + 1);
                                    uint8_t seen = mr.load();
                                    while (seen < want && !mr.compare_exchange_weak(seen, want)) {}
                                    std::atomic_ref<uint8_t> orf(outs[pstm][(size_t)p]);
                                    uint8_t o = orf.load();
                                    for (;;) {
                                        if (o == 0) return;
                                        if (orf.compare_exchange_weak(o, (uint8_t)(o - 1))) break;
                                    }
                                    if (o == 1) {
                                        const int nd = (int)mr.load();
                                        if (gMemStats) { if (nd == d + 1) ++gLossAtNext; else ++gLossDeeper; }
                                        if (nd == d + 1) next.setAtomic(p, pstm, false);
                                        else { myDeep.push_back(evPack(nd, p, pstm, false)); ++deeperCount; }
                                    }
                                } else {
                                    next.setAtomic(p, pstm, true);
                                }
                            });
                            occ.clear(pos, L.k);
                        }
                    }
                }
            }
        });
        // A loss whose depth exceeds d+1 -- possible when a conversion seeded a
        // deeper `mw` than anything inside the table -- goes back on the sparse
        // list.  Measured at nought on every material tried, but a queue that
        // silently drops such a claim would lose the entry altogether.
        if (deeperCount.load()) {
            for (auto& td : tdeep)
                for (const Ev e : td) {
                    const int nd = evDepth(e);
                    if (nd > maxDeep) maxDeep = nd;
                    pushDeep(nd, evSlot(e), evStm(e), evWin(e));
                }
        }
        cur.w.swap(next.w);
        cur.l.swap(next.l);
        next.clear();
    }

    if (gTimeStats)
        std::fprintf(stderr, "  TIME %s %dx%d: init %.2fs, propagate %.2fs, merge-allocs %llu\n",
                     m.name().c_str(), t.n, t.n, tInit,
                     std::chrono::duration<double>(std::chrono::steady_clock::now() - t0Prop).count(),
                     (unsigned long long)gMerges.load());
    if (gMemStats)
        std::fprintf(stderr, "  MEM loss-claims: at d+1 %llu, deeper %llu | peak queued %.0f MB\n",
                     (unsigned long long)gLossAtNext.load(),
                     (unsigned long long)gLossDeeper.load(),
                     (double)gPeakQueued.load() * sizeof(Ev) / 1048576.0);
    for (int s = 0; s < 2; ++s)
        for (auto& x : t.v[s]) if (x == GUNK) x = 0;     // never resolved: drawn
    t.maxAbs = 0;
    for (int s = 0; s < 2; ++s)
        for (int16_t x : t.v[s]) {
            if (x == GILL) continue;
            const int q = x < 0 ? -x : x;
            if (q > t.maxAbs) t.maxAbs = q;
        }
    if (progress)
        std::fprintf(stderr, "  %s %dx%d: %llu slots, deepest %d\n", m.name().c_str(),
                     t.n, t.n, (unsigned long long)N, t.maxAbs ? t.maxAbs - 1 : 0);
}

} // namespace


// ---------------------------------------------------------------------------
// The on-disk form.  One file per table of the chain, named after the material
// and the board, so a five-man configuration is present only when everything
// its captures convert into is present too -- the same bargain the kings store
// and the mixed store make.
//
// The header carries the material as text.  A file records values, not rules,
// and the one way a reader can tell what game a table was solved under is if
// the writer says so; `mixed.cpp` had to retire an entire generation of files
// by bumping a version number for want of that.
// ---------------------------------------------------------------------------
namespace {

constexpr U32 GEN_FILE_VERSION = 2;

// Entries are written one byte wide when the table's deepest value fits, and
// two when it does not.  Nothing here ever needs sixteen bits of range -- the
// deepest KQKR value is 67 plies on 8 x 8 and 103 on 10 x 10 -- but "nothing
// here" is not "nothing ever": KRKN is already 79 plies on 8 x 8, and a bigger
// board could carry it past a signed byte.  So the width is a property of the
// table, decided when it is written and recorded in the header, rather than a
// constant chosen once from the tables that happened to exist.
//
// In the narrow form -128 is the dead marker; values run -126..126 and 127 is
// unused, so the marker cannot collide with a real depth.
constexpr int GEN_NARROW_MAX  = 126;
constexpr int8_t GEN_NARROW_DEAD = -128;

struct GenHeader {
    char    magic[8];        // "GENRLTB"
    U32     version;
    U32     n;
    U64     nslots;
    U64     hash;
    U32     width;           // bytes per entry: 1 or 2
    char    key[60];         // the material, rule set and royalty flags
};
static_assert(sizeof(GenHeader) == 96, "the on-disk general header is fixed at 96 bytes");

U64 genHash(const void* p, size_t len) {
    const unsigned char* q = (const unsigned char*)p;
    U64 h = 1469598103934665603ull;
    for (size_t i = 0; i < len; ++i) { h ^= q[i]; h *= 1099511628211ull; }
    return h;
}

std::string genFileName(const GenMat& m, int n, bool d4) {
    // The ranking is part of the file's identity: the same material solved on
    // the two indices has the same values in a different order, and a reader
    // that took one for the other would be answering with another position's
    // entry every time.
    return m.key() + "-n" + std::to_string(n) + (d4 ? "-d4" : "") + ".gen";
}

bool genLoad(const std::string& path, TableGen& t) {
    std::FILE* f = std::fopen(path.c_str(), "rb");
    if (!f) return false;
    GenHeader h{};
    if (std::fread(&h, sizeof h, 1, f) != 1) { std::fclose(f); return false; }
    const std::string key = t.mat.key();
    if (std::memcmp(h.magic, "GENRLTB", 8) != 0 || h.version != GEN_FILE_VERSION ||
        h.n != (U32)t.n || h.nslots != t.slots() ||
        (h.width != 1 && h.width != 2) ||
        std::strncmp(h.key, key.c_str(), sizeof h.key) != 0) { std::fclose(f); return false; }
    const size_t N = (size_t)t.slots();
    std::vector<int16_t> pay(N * 2);
    if (h.width == 1) {
        std::vector<int8_t> raw(N * 2);
        if (std::fread(raw.data(), 1, raw.size(), f) != raw.size()) { std::fclose(f); return false; }
        std::fclose(f);
        if (genHash(raw.data(), raw.size()) != h.hash) {
            std::fprintf(stderr, "general: %s fails its payload hash -- solving instead\n",
                         path.c_str());
            return false;
        }
        for (size_t i = 0; i < raw.size(); ++i)
            pay[i] = raw[i] == GEN_NARROW_DEAD ? GILL : (int16_t)raw[i];
    } else {
        if (std::fread(pay.data(), sizeof(int16_t), pay.size(), f) != pay.size()) {
            std::fclose(f); return false;
        }
        std::fclose(f);
        if (genHash(pay.data(), pay.size() * sizeof(int16_t)) != h.hash) {
            std::fprintf(stderr, "general: %s fails its payload hash -- solving instead\n",
                         path.c_str());
            return false;
        }
    }
    t.v[0].assign(pay.begin(), pay.begin() + N);
    t.v[1].assign(pay.begin() + N, pay.end());
    t.maxAbs = 0;
    for (int s2 = 0; s2 < 2; ++s2)
        for (int16_t x : t.v[s2]) {
            if (x == GILL) continue;
            const int q = x < 0 ? -x : x;
            if (q > t.maxAbs) t.maxAbs = q;
        }
    return true;
}

void genSave(const std::string& path, const TableGen& t) {
    const size_t N = (size_t)t.slots();
    std::vector<int16_t> pay;
    pay.reserve(N * 2);
    pay.insert(pay.end(), t.v[0].begin(), t.v[0].end());
    pay.insert(pay.end(), t.v[1].begin(), t.v[1].end());
    const bool narrow = t.maxAbs <= GEN_NARROW_MAX;
    std::vector<int8_t> small;
    if (narrow) {
        small.resize(pay.size());
        for (size_t i = 0; i < pay.size(); ++i)
            small[i] = pay[i] == GILL ? GEN_NARROW_DEAD : (int8_t)pay[i];
    }
    const void*  data  = narrow ? (const void*)small.data() : (const void*)pay.data();
    const size_t bytes = narrow ? small.size() : pay.size() * sizeof(int16_t);
    GenHeader h{};
    std::memcpy(h.magic, "GENRLTB", 8);
    h.version = GEN_FILE_VERSION;
    h.n = (U32)t.n;
    h.nslots = t.slots();
    h.width = narrow ? 1u : 2u;
    h.hash = genHash(data, bytes);
    const std::string key = t.mat.key();
    std::snprintf(h.key, sizeof h.key, "%s", key.c_str());
    const std::string tmp = path + ".tmp";
    std::FILE* f = std::fopen(tmp.c_str(), "wb");
    if (!f) return;
    bool ok = std::fwrite(&h, sizeof h, 1, f) == 1 &&
              std::fwrite(data, 1, bytes, f) == bytes;
    ok = (std::fclose(f) == 0) && ok;
    // Written aside and moved into place, so that a run killed mid-write
    // leaves no half-file for the next one to read.
    if (ok) std::rename(tmp.c_str(), path.c_str());
    else    std::remove(tmp.c_str());
}

} // namespace

// The D4-reduced ranking is the default.  It is checked against the plain one
// position by position -- the two put identical values in different places, so
// they cannot be compared as files -- and `--plain` turns it off, which is what
// that check uses to get a second opinion.
bool gGenD4 = true;

const TableGen* genSolve(const GenMat& m0, int n, int threads, GenCache& cache,
                         bool progress, const std::string& storeDir, GenCounts* counts,
                         double minSeconds) {
    (void)threads;
    GenMat m = m0;
    m.sort();
    if (!m.playable()) return nullptr;              // a finished game, not a table
    const std::string k = m.key() + "-n" + std::to_string(n) + (gGenD4 ? "-d4" : "");
    auto it = cache.find(k);
    if (it != cache.end()) return it->second.get();

    auto t = std::make_unique<TableGen>(m, n, gGenD4);
    Layout L; L.nw = (int)m.w.size(); L.k = m.men();
    const std::string path = storeDir.empty() ? std::string()
                                              : storeDir + "/" + genFileName(m, n, gGenD4);
    // Build what every capture converts into, first, so the solve below can
    // read them.  The recursion terminates because a capture always leaves
    // fewer men.
    t->subW.assign(m.w.size(), nullptr);
    t->subB.assign(m.b.size(), nullptr);
    cache.emplace(k, nullptr);                      // reserve, guard against cycles
    for (int side = 0; side < 2; ++side) {
        const std::vector<U8>& men = side == 0 ? m.w : m.b;
        for (size_t i = 0; i < men.size(); ++i) {
            GenMat sm = m.without(side, (int)i);
            const TableGen* s = sm.playable()
                ? genSolve(sm, n, threads, cache, progress, storeDir, counts, minSeconds)
                : nullptr;
            if (side == 0) t->subW[i] = s; else t->subB[i] = s;
        }
    }
    // The conversions had to be built first either way: a loaded table still
    // needs them, because the explorer prices a capture by reading them.
    bool got = false;
    if (!path.empty()) got = genLoad(path, *t);
    if (got) { if (counts) ++counts->loaded; }
    else {
        const auto t0 = std::chrono::steady_clock::now();
        if (t->d4) solveOneD4(*t, threads, progress);
        else       solveOne(*t, threads, progress);
        const double secs = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - t0).count();
        if (counts) ++counts->solved;
        if (!path.empty() && secs >= minSeconds) genSave(path, *t);
    }
    TableGen* raw = t.get();
    cache[k] = std::move(t);
    return raw;
}


// ---------------------------------------------------------------------------
// The reader API declared in general.hpp.  Thin wrappers over the same
// generator the solve used: the explorer must not have a second opinion about
// what a legal move is.
// ---------------------------------------------------------------------------
bool genLegal(const TableGen& t, const Sq* sq, int stm) {
    Layout L; L.nw = (int)t.mat.w.size(); L.k = t.mat.men();
    if (!distinct(sq, L.k)) return false;
    const GenGeo& G = genGeoFor(t.n);
    OccMap occ(t.g.nsq);
    occ.set(sq, L.k);
    const bool ok = legalPlacement(G, occ, t.mat, L, sq, stm);
    occ.clear(sq, L.k);
    return ok;
}

std::vector<GenMove> genMoveList(const TableGen& t, const Sq* sq, int stm) {
    Layout L; L.nw = (int)t.mat.w.size(); L.k = t.mat.men();
    std::vector<GenMove> out;
    if (!distinct(sq, L.k)) return out;
    const GenGeo& G = genGeoFor(t.n);
    OccMap occ(t.g.nsq);
    occ.set(sq, L.k);
    forEachMove(G, occ, t.mat, L, sq, stm, [&](const GMove& mv) {
        out.push_back(GenMove{ mv.mover, mv.to, mv.cap });
    });
    occ.clear(sq, L.k);
    return out;
}

int16_t genValueAfter(const TableGen& t, const Sq* sq, int stm, const GenMove& mv, bool& ends) {
    Layout L; L.nw = (int)t.mat.w.size(); L.k = t.mat.men();
    if (mv.cap < 0) {
        ends = false;
        Sq out[GEN_MAXMEN];
        for (int q = 0; q < L.k; ++q) out[q] = sq[q];
        out[mv.mover] = mv.to;
        U64 sl;
        if (!t.rank(out, sl)) return 0;
        return t.v[1 - stm][(size_t)sl];
    }
    const int capSide = 1 - stm;
    const int capIdx  = mv.cap - L.lo(capSide);
    const TableGen* sub = capSide == 0 ? t.subW[(size_t)capIdx] : t.subB[(size_t)capIdx];
    ends = (sub == nullptr);
    return convValue(t, L, sq, GMove{ mv.mover, mv.to, mv.cap }, stm);
}

bool genQuiet(const TableGen& t, const Sq* sq) {
    Layout L; L.nw = (int)t.mat.w.size(); L.k = t.mat.men();
    if (!distinct(sq, L.k)) return false;
    const GenGeo& G = genGeoFor(t.n);
    OccMap occ(t.g.nsq);
    occ.set(sq, L.k);
    bool any = false;
    for (int stm = 0; stm < 2 && !any; ++stm)
        forEachMove(G, occ, t.mat, L, sq, stm, [&](const GMove& mv) {
            if (mv.cap >= 0) any = true;
        });
    occ.clear(sq, L.k);
    return !any;
}

// ---------------------------------------------------------------------------
// The two independent checks, kept for the reason README gives: a wrong table
// here would be plausible rather than loud.
// ---------------------------------------------------------------------------
U64 genVerify(const TableGen& t, bool progress) {
    const Geometry& g = t.g;
    const GenMat& m = t.mat;
    Layout L; L.nw = (int)m.w.size(); L.k = m.men();
    const GenGeo& G = genGeoFor(t.n);
    OccMap occ(g.nsq);
    Sq sq[GEN_MAXMEN];
    U64 bad = 0;
    for (U64 i = 0; i < t.slots(); ++i) {
        t.unrank(i, sq);
        if (!distinct(sq, L.k)) continue;
        // Under reduction a slot whose remaining men are not canonical holds no
        // position; it is a duplicate and there is nothing to re-derive.
        if (t.d4 && !t.idx4.restCanonical(t.idx4.pairIdOf(i), sq + 2)) continue;
        occ.set(sq, L.k);
        for (int stm = 0; stm < 2; ++stm) {
            const int16_t have = t.v[stm][(size_t)i];
            if (have == GILL) continue;
            int best = INT_MIN;             // re-derived value, as a comparable
            int nmoves = 0;
            int bestWin = INT_MAX, worstLoss = 0;
            bool anyDraw = false;
            forEachMove(G, occ, m, L, sq, stm, [&](const GMove& mv) {
                ++nmoves;
                int16_t u;
                if (mv.cap >= 0) u = convValue(t, L, sq, mv, stm);
                else {
                    Sq out[GEN_MAXMEN];
                    for (int q = 0; q < L.k; ++q) out[q] = sq[q];
                    out[mv.mover] = mv.to;
                    U64 sl;
                    if (!t.rank(out, sl)) return;
                    u = t.v[1 - stm][(size_t)sl];
                }
                if (u == GILL) return;
                if (u < 0)      bestWin   = std::min(bestWin, 1 - (int)u);
                else if (u > 0) worstLoss = std::max(worstLoss, (int)u + 1);
                else            anyDraw = true;
            });
            if (nmoves == 0) {
                bool lost = false;
                if (!m.capture) {
                    const Sq myK = kingOf(m, L, sq, occ, stm);
                    lost = myK >= 0 && attackedBy(G, occ, m, L, sq, myK, 1 - stm);
                }
                best = lost ? -1 : 0;
            } else if (bestWin != INT_MAX) best = bestWin;
            else if (anyDraw)              best = 0;
            else                           best = -worstLoss;
            if (best != (int)have) {
                if (bad < 12)
                    std::fprintf(stderr, "  GEN MISMATCH slot %llu stm %d: table=%d derived=%d\n",
                                 (unsigned long long)i, stm, (int)have, best);
                ++bad;
            }
        }
        occ.clear(sq, L.k);
    }
    if (progress)
        std::fprintf(stderr, "  verification: %llu mismatches\n", (unsigned long long)bad);
    return bad;
}

U64 genBruteForce(const TableGen& t, int threads, bool progress) {
    // A sweep solver: rescan everything once per ply until nothing moves.  It
    // shares the move generator with the real solver -- there is only one
    // definition of how a piece moves in this file, deliberately -- but none
    // of the induction, which is where the interesting mistakes live.
    const Geometry& g = t.g;
    const GenMat& m = t.mat;
    Layout L; L.nw = (int)m.w.size(); L.k = m.men();
    const U64 N = t.slots();
    std::vector<int16_t> b[2];
    for (int s = 0; s < 2; ++s) b[s].assign((size_t)N, GUNK);

    const GenGeo& G = genGeoFor(t.n);
    parDyn(threads, N, 4096, [&](int, auto claim) {
        OccMap occ(g.nsq);
        Sq sq[GEN_MAXMEN];
        U64 lo, hi;
        while (claim(lo, hi))
        for (U64 i = lo; i < hi; ++i) {
            t.unrank(i, sq);
            if (!distinct(sq, L.k)) { b[0][(size_t)i] = GILL; b[1][(size_t)i] = GILL; continue; }
            if (t.d4 && !t.idx4.restCanonical(t.idx4.pairIdOf(i), sq + 2)) {
                b[0][(size_t)i] = GILL; b[1][(size_t)i] = GILL; continue;
            }
            occ.set(sq, L.k);
            for (int stm = 0; stm < 2; ++stm)
                if (!legalPlacement(G, occ, m, L, sq, stm)) b[stm][(size_t)i] = GILL;
            occ.clear(sq, L.k);
        }
    });

    // The deepest value any conversion can hand us, so that a quiet round is
    // not mistaken for the end while seeds still sit above it.  This is the
    // same trap brute.cpp fell into for the three-man endgames.
    int seedMax = 1;
    for (const TableGen* s : t.subW) if (s && s->maxAbs > seedMax) seedMax = s->maxAbs;
    for (const TableGen* s : t.subB) if (s && s->maxAbs > seedMax) seedMax = s->maxAbs;

    for (int d = 1;; ++d) {
        std::atomic<U64> madeA{0};
        parDyn(threads, N, 4096, [&](int, auto claim) {
          OccMap occ(g.nsq);
          Sq sq[GEN_MAXMEN];
          U64 local = 0;
          U64 lo, hi;
          while (claim(lo, hi))
          for (U64 i = lo; i < hi; ++i) {
            t.unrank(i, sq);
            if (!distinct(sq, L.k)) continue;
            if (t.d4 && !t.idx4.restCanonical(t.idx4.pairIdOf(i), sq + 2)) continue;
            occ.set(sq, L.k);
            for (int stm = 0; stm < 2; ++stm) {
                if (b[stm][(size_t)i] != GUNK) continue;
                int nmoves = 0, bestWin = INT_MAX, worstLoss = 0;
                bool anyDraw = false, anyUnknown = false;
                forEachMove(G, occ, m, L, sq, stm, [&](const GMove& mv) {
                    ++nmoves;
                    int16_t u;
                    if (mv.cap >= 0) u = convValue(t, L, sq, mv, stm);
                    else {
                        Sq out[GEN_MAXMEN];
                        for (int q = 0; q < L.k; ++q) out[q] = sq[q];
                        out[mv.mover] = mv.to;
                        U64 sl;
                        if (!t.rank(out, sl)) return;
                        u = b[1 - stm][(size_t)sl];
                    }
                    if (u == GILL) return;
                    if (u == GUNK) { anyUnknown = true; return; }
                    if (u < 0)      bestWin   = std::min(bestWin, 1 - (int)u);
                    else if (u > 0) worstLoss = std::max(worstLoss, (int)u + 1);
                    else            anyDraw = true;
                });
                if (nmoves == 0) {
                    bool lost = false;
                    if (!m.capture) {
                        const Sq myK = kingOf(m, L, sq, occ, stm);
                        lost = myK >= 0 && attackedBy(G, occ, m, L, sq, myK, 1 - stm);
                    }
                    b[stm][(size_t)i] = lost ? (int16_t)-1 : (int16_t)0;
                    ++local;
                } else if (bestWin == d) { b[stm][(size_t)i] = (int16_t)d; ++local; }
                else if (!anyUnknown && bestWin == INT_MAX) {
                    b[stm][(size_t)i] = anyDraw ? (int16_t)0 : (int16_t)-worstLoss;
                    ++local;
                }
            }
            occ.clear(sq, L.k);
          }
          madeA += local;
        });
        if (!madeA.load() && d > seedMax) break;
        if (d > 20000) break;
    }
    for (int s = 0; s < 2; ++s)
        for (auto& x : b[s]) if (x == GUNK) x = 0;

    U64 bad = 0;
    Sq dbg[GEN_MAXMEN];
    for (int s = 0; s < 2; ++s)
        for (U64 i = 0; i < N; ++i)
            if (b[s][(size_t)i] != t.v[s][(size_t)i]) {
                if (bad < 12) {
                    t.unrank(i, dbg);
                    std::fprintf(stderr, "  GEN BRUTE MISMATCH stm %d slot %llu: table=%d brute=%d\n",
                                 s, (unsigned long long)i, (int)t.v[s][(size_t)i],
                                 (int)b[s][(size_t)i]);
                }
                ++bad;
            }
    if (progress)
        std::fprintf(stderr, "  brute force: %llu disagreements\n", (unsigned long long)bad);
    return bad;
}

} // namespace kqk
