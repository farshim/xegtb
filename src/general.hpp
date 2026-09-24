// general.hpp -- any bag of men a side, either rule set.
//
// Every other solver here is written for one shape of material.  The shared
// solver needs Black bare; kqkr.cpp needs one man a side; kqkbb.cpp is one
// white man against two black; mixed.cpp is two unlike white men against one
// black; kings.cpp is kings against kings.  Between them they answer 220 of
// the 1,260 materials of at most five men under capture rules and 44 of the 85
// under the ordinary ones.  The rest are not hard in any new way -- they are
// simply shapes nobody wrote a solver for, and there are twenty-eight of them.
//
// So this file does not add a twenty-ninth.  It takes the material itself as
// data: two lists of men, a rule set, and a board.  Everything the other
// solvers fold to compile-time constants -- how many men, which rays, who may
// be captured, what a capture leaves -- is read from those lists at run time.
// That is slower per entry than a templated solver and it gives up the D4
// reduction (see GenIndex), but it is the only way to cover a space this
// irregular without writing a file per shape.
//
// WHAT MAKES A SIDE BEATEN.  Two different conditions are in play, and which
// one applies is a property of the variant, not of the position:
//
//   * a side that has kings is beaten when its LAST KING is captured;
//   * a side that has none is beaten when its LAST MAN is captured.
//
// That distinction cannot be re-derived from a position part-way through.  A
// White with no kings left might be a kingless side still fighting with a
// queen, or a royal side that has just been beaten, and those are opposite
// verdicts.  So `royalW` and `royalB` are carried in the material, fixed by
// the root and inherited by every sub-material.  A material in which a royal
// side has no king, or a kingless side has no men, is not a table at all: it
// is a finished game, and the capture that reaches it is scored on the spot.
#pragma once

#include "table.hpp"
#include "genindex.hpp"

#include <algorithm>
#include <map>
#include <memory>
#include <string>
#include <vector>

namespace kqk {

// The order men are written in, which is not the order CapPiece numbers them:
// K, Q, R, B, N is how a material is spelled everywhere in this project.
inline int genRank(int p) {
    return p == CP_KING   ? 0 : p == CP_QUEEN ? 1 : p == CP_ROOK ? 2
         : p == CP_BISHOP ? 3 : 4;
}

struct GenMat {
    std::vector<U8> w, b;          // CapPiece kinds, each side in genRank order
    bool royalW = true;            // beaten when the last king goes ...
    bool royalB = true;            // ... rather than when the last man goes
    bool capture = true;           // capture rules; false = checkmate and stalemate

    int men() const { return (int)w.size() + (int)b.size(); }

    static int kings(const std::vector<U8>& s) {
        int k = 0;
        for (U8 p : s) if (p == CP_KING) ++k;
        return k;
    }

    // Is this side still in the game?  The two conditions above, as a
    // predicate on a side's remaining men.
    static bool alive(const std::vector<U8>& s, bool royal) {
        return royal ? kings(s) > 0 : !s.empty();
    }
    bool aliveW() const { return alive(w, royalW); }
    bool aliveB() const { return alive(b, royalB); }

    // A material worth building a table for: both sides still playing.  Anything
    // else is a result, not a position.
    bool playable() const { return aliveW() && aliveB(); }

    void sort() {
        auto by = [](U8 x, U8 y) { return genRank(x) < genRank(y); };
        std::stable_sort(w.begin(), w.end(), by);
        std::stable_sort(b.begin(), b.end(), by);
    }

    // What is left when the man at index `i` of `side` is taken.
    GenMat without(int side, int i) const {
        GenMat r = *this;
        std::vector<U8>& s = side == 0 ? r.w : r.b;
        s.erase(s.begin() + i);
        return r;
    }

    std::string letters(const std::vector<U8>& s) const {
        std::string o;
        for (U8 p : s) o += capPieceLetter(p);
        return o;
    }
    std::string name() const {
        std::string o = letters(w);
        o += " vs ";
        o += letters(b);
        return o;
    }
    // A file-name and cache key: the men, the rule set, and the two royalty
    // flags, which are part of the variant and so part of the table's identity.
    std::string key() const {
        std::string o = letters(w) + "v" + letters(b);
        o += capture ? "-cap" : "-mate";
        if (!royalW) o += "-wk0";
        if (!royalB) o += "-bk0";
        return o;
    }
    bool operator<(const GenMat& o) const { return key() < o.key(); }
};

// ---------------------------------------------------------------------------
// The index.  A plain ordered product: one square per man, no symmetry
// reduction at all.
//
// That costs a factor of eight in memory against the reduced solvers, and it
// is a deliberate trade for two reasons.  The first is that the reduction in
// index.hpp is built around a canonical KING PAIR, and half the materials here
// have no such pair -- a side may have no king, or three.  The second is the
// one mixed.cpp gives: an unreduced index shares no canonicalisation with the
// reduced solvers, so running this over a material one of THEM can do and
// comparing entry by entry is a real check rather than a tautology.
//
// The cost is affordable where it matters.  Four men on 8 x 8 is 16.8 M slots;
// five men on 6 x 6 is 60 M.  Five men on 8 x 8 is 1.07 G slots and wants the
// reduction, which is why maxMenFor() below refuses boards that would not fit
// rather than pretending.
// ---------------------------------------------------------------------------
class GenIndex {
public:
    int nsq = 0, k = 0;
    U64 nslots = 0;

    GenIndex() = default;
    GenIndex(int nsquares, int nmen) : nsq(nsquares), k(nmen) {
        nslots = 1;
        for (int i = 0; i < k; ++i) nslots *= (U64)nsq;
    }
    inline U64 encode(const Sq* sq) const {
        U64 i = 0;
        for (int j = 0; j < k; ++j) i = i * (U64)nsq + (U64)sq[j];
        return i;
    }
    inline void decode(U64 i, Sq* sq) const {
        for (int j = k - 1; j >= 0; --j) { sq[j] = (Sq)(i % (U64)nsq); i /= (U64)nsq; }
    }
};

// Signed and relative to the side to move, but carrying one MORE than the
// distance, which the other signed tables here do not:
//   v = +(plies + 1)   the side to move wins in `plies`
//   v = -(plies + 1)   the side to move loses in `plies`
//   v = 0              drawn
//   v = VC_DEAD        not a position (two men on one square, or, under the
//                      ordinary rules, the idle king standing in check)
// The offset is forced by this solver's reach: checkmate, and under capture
// rules every stalemate, is a loss in NOUGHT plies, and writing that as 0
// would make it a draw.  See the head of general.cpp.
class TableGen {
public:
    GenMat mat;
    int n = 0;
    Geometry g;
    GenIndex idx;
    // The D4-reduced ranking, used when `d4` is set.  Both are built: the
    // plain one is what the reduced one is checked against, and keeping it
    // costs two vectors of nothing.
    GenIndexD4 idx4;
    bool d4 = false;
    std::vector<int16_t> v[2];      // [side to move][slot]
    int maxAbs = 0;

    // The sub-tables this one converts into: subW[i] is what is left when
    // White's man i is captured, subB[i] likewise for Black's.  A null entry
    // means the capture ends the game rather than reaching a table, and
    // endW/endB say which way.
    std::vector<const TableGen*> subW, subB;
    std::vector<int> endW, endB;    // +1 the capturing side wins outright, 0 unused

    TableGen(const GenMat& m, int edge, bool reduced = false)
        : mat(m), n(edge), g(edge), d4(reduced) {
        idx = GenIndex(g.nsq, mat.men());
        if (d4) idx4 = GenIndexD4(g, mat.men());
    }

    U64 slots() const { return d4 ? idx4.nslots : idx.nslots; }
    // The slot a placement ranks to.  Under reduction this is the canonical
    // image's slot, so orbit-mates agree; without it, the placement itself.
    inline bool rank(const Sq* sq, U64& out) const {
        if (!d4) { out = idx.encode(sq); return true; }
        return idx4.slotOf(sq, out);
    }
    inline void unrank(U64 slot, Sq* sq) const {
        if (!d4) idx.decode(slot, sq); else idx4.decode(slot, sq);
    }

    inline int16_t at(U64 slot, int stm) const { return v[stm][slot]; }

    // How many men this board can hold before the unreduced index stops being
    // affordable.  Twelve bytes a slot: the two value arrays at two bytes each,
    // and the out-counter and the slowest-win tracker, also one pair of two-byte
    // arrays each, which live for the whole solve.  Counting only the values --
    // which this first did -- understates the peak by three times and would let
    // the solver accept a board it then dies on.
    static constexpr double BYTES_PER_SLOT = 12.0;
    static int maxMenFor(int edge, double budgetBytes = 3e9) {
        const double sq = (double)edge * edge;
        double slots = 1;
        int k = 0;
        for (;; ++k) {
            const double next = slots * sq;
            if (next * BYTES_PER_SLOT > budgetBytes) break;
            slots = next;
        }
        return k;
    }
};

// How the tables of a chain came to exist, so that "the site played this off
// the drive" stays a checkable statement rather than an assumption.
struct GenCounts { int loaded = 0, solved = 0; };

// Solve `m` on an `n` x `n` board, building whatever sub-tables it converts
// into first.  `cache` owns every table built along the way and must outlive
// the one returned.
//
// `storeDir`, when not empty, is a directory of .gen files: every table of the
// chain is read from there when it is present and written there when it is
// not.  Without it the whole chain is re-solved on every call, which for four
// men on 9 x 9 is fifty seconds -- fine for a command, useless for a web page.
using GenCache = std::map<std::string, std::unique_ptr<TableGen>>;
extern bool gGenD4;      // solve on the D4-reduced ranking
// `minSeconds` is the same rule the rest of the store obeys: a table is
// written only when solving it cost more than this, so a cheap one is re-solved
// rather than filling the directory.  `serve --read-only` implements itself by
// setting it beyond any possible solve time, which is why this has to be
// threaded through -- without it the general solver wrote to a store the user
// had asked it not to touch.
const TableGen* genSolve(const GenMat& m, int n, int threads, GenCache& cache,
                         bool progress, const std::string& storeDir = "",
                         GenCounts* counts = nullptr, double minSeconds = 0.0);

// A forward re-derivation of every entry from its successors, the same check
// verify.cpp makes for the shared solver.  Returns the number of mismatches.
U64 genVerify(const TableGen& t, bool progress);

// An independent, single-threaded reference over the same material, compared
// entry by entry.  Returns the number of disagreements.
U64 genBruteForce(const TableGen& t, int threads, bool progress);

// Parse "KQN" / "kqn" into a list of men.  Returns false on an unknown letter.
bool genParseMen(const std::string& s, std::vector<U8>& out);

// ---------------------------------------------------------------------------
// Reading a solved table.  The browser explorer needs exactly these three
// things, and they are exported rather than reimplemented so that what the
// site plays and what the solver proved come from one move generator.
// ---------------------------------------------------------------------------

// A move, in terms of the position's own indices: which man moved, where it
// landed, and which man it took (-1 for none).
struct GenMove { int mover = -1; Sq to = -1; int cap = -1; };

// Is this placement a position of `t`'s material, with `stm` to move?
bool genLegal(const TableGen& t, const Sq* sq, int stm);

// Every legal move.
std::vector<GenMove> genMoveList(const TableGen& t, const Sq* sq, int stm);

// The value of the position `mv` leads to, stated for the player to move
// there, in this file's encoding.  `ends` comes back true when the move
// finishes the game -- it took the opponent's last king, or its last man when
// it had none -- and there is no position to walk on to.
int16_t genValueAfter(const TableGen& t, const Sq* sq, int stm, const GenMove& mv, bool& ends);

// No capture available to either side, whoever is to move.
bool genQuiet(const TableGen& t, const Sq* sq);

} // namespace kqk
