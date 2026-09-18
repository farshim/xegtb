// table.hpp -- the tablebase object and its public API.
//
// One object serves every endgame.  `Pos::wp[0 .. mat.np)` are the squares of
// White's non-king pieces; `Material` says how many there are and what they
// are.  The index, the solver and the file format are shared -- only the ray
// sets and the arity differ.
#pragma once

#include <functional>
#include <memory>
#include <string>
#include <vector>

#include "geometry.hpp"
#include "bytearray.hpp"
#include "index.hpp"
#include "indexbb.hpp"
#include "indexkk.hpp"
#include "movegen.hpp"

namespace kqk {

struct Stats {
    U64 slotsPerSide = 0;

    // Counts over canonical slots (one per symmetry class).
    U64 wLive = 0, wWin = 0, wDraw = 0;
    U64 bLive = 0, bLoss = 0, bDraw = 0, bMate = 0, bStale = 0, bEnPrise = 0;
    // Under capture rules a stalemate is a loss rather than a draw, so it
    // leaves bDraw/bStale and joins bLoss.  bStaleLoss counts those, kept
    // apart from bMate so the two terminals stay distinguishable.
    U64 bStaleLoss = 0, fbStaleLoss = 0;
    // bEnPrise counts black-to-move draws in which Black may simply take one
    // of White's pieces, leaving material that cannot mate.

    // The same counts weighted by orbit size, i.e. over the whole board with
    // no symmetry reduction.  These are what published figures report.
    U64 fwLive = 0, fwWin = 0, fwDraw = 0;
    U64 fbLive = 0, fbLoss = 0, fbDraw = 0, fbMate = 0, fbStale = 0, fbEnPrise = 0;

    U32 maxPly = 0;             // deepest win, in plies (white to move)
    Pos longest;                // one position realising it
    U64 longestSlot = ~0ull;    // its slot, so the choice is reproducible
    std::vector<U64> histW;     // canonical white-to-move wins, by ply
    std::vector<U64> histWFull; // the same, weighted by orbit size
};

enum class Outcome { Illegal, Win, Draw, Loss };

struct ProbeResult {
    Outcome outcome = Outcome::Illegal;
    int plies = -1;       // distance to mate in plies, -1 when not a mate line
    int moves = -1;       // the usual "mate in N" count
};

struct Move {
    Pos after;            // resulting placement
    int captured = -1;    // index of the white piece Black took, or -1
};

class Table {
public:
    int n;
    Material mat;
    Geometry geo;
    Index idx;
    ByteArray w;         // white to move, nslots entries
    ByteArray b;         // black to move, nslots entries
    Stats st;

    // Capture rules, in the only form this material can take them.  With one
    // king a side the theorem in the paper says the capture game equals chess
    // with two clauses changed: stalemate becomes a loss, and a checkmate
    // becomes a draw when the mated side is totally immobile under rule 2.
    // The second cannot arise here -- a cornered king has three on-board
    // neighbours and two knights can block at most two of them -- so for this
    // material the capture rules are exactly "stalemate loses", and that is
    // what this flag switches on.
    bool stalemateLoss = false;

    // Owns the next table down when the conversion chain is more than one deep
    // (KNNNK -> KNNK -> KNK under capture rules), so that the whole chain
    // outlives the table at the top of it.
    std::unique_ptr<Table> keepAlive;

    // The table this one converts into when Black captures, or null when
    // Black's capture is an immediate draw and no table is needed.  Only
    // KNNNK sets it, to a KNNK table on the same board: two knights cannot
    // *force* mate, but they can mate, so a black king that grabs a knight
    // has to be looked up rather than assumed safe.  See geometry.hpp.
    const Table* sub = nullptr;

    Table(int edge, Endgame eg = Endgame::KQK)
        : n(edge), mat(Material::of(eg)), geo(edge), idx(geo, mat) {}

    U64 nslots() const { return idx.nslots; }
    Endgame endgame() const { return mat.eg; }

    // ---- generation, verification, i/o ------------------------------------
    void generate(int threads, bool progress);
    // Recomputes every entry from its successors and compares.  Returns the
    // number of mismatches; 0 means the table satisfies the Bellman equations
    // everywhere.  `stride` > 1 checks a deterministic sample.
    U64 verify(int threads, U64 stride, bool progress) const;
    void computeStats(int threads);

    void save(const std::string& path, bool rle) const;
    static std::unique_ptr<Table> load(const std::string& path);

    // ---- probing ----------------------------------------------------------
    ProbeResult probe(const Pos& p, bool whiteToMove) const;
    // Best move for the side to move, or false when there is none.
    bool bestMove(const Pos& p, bool whiteToMove, Move& out) const;
    // Optimal play from the given position, as a list of resulting placements.
    std::vector<Move> principalVariation(const Pos& p, bool whiteToMove) const;

    // Raw entry access; returns V_DEAD for placements that are not legal.
    U8 valueAt(const Pos& p, bool whiteToMove) const {
        for (int i = 0; i < mat.np; ++i) {
            if (p.wp[i] == p.wk || p.wp[i] == p.bk) return V_DEAD;
            for (int j = i + 1; j < mat.np; ++j)
                if (p.wp[i] == p.wp[j]) return V_DEAD;
        }
        U64 s;
        if (!idx.slotOf(p, s)) return V_DEAD;
        return whiteToMove ? w[s] : b[s];
    }

    // Number of board placements in this position's symmetry class.
    int orbitSize(const Pos& p) const {
        int fixed = 0;
        for (int g = 0; g < NSYM; ++g)
            if (geo.image(g, p.wk) == p.wk && geo.image(g, p.bk) == p.bk &&
                idx.cfgFixedBy(g, p.wp))
                ++fixed;
        return NSYM / fixed;
    }
};

// Splits [0, count) into `threads` dynamically scheduled chunks and runs
// body(lo, hi, threadId) on each.
void parallelFor(U64 count, U64 grain, int threads,
                 const std::function<void(U64, U64, int)>& body);

// ---------------------------------------------------------------------------
// The reference implementation: the same endgame solved without any symmetry
// reduction, one byte per placement, single threaded.  Only usable for small
// boards -- it needs n^(2 + 2*np) bytes -- but it is the yardstick the real
// generator is measured against.  See brute.cpp.
// ---------------------------------------------------------------------------
class BruteForce {
public:
    const Geometry& g;
    Material mat;
    U64 stride1 = 0, stride2 = 0;   // index strides for the piece squares
    std::vector<U8> w, b;

    // The table Black's captures convert into, or null when they are draws.
    // Only KNNNK passes one; see Table::sub.
    const Table* sub = nullptr;
    bool staleLoss_ = false;   // capture rules: stalemate is a loss

    BruteForce(const Geometry& geo, Material m, const Table* subTable = nullptr,
               bool staleLoss = false);
    U64 index(const Pos& p) const;
    U8 at(const Pos& p, bool whiteToMove) const;
    Stats census() const;   // whole-board counts only (the f* fields)
};

// ---------------------------------------------------------------------------
// A table-free mating rule for KQK, and its exhaustive scorer.  See policy.cpp.
// ---------------------------------------------------------------------------
struct PolicyScore {
    int n = 0;
    U64 positions = 0;      // legal white-to-move placements scored
    int optimum = 0;        // deepest win in the tablebase, in moves
    int worst = 0;          // deepest win under the rule, in moves
    Pos worstPos{};         // a position realising it
    Pos failPos{};          // a position the rule never mates from, when any
    U64 stuck = 0;          // positions where the rule has no move at all
    U64 cyclic = 0;         // positions from which it never mates
    U64 rule[7] = {0};      // how often each of the six rules fired
    std::vector<Pos> line;  // the worst case played out, after each White move
    std::vector<int> cage;  // the cage size after each of those moves
};

// Scores the rule on an n x n board against every black defence.  `oracle`
// substitutes the tablebase's own best move for the rule; that must reproduce
// `optimum` exactly, which is the control saying the scorer measures the rule
// and not itself.
PolicyScore policyScore(int n, bool oracle, int threads);

// Compares `t` against a freshly built BruteForce, position by position and
// census line by census line.  Returns the number of disagreements.
U64 bruteForceCheck(const Table& t, bool progress);


// ---------------------------------------------------------------------------
// KQKR and KQKB: king and queen against king and one black man, a rook or a
// bishop.  Black is armed, so the entries are signed and the table converts
// into KQK when White captures and into KRK or KBK when Black does.  One
// solver serves both; see kqkr.cpp.
// ---------------------------------------------------------------------------
enum : int16_t {
    VK_DRAW    = 0,
    VK_DEAD    = 32766,
    VK_UNKNOWN = 32767,
};

struct KqkrStats {
    U64 slots = 0;
    U64 wLegal = 0, wWin = 0, wLoss = 0, wDraw = 0;   // white to move
    U64 bLegal = 0, bWin = 0, bLoss = 0, bDraw = 0;   // black to move; win = White wins
    int maxWinPly  = 0;      // deepest white-to-move win, in plies
    int maxLossPly = 0;      // deepest white-to-move loss, in plies
    Pos deepest{};           // a position realising maxWinPly
    Pos deepestLoss{};       // a position realising maxLossPly
    std::vector<U64> histW;  // white-to-move wins by ply
    // Capture rules only: terminals that are draws under the ordinary rules
    // and losses here, counted by the side that is stalemated.  `immobile`
    // counts the other clause of the theorem -- no chess move and no rule 2
    // move either, which is a draw under both rule sets.  For this material it
    // cannot happen, and the solver checks that rather than assuming it.
    U64 staleLossW = 0, staleLossB = 0, immobile = 0;
    double seconds = 0;
};

class TableKQKR {
public:
    int n;
    Geometry geo;
    Material mat;                 // KQKR or KQKB; mat.piece[1] is Black's man
    Index idx;
    std::vector<int16_t> w, b;    // white to move / black to move
    KqkrStats st;

    // Capture-the-king rules.  With one king a side the paper's theorem makes
    // them ordinary chess with a single clause changed -- a side with no legal
    // move loses instead of drawing, unless it is totally immobile -- so they
    // are a flag on this solver rather than a solver of their own.  The two
    // conversions inherit it.
    bool stalemateLoss = false;

    explicit TableKQKR(int edge, Endgame eg = Endgame::KQKR)
        : n(edge), geo(edge), mat(Material::of(eg)), idx(geo, mat) {}

    void generate(int threads, bool progress);
    // Recomputes every entry from its successors with the forward move
    // generator alone.  Returns the number of mismatches.
    U64 verify(int threads, bool progress) const;
    // Signed value; see kqkr.cpp for the encoding.  wp[0] is White's queen,
    // wp[1] Black's rook.
    int16_t valueAt(const Pos& p, bool whiteToMove) const;
};

// What ...xQ leaves: KRK for a black rook, KBK for a black bishop.
Endgame subEndgame(Endgame eg);

// The raw move generators, exposed so a test can compare them against an
// independent implementation.  fn(wk, bk, wq, br, captured); a captured man's
// square is -1.
void kqkrGenWhiteRaw(const Geometry& g, Piece bp, Sq wk, Sq bk, Sq wq, Sq br,
                     const std::function<void(Sq, Sq, Sq, Sq, bool)>& fn);
void kqkrGenBlackRaw(const Geometry& g, Piece bp, Sq wk, Sq bk, Sq wq, Sq br,
                     const std::function<void(Sq, Sq, Sq, Sq, bool)>& fn);

// Walks the legal moves of a KQKR position, reporting each successor and the
// value it leads to -- for a capture that value comes from the KQK or KRK
// table, which is where the win usually actually lands.
void kqkrMoves(const TableKQKR& t, const Pos& p, bool whiteToMove,
               const std::function<void(const Pos&, bool, int16_t)>& fn);

// Cross-checks the KQKR move generator against a naive one, and the index
// against the definition of a D4 orbit, on random placements.  These cover the
// two components the n <= 6 brute force cannot reach on a large board.
// Returns the number of disagreements.
U64 kqkrSelfCheck(int lo, int hi, U64 trials, bool progress,
                  Endgame eg = Endgame::KQKR);

// The same endgame solved with no symmetry and by a different algorithm,
// compared placement by placement.  n^8 entries: small boards only.
U64 kqkrBruteForceCheck(const TableKQKR& t, bool progress);


// ---------------------------------------------------------------------------
// KQKBB: king and queen against king and two bishops.  Five men, Black armed
// with two like pieces, so the entries are signed as in KQKR and the table
// converts twice over: into KQKB when White takes a bishop, and into KBBK read
// with the colours swapped when Black takes the queen.  Both sub-tables are
// owned here, so that a probe or a principal variation can still price a
// capture after generation is over.  See kqkbb.cpp and indexbb.hpp.
// ---------------------------------------------------------------------------
struct KqkbbStats {
    U64 slots = 0;
    U64 wLegal = 0, wWin = 0, wLoss = 0, wDraw = 0;   // white to move
    U64 bLegal = 0, bWin = 0, bLoss = 0, bDraw = 0;   // black to move; win = White wins
    int maxWinPly  = 0;      // deepest white-to-move win, in plies
    int maxLossPly = 0;      // deepest white-to-move loss, in plies
    PosBB deepest{};         // a position realising maxWinPly
    PosBB deepestLoss{};     // a position realising maxLossPly
    std::vector<U64> histW;  // white-to-move wins by ply
    // Positions from which some capture loses for the side making it, and
    // which are therefore re-tested forwards at every ply.  Zero on every
    // board tried so far; see the head of kqkbb.cpp for why the machinery is
    // there anyway.
    U64 watched = 0;
    double seconds = 0;
};

class TableKQKBB {
public:
    int n;
    Geometry   geo;
    IndexKQKBB idx;
    std::vector<int16_t> w, b;          // white to move / black to move

    // The two conversions, built on demand and then kept.  Mutable because a
    // probe or a verification pass is const and still has to be able to price
    // a capture, which means building them if generate() has not already.
    mutable std::unique_ptr<TableKQKR> kqkb;    // White took a bishop
    mutable std::unique_ptr<Table>     kbbk;    // Black took the queen, reversed
    KqkbbStats st;

    explicit TableKQKBB(int edge) : n(edge), geo(edge), idx(geo) {}

    U64 nslots() const { return idx.nslots; }

    // Builds the two sub-tables unless they are already there.
    void buildSubTables(int threads, bool progress) const;
    void generate(int threads, bool progress);
    // Recomputes every entry from its successors with the forward move
    // generator alone.  Returns the number of mismatches.
    U64 verify(int threads, bool progress) const;
    // Signed value, White-relative; see kqkbb.cpp for the encoding.
    int16_t valueAt(const PosBB& p, bool whiteToMove) const;
};

// The raw KQKBB move generators, exposed so a test can compare them against an
// independent implementation.  fn(wk, bk, wq, b1, b2, captured); a captured
// man's square is -1.
void kqkbbGenWhiteRaw(const Geometry& g, Sq wk, Sq bk, Sq wq, Sq b1, Sq b2,
                      const std::function<void(Sq, Sq, Sq, Sq, Sq, bool)>& fn);
void kqkbbGenBlackRaw(const Geometry& g, Sq wk, Sq bk, Sq wq, Sq b1, Sq b2,
                      const std::function<void(Sq, Sq, Sq, Sq, Sq, bool)>& fn);

// Walks the legal moves of a KQKBB position, reporting each successor and the
// value it leads to -- for a capture that value comes from the KQKB or KBBK
// table, which is where the game usually actually ends.
void kqkbbMoves(const TableKQKBB& t, const PosBB& p, bool whiteToMove,
                const std::function<void(const PosBB&, bool, int16_t)>& fn);

// The same endgame with no symmetry and by a different algorithm, compared
// placement by placement.  n^10 entries: the smallest boards only.
U64 kqkbbBruteForceCheck(const TableKQKBB& t, bool progress);

// The move generator against a naive one, and the index against the definition
// of a D4 orbit -- with the two bishops named both ways round -- on random
// placements.  Covers on large boards what the brute force covers on small
// ones.  Returns the number of disagreements.
U64 kqkbbSelfCheck(int lo, int hi, U64 trials, bool progress);


// ---------------------------------------------------------------------------
// KQKK: king and queen against TWO black kings, which may stand beside each
// other but not beside the white king, and where a mate counts only when both
// black kings are mated at once.  See kqkk.cpp for the rules and indexkk.hpp
// for the index -- the block key is a king *triple*, so this endgame shares
// the board geometry with the rest of the program but not the index codec.
//
// Black can still never give check (a black king never stands beside the white
// king), White can still never capture (kings are not takeable) and Black's
// one capture, ...KxQ, still leaves material that cannot mate.  So the entries
// are unsigned bytes and the induction is the same strict two-phase
// alternation solver.cpp uses, not the signed, converting machinery of KQKR.
// ---------------------------------------------------------------------------

// Which reading of "a mate counts only when both kings are mated" the table
// holds.  The two differ in exactly one predicate; see kqkk.cpp.
enum class KkRules : uint8_t {
    Strict = 0,   // Black may not leave *either* king attacked
    Loose  = 1,   // Black may not leave *both* kings attacked at once
};

inline const char* kkRulesName(KkRules r) {
    return r == KkRules::Loose ? "loose" : "strict";
}

struct KqkkStats {
    U64 slots = 0;

    // Over canonical slots, one per symmetry class.
    U64 wLive = 0, wWin = 0, wDraw = 0;
    U64 bLive = 0, bLoss = 0, bDraw = 0, bMate = 0, bStale = 0, bEnPrise = 0;
    // Of the stalemates, those in which exactly one black king is attacked:
    // the single mates that this variant declines to count, and so the price
    // of the rule, position by position.
    U64 bStale1 = 0;
    // The same, weighted by orbit size: counts over the whole board.
    U64 fwLive = 0, fwWin = 0, fwDraw = 0;
    U64 fbLive = 0, fbLoss = 0, fbDraw = 0, fbMate = 0, fbStale = 0, fbEnPrise = 0;
    U64 fbStale1 = 0;

    U32 maxPly = 0;              // deepest win, in plies, white to move
    PosKK longest{};             // one position realising it
    U64 longestSlot = ~0ull;     // its slot, so the choice is reproducible
    std::vector<U64> histW;      // canonical white-to-move wins, by ply
    std::vector<U64> histWFull;  // the same, weighted by orbit size
    double seconds = 0;
};

class TableKQKK {
public:
    int        n;
    KkRules    rules;
    Geometry   geo;
    IndexKQKK  idx;
    std::vector<U8> w;    // white to move, nslots entries
    std::vector<U8> b;    // black to move
    KqkkStats  st;

    explicit TableKQKK(int edge, KkRules r = KkRules::Strict)
        : n(edge), rules(r), geo(edge), idx(geo) {}

    U64 nslots() const { return idx.nslots; }

    void generate(int threads, bool progress);
    // Re-derives every entry from its successors with the forward move
    // generator and the full canonicalisation.  Returns the mismatch count.
    U64  verify(int threads, bool progress) const;
    void computeStats(int threads);

    void save(const std::string& path, bool rle) const;
    static std::unique_ptr<TableKQKK> load(const std::string& path);

    // Raw entry; V_DEAD for placements that are not legal positions.
    U8 valueAt(const PosKK& p, bool whiteToMove) const;
    ProbeResult probe(const PosKK& p, bool whiteToMove) const;
    bool legal(const PosKK& p, bool whiteToMove) const;
    // Is black king `which` (0 or 1) attacked by the queen?
    bool inCheck(const PosKK& p, int which) const;

    // Best move for the side to move; `capture` says it was ...KxQ, which ends
    // the game as a draw and so has no successor inside this table.
    bool bestMove(const PosKK& p, bool whiteToMove, PosKK& out, bool& capture) const;
    std::vector<PosKK> principalVariation(const PosKK& p, bool whiteToMove) const;
};

// Walks the legal moves of a KQKK position, reporting each successor, whether
// it took the queen, and the value it leads to.  A capture reports V_DRAW: the
// position it leaves, a white king against two black kings, is outside this
// table and is drawn.
void kqkkMoves(const TableKQKK& t, const PosKK& p, bool whiteToMove,
               const std::function<void(const PosKK&, bool, U8)>& fn);

// The same endgame with no symmetry reduction and by a different algorithm --
// forward sweeps by ply -- compared against `t` at every one of the n^8
// ordered placements, which checks the index as well as the values.  Needs
// n^8 bytes per side: small boards only.
U64 kqkkBruteForceCheck(const TableKQKK& t, bool progress);

// The move generator against a naive one, and the table value against the
// definition of its symmetry class, on random placements.  Covers on large
// boards what the brute force covers on small ones.
U64 kqkkSelfCheck(int lo, int hi, U64 trials, bool progress);

// ---------------------------------------------------------------------------
// KQKK under CAPTURE rules: every king is an ordinary capturable man and a
// player wins by capturing all of the opponent's.  No check, no mate, no
// stalemate, and both sides can win.  See kqkkcap.cpp.  Entries are signed and **relative to the side to move**:
//   v > 0   the side to move wins in v plies
//   v < 0   the side to move loses in -v plies
//   v == 0  drawn
// (kqkr.cpp is White-relative instead; here both sides win often enough that
// the symmetric form, which needs no sign flips, is much the safer one.)
// ---------------------------------------------------------------------------
enum : int16_t {
    VC_DEAD    = 32766,
    VC_UNKNOWN = 32767,
};

struct KqkkCapStats {
    U64 slots = 0;
    // Over canonical slots, one per symmetry class.  "win" always means the
    // side to move wins.
    U64 wWin = 0, wDraw = 0, wLoss = 0;      // white to move
    U64 bWin = 0, bDraw = 0, bLoss = 0;      // black to move
    // The same weighted by orbit size: counts over the whole board.
    U64 fwWin = 0, fwDraw = 0, fwLoss = 0;
    U64 fbWin = 0, fbDraw = 0, fbLoss = 0;
    int   maxWhite = 0, maxBlack = 0;        // deepest forced win, in plies
    PosKK deepestWhite{}, deepestBlack{};
    // The sub-endgames, which are results in their own right.
    U64 kkkBlackWins = 0, kkkLive = 0;  int kkkDeepest = 0;   // K vs K+K, black to move
    U64 kqkWhiteWins = 0, kqkLive = 0;  int kqkDeepest = 0;   // K+Q vs K, white to move
    // Both sub-tables are solved and verified for both sides to move, so the
    // other half of each is reported too.  Neither is idle: with White to move
    // in K vs K+K he can sometimes take a king and reach bare kings, and with
    // Black to move in K+Q vs K he can sometimes take the queen -- and where
    // the kings are already touching, take the white king outright.
    U64 kkkWtmBlackWins = 0, kkkWtmDraws = 0;
    U64 kqkBtmWhiteWins = 0, kqkBtmDraws = 0, kqkBtmBlackWins = 0;
    U64 kkDraws = 0, kkLive = 0;                              // K vs K, white to move
    // Restricted to *quiet* placements -- nothing hanging: no black king
    // attacked by the queen, none beside the white king.  These are exactly
    // the placements the mating rules of kqkk.cpp call legal with White to
    // move, so the two rule sets can be compared over the same set.
    U64 qwWin = 0, qwDraw = 0, qwLoss = 0;
    U64 qbWin = 0, qbDraw = 0, qbLoss = 0;
    double seconds = 0;
};

class TableKQKKCap {
public:
    int       n;
    Geometry  geo;
    IndexKQKK idx;    // king triples, kings allowed to touch
    Index     idx3;   // KQK material, likewise -- also the king-pair enumeration
    std::vector<int16_t> w, b;                  // K + Q vs K + K
    std::vector<int16_t> kkW, kkB;              // K vs K
    std::vector<int16_t> k3W, k3B;              // K vs K + K
    std::vector<int16_t> q3W, q3B;              // K + Q vs K
    KqkkCapStats st;

    explicit TableKQKKCap(int edge)
        : n(edge), geo(edge), idx(geo, true),
          idx3(geo, Material::of(Endgame::KQK), true) {}

    U64 nslots() const { return idx.nslots; }

    // The two king-only tables, K vs K and K vs K + K.  The second is a
    // three-man endgame on its own and much the cheaper of the two builds,
    // so `--kvkk` stops here.
    void solveKingTables(bool progress);
    // Those two and K + Q vs K, which the four-man induction also needs.
    void solveSubTables(bool progress);
    void generate(int threads, bool progress);
    // Re-derives every entry of every table from its successors.  Returns the
    // number of mismatches.
    U64  verify(int threads, bool progress) const;
    void computeStats(int threads);

    void save(const std::string& path) const;
    static std::unique_ptr<TableKQKKCap> load(const std::string& path);

    int16_t valueAt(const PosKK& p, bool whiteToMove) const;
    int16_t kkValue(Sq wk, Sq bk, bool whiteToMove) const;
    int16_t k3Value(Sq wk, Sq a, Sq b, bool whiteToMove) const;
    int16_t q3Value(Sq wk, Sq wq, Sq bk, bool whiteToMove) const;
};

// Walks the legal moves of a capture-rules KQKK position.  `fn(after, kind,
// value)` reports the resulting placement, what the move did, and the value of
// what it leads to, from the point of view of the side moving *next*.  A
// captured man's square is -1 in `after`; `kind` is one of these:
enum class CapMove : uint8_t { Quiet, TakesKing, TakesQueen, TakesWhiteKing };
void kqkkCapMoves(const TableKQKKCap& t, const PosKK& p, bool whiteToMove,
                  const std::function<void(const PosKK&, CapMove, int16_t)>& fn);

// The same endgame with no symmetry at all and by a different algorithm,
// compared placement by placement.  Needs n^8 entries: small boards only.
U64 kqkkCapBruteForceCheck(const TableKQKKCap& t, bool progress);

// ---------------------------------------------------------------------------
// Kings only, under CAPTURE rules: w white kings against b black kings, for
// 1 <= w <= 3 and 1 <= b <= 2.  See kings.cpp.  This is kqkkcap.cpp's rule set
// with the queen deleted, so every man on the board is royal and either side
// may take.  Entries are signed and relative to the side to move, exactly as
// there: v > 0 the mover wins in v plies, v < 0 the mover loses in -v, 0 drawn.
//
// Unlike every other table here, material falls on BOTH sides, so one object
// holds the whole conversion lattice -- (1,1) up to (w,b) -- and `subStats`
// reports the smaller endgames, which are results in their own right.
// ---------------------------------------------------------------------------
// The four men the capture-rules solver knows.  Every one of these move sets
// is D4-invariant, so the symmetry reduction is the same whichever is on the
// board.  Two things separate them.  Sliders (rook, bishop, queen) can be
// blocked; steppers (king, knight) cannot.  And the attack relation is
// symmetric only between men that share a ray family: rook attacks rook and
// bishop attacks bishop reciprocally, but a rook bearing on a knight or on a
// BISHOP is not bearing from a square either of them attacks -- a square on
// the bishop's rank or file is never on its diagonal -- so it cannot be taken
// in reply.  The queen is the one man that owns both families, so it can bear
// on a rook along a rank while being defended along a diagonal, which is the
// thing two rooks can never do for each other.
enum CapPiece { CP_KING = 0, CP_ROOK = 1, CP_KNIGHT = 2, CP_BISHOP = 3, CP_QUEEN = 4 };

inline char capPieceLetter(int p) {
    return p == CP_ROOK ? 'R' : p == CP_KNIGHT ? 'N'
         : p == CP_BISHOP ? 'B' : p == CP_QUEEN ? 'Q' : 'K';
}
inline const char* capPieceName(int p) {
    return p == CP_ROOK ? "rook" : p == CP_KNIGHT ? "knight"
         : p == CP_BISHOP ? "bishop" : p == CP_QUEEN ? "queen" : "king";
}
inline bool capIsSlider(int p) {
    return p == CP_ROOK || p == CP_BISHOP || p == CP_QUEEN;
}
// Rays walked by a slider: start offset into the direction table, and stride.
// Even directions are the orthogonals, odd ones the diagonals.
inline int capRayStart(int p)  { return p == CP_BISHOP ? 1 : 0; }
inline int capRayStride(int p) { return p == CP_QUEEN ? 1 : 2; }
inline int capMaxRays(int p)   { return p == CP_QUEEN ? 8 : 4; }

// Two unlike white men against one black man, under capture rules.  See
// src/mixed.cpp: the white pair is ordered and the lattice branches on which
// man Black takes, neither of which the kings.cpp index can express.
struct MixedStats {
    int n = 0;
    U64 positions = 0;
    U64 wWin = 0, wDraw = 0, wLoss = 0;
    U64 bWin = 0, bDraw = 0, bLoss = 0;
    int deepestWhite = 0, deepestBlack = 0;
    std::vector<Sq> posWhite, posBlack;
    U64 quiet = 0, quietWinW = 0, quietWinB = 0;
    U64 sub0Win = 0, sub0Draw = 0, sub0Loss = 0;
    U64 sub1Win = 0, sub1Draw = 0, sub1Loss = 0;
    int sub0Deep = 0, sub1Deep = 0;
    std::string line;
    std::vector<int> trace;   // value at each ply of `line`, mover-relative
    double seconds = 0;
};

int runMixed(int n, int whitePiece0, int whitePiece1, int blackPiece,
             int threads, bool wantLine, bool wantQuiet, MixedStats& out);

struct KingsStats {
    int n = 0, w = 0, b = 0;
    U64 slots     = 0;    // canonical slots per side to move
    U64 positions = 0;    // real placements, orbit weighted
    // White-relative counts over the whole board, one row per side to move.
    U64 wWin = 0, wDraw = 0, wLoss = 0;
    U64 bWin = 0, bDraw = 0, bLoss = 0;
    int deepestWhite = 0, deepestBlack = 0;   // plies
    std::vector<Sq> posWhite, posBlack;       // w white squares, then b black
    double seconds = 0;
    U64  mismatches = 0;
    bool verified = false;
};

class TableKings {
public:
    // The piece codes swap the king's step for a rook's ray or a knight's
    // jump in the one place the piece enters the solver; the index, the D4
    // reduction and the conversion lattice are the same for all of them.
    TableKings(int edge, int whiteMen, int blackMen,
               int whitePiece = CP_KING, int blackPiece = CP_KING);
    ~TableKings();
    TableKings(const TableKings&) = delete;
    TableKings& operator=(const TableKings&) = delete;

    void generate(int threads, bool progress);
    void census(int threads, bool verify);

    // Use `dir` as a store of .tb files: any table of the lattice already
    // there is mapped and used as it stands, and any table solved here is
    // written back.  `verify` checks the payload hash on the way in.
    void store(const std::string& dir, bool verify);

    const KingsStats& stats() const;              // the (w, b) table itself
    const KingsStats& subStats(int w, int b) const;   // one of its conversions

    int16_t     probe(const std::vector<Sq>& W, const std::vector<Sq>& B, bool whiteToMove) const;
    std::string line(const std::vector<Sq>& W, const std::vector<Sq>& B,
                     bool whiteToMove, int cap) const;
    std::string square(Sq s) const;
    Sq          parse(const std::string& t) const;

    struct Impl;
private:
    std::unique_ptr<Impl> p;
    friend U64 kingsBruteForceCheck(const TableKings&);
};

// The same lattice solved with no index and no material split: one hash of
// every state of every material, value iterated to a fixpoint and then compared
// position by position.  Checks the combinatorial index, the D4 reduction and
// the conversion seeding in one pass.  Small boards only.
U64 kingsBruteForceCheck(const TableKings& t);

} // namespace kqk
