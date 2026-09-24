// geometry.hpp -- board geometry, D4 symmetry, materials and attack
// primitives for an n x n board.  Squares are numbered s = rank * n + file,
// both 0-based.
//
// The same geometry serves every endgame this program computes.  They differ
// in which of the eight rays White's pieces may travel along, and in how many
// such pieces there are.  D4 maps orthogonal rays to orthogonal rays and
// diagonal rays to diagonal rays, so the symmetry reduction below is valid for
// any of them without change.
#pragma once

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <vector>

namespace kqk {

using Sq  = int32_t;
using U8  = uint8_t;
using U16 = uint16_t;
using U32 = uint32_t;
using U64 = uint64_t;

// ---------------------------------------------------------------------------
// Encoding of one table entry.
//   0 .. MAX_PLY : distance to mate in plies.  Black-to-move entries are
//                  losses and always even, white-to-move entries are wins and
//                  always odd.
//   V_DRAW       : theoretically drawn.
//   V_UNKNOWN    : not yet resolved (only during generation).
//   V_DEAD       : slot does not denote a legal, canonical position.
// ---------------------------------------------------------------------------
enum : U8 {
    MAX_PLY   = 250,
    V_DRAW    = 251,
    V_UNKNOWN = 252,
    V_DEAD    = 253,
};

inline bool isDtm(U8 v) { return v <= MAX_PLY; }

// The eight elements of the dihedral group D4 acting on the board.
constexpr int NSYM = 8;

// The eight ray directions, as (file, rank) deltas.  Orthogonal and diagonal
// alternate, so the orthogonal rays are exactly the even indices and the
// diagonal rays the odd ones.  A rook is a queen that starts at 0 and strides
// by two; a bishop is one that starts at 1 and strides by two.
constexpr int DIR_F[8] = {  1,  1,  0, -1, -1, -1,  0,  1 };
constexpr int DIR_R[8] = {  0,  1,  1,  1,  0, -1, -1, -1 };

// The knight's eight jumps, as (file, rank) deltas.  Like the ray table above
// this set is D4-invariant, so the symmetry reduction is unaffected.
constexpr int NF[8] = {  1,  2,  2,  1, -1, -2, -2, -1 };
constexpr int NR[8] = {  2,  1, -1, -2, -2, -1,  1,  2 };

// White's pieces.  Black always has a bare king.
enum class Piece : uint8_t { Queen = 0, Rook = 1, Bishop = 2, Knight = 3 };

// Rays, for the three sliders.  Meaningless for a knight, which jumps.
constexpr bool isSlider(Piece p) { return p != Piece::Knight; }
constexpr int dirBegin(Piece p) { return p == Piece::Bishop ? 1 : 0; }
constexpr int dirStep (Piece p) { return p == Piece::Queen  ? 1 : 2; }

inline const char* pieceName(Piece p) {
    return p == Piece::Rook   ? "rook"
         : p == Piece::Bishop ? "bishop"
         : p == Piece::Knight ? "knight"
                              : "queen";
}
inline char pieceLetter(Piece p) {
    return p == Piece::Rook   ? 'R'
         : p == Piece::Bishop ? 'B'
         : p == Piece::Knight ? 'N'
                              : 'Q';
}

// At most this many white non-king pieces.
constexpr int MAXWP = 3;

// ---------------------------------------------------------------------------
// The endgames.  Every one of them must satisfy the invariant the whole solver
// rests on: **Black taking any one white piece must leave an immediate draw.**
//
//   KQK, KRK   Black takes the piece  -> bare kings.
//   KBBK       Black takes a bishop   -> KBK, which is also a draw -- under the
//              ORDINARY rules only.  Under capture rules a lone bishop and king
//              can take a bare king's last square away, so KBK is not drawn
//              there and KBBK converts into it, exactly as KNNK converts into
//              KNK.  See Table::stalemateLoss and attachSub().
//   KBNK       Black takes the bishop -> KNK, or the knight -> KBK; both drawn.
//   KNK        Black takes the knight -> bare kings.
//   KNNK       Black takes a knight   -> KNK, which contains no mate at all --
//              not merely no *forced* mate: with one knight there is no
//              placement whatever in which a king is mated, so the position is
//              dead drawn and the invariant holds in its strongest form.
//
// KRRK and KQQK look superficially similar and do *not* qualify: taking one
// rook leaves KRK, which White wins, so those tables cannot be solved without
// the table they convert into.
//
// KNNNK is the same kind of exception and it is easy to get wrong.  Two
// knights cannot *force* mate, which tempts one to score a knight capture as
// an immediate draw -- but "cannot force" is not "cannot".  KNNK contains 120
// mates on 8x8, so a black king that grabs a knight and lands in a net is
// still lost, and KNNNK must read its value out of the KNNK table rather than
// assume it.  It therefore has its own solver, in knnnk.cpp, and appears in
// this enum only for the geometry and the index codec.
//
// KQKR and KQKB are the endgames here that deliberately break the invariant:
// Black has a man, so Black can check, can mate, and taking the queen leaves a
// position White does not simply draw.  They therefore do not use the solver in
// solver.cpp at all -- they share the one in kqkr.cpp, which handles conversion
// into KQK and into the table Black's capture leaves (KRK, or KBK).  They
// appear in this enum only so that they can share the board geometry and the
// index codec, both of which care about nothing beyond how many non-king men
// there are and whether they are alike.
//
// KQKB earns its place by being what KQKBB converts into: White taking one of
// the two bishops leaves king and queen against king and bishop, and kqkbb.cpp
// can no more assume the value of that than KNNNK can assume the value of
// KNNK.  KQKBB itself is not in this enum -- with three black men it shares
// neither the index codec nor the block layout; see indexbb.hpp.
// ---------------------------------------------------------------------------
enum class Endgame : uint8_t { KQK = 0, KRK = 1, KBBK = 2, KBNK = 3, KQKR = 4,
                               KNNK = 5, KNNNK = 6, KNK = 7, KBK = 8, KQKB = 9,
                               // One white man against one black man, the rest
                               // of the sixteen.  KQKR and KQKB came first
                               // because KQKBB needed them; these complete the
                               // set, and between them and the colour mirror
                               // they answer every four-man endgame in which
                               // both sides are armed.  Ordered so that the
                               // white man is never weaker than the black one:
                               // the other ordering is the same table read
                               // from the other side.
                               KQKQ = 10, KQKN = 11, KRKR = 12, KRKB = 13,
                               KRKN = 14, KBKB = 15, KBKN = 16, KNKN = 17,
                               // Two white men against a bare black king, the
                               // seven the shared solver did not have.  KBBK,
                               // KBNK and KNNK were the three whose captures
                               // leave material that cannot mate; these seven
                               // all leave material that can, so every one of
                               // them converts under both rule sets.
                               KQQK = 18, KQRK = 19, KQBK = 20, KQNK = 21,
                               KRRK = 22, KRBK = 23, KRNK = 24,
                               // Three white men against a bare black king.
                               // KNNNK was the only one the index could hold,
                               // because three alike are an unordered triple
                               // and nothing else fitted; these nineteen are
                               // the rest of the multiset.
                               KQQQK = 25,
                               KQQRK = 26,
                               KQQBK = 27,
                               KQQNK = 28,
                               KQRRK = 29,
                               KQRBK = 30,
                               KQRNK = 31,
                               KQBBK = 32,
                               KQBNK = 33,
                               KQNNK = 34,
                               KRRRK = 35,
                               KRRBK = 36,
                               KRRNK = 37,
                               KRBBK = 38,
                               KRBNK = 39,
                               KRNNK = 40,
                               KBBBK = 41,
                               KBBNK = 42,
                               KBNNK = 43 };
constexpr int NUM_ENDGAMES = 44;

// How White's men have to be encoded -- what the index must tell apart.  Two
// men of the same type and colour are interchangeable and their configuration
// is a SET; two of different types are not and it is a sequence.  With three
// men there are three cases rather than two, and the middle one -- a pair and
// an odd man -- is the one that did not exist before.
enum class CfgShape : uint8_t {
    One,             // one man: the square
    PairOrdered,     // two unlike: an ordered pair
    PairUnordered,   // two alike: an unordered pair
    TripleAlike,     // three alike: an unordered triple
    TriplePairOdd,   // two alike in slots 0 and 1, a third man in slot 2
    TripleOrdered,   // three unlike: an ordered triple
};

// The three-man materials, in the order the index wants them: for a pair and
// an odd man, the pair first, so that sorting the first two normalises the
// configuration and the third is left alone.
struct ThreeMan { Piece a, b, c; CfgShape shape; };
constexpr ThreeMan THREE_MAN[] = {
    { Piece::Queen, Piece::Queen, Piece::Queen,   CfgShape::TripleAlike     },  // KQQQK
    { Piece::Queen, Piece::Queen, Piece::Rook,    CfgShape::TriplePairOdd   },  // KQQRK
    { Piece::Queen, Piece::Queen, Piece::Bishop,  CfgShape::TriplePairOdd   },  // KQQBK
    { Piece::Queen, Piece::Queen, Piece::Knight,  CfgShape::TriplePairOdd   },  // KQQNK
    { Piece::Rook,  Piece::Rook,  Piece::Queen,   CfgShape::TriplePairOdd   },  // KQRRK
    { Piece::Queen, Piece::Rook,  Piece::Bishop,  CfgShape::TripleOrdered   },  // KQRBK
    { Piece::Queen, Piece::Rook,  Piece::Knight,  CfgShape::TripleOrdered   },  // KQRNK
    { Piece::Bishop, Piece::Bishop, Piece::Queen,   CfgShape::TriplePairOdd   },  // KQBBK
    { Piece::Queen, Piece::Bishop, Piece::Knight,  CfgShape::TripleOrdered   },  // KQBNK
    { Piece::Knight, Piece::Knight, Piece::Queen,   CfgShape::TriplePairOdd   },  // KQNNK
    { Piece::Rook,  Piece::Rook,  Piece::Rook,    CfgShape::TripleAlike     },  // KRRRK
    { Piece::Rook,  Piece::Rook,  Piece::Bishop,  CfgShape::TriplePairOdd   },  // KRRBK
    { Piece::Rook,  Piece::Rook,  Piece::Knight,  CfgShape::TriplePairOdd   },  // KRRNK
    { Piece::Bishop, Piece::Bishop, Piece::Rook,    CfgShape::TriplePairOdd   },  // KRBBK
    { Piece::Rook,  Piece::Bishop, Piece::Knight,  CfgShape::TripleOrdered   },  // KRBNK
    { Piece::Knight, Piece::Knight, Piece::Rook,    CfgShape::TriplePairOdd   },  // KRNNK
    { Piece::Bishop, Piece::Bishop, Piece::Bishop,  CfgShape::TripleAlike     },  // KBBBK
    { Piece::Bishop, Piece::Bishop, Piece::Knight,  CfgShape::TriplePairOdd   },  // KBBNK
    { Piece::Knight, Piece::Knight, Piece::Bishop,  CfgShape::TriplePairOdd   },  // KBNNK
};
constexpr int THREE_MAN_FIRST = 25;   // the enum value THREE_MAN[0] describes
constexpr bool isThreeMan(Endgame e) {
    return (int)e >= THREE_MAN_FIRST && (int)e < THREE_MAN_FIRST + 19;
}

// Does Black have a man besides the king?  Only the one-against-one endgames
// do, and only the solver in kqkr.cpp may be used on them.
constexpr bool blackArmed(Endgame e) {
    return e == Endgame::KQKR || e == Endgame::KQKB || e == Endgame::KQKQ ||
           e == Endgame::KQKN || e == Endgame::KRKR || e == Endgame::KRKB ||
           e == Endgame::KRKN || e == Endgame::KBKB || e == Endgame::KBKN ||
           e == Endgame::KNKN;
}
// Black's man, for those.  Meaningless for anything else.
constexpr Piece blackPieceOf(Endgame e) {
    return e == Endgame::KQKB || e == Endgame::KRKB || e == Endgame::KBKB ? Piece::Bishop
         : e == Endgame::KQKN || e == Endgame::KRKN || e == Endgame::KBKN ||
           e == Endgame::KNKN ? Piece::Knight
         : e == Endgame::KQKQ ? Piece::Queen
                              : Piece::Rook;
}
// White's man, for those.  For everything else pieceOf(e, 0) says it too; this
// exists so the armed solver can ask without knowing the shape.
constexpr Piece whitePieceOf(Endgame e) {
    return e == Endgame::KRKR || e == Endgame::KRKB || e == Endgame::KRKN ? Piece::Rook
         : e == Endgame::KBKB || e == Endgame::KBKN ? Piece::Bishop
         : e == Endgame::KNKN ? Piece::Knight
                              : Piece::Queen;
}
// The endgame a capture leaves: one man and two kings, which the shared
// solver already has for every piece.
// The endgame of TWO white men against a bare king, for any pair of pieces.
// A three-man endgame converts into one of these when a man is taken, and
// there are exactly ten of them.
constexpr Endgame twoManEndgame(Piece a, Piece b) {
    // Ordered so that the comparison below is a small decision tree rather
    // than a table: queen, rook, bishop, knight.
    const Piece hi = (int)a <= (int)b ? a : b;
    const Piece lo = (int)a <= (int)b ? b : a;
    return hi == Piece::Queen
             ? (lo == Piece::Queen ? Endgame::KQQK : lo == Piece::Rook ? Endgame::KQRK
              : lo == Piece::Bishop ? Endgame::KQBK : Endgame::KQNK)
         : hi == Piece::Rook
             ? (lo == Piece::Rook ? Endgame::KRRK : lo == Piece::Bishop ? Endgame::KRBK
                                                                        : Endgame::KRNK)
         : hi == Piece::Bishop
             ? (lo == Piece::Bishop ? Endgame::KBBK : Endgame::KBNK)
                                    : Endgame::KNNK;
}

constexpr Endgame bareEndgameOf(Piece p) {
    return p == Piece::Rook ? Endgame::KRK
         : p == Piece::Bishop ? Endgame::KBK
         : p == Piece::Knight ? Endgame::KNK
                              : Endgame::KQK;
}

// Compile-time views of an endgame.  The solver, the index codec and the move
// generator are all templated on the Endgame and read these, so the piece
// count, the ray sets and the attack tests fold away to constants.
constexpr int npOf(Endgame e) {
    return isThreeMan(e) ? 3
         : e == Endgame::KNNNK ? 3
         : (e == Endgame::KBBK || e == Endgame::KBNK || e == Endgame::KNNK ||
            e == Endgame::KQQK || e == Endgame::KQRK || e == Endgame::KQBK ||
            e == Endgame::KQNK || e == Endgame::KRRK || e == Endgame::KRBK ||
            e == Endgame::KRNK || blackArmed(e)) ? 2 : 1;
}
// For KQKR this reports the queen and the rook in that order; the rook is
// Black's, which only the KQKR solver needs to know.  The index does not: it
// asks solely for the count and for whether the two are interchangeable.
constexpr Piece pieceOf(Endgame e, int i = 0) {
    return isThreeMan(e)
             ? (i == 0 ? THREE_MAN[(int)e - THREE_MAN_FIRST].a
              : i == 1 ? THREE_MAN[(int)e - THREE_MAN_FIRST].b
                       : THREE_MAN[(int)e - THREE_MAN_FIRST].c)
         : e == Endgame::KQQK  ? Piece::Queen
         : e == Endgame::KQRK  ? (i == 0 ? Piece::Queen : Piece::Rook)
         : e == Endgame::KQBK  ? (i == 0 ? Piece::Queen : Piece::Bishop)
         : e == Endgame::KQNK  ? (i == 0 ? Piece::Queen : Piece::Knight)
         : e == Endgame::KRRK  ? Piece::Rook
         : e == Endgame::KRBK  ? (i == 0 ? Piece::Rook  : Piece::Bishop)
         : e == Endgame::KRNK  ? (i == 0 ? Piece::Rook  : Piece::Knight)
         : blackArmed(e)       ? (i == 0 ? whitePieceOf(e) : blackPieceOf(e))
         : e == Endgame::KRK   ? Piece::Rook
         : e == Endgame::KBBK  ? Piece::Bishop
         : e == Endgame::KBNK  ? (i == 0 ? Piece::Bishop : Piece::Knight)
         : e == Endgame::KNNK  ? Piece::Knight
         : e == Endgame::KNNNK ? Piece::Knight
         : e == Endgame::KNK   ? Piece::Knight
         : e == Endgame::KBK   ? Piece::Bishop
                               : Piece::Queen;
}
// Are White's two pieces interchangeable?  If they are, a configuration is an
// unordered pair and half the table disappears; if not, it is an ordered one.
constexpr bool identicalOf(Endgame e) {
    // KRKR has two rooks and they are NOT interchangeable: one is White's and
    // one is Black's, and swapping them is a different position.  Only two men
    // of the same colour and type collapse into an unordered pair.
    return e == Endgame::KBBK || e == Endgame::KNNK || e == Endgame::KNNNK ||
           e == Endgame::KQQK || e == Endgame::KRRK ||
           // three alike, the rest of them
           e == Endgame::KQQQK || e == Endgame::KRRRK || e == Endgame::KBBBK;
}

constexpr CfgShape cfgShapeOf(Endgame e) {
    return isThreeMan(e)        ? THREE_MAN[(int)e - THREE_MAN_FIRST].shape
         : npOf(e) == 1         ? CfgShape::One
         : npOf(e) == 3         ? CfgShape::TripleAlike        // KNNNK
         : identicalOf(e)       ? CfgShape::PairUnordered
                                : CfgShape::PairOrdered;
}

// Dispatch a call over the endgames, so one templated body serves them all.
#define KQK_DISPATCH(eg, CALL)                          \
    switch (eg) {                                       \
        case Endgame::KQK:  return CALL(Endgame::KQK);  \
        case Endgame::KRK:  return CALL(Endgame::KRK);  \
        case Endgame::KBBK: return CALL(Endgame::KBBK); \
        case Endgame::KBNK: return CALL(Endgame::KBNK); \
        case Endgame::KNNK: return CALL(Endgame::KNNK); \
        case Endgame::KNNNK:return CALL(Endgame::KNNNK);\
        case Endgame::KNK:  return CALL(Endgame::KNK);  \
        case Endgame::KBK:  return CALL(Endgame::KBK);  \
        case Endgame::KQKB: return CALL(Endgame::KQKB); \
        case Endgame::KQKQ: return CALL(Endgame::KQKQ); \
        case Endgame::KQKN: return CALL(Endgame::KQKN); \
        case Endgame::KRKR: return CALL(Endgame::KRKR); \
        case Endgame::KRKB: return CALL(Endgame::KRKB); \
        case Endgame::KRKN: return CALL(Endgame::KRKN); \
        case Endgame::KBKB: return CALL(Endgame::KBKB); \
        case Endgame::KBKN: return CALL(Endgame::KBKN); \
        case Endgame::KNKN: return CALL(Endgame::KNKN); \
        case Endgame::KQQK: return CALL(Endgame::KQQK); \
        case Endgame::KQRK: return CALL(Endgame::KQRK); \
        case Endgame::KQBK: return CALL(Endgame::KQBK); \
        case Endgame::KQNK: return CALL(Endgame::KQNK); \
        case Endgame::KRRK: return CALL(Endgame::KRRK); \
        case Endgame::KRBK: return CALL(Endgame::KRBK); \
        case Endgame::KRNK: return CALL(Endgame::KRNK); \
        case Endgame::KQQQK: return CALL(Endgame::KQQQK); \
        case Endgame::KQQRK: return CALL(Endgame::KQQRK); \
        case Endgame::KQQBK: return CALL(Endgame::KQQBK); \
        case Endgame::KQQNK: return CALL(Endgame::KQQNK); \
        case Endgame::KQRRK: return CALL(Endgame::KQRRK); \
        case Endgame::KQRBK: return CALL(Endgame::KQRBK); \
        case Endgame::KQRNK: return CALL(Endgame::KQRNK); \
        case Endgame::KQBBK: return CALL(Endgame::KQBBK); \
        case Endgame::KQBNK: return CALL(Endgame::KQBNK); \
        case Endgame::KQNNK: return CALL(Endgame::KQNNK); \
        case Endgame::KRRRK: return CALL(Endgame::KRRRK); \
        case Endgame::KRRBK: return CALL(Endgame::KRRBK); \
        case Endgame::KRRNK: return CALL(Endgame::KRRNK); \
        case Endgame::KRBBK: return CALL(Endgame::KRBBK); \
        case Endgame::KRBNK: return CALL(Endgame::KRBNK); \
        case Endgame::KRNNK: return CALL(Endgame::KRNNK); \
        case Endgame::KBBBK: return CALL(Endgame::KBBBK); \
        case Endgame::KBBNK: return CALL(Endgame::KBBNK); \
        case Endgame::KBNNK: return CALL(Endgame::KBNNK); \
        default:            return CALL(Endgame::KQKR); \
    }

struct Material {
    Endgame eg = Endgame::KQK;
    int     np = 1;                                  // white non-king pieces
    Piece   piece[MAXWP] = { Piece::Queen, Piece::Queen, Piece::Queen };
    bool    identical = false;                       // np == 2, same type: an unordered pair

    static Material of(Endgame e) {
        Material m;
        m.eg = e;
        m.np = npOf(e);
        m.identical = identicalOf(e);
        for (int i = 0; i < m.np; ++i) m.piece[i] = pieceOf(e, i);
        return m;
    }

    const char* name() const {
        switch (eg) {
            case Endgame::KRK:  return "KRK";
            case Endgame::KBBK: return "KBBK";
            case Endgame::KBNK: return "KBNK";
            case Endgame::KQKR: return "KQKR";
            case Endgame::KQKB: return "KQKB";
            case Endgame::KQKQ: return "KQKQ";
            case Endgame::KQKN: return "KQKN";
            case Endgame::KRKR: return "KRKR";
            case Endgame::KRKB: return "KRKB";
            case Endgame::KRKN: return "KRKN";
            case Endgame::KBKB: return "KBKB";
            case Endgame::KBKN: return "KBKN";
            case Endgame::KNKN: return "KNKN";
            case Endgame::KQQK: return "KQQK";
            case Endgame::KQRK: return "KQRK";
            case Endgame::KQBK: return "KQBK";
            case Endgame::KQNK: return "KQNK";
            case Endgame::KRRK: return "KRRK";
            case Endgame::KRBK: return "KRBK";
            case Endgame::KRNK: return "KRNK";
            case Endgame::KQQQK: return "KQQQK";
            case Endgame::KQQRK: return "KQQRK";
            case Endgame::KQQBK: return "KQQBK";
            case Endgame::KQQNK: return "KQQNK";
            case Endgame::KQRRK: return "KQRRK";
            case Endgame::KQRBK: return "KQRBK";
            case Endgame::KQRNK: return "KQRNK";
            case Endgame::KQBBK: return "KQBBK";
            case Endgame::KQBNK: return "KQBNK";
            case Endgame::KQNNK: return "KQNNK";
            case Endgame::KRRRK: return "KRRRK";
            case Endgame::KRRBK: return "KRRBK";
            case Endgame::KRRNK: return "KRRNK";
            case Endgame::KRBBK: return "KRBBK";
            case Endgame::KRBNK: return "KRBNK";
            case Endgame::KRNNK: return "KRNNK";
            case Endgame::KBBBK: return "KBBBK";
            case Endgame::KBBNK: return "KBBNK";
            case Endgame::KBNNK: return "KBNNK";
            case Endgame::KNNK: return "KNNK";
            case Endgame::KNNNK:return "KNNNK";
            case Endgame::KNK:  return "KNK";
            case Endgame::KBK:  return "KBK";
            default:            return "KQK";
        }
    }
    const char* have() const {
        switch (eg) {
            case Endgame::KRK:  return "white has a rook";
            case Endgame::KBBK: return "white has two bishops";
            case Endgame::KBNK: return "white has a bishop and a knight";
            case Endgame::KQKR: return "white has a queen, black a rook";
            case Endgame::KQKB: return "white has a queen, black a bishop";
            case Endgame::KQKQ: return "white has a queen, black a queen";
            case Endgame::KQKN: return "white has a queen, black a knight";
            case Endgame::KRKR: return "white has a rook, black a rook";
            case Endgame::KRKB: return "white has a rook, black a bishop";
            case Endgame::KRKN: return "white has a rook, black a knight";
            case Endgame::KBKB: return "white has a bishop, black a bishop";
            case Endgame::KBKN: return "white has a bishop, black a knight";
            case Endgame::KNKN: return "white has a knight, black a knight";
            case Endgame::KQQK: return "white has two queens";
            case Endgame::KQRK: return "white has a queen and a rook";
            case Endgame::KQBK: return "white has a queen and a bishop";
            case Endgame::KQNK: return "white has a queen and a knight";
            case Endgame::KRRK: return "white has two rooks";
            case Endgame::KRBK: return "white has a rook and a bishop";
            case Endgame::KRNK: return "white has a rook and a knight";
            case Endgame::KQQQK: return "white has three queens";
            case Endgame::KQQRK: return "white has two queens and a rook";
            case Endgame::KQQBK: return "white has two queens and a bishop";
            case Endgame::KQQNK: return "white has two queens and a knight";
            case Endgame::KQRRK: return "white has a queen and two rooks";
            case Endgame::KQRBK: return "white has a queen and a rook and a bishop";
            case Endgame::KQRNK: return "white has a queen and a rook and a knight";
            case Endgame::KQBBK: return "white has a queen and two bishops";
            case Endgame::KQBNK: return "white has a queen and a bishop and a knight";
            case Endgame::KQNNK: return "white has a queen and two knights";
            case Endgame::KRRRK: return "white has three rooks";
            case Endgame::KRRBK: return "white has two rooks and a bishop";
            case Endgame::KRRNK: return "white has two rooks and a knight";
            case Endgame::KRBBK: return "white has a rook and two bishops";
            case Endgame::KRBNK: return "white has a rook and a bishop and a knight";
            case Endgame::KRNNK: return "white has a rook and two knights";
            case Endgame::KBBBK: return "white has three bishops";
            case Endgame::KBBNK: return "white has two bishops and a knight";
            case Endgame::KBNNK: return "white has a bishop and two knights";
            case Endgame::KNNK: return "white has two knights";
            case Endgame::KNNNK:return "white has three knights";
            case Endgame::KNK:  return "white has a knight";
            case Endgame::KBK:  return "white has a bishop";
            default:            return "white has a queen";
        }
    }
    char letter(int i) const { return pieceLetter(piece[i]); }
    // The label a square of piece i is printed and parsed under: wQ, wR, wB1,
    // wB2, wB, wN.  Only like pieces need the number.
    std::string label(int i) const {
        std::string s = (blackArmed(eg) && i == 1) ? "b" : "w";
        s += letter(i);
        if (np > 1 && identical) s += char('1' + i);
        return s;
    }
};

inline bool parseEndgame(const std::string& t, Endgame& out) {
    std::string v;
    for (char c : t) v += char(c >= 'A' && c <= 'Z' ? c - 'A' + 'a' : c);
    if (v == "kqk"  || v == "queen"   || v == "q")  { out = Endgame::KQK;  return true; }
    if (v == "krk"  || v == "rook"    || v == "r")  { out = Endgame::KRK;  return true; }
    if (v == "kbbk" || v == "bishops" || v == "bb") { out = Endgame::KBBK; return true; }
    if (v == "kbnk" || v == "bn")                   { out = Endgame::KBNK; return true; }
    if (v == "knnk" || v == "nn")                   { out = Endgame::KNNK; return true; }
    if (v == "knnnk"|| v == "nnn")                  { out = Endgame::KNNNK;return true; }
    if (v == "knk"  || v == "n")                    { out = Endgame::KNK;  return true; }
    if (v == "kbk"  || v == "b")                    { out = Endgame::KBK;  return true; }
    if (v == "kqkr" || v == "qr")                   { out = Endgame::KQKR; return true; }
    if (v == "kqkb" || v == "qb")                   { out = Endgame::KQKB; return true; }
    if (v == "kqkq" || v == "qq")                   { out = Endgame::KQKQ; return true; }
    if (v == "kqkn" || v == "qn")                   { out = Endgame::KQKN; return true; }
    if (v == "krkr" || v == "rr")                   { out = Endgame::KRKR; return true; }
    if (v == "krkb" || v == "rb")                   { out = Endgame::KRKB; return true; }
    if (v == "krkn" || v == "rn")                   { out = Endgame::KRKN; return true; }
    if (v == "kbkb" || v == "bb2")                  { out = Endgame::KBKB; return true; }
    if (v == "kbkn" || v == "bn2")                  { out = Endgame::KBKN; return true; }
    if (v == "knkn" || v == "nn2")                  { out = Endgame::KNKN; return true; }
    if (v == "kqqk" || v == "qq2")                  { out = Endgame::KQQK; return true; }
    if (v == "kqrk" || v == "qr2")                  { out = Endgame::KQRK; return true; }
    if (v == "kqbk" || v == "qb2")                  { out = Endgame::KQBK; return true; }
    if (v == "kqnk" || v == "qn2")                  { out = Endgame::KQNK; return true; }
    if (v == "krrk" || v == "rr2")                  { out = Endgame::KRRK; return true; }
    if (v == "krbk" || v == "rb2")                  { out = Endgame::KRBK; return true; }
    if (v == "krnk" || v == "rn2")                  { out = Endgame::KRNK; return true; }
    if (v == "kqqqk") { out = Endgame::KQQQK; return true; }
    if (v == "kqqrk") { out = Endgame::KQQRK; return true; }
    if (v == "kqqbk") { out = Endgame::KQQBK; return true; }
    if (v == "kqqnk") { out = Endgame::KQQNK; return true; }
    if (v == "kqrrk") { out = Endgame::KQRRK; return true; }
    if (v == "kqrbk") { out = Endgame::KQRBK; return true; }
    if (v == "kqrnk") { out = Endgame::KQRNK; return true; }
    if (v == "kqbbk") { out = Endgame::KQBBK; return true; }
    if (v == "kqbnk") { out = Endgame::KQBNK; return true; }
    if (v == "kqnnk") { out = Endgame::KQNNK; return true; }
    if (v == "krrrk") { out = Endgame::KRRRK; return true; }
    if (v == "krrbk") { out = Endgame::KRRBK; return true; }
    if (v == "krrnk") { out = Endgame::KRRNK; return true; }
    if (v == "krbbk") { out = Endgame::KRBBK; return true; }
    if (v == "krbnk") { out = Endgame::KRBNK; return true; }
    if (v == "krnnk") { out = Endgame::KRNNK; return true; }
    if (v == "kbbbk") { out = Endgame::KBBBK; return true; }
    if (v == "kbbnk") { out = Endgame::KBBNK; return true; }
    if (v == "kbnnk") { out = Endgame::KBNNK; return true; }
    return false;
}

class Geometry {
public:
    int n   = 0;   // board edge length
    int nsq = 0;   // n * n

    // symTab[g * nsq + s] is the image of square s under symmetry g.
    std::vector<Sq> symTab;

    // triId[s] >= 0 exactly when s lies in the fundamental triangle of D4.
    std::vector<int32_t> triId;
    std::vector<Sq>      triSq;    // inverse of triId

    // For each triangle square, the elements of D4 that fix it.  Element 0
    // (the identity) is always present and always comes first.
    std::vector<std::vector<U8>> triStab;

    // For each square, the elements of D4 that carry it into the fundamental
    // triangle.  There is exactly one for a square off every symmetry axis,
    // which is the overwhelmingly common case, so canonicalisation is usually
    // three table lookups rather than a loop over the whole group.
    std::vector<U8> canonSym;      // NSYM entries per square
    std::vector<U8> canonSymLen;

    explicit Geometry(int edge) : n(edge), nsq(edge * edge) {
        buildSymmetry();
        buildTriangle();
    }

    inline int file(Sq s) const { return s % n; }
    inline int rank(Sq s) const { return s / n; }
    inline Sq  sq(int f, int r) const { return r * n + f; }
    inline bool onBoard(int f, int r) const {
        return (unsigned)f < (unsigned)n && (unsigned)r < (unsigned)n;
    }
    inline Sq image(int g, Sq s) const { return symTab[(size_t)g * nsq + s]; }
    // Square colour.  Bishops never leave their own colour, which is why two
    // same-coloured bishops cannot mate -- a fact this program computes rather
    // than assumes.
    inline int colour(Sq s) const { return (file(s) + rank(s)) & 1; }

    // True when two kings stand on the same or on touching squares, i.e. when
    // the pair is illegal.
    inline bool kingsTouch(Sq a, Sq b) const {
        int df = file(a) - file(b), dr = rank(a) - rank(b);
        return df >= -1 && df <= 1 && dr >= -1 && dr <= 1;
    }

    // Does a piece of the given kind on `from` attack `to`, given that `blk0`
    // and `blk1` are the only men that can stand in the way?  The relation is
    // symmetric in from/to.  O(1): with a bounded number of candidate
    // blockers, "is it strictly between" is just arithmetic on the ray
    // parameter, so no ray is ever walked.
    inline bool attacks(Piece p, Sq from, Sq to, Sq blk0, Sq blk1 = -1) const {
        if (from == to) return false;
        int ff = file(from), fr = rank(from);
        int df = file(to) - ff, dr = rank(to) - fr;
        if (p == Piece::Knight) {                   // jumps; nothing can block
            int a = df < 0 ? -df : df, b = dr < 0 ? -dr : dr;
            return (a == 1 && b == 2) || (a == 2 && b == 1);
        }
        bool orth = (df == 0 || dr == 0);
        bool diag = (df == dr || df == -dr);        // from != to, so never both
        if (orth) { if (p == Piece::Bishop) return false; }
        else if (diag) { if (p == Piece::Rook) return false; }
        else return false;
        int sf = (df > 0) - (df < 0), sr = (dr > 0) - (dr < 0);
        int steps = df ? (df > 0 ? df : -df) : (dr > 0 ? dr : -dr);
        return !between(ff, fr, sf, sr, steps, blk0) &&
               !between(ff, fr, sf, sr, steps, blk1);
    }

    // The same with three candidate blockers, which is what five men on the
    // board need: a queen looking at the black king past the white king and
    // two bishops, or a bishop looking at the white king past the black king,
    // the queen and its fellow bishop.  See kqkbb.cpp.
    inline bool attacks(Piece p, Sq from, Sq to, Sq blk0, Sq blk1, Sq blk2) const {
        return attacks(p, from, to, blk0, blk1) &&
               !blockedBy(p, from, to, blk2);
    }

    // ---- square names -----------------------------------------------------
    // Algebraic ("d4") while n <= 26, otherwise "file,rank" with 0-based
    // coordinates.  Parsing accepts either form on any board size.
    std::string name(Sq s) const {
        if (s < 0 || s >= nsq) return "??";
        if (n <= 26) return std::string(1, char('a' + file(s))) + std::to_string(rank(s) + 1);
        return std::to_string(file(s)) + "," + std::to_string(rank(s));
    }

    Sq parse(const std::string& t) const {
        if (t.empty()) return -1;
        auto comma = t.find(',');
        if (comma != std::string::npos) {
            int f = std::atoi(t.substr(0, comma).c_str());
            int r = std::atoi(t.substr(comma + 1).c_str());
            return onBoard(f, r) ? sq(f, r) : -1;
        }
        char c = t[0];
        if (c >= 'A' && c <= 'Z') c = char(c - 'A' + 'a');
        if (c < 'a' || c > 'z') return -1;
        int f = c - 'a';
        int r = std::atoi(t.c_str() + 1) - 1;
        return onBoard(f, r) ? sq(f, r) : -1;
    }

    // Does `blk` stand strictly between `from` and `to`, on the ray joining
    // them?  Only meaningful when the two are in fact joined by a ray of p's
    // kind, which is why it is used only to narrow an attacks() that held.
    inline bool blockedBy(Piece p, Sq from, Sq to, Sq blk) const {
        if (blk < 0 || p == Piece::Knight) return false;
        int ff = file(from), fr = rank(from);
        int df = file(to) - ff, dr = rank(to) - fr;
        int sf = (df > 0) - (df < 0), sr = (dr > 0) - (dr < 0);
        int steps = df ? (df > 0 ? df : -df) : (dr > 0 ? dr : -dr);
        return between(ff, fr, sf, sr, steps, blk);
    }

private:
    // Does `blk` sit strictly between the ray origin and a point `steps` along it?
    inline bool between(int ff, int fr, int sf, int sr, int steps, Sq blk) const {
        if (blk < 0) return false;
        int bdf = file(blk) - ff, bdr = rank(blk) - fr;
        int k = sf ? bdf * sf : bdr * sr;
        return k > 0 && k < steps && bdf == sf * k && bdr == sr * k;
    }

    void buildSymmetry() {
        symTab.assign((size_t)NSYM * nsq, 0);
        for (int r = 0; r < n; ++r)
            for (int f = 0; f < n; ++f) {
                Sq s = sq(f, r);
                int mf = n - 1 - f, mr = n - 1 - r;
                Sq img[NSYM] = {
                    sq(f,  r),   // identity
                    sq(mf, r),   // mirror files
                    sq(f,  mr),  // mirror ranks
                    sq(mf, mr),  // rotate 180
                    sq(r,  f),   // transpose (reflect in the a1-h8 diagonal)
                    sq(mr, f),   // rotate 90
                    sq(r,  mf),  // rotate 270
                    sq(mr, mf),  // anti-transpose
                };
                for (int g = 0; g < NSYM; ++g) symTab[(size_t)g * nsq + s] = img[g];
            }
    }

    // The fundamental domain of D4: the closed triangle { 2f <= n-1,
    // 2r <= n-1, r <= f }.  Every D4 orbit of squares meets it exactly once.
    void buildTriangle() {
        triId.assign(nsq, -1);
        triSq.clear();
        for (int r = 0; r < n; ++r)
            for (int f = 0; f < n; ++f) {
                if (2 * f <= n - 1 && 2 * r <= n - 1 && r <= f) {
                    triId[sq(f, r)] = (int32_t)triSq.size();
                    triSq.push_back(sq(f, r));
                }
            }
        triStab.assign(triSq.size(), {});
        for (size_t i = 0; i < triSq.size(); ++i)
            for (int g = 0; g < NSYM; ++g)
                if (image(g, triSq[i]) == triSq[i]) triStab[i].push_back((U8)g);

        canonSym.assign((size_t)nsq * NSYM, 0);
        canonSymLen.assign(nsq, 0);
        for (Sq s = 0; s < nsq; ++s) {
            int len = 0;
            for (int g = 0; g < NSYM; ++g)
                if (triId[image(g, s)] >= 0) canonSym[(size_t)s * NSYM + len++] = (U8)g;
            canonSymLen[s] = (U8)len;
        }
    }
};

// Every square a piece of kind P standing on `from` can move to, given that
// o0, o1 and o2 are the only other men on the board.  `fn(to)` returns false
// to stop the walk early.
//
// Because every piece here moves symmetrically, this doubles as the set of
// squares the piece could have come *from* to arrive at `from` -- which is
// exactly what the retrograde pass needs, so the forward generator and the
// unmove generator are one function rather than two that must be kept in step.
// The five-man form: four other men can block a ray rather than three.  It
// forwards to the three-man one by folding o3 into the occupancy test, which
// keeps one definition of how a piece moves.
template <Piece P, class F>
inline bool forEachMove(const Geometry& g, Sq from, Sq o0, Sq o1, Sq o2, Sq o3, F&& fn);

template <Piece P, class F>
inline bool forEachMove(const Geometry& g, Sq from, Sq o0, Sq o1, Sq o2, F&& fn) {
    const int ff = g.file(from), fr = g.rank(from);
    if constexpr (P == Piece::Knight) {
        for (int d = 0; d < 8; ++d) {
            int f = ff + NF[d], r = fr + NR[d];
            if (!g.onBoard(f, r)) continue;
            Sq t = g.sq(f, r);
            if (t == o0 || t == o1 || t == o2) continue;   // occupied
            if (!fn(t)) return false;
        }
    } else {
        constexpr int begin = dirBegin(P), step = dirStep(P);
        const int nn = g.n;
        for (int d = begin; d < 8; d += step) {
            const int sf = DIR_F[d], sr = DIR_R[d];
            const int stepSq = sr * nn + sf;
            int f = ff + sf, r = fr + sr;
            Sq t = from + stepSq;
            while ((unsigned)f < (unsigned)nn && (unsigned)r < (unsigned)nn) {
                if (t == o0 || t == o1 || t == o2) break;  // blocked
                if (!fn(t)) return false;
                f += sf; r += sr; t += stepSq;
            }
        }
    }
    return true;
}

template <Piece P, class F>
inline bool forEachMove(const Geometry& g, Sq from, Sq o0, Sq o1, Sq o2, Sq o3, F&& fn) {
    const int ff = g.file(from), fr = g.rank(from);
    if constexpr (P == Piece::Knight) {
        for (int d = 0; d < 8; ++d) {
            int f = ff + NF[d], r = fr + NR[d];
            if (!g.onBoard(f, r)) continue;
            Sq t = g.sq(f, r);
            if (t == o0 || t == o1 || t == o2 || t == o3) continue;
            if (!fn(t)) return false;
        }
    } else {
        constexpr int begin = dirBegin(P), step = dirStep(P);
        const int nn = g.n;
        for (int d = begin; d < 8; d += step) {
            const int sf = DIR_F[d], sr = DIR_R[d];
            const int stepSq = sr * nn + sf;
            int f = ff + sf, r = fr + sr;
            Sq t = from + stepSq;
            while ((unsigned)f < (unsigned)nn && (unsigned)r < (unsigned)nn) {
                if (t == o0 || t == o1 || t == o2 || t == o3) break;
                if (!fn(t)) return false;
                f += sf; r += sr; t += stepSq;
            }
        }
    }
    return true;
}

} // namespace kqk
