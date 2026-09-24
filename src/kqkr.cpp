// kqkr.cpp -- king and queen against king and one black piece: a rook (KQKR)
// or a bishop (KQKB).
//
// The two are one solver.  Nothing below depends on how Black's man moves
// beyond three things -- which squares it attacks, which rays it travels, and
// what material its capture leaves -- so the piece is a parameter, `bp`, and
// the conversion table Black's capture leads to is chosen beside it: KRK for a
// rook, KBK for a bishop.  KQKB exists because kqkbb.cpp needs it: White
// taking one of two black bishops leaves exactly this.
//
// Why this needs its own solver
// -----------------------------
// Every other endgame here rests on Black being bare: Black can never check,
// never mate, never win, and every capture Black can make ends the game as a
// draw.  KQKR breaks all of it.  Black has a rook, so
//
//   * a white-to-move entry can be a loss as well as a win or a draw;
//   * Black's ...RxQ or ...KxQ leaves a bare white king against king and rook,
//     which White *loses*;
//   * White's QxR or KxR leaves KQK, which White wins.
//
// So the table is signed, and it converts.  Both conversions leave material
// this program already solves exactly, and neither can ever be reached from
// inside KQKR by an un-move (a predecessor of a four-man position under a
// capture would have five men), so no un-capture generator is needed: the
// captures are read forwards out of the KQK and KRK tables and enter the
// induction as ordinary successors of known value.
//
// One fact simplifies the bookkeeping considerably.  **No capture is ever bad
// for the side making it.** White taking the rook leaves KQK, which is a white
// win or a draw but never a loss; Black taking the queen leaves king and rook
// against a bare king, which is a black win or a draw but never a loss.  A
// converting move can therefore seed a win, and can block the opponent from
// ever proving a forced loss, but it never has to be scheduled as a loss at a
// particular depth.
//
// Structure
// ---------
// Backward induction by ply, as in solver.cpp, but with four propagations
// rather than two, because both sides can be the winner:
//
//   d odd    White mates in d, white to move  <- retract White's move from
//            "White mates in d-1, black to move"
//            Black mates in d, black to move  <- retract Black's move from
//            "Black mates in d-1, white to move"
//   d even   White mates in d, black to move  <- every black move leads to
//            "White mates in <= d-1", the worst of them exactly d-1
//            Black mates in d, white to move  <- likewise for White
//
// The winner-to-move steps are retractions; the loser-to-move steps generate
// candidates by retraction and then re-test them by forward move generation.
// As in solver.cpp there is no successor counter: on a symmetry-reduced index
// an edge between orbits of different size is seen a different number of times
// from its two ends, so counters do not work.
#include "table.hpp"

#include <atomic>
#include <map>
#include <random>
#include <set>
#include <chrono>
#include <cstdio>
#include <thread>

namespace kqk {

// What ...xQ leaves: Black's man and the bare white king, which this program
// already solves.  A rook mates there and a bishop does not, but the solver
// below does not care which -- it reads the value out of the table either way.
Endgame subEndgame(Endgame eg) {
    return bareEndgameOf(blackPieceOf(eg));
}

namespace {

// ---------------------------------------------------------------------------
// Entry encoding.  Signed, and from White's point of view throughout:
//     v > 0   White mates in v-1 plies
//     v < 0   Black mates in -v-1 plies
//     v == 0  drawn
// The two sentinels are positive and larger than any reachable depth.
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
// Attack tests.  A square is passed as -1 when that man has been captured, and
// Geometry::attacks treats a negative blocker as absent, so the same call
// serves before and after a capture.
// ---------------------------------------------------------------------------
inline bool blackChecked(const Geometry& g, Piece wp, Sq wk, Sq bk, Sq wq, Sq br) {
    return kqkrBlackChecked(g, wp, wk, bk, wq, br);
}
inline bool whiteChecked(const Geometry& g, Piece bp, Sq wk, Sq bk, Sq wq, Sq br) {
    return kqkrWhiteChecked(g, bp, wk, bk, wq, br);
}

// ---------------------------------------------------------------------------
// Rule 2 mobility: has this side ANY move at all, check disregarded?  A man of
// the *enemy* on a square is not a blocker -- it can be taken -- so only one's
// own men block.  This is the predicate the capture rules turn on: a side with
// no chess move loses if it has a move here, and draws if it has none.
//
// For this material it can only ever answer yes.  A king in a corner has three
// neighbours on the board and the one other man of its colour can block at
// most one of them; a queen or a rook or a bishop in a corner likewise.  The
// solver computes it anyway and counts the cases, so that the claim is checked
// on every board rather than believed.
// ---------------------------------------------------------------------------
inline bool kingHasSquare(const Geometry& g, Sq from, Sq own) {
    const int f0 = g.file(from), r0 = g.rank(from);
    for (int df = -1; df <= 1; ++df)
        for (int dr = -1; dr <= 1; ++dr) {
            if (!df && !dr) continue;
            const int f = f0 + df, r = r0 + dr;
            if (g.onBoard(f, r) && g.sq(f, r) != own) return true;
        }
    return false;
}
// Every move of ONE man: the rays of a slider or the jumps of a knight, with
// `own` blocking, the enemy king blocking (it can never legally be taken, and
// a position where it could be is not in this table), and `prey` capturable.
// Black's man has been a parameter here since the file was written; White's is
// one now too, and that is the whole of what made this solver "KQKR" rather
// than "one white man against one black man".
template <class F>
inline void manMoves(const Geometry& g, Piece p, Sq from, Sq own, Sq king, Sq prey,
                     F&& fn) {
    const int f0 = g.file(from), r0 = g.rank(from);
    if (p == Piece::Knight) {
        for (int d = 0; d < 8; ++d) {
            const int f = f0 + NF[d], r = r0 + NR[d];
            if (!g.onBoard(f, r)) continue;
            const Sq t = g.sq(f, r);
            if (t == own || t == king) continue;
            fn(t, t == prey);
        }
        return;
    }
    for (int d = dirBegin(p); d < 8; d += dirStep(p)) {
        int f = f0 + DIR_F[d], r = r0 + DIR_R[d];
        while (g.onBoard(f, r)) {
            const Sq t = g.sq(f, r);
            if (t == own || t == king) break;
            const bool cap = (t == prey);
            fn(t, cap);
            if (cap) break;
            f += DIR_F[d]; r += DIR_R[d];
        }
    }
}

// The same man, retracted: where it could have come from, nothing capturable
// because a predecessor under a capture would have five men.
template <class F>
inline void manRetract(const Geometry& g, Piece p, Sq from, Sq o0, Sq o1, Sq o2, F&& fn) {
    switch (p) {
        case Piece::Rook:   forEachMove<Piece::Rook>  (g, from, o0, o1, o2, fn); break;
        case Piece::Bishop: forEachMove<Piece::Bishop>(g, from, o0, o1, o2, fn); break;
        case Piece::Knight: forEachMove<Piece::Knight>(g, from, o0, o1, o2, fn); break;
        default:            forEachMove<Piece::Queen> (g, from, o0, o1, o2, fn); break;
    }
}

inline bool sliderHasSquare(const Geometry& g, Piece p, Sq from, Sq own) {
    const int f0 = g.file(from), r0 = g.rank(from);
    for (int d = dirBegin(p); d < 8; d += dirStep(p)) {
        const int f = f0 + DIR_F[d], r = r0 + DIR_R[d];
        if (g.onBoard(f, r) && g.sq(f, r) != own) return true;
    }
    return false;
}
inline bool manHasSquare(const Geometry& g, Piece p, Sq from, Sq own) {
    if (p != Piece::Knight) return sliderHasSquare(g, p, from, own);
    const int f0 = g.file(from), r0 = g.rank(from);
    for (int d = 0; d < 8; ++d) {
        const int f = f0 + NF[d], r = r0 + NR[d];
        if (g.onBoard(f, r) && g.sq(f, r) != own) return true;
    }
    return false;
}
inline bool whiteMobile(const Geometry& g, Piece wp, Sq wk, Sq wq) {
    return kingHasSquare(g, wk, wq) || manHasSquare(g, wp, wq, wk);
}
inline bool blackMobile(const Geometry& g, Piece bp, Sq bk, Sq br) {
    return kingHasSquare(g, bk, br) || manHasSquare(g, bp, br, bk);
}

// The value of a position in which the side to move has no legal chess move.
// Under the ordinary rules that is mate when in check and a draw otherwise;
// under the capture rules it is a loss whenever the side has a rule 2 move,
// and a draw when it is totally immobile -- the one clause that separates the
// two games for one king a side.  `loss` is the encoding of losing at ply 0.
inline int16_t terminal(bool capture, bool inCheck, bool mobile, int16_t loss,
                        bool& immobile) {
    if (!capture) return inCheck ? loss : (int16_t)VK_DRAW;
    immobile = !mobile;
    return mobile ? loss : (int16_t)VK_DRAW;
}

// ---------------------------------------------------------------------------
// Forward move generation.  fn(wk, bk, wq, br, captured) receives the position
// after the move; `captured` is true when the move took the opposing man, in
// which case that man's square is -1.  Only legal moves are produced.
// ---------------------------------------------------------------------------
template <class F>
inline void genWhite(const Geometry& g, Piece wp, Piece bp, Sq wk, Sq bk, Sq wq, Sq br,
                     F&& fn) {
    // king
    const int f0 = g.file(wk), r0 = g.rank(wk);
    for (int df = -1; df <= 1; ++df)
        for (int dr = -1; dr <= 1; ++dr) {
            if (!df && !dr) continue;
            int f = f0 + df, r = r0 + dr;
            if (!g.onBoard(f, r)) continue;
            Sq t = g.sq(f, r);
            if (t == wq) continue;                       // own man
            if (g.kingsTouch(t, bk)) continue;           // into the black king
            Sq nbr = (t == br) ? -1 : br;
            if (whiteChecked(g, bp, t, bk, wq, nbr)) continue;
            fn(t, bk, wq, nbr, nbr < 0);
        }
    // White's man
    manMoves(g, wp, wq, wk, bk, br, [&](Sq t, bool cap) {
        const Sq nbr = cap ? -1 : br;
        if (!whiteChecked(g, bp, wk, bk, t, nbr)) fn(wk, bk, t, nbr, cap);
    });
}

template <class F>
inline void genBlack(const Geometry& g, Piece wp, Piece bp, Sq wk, Sq bk, Sq wq, Sq br,
                     F&& fn) {
    // king
    const int f0 = g.file(bk), r0 = g.rank(bk);
    for (int df = -1; df <= 1; ++df)
        for (int dr = -1; dr <= 1; ++dr) {
            if (!df && !dr) continue;
            int f = f0 + df, r = r0 + dr;
            if (!g.onBoard(f, r)) continue;
            Sq t = g.sq(f, r);
            if (t == br) continue;                       // own man
            if (g.kingsTouch(wk, t)) continue;
            Sq nwq = (t == wq) ? -1 : wq;
            if (blackChecked(g, wp, wk, t, nwq, br)) continue;
            fn(wk, t, nwq, br, nwq < 0);
        }
    // Black's man
    manMoves(g, bp, br, bk, wk, wq, [&](Sq t, bool cap) {
        const Sq nwq = cap ? -1 : wq;
        if (!blackChecked(g, wp, wk, bk, nwq, t)) fn(wk, bk, nwq, t, cap);
    });
}

// ---------------------------------------------------------------------------
// Un-move generation.  Only non-capturing moves are retracted: a predecessor
// under a capture would have five men and is not in this table.  `fn(wk, bk,
// wq, br)` receives a legal predecessor with the other side to move.
// ---------------------------------------------------------------------------
template <class F>
inline void retractWhite(const Geometry& g, Piece wp, Piece bp, Sq wk, Sq bk, Sq wq,
                         Sq br, F&& fn) {
    // the white king came from an adjacent empty square
    const int f0 = g.file(wk), r0 = g.rank(wk);
    for (int df = -1; df <= 1; ++df)
        for (int dr = -1; dr <= 1; ++dr) {
            if (!df && !dr) continue;
            int f = f0 + df, r = r0 + dr;
            if (!g.onBoard(f, r)) continue;
            Sq t = g.sq(f, r);
            if (t == wq || t == br || t == bk) continue;
            if (g.kingsTouch(t, bk)) continue;
            if (blackChecked(g, wp, t, bk, wq, br)) continue;  // black in check, white to move
            fn(t, bk, wq, br);
        }
    // White's man came from any square it could have travelled from
    manRetract(g, wp, wq, wk, bk, br, [&](Sq t) {
        if (!blackChecked(g, wp, wk, bk, t, br)) fn(wk, bk, t, br);
        return true;
    });
}

template <class F>
inline void retractBlack(const Geometry& g, Piece wp, Piece bp, Sq wk, Sq bk, Sq wq,
                         Sq br, F&& fn) {
    const int f0 = g.file(bk), r0 = g.rank(bk);
    for (int df = -1; df <= 1; ++df)
        for (int dr = -1; dr <= 1; ++dr) {
            if (!df && !dr) continue;
            int f = f0 + df, r = r0 + dr;
            if (!g.onBoard(f, r)) continue;
            Sq t = g.sq(f, r);
            if (t == wq || t == br || t == wk) continue;
            if (g.kingsTouch(wk, t)) continue;
            if (whiteChecked(g, bp, wk, t, wq, br)) continue;   // white in check, black to move
            fn(wk, t, wq, br);
        }
    auto back = [&](Sq t) {
        if (!whiteChecked(g, bp, wk, bk, wq, t)) fn(wk, bk, wq, t);
        return true;
    };
    manRetract(g, bp, br, wk, bk, wq, back);
}

// ---------------------------------------------------------------------------
// The two conversions, read forwards out of tables this program already has.
// Both return the value of the position *after* the capture, in the encoding
// above.
// ---------------------------------------------------------------------------
struct Conv {
    const Table& kqk;   // white king, queen, bare black king
    const Table& sub;   // Black's man and the bare white king, colours swapped

    // White has just taken Black's man: KQK with Black to move.
    int16_t afterWhiteTakes(Sq wk, Sq bk, Sq wq) const {
        Pos p; p.wk = wk; p.bk = bk; p.wp[0] = wq;
        U8 v = kqk.valueAt(p, false);
        return isDtm(v) ? wMate((int)v) : (int16_t)VK_DRAW;
    }
    // Black has just taken the queen: a bare white king against king and
    // Black's man, White to move.  In KRK (or KBK) terms that man's owner is
    // "White", so the two kings swap roles and it is the bare side -- "Black"
    // -- to move.
    int16_t afterBlackTakes(Sq wk, Sq bk, Sq br) const {
        Pos p; p.wk = bk; p.bk = wk; p.wp[0] = br;
        U8 v = sub.valueAt(p, false);
        return isDtm(v) ? bMate((int)v) : (int16_t)VK_DRAW;
    }
};

} // namespace

// Exposed for the differential move-generator test in tests/.
void kqkrGenWhiteRaw(const Geometry& g, Piece wp, Piece bp, Sq wk, Sq bk, Sq wq, Sq br,
                     const std::function<void(Sq, Sq, Sq, Sq, bool)>& fn) {
    genWhite(g, wp, bp, wk, bk, wq, br, fn);
}
void kqkrGenBlackRaw(const Geometry& g, Piece wp, Piece bp, Sq wk, Sq bk, Sq wq, Sq br,
                     const std::function<void(Sq, Sq, Sq, Sq, bool)>& fn) {
    genBlack(g, wp, bp, wk, bk, wq, br, fn);
}

// ---------------------------------------------------------------------------
int16_t TableKQKR::valueAt(const Pos& p, bool whiteToMove) const {
    if (p.wp[0] == p.wk || p.wp[0] == p.bk || p.wp[1] == p.wk ||
        p.wp[1] == p.bk || p.wp[0] == p.wp[1]) return VK_DEAD;
    U64 s;
    if (!idx.slotOf(p, s)) return VK_DEAD;
    return whiteToMove ? w[s] : b[s];
}

void TableKQKR::generate(int threads, bool progress) {
    const Geometry& g = geo;
    const Piece bp = blackPieceOf(mat.eg);
    const Piece wp = whitePieceOf(mat.eg);
    const U32 npc = idx.npc;
    const U64 nkk = idx.nkk;
    Timer clock;

    w.assign(idx.nslots, VK_DEAD);
    b.assign(idx.nslots, VK_DEAD);

    // Both conversions are played under the same rules as the table itself.
    // Under the capture rules that matters twice over: KQK wins from more
    // placements, because a stalemate is a win there too, and K+B vs K stops
    // being a dead draw at all -- a lone bishop and king can take a bare
    // king's last square away.
    Table kqk(n, bareEndgameOf(whitePieceOf(mat.eg)));
    kqk.stalemateLoss = stalemateLoss; kqk.generate(threads, false);
    Table sub(n, subEndgame(mat.eg));
    sub.stalemateLoss = stalemateLoss; sub.generate(threads, false);
    const Conv conv{kqk, sub};
    if (progress)
        std::fprintf(stderr, "  sub-tables KQK and KRK built, %.2fs\n", clock.s());

    // ---- initialisation ---------------------------------------------------
    // Dead slots, mates, stalemates, and the conversion seeds.  A seed is an
    // upper bound realised by an actual capture; the induction below may still
    // find something shorter and overwrite it.
    std::atomic<U64> nMateW{0}, nMateB{0}, nStaleW{0}, nStaleB{0}, nImmobile{0};
    std::atomic<int> seedMax{0};
    parallelFor(nkk, 64, threads, [&](U64 lo, U64 hi, int) {
        U64 lw = 0, lb = 0, lsw = 0, lsb = 0, limm = 0; int lseed = 0;
        for (U64 kk = lo; kk < hi; ++kk) {
            const Sq wk = idx.kkWk[kk], bk = idx.kkBk[kk];
            const U64 base = kk * npc;
            Pos p; p.wk = wk; p.bk = bk;
            for (U32 pc = 0; pc < npc; ++pc) {
                idx.decode(pc, p.wp);
                if (!idx.cfgLive(p.wp, wk, bk)) continue;
                if (!idx.cfgIsCanonical((int32_t)kk, p.wp)) continue;
                const Sq wq = p.wp[0], br = p.wp[1];

                // White to move: legal unless Black stands in check.
                if (!blackChecked(g, wp, wk, bk, wq, br)) {
                    int moves = 0; int16_t best = VK_UNKNOWN;
                    genWhite(g, wp, bp, wk, bk, wq, br, [&](Sq a, Sq bb, Sq q, Sq r, bool cap) {
                        ++moves;
                        if (!cap) return;
                        int16_t v = conv.afterWhiteTakes(a, bb, q);
                        (void)r;
                        if (isWin(v) && (best == VK_UNKNOWN || v < best)) best = v;
                    });
                    if (moves == 0) {
                        const bool chk = whiteChecked(g, bp, wk, bk, wq, br);
                        bool imm = false;
                        w[base + pc] = terminal(stalemateLoss, chk,
                                                whiteMobile(g, wp, wk, wq), bMate(0), imm);
                        if (chk) ++lw;
                        else if (isLoss(w[base + pc])) ++lsw;
                        if (imm) ++limm;
                    } else if (best != VK_UNKNOWN) {
                        int16_t seed = wMate(winPly(best) + 1);
                        w[base + pc] = seed;
                        if (winPly(seed) > lseed) lseed = winPly(seed);
                    } else {
                        w[base + pc] = VK_UNKNOWN;
                    }
                }
                // Black to move: legal unless White stands in check.
                if (!whiteChecked(g, bp, wk, bk, wq, br)) {
                    int moves = 0; int16_t best = VK_UNKNOWN;
                    genBlack(g, wp, bp, wk, bk, wq, br, [&](Sq a, Sq bb, Sq q, Sq r, bool cap) {
                        ++moves;
                        if (!cap) return;
                        int16_t v = conv.afterBlackTakes(a, bb, r);
                        (void)q;
                        if (isLoss(v) && (best == VK_UNKNOWN || v > best)) best = v;
                    });
                    if (moves == 0) {
                        const bool chk = blackChecked(g, wp, wk, bk, wq, br);
                        bool imm = false;
                        b[base + pc] = terminal(stalemateLoss, chk,
                                                blackMobile(g, bp, bk, br), wMate(0), imm);
                        if (chk) ++lb;
                        else if (isWin(b[base + pc])) ++lsb;
                        if (imm) ++limm;
                    } else if (best != VK_UNKNOWN) {
                        int16_t seed = bMate(lossPly(best) + 1);
                        b[base + pc] = seed;
                        if (lossPly(seed) > lseed) lseed = lossPly(seed);
                    } else {
                        b[base + pc] = VK_UNKNOWN;
                    }
                }
            }
        }
        nMateW.fetch_add(lb, std::memory_order_relaxed);   // black mated: White wins
        nMateB.fetch_add(lw, std::memory_order_relaxed);   // white mated: Black wins
        nStaleW.fetch_add(lsb, std::memory_order_relaxed); // black stalemated: a loss
        nStaleB.fetch_add(lsw, std::memory_order_relaxed);
        nImmobile.fetch_add(limm, std::memory_order_relaxed);
        int cur = seedMax.load(std::memory_order_relaxed);
        while (lseed > cur && !seedMax.compare_exchange_weak(cur, lseed)) {}
    });

    if (progress)
        std::fprintf(stderr, "  init: %llu king pairs, %llu mates of Black, %llu of White,"
                             " deepest conversion %d plies, %.2fs\n",
                     (unsigned long long)nkk, (unsigned long long)nMateW.load(),
                     (unsigned long long)nMateB.load(), seedMax.load(), clock.s());

    // ---- backward induction ----------------------------------------------
    int16_t* W = w.data();
    int16_t* B = b.data();
    const int seedCeil = seedMax.load();
    for (int d = 1;; ++d) {
        if (d > 30000) { std::fprintf(stderr, "error: depth overflow\n"); std::exit(2); }
        std::atomic<U64> made{0};
        if (d & 1) {
            // Winner to move: retract, and claim any entry not already at least
            // this good.  A conversion seed sitting on the entry is an upper
            // bound and may legitimately be improved here.
            parallelFor(nkk, 32, threads, [&](U64 lo, U64 hi, int) {
                U64 local = 0;
                Pos p;
                for (U64 kk = lo; kk < hi; ++kk) {
                    const Sq wk = idx.kkWk[kk], bk = idx.kkBk[kk];
                    p.wk = wk; p.bk = bk;
                    const U64 base = kk * npc;
                    for (U32 pc = 0; pc < npc; ++pc) {
                        const int16_t vb = B[base + pc], vw = W[base + pc];
                        const bool srcW = isWin(vb)  && winPly(vb)  == d - 1;
                        const bool srcB = isLoss(vw) && lossPly(vw) == d - 1;
                        if (!srcW && !srcB) continue;
                        idx.decode(pc, p.wp);
                        if (srcW) {   // White mates in d-1 with Black to move
                            retractWhite(g, wp, bp, wk, bk, p.wp[0], p.wp[1],
                                         [&](Sq a, Sq bb, Sq q, Sq r) {
                                Pos t; t.wk = a; t.bk = bb; t.wp[0] = q; t.wp[1] = r;
                                U64 s;
                                if (!idx.slotOf(t, s)) return;
                                int16_t cur = aload(W, s);
                                if (cur == VK_DEAD) return;
                                if (cur == VK_UNKNOWN || (isWin(cur) && winPly(cur) > d)) {
                                    astore(W, s, wMate(d)); ++local;
                                }
                            });
                        }
                        if (srcB) {   // Black mates in d-1 with White to move
                            retractBlack(g, wp, bp, wk, bk, p.wp[0], p.wp[1],
                                         [&](Sq a, Sq bb, Sq q, Sq r) {
                                Pos t; t.wk = a; t.bk = bb; t.wp[0] = q; t.wp[1] = r;
                                U64 s;
                                if (!idx.slotOf(t, s)) return;
                                int16_t cur = aload(B, s);
                                if (cur == VK_DEAD) return;
                                if (cur == VK_UNKNOWN || (isLoss(cur) && lossPly(cur) > d)) {
                                    astore(B, s, bMate(d)); ++local;
                                }
                            });
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
            parallelFor(nkk, 32, threads, [&](U64 lo, U64 hi, int) {
                U64 local = 0;
                Pos p;
                for (U64 kk = lo; kk < hi; ++kk) {
                    const Sq wk = idx.kkWk[kk], bk = idx.kkBk[kk];
                    p.wk = wk; p.bk = bk;
                    const U64 base = kk * npc;
                    for (U32 pc = 0; pc < npc; ++pc) {
                        const int16_t vw = W[base + pc], vb = B[base + pc];
                        const bool srcW = isWin(vw)  && winPly(vw)  == d - 1;
                        const bool srcB = isLoss(vb) && lossPly(vb) == d - 1;
                        if (!srcW && !srcB) continue;
                        idx.decode(pc, p.wp);
                        if (srcW) {   // candidates: black-to-move losses at ply d
                            retractBlack(g, wp, bp, wk, bk, p.wp[0], p.wp[1],
                                         [&](Sq a, Sq bb, Sq q, Sq r) {
                                Pos t; t.wk = a; t.bk = bb; t.wp[0] = q; t.wp[1] = r;
                                U64 s;
                                if (!idx.slotOf(t, s)) return;
                                if (aload(B, s) != VK_UNKNOWN) return;
                                int worst = -1; bool all = true;
                                genBlack(g, wp, bp, a, bb, q, r,
                                         [&](Sq a2, Sq b2, Sq q2, Sq r2, bool cap) {
                                    if (!all) return;
                                    int16_t v;
                                    if (cap) v = conv.afterBlackTakes(a2, b2, r2);
                                    else {
                                        Pos u; u.wk = a2; u.bk = b2; u.wp[0] = q2; u.wp[1] = r2;
                                        U64 s2;
                                        if (!idx.slotOf(u, s2)) { all = false; return; }
                                        v = aload(W, s2);
                                    }
                                    if (!isWin(v)) { all = false; return; }
                                    if (winPly(v) > worst) worst = winPly(v);
                                });
                                if (all && worst == d - 1) { astore(B, s, wMate(d)); ++local; }
                            });
                        }
                        if (srcB) {   // candidates: white-to-move losses at ply d
                            retractWhite(g, wp, bp, wk, bk, p.wp[0], p.wp[1],
                                         [&](Sq a, Sq bb, Sq q, Sq r) {
                                Pos t; t.wk = a; t.bk = bb; t.wp[0] = q; t.wp[1] = r;
                                U64 s;
                                if (!idx.slotOf(t, s)) return;
                                if (aload(W, s) != VK_UNKNOWN) return;
                                int worst = -1; bool all = true;
                                genWhite(g, wp, bp, a, bb, q, r,
                                         [&](Sq a2, Sq b2, Sq q2, Sq r2, bool cap) {
                                    if (!all) return;
                                    int16_t v;
                                    if (cap) v = conv.afterWhiteTakes(a2, b2, q2);
                                    else {
                                        Pos u; u.wk = a2; u.bk = b2; u.wp[0] = q2; u.wp[1] = r2;
                                        U64 s2;
                                        if (!idx.slotOf(u, s2)) { all = false; return; }
                                        v = aload(B, s2);
                                    }
                                    if (!isLoss(v)) { all = false; return; }
                                    if (lossPly(v) > worst) worst = lossPly(v);
                                });
                                if (all && worst == d - 1) { astore(W, s, bMate(d)); ++local; }
                            });
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
    st = KqkrStats{};
    st.slots = idx.nslots;
    // Carried across the reset: these were counted during initialisation.
    st.staleLossB = nStaleW.load();
    st.staleLossW = nStaleB.load();
    st.immobile   = nImmobile.load();
    std::atomic<U64> wWin{0}, wLoss{0}, wDraw{0}, wLegal{0};
    std::atomic<U64> bWin{0}, bLoss{0}, bDraw{0}, bLegal{0};
    std::atomic<int> deepW{-1}, deepB{-1};
    std::atomic<U64> deepWslot{0}, deepBslot{0};
    parallelFor(nkk, 64, threads, [&](U64 lo, U64 hi, int) {
        U64 aw = 0, al = 0, ad = 0, an = 0, bw = 0, bl = 0, bd = 0, bn = 0;
        for (U64 kk = lo; kk < hi; ++kk) {
            const U64 base = kk * npc;
            for (U32 pc = 0; pc < npc; ++pc) {
                int16_t& vw = w[base + pc];
                if (vw != VK_DEAD) {
                    if (vw == VK_UNKNOWN) vw = VK_DRAW;
                    ++an;
                    if (isWin(vw)) { ++aw;
                        int pl = winPly(vw);
                        int cur = deepW.load(std::memory_order_relaxed);
                        while (pl > cur && !deepW.compare_exchange_weak(cur, pl)) {}
                        if (pl >= deepW.load(std::memory_order_relaxed))
                            deepWslot.store(base + pc, std::memory_order_relaxed);
                    }
                    else if (isLoss(vw)) { ++al;
                        int pl = lossPly(vw);
                        int cur = deepB.load(std::memory_order_relaxed);
                        while (pl > cur && !deepB.compare_exchange_weak(cur, pl)) {}
                        if (pl >= deepB.load(std::memory_order_relaxed))
                            deepBslot.store(base + pc, std::memory_order_relaxed);
                    }
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
    });
    st.wLegal = wLegal; st.wWin = wWin; st.wLoss = wLoss; st.wDraw = wDraw;
    st.bLegal = bLegal; st.bWin = bWin; st.bLoss = bLoss; st.bDraw = bDraw;
    st.maxWinPly  = deepW.load() < 0 ? 0 : deepW.load();
    st.maxLossPly = deepB.load() < 0 ? 0 : deepB.load();

    // Recover a position realising the deepest win, deterministically: the
    // lowest slot at that depth, so repeated runs name the same one.
    auto findDeepest = [&](bool win, int ply, Pos& out) {
        if (ply <= 0 && !win) return;
        for (U64 kk = 0; kk < nkk; ++kk) {
            const U64 base = kk * npc;
            for (U32 pc = 0; pc < npc; ++pc) {
                int16_t v = w[base + pc];
                bool hit = win ? (isWin(v) && winPly(v) == ply)
                               : (isLoss(v) && lossPly(v) == ply);
                if (!hit) continue;
                out.wk = idx.kkWk[kk]; out.bk = idx.kkBk[kk];
                idx.decode(pc, out.wp);
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
    findDeepest(true,  st.maxWinPly,  st.deepest);
    if (st.wLoss) findDeepest(false, st.maxLossPly, st.deepestLoss);
    st.seconds = clock.s();
}

// Both conversions are played under the same rules as the table itself; see
// the note in verify() for what that changes.
void TableKQKR::buildSubTables(int threads, bool progress) const {
    if (!convQ) {
        convQ = std::make_unique<Table>(n, bareEndgameOf(whitePieceOf(mat.eg)));
        convQ->stalemateLoss = stalemateLoss;
        convQ->generate(threads, progress);
    }
    if (!convB) {
        convB = std::make_unique<Table>(n, subEndgame(mat.eg));
        convB->stalemateLoss = stalemateLoss;
        convB->generate(threads, progress);
    }
}

void kqkrMoves(const TableKQKR& t, const Pos& p, bool whiteToMove,
               const std::function<void(const Pos&, bool, int16_t)>& fn) {
    const Geometry& g = t.geo;
    const Piece bp = blackPieceOf(t.mat.eg);
    const Piece wp = whitePieceOf(t.mat.eg);
    t.buildSubTables(1, false);
    const Conv conv{*t.convQ, *t.convB};
    auto emit = [&](Sq a, Sq b2, Sq q, Sq r, bool cap, bool white) {
        Pos u; u.wk = a; u.bk = b2; u.wp[0] = q; u.wp[1] = r;
        int16_t v;
        if (cap) v = white ? conv.afterWhiteTakes(a, b2, q) : conv.afterBlackTakes(a, b2, r);
        else     v = t.valueAt(u, !white);
        fn(u, cap, v);
    };
    if (whiteToMove)
        genWhite(g, wp, bp, p.wk, p.bk, p.wp[0], p.wp[1],
                 [&](Sq a, Sq b2, Sq q, Sq r, bool cap) { emit(a, b2, q, r, cap, true); });
    else
        genBlack(g, wp, bp, p.wk, p.bk, p.wp[0], p.wp[1],
                 [&](Sq a, Sq b2, Sq q, Sq r, bool cap) { emit(a, b2, q, r, cap, false); });
}

// ---------------------------------------------------------------------------
// Bellman re-derivation: recompute every entry from its successors with the
// forward move generator alone, and compare.  Returns the mismatch count.
// ---------------------------------------------------------------------------
U64 TableKQKR::verify(int threads, bool progress) const {
    const Geometry& g = geo;
    const Piece bp = blackPieceOf(mat.eg);
    const Piece wp = whitePieceOf(mat.eg);
    const U32 npc = idx.npc;
    const U64 nkk = idx.nkk;
    // Both conversions are played under the same rules as the table itself.
    // Under the capture rules that matters twice over: KQK wins from more
    // placements, because a stalemate is a win there too, and K+B vs K stops
    // being a dead draw at all -- a lone bishop and king can take a bare
    // king's last square away.
    Table kqk(n, bareEndgameOf(whitePieceOf(mat.eg)));
    kqk.stalemateLoss = stalemateLoss; kqk.generate(threads, false);
    Table sub(n, subEndgame(mat.eg));
    sub.stalemateLoss = stalemateLoss; sub.generate(threads, false);
    const Conv conv{kqk, sub};
    std::atomic<U64> bad{0};

    parallelFor(nkk, 64, threads, [&](U64 lo, U64 hi, int) {
        U64 local = 0;
        Pos p;
        for (U64 kk = lo; kk < hi; ++kk) {
            const Sq wk = idx.kkWk[kk], bk = idx.kkBk[kk];
            p.wk = wk; p.bk = bk;
            const U64 base = kk * npc;
            for (U32 pc = 0; pc < npc; ++pc) {
                idx.decode(pc, p.wp);
                if (!idx.cfgLive(p.wp, wk, bk)) continue;
                if (!idx.cfgIsCanonical((int32_t)kk, p.wp)) continue;
                const Sq wq = p.wp[0], br = p.wp[1];

                for (int side = 0; side < 2; ++side) {
                    const bool wtm = (side == 0);
                    const int16_t stored = wtm ? w[base + pc] : b[base + pc];
                    const bool legal = wtm ? !blackChecked(g, wp, wk, bk, wq, br)
                                           : !whiteChecked(g, bp, wk, bk, wq, br);
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
                    if (wtm)
                        genWhite(g, wp, bp, wk, bk, wq, br,
                                 [&](Sq a, Sq b2, Sq q, Sq r, bool cap) {
                            if (cap) { see(conv.afterWhiteTakes(a, b2, q)); return; }
                            Pos u; u.wk = a; u.bk = b2; u.wp[0] = q; u.wp[1] = r;
                            U64 s; if (!idx.slotOf(u, s)) { ++moves; allLose = false; return; }
                            see(b[s]);
                        });
                    else
                        genBlack(g, wp, bp, wk, bk, wq, br,
                                 [&](Sq a, Sq b2, Sq q, Sq r, bool cap) {
                            if (cap) { see(conv.afterBlackTakes(a, b2, r)); return; }
                            Pos u; u.wk = a; u.bk = b2; u.wp[0] = q; u.wp[1] = r;
                            U64 s; if (!idx.slotOf(u, s)) { ++moves; allLose = false; return; }
                            see(w[s]);
                        });

                    int16_t want;
                    if (moves == 0) {
                        const bool inCheck = wtm ? whiteChecked(g, bp, wk, bk, wq, br)
                                                 : blackChecked(g, wp, wk, bk, wq, br);
                        const bool mobile = wtm ? whiteMobile(g, wp, wk, wq)
                                                : blackMobile(g, bp, bk, br);
                        bool imm = false;
                        want = terminal(stalemateLoss, inCheck, mobile,
                                        wtm ? bMate(0) : wMate(0), imm);
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
        bad.fetch_add(local, std::memory_order_relaxed);
    });
    if (progress)
        std::fprintf(stderr, "  verify: %llu mismatches\n", (unsigned long long)bad.load());
    return bad.load();
}

// ---------------------------------------------------------------------------
// The reference implementation: the same endgame with no symmetry at all, one
// entry per placement, and a different algorithm -- repeated Bellman relaxation
// to a fixpoint rather than backward induction by ply.  n^8 entries, so only
// small boards, but it is what catches indexing bugs, which a self-consistency
// check structurally cannot.
// ---------------------------------------------------------------------------
U64 kqkrBruteForceCheck(const TableKQKR& t, bool progress) {
    const Geometry& g = t.geo;
    const Piece bp = blackPieceOf(t.mat.eg);
    const Piece wp = whitePieceOf(t.mat.eg);
    const bool cap = t.stalemateLoss;
    const int nsq = g.nsq;
    const U64 N = (U64)nsq * nsq * nsq * nsq;
    std::vector<int16_t> W(N, VK_DEAD), B(N, VK_DEAD);
    auto ix = [&](Sq wk, Sq bk, Sq wq, Sq br) {
        return (((U64)wk * nsq + bk) * nsq + wq) * nsq + br;
    };
    Table kqk(t.n, bareEndgameOf(whitePieceOf(t.mat.eg)));
    kqk.stalemateLoss = t.stalemateLoss; kqk.generate(1, false);
    Table sub(t.n, subEndgame(t.mat.eg));
    sub.stalemateLoss = t.stalemateLoss; sub.generate(1, false);
    const Conv conv{kqk, sub};

    // Every placement, in both sides-to-move.  A lambda so the three passes
    // below share exactly one definition of what a legal placement is.
    auto forEachPlacement = [&](auto&& body) {
        for (Sq wk = 0; wk < nsq; ++wk)
        for (Sq bk = 0; bk < nsq; ++bk) {
            if (g.kingsTouch(wk, bk)) continue;
            for (Sq wq = 0; wq < nsq; ++wq) {
                if (wq == wk || wq == bk) continue;
                for (Sq br = 0; br < nsq; ++br) {
                    if (br == wk || br == bk || br == wq) continue;
                    body(wk, bk, wq, br);
                }
            }
        }
    };

    // ---- terminals, and how deep a conversion can reach -------------------
    int convCeil = 0;
    forEachPlacement([&](Sq wk, Sq bk, Sq wq, Sq br) {
        U64 i = ix(wk, bk, wq, br);
        bool imm = false;
        if (!blackChecked(g, wp, wk, bk, wq, br)) {
            int mv = 0;
            genWhite(g, wp, bp, wk, bk, wq, br, [&](Sq a, Sq b2, Sq q, Sq, bool cap) {
                ++mv;
                if (!cap) return;
                int16_t v = conv.afterWhiteTakes(a, b2, q);
                if (isWin(v) && winPly(v) + 1 > convCeil) convCeil = winPly(v) + 1;
            });
            W[i] = mv ? VK_UNKNOWN
                      : terminal(cap, whiteChecked(g, bp, wk, bk, wq, br),
                                 whiteMobile(g, wp, wk, wq), bMate(0), imm);
        }
        if (!whiteChecked(g, bp, wk, bk, wq, br)) {
            int mv = 0;
            genBlack(g, wp, bp, wk, bk, wq, br, [&](Sq a, Sq b2, Sq, Sq r, bool cap) {
                ++mv;
                if (!cap) return;
                int16_t v = conv.afterBlackTakes(a, b2, r);
                if (isLoss(v) && lossPly(v) + 1 > convCeil) convCeil = lossPly(v) + 1;
            });
            B[i] = mv ? VK_UNKNOWN
                      : terminal(cap, blackChecked(g, wp, wk, bk, wq, br),
                                 blackMobile(g, bp, bk, br), wMate(0), imm);
        }
    });

    // ---- one forward sweep per ply ----------------------------------------
    // Deliberately not the algorithm in generate(): no un-moves, no candidate
    // sets, no symmetry.  A position is settled at ply d purely by looking at
    // what its own moves lead to.
    for (int d = 1;; ++d) {
        U64 made = 0;
        forEachPlacement([&](Sq wk, Sq bk, Sq wq, Sq br) {
            U64 i = ix(wk, bk, wq, br);
            for (int side = 0; side < 2; ++side) {
                const bool wtm = (side == 0);
                int16_t cur = wtm ? W[i] : B[i];
                if (cur != VK_UNKNOWN) continue;
                bool wins = false, allLose = true;
                int worst = -1;
                auto see = [&](int16_t v) {
                    // "v" is the successor, with the opponent to move.
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
                if (wtm)
                    genWhite(g, wp, bp, wk, bk, wq, br, [&](Sq a, Sq b2, Sq q, Sq r, bool cap) {
                        see(cap ? conv.afterWhiteTakes(a, b2, q) : B[ix(a, b2, q, r)]);
                    });
                else
                    genBlack(g, wp, bp, wk, bk, wq, br, [&](Sq a, Sq b2, Sq q, Sq r, bool cap) {
                        see(cap ? conv.afterBlackTakes(a, b2, r) : W[ix(a, b2, q, r)]);
                    });
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
    forEachPlacement([&](Sq wk, Sq bk, Sq wq, Sq br) {
        Pos p; p.wk = wk; p.bk = bk; p.wp[0] = wq; p.wp[1] = br;
        U64 i = ix(wk, bk, wq, br);
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
// board: the move generator and the index.  The brute force stops at n = 6
// because it needs n^8 entries, and the Bellman check shares this file's move
// generator, so without these two nothing would test either one at n = 16.
// ---------------------------------------------------------------------------
namespace {

// A deliberately naive legal-move generator: an occupancy board, rays walked
// one square at a time, check detected by scanning.  Shares nothing with the
// generators above beyond board arithmetic.
struct Naive {
    const Geometry& g;
    Piece bp;
    // Black's rays, written out as (df, dr) pairs rather than read from the
    // shared direction table, so that a bug in that table cannot hide here.
    static constexpr int ORTHO[8] = {1,0, 0,1, -1,0, 0,-1};
    static constexpr int DIAG[8]  = {1,1, -1,1, -1,-1, 1,-1};
    Naive(const Geometry& geo, Piece black) : g(geo), bp(black) {}
    const int* bray() const { return bp == Piece::Bishop ? DIAG : ORTHO; }
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
    std::vector<char> board(Sq wk, Sq bk, Sq wq, Sq br) const {
        std::vector<char> occ(g.nsq, 0);
        if (wk >= 0) occ[wk] = 1;
        if (bk >= 0) occ[bk] = 1;
        if (wq >= 0) occ[wq] = 1;
        if (br >= 0) occ[br] = 1;
        return occ;
    }
    bool wCheck(Sq wk, Sq bk, Sq wq, Sq br) const {
        if (g.kingsTouch(wk, bk)) return true;
        if (br < 0) return false;
        return rayHits(br, wk, board(wk, bk, wq, br), bray(), 4);
    }
    bool bCheck(Sq wk, Sq bk, Sq wq, Sq br) const {
        if (g.kingsTouch(wk, bk)) return true;
        if (wq < 0) return false;
        static const int all8[16] = {1,0, 1,1, 0,1, -1,1, -1,0, -1,-1, 0,-1, 1,-1};
        return rayHits(wq, bk, board(wk, bk, wq, br), all8, 8);
    }
    void white(Sq wk, Sq bk, Sq wq, Sq br, std::set<U64>& out) const {
        auto add = [&](Sq a, Sq b, Sq q, Sq r) {
            if (wCheck(a, b, q, r)) return;
            out.insert((((U64)(a+1) * 4096 + (b+1)) * 4096 + (q+1)) * 4096 + (r+1));
        };
        for (Sq t = 0; t < g.nsq; ++t) {
            if (t == wk || !g.kingsTouch(wk, t) || t == wq) continue;
            add(t, bk, wq, t == br ? -1 : br);
        }
        static const int all8[16] = {1,0, 1,1, 0,1, -1,1, -1,0, -1,-1, 0,-1, 1,-1};
        for (int d = 0; d < 8; ++d) {
            int f = g.file(wq) + all8[2*d], r = g.rank(wq) + all8[2*d+1];
            while (g.onBoard(f, r)) {
                Sq t = g.sq(f, r);
                if (t == wk || t == bk) break;
                add(wk, bk, t, t == br ? -1 : br);
                if (t == br) break;
                f += all8[2*d]; r += all8[2*d+1];
            }
        }
    }
    void black(Sq wk, Sq bk, Sq wq, Sq br, std::set<U64>& out) const {
        auto add = [&](Sq a, Sq b, Sq q, Sq r) {
            if (bCheck(a, b, q, r)) return;
            out.insert((((U64)(a+1) * 4096 + (b+1)) * 4096 + (q+1)) * 4096 + (r+1));
        };
        for (Sq t = 0; t < g.nsq; ++t) {
            if (t == bk || !g.kingsTouch(bk, t) || t == br) continue;
            add(wk, t, t == wq ? -1 : wq, br);
        }
        const int* ray = bray();
        for (int d = 0; d < 4; ++d) {
            int f = g.file(br) + ray[2*d], r = g.rank(br) + ray[2*d+1];
            while (g.onBoard(f, r)) {
                Sq t = g.sq(f, r);
                if (t == bk || t == wk) break;
                add(wk, bk, t == wq ? -1 : wq, t);
                if (t == wq) break;
                f += ray[2*d]; r += ray[2*d+1];
            }
        }
    }
};

} // namespace

U64 kqkrSelfCheck(int lo, int hi, U64 trials, bool progress, Endgame eg) {
    U64 bad = 0;
    const Piece bp = blackPieceOf(eg);
    const Piece wp = whitePieceOf(eg);
    for (int n = lo; n <= hi; ++n) {
        Geometry g(n);
        Naive nv(g, bp);
        Index idx(g, Material::of(eg));
        std::mt19937_64 rng(20260906u + n);
        std::uniform_int_distribution<int> pick(0, g.nsq - 1);
        U64 mgBad = 0, ixBad = 0, tested = 0;
        std::map<U64, U64> slotOwner;      // slot -> the orbit it was first seen from
        for (U64 i = 0; i < trials; ++i) {
            Pos p;
            p.wk = pick(rng); p.bk = pick(rng); p.wp[0] = pick(rng); p.wp[1] = pick(rng);
            if (p.wk == p.bk || p.wk == p.wp[0] || p.wk == p.wp[1] ||
                p.bk == p.wp[0] || p.bk == p.wp[1] || p.wp[0] == p.wp[1]) continue;
            if (g.kingsTouch(p.wk, p.bk)) continue;
            ++tested;

            // (a) the index: every D4 image must land on the same slot, and no
            //     two distinct orbits may share one.
            U64 s0;
            if (!idx.slotOf(p, s0)) { ++ixBad; continue; }
            U64 orbit = ~0ull;
            for (int sym = 0; sym < NSYM; ++sym) {
                Pos q; q.wk = g.image(sym, p.wk); q.bk = g.image(sym, p.bk);
                q.wp[0] = g.image(sym, p.wp[0]); q.wp[1] = g.image(sym, p.wp[1]);
                U64 s;
                if (!idx.slotOf(q, s) || s != s0) { ++ixBad; break; }
                U64 k = (((U64)q.wk * g.nsq + q.bk) * g.nsq + q.wp[0]) * g.nsq + q.wp[1];
                if (k < orbit) orbit = k;
            }
            auto it = slotOwner.find(s0);
            if (it == slotOwner.end()) slotOwner.emplace(s0, orbit);
            else if (it->second != orbit) ++ixBad;

            // (b) the move generators, against the naive ones
            for (int side = 0; side < 2; ++side) {
                const bool wtm = (side == 0);
                if (wtm ? nv.bCheck(p.wk, p.bk, p.wp[0], p.wp[1])
                        : nv.wCheck(p.wk, p.bk, p.wp[0], p.wp[1])) continue;
                std::set<U64> mine, theirs;
                auto rec = [&](Sq a, Sq b, Sq q, Sq r, bool) {
                    mine.insert((((U64)(a+1) * 4096 + (b+1)) * 4096 + (q+1)) * 4096 + (r+1));
                };
                if (wtm) { kqkrGenWhiteRaw(g, wp, bp, p.wk, p.bk, p.wp[0], p.wp[1], rec);
                           nv.white(p.wk, p.bk, p.wp[0], p.wp[1], theirs); }
                else     { kqkrGenBlackRaw(g, wp, bp, p.wk, p.bk, p.wp[0], p.wp[1], rec);
                           nv.black(p.wk, p.bk, p.wp[0], p.wp[1], theirs); }
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
