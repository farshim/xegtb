// kqkkcap.cpp -- king and queen against two black kings, under CAPTURE rules.
//
// The rules
// ---------
// **Every king is an ordinary man, and a player wins by capturing all of the
// opponent's.**  In full, for any number of kings a side; everything not
// listed here is chess:
//
//   1. Every man moves and captures exactly as in chess, kings included: one
//      square in any direction, taking whatever stands on it.
//   2. A king is an ordinary piece in respect of check.  It may move to an
//      attacked square, it may be left standing on one, and it may be captured
//      like any other man -- by anything, another king included.  There is no
//      check, no checkmate and no pin: *every* move that obeys rule 1 may be
//      played, and a side that needs to walk a king into an attacked square is
//      free to.
//   3. A player wins the instant the opponent's *last* king is taken.  The
//      game ends with that capture and nothing that would have followed it
//      matters -- in particular the last king may be taken by a move that
//      leaves the capturer's own king hanging.  Losing a king while others
//      remain costs a piece and nothing more.
//   4. A player who still has a king and no legal move is stalemated, and the
//      game is drawn.  That is the `!moves` case in Acc::value below.
//   5. Promotion and en passant are as in chess.  Castling plays no part.
//
// Neither black king is privileged over the other, and neither over the white
// one; the only asymmetry is that Black has two kings to lose and White one.
//
// One king a side: this is chess, up to stalemate
// -----------------------------------------------
// With k = 1 the rules above are the ordinary game with exactly one clause
// changed.  Call a position *sound* if the side not to move does not have its
// king attacked -- the condition every position reachable in chess satisfies,
// and the one the index uses to decide which slots are legal.  Then for sound
// positions these rules agree with chess except where the side to move has no
// legal chess move, and there:
//
//   * if it has a move under rule 2, it loses.  This is the familiar half:
//     **what the ordinary rules call stalemate is a loss here**, because the
//     moves that give the king away are legal and one of them must be played.
//     It is why `K + Q vs K` below is won from every position, in 17 plies
//     rather than the 19 of ordinary KQK, whose extra move is the one White
//     spends dodging a stalemate.
//   * if it has no move under rule 2 either -- *total immobility* -- rule 4
//     draws.  Where the immobile king is unattacked that agrees with chess;
//     where it is attacked, chess says checkmate and these rules say draw, and
//     that is the only case in which capture rules are the kinder of the two.
//
// Immobility needs at least four men on the immobile side: every square beside
// its king must hold one of its own men, and a king has at least three such
// squares.  Every side of every table built here has two -- king and queen, or
// king and king -- so rule 4 never fires in this program, and the code below
// sees only the first half of that dichotomy.  README section 5 states the
// theorem, its proof and the classification of the surviving stalemates.
//
// What that changes, against the mating rules of kqkk.cpp:
//
//   * **A fork wins a king, not the game.**  White must take one king and then
//     hunt the other, which is what the endgame is now about.
//   * **The two black kings defend each other.**  Q x K is answered by K x Q,
//     so a capture is only safe when the white king covers the square.
//   * **White can lose.**  A black king beside the white king takes it and the
//     game is over, whatever else stands on the board.
//   * **The queen is not expendable.**  ...K x Q leaves a white king against
//     two black kings, and that is a black *win*, not a draw: two kings, kept
//     side by side so that neither can be taken safely, corner a lone king and
//     capture it.  This program computes that rather than assuming it; see
//     `K vs K + K` in the census, which is a black win from every position
//     with Black to move.
//
// So the table converts into three sub-tables, all under the same rules and
// all built here:
//
//     K vs K        the bare race: a draw unless the kings already touch
//     K vs K + K    after ...K x Q -- Black wins
//     K + Q vs K    after White takes a king -- White wins, and with no
//                   stalemate to dodge it is faster than ordinary KQK
//
// Encoding
// --------
// Values are **relative to the side to move**: v > 0 means the side to move
// wins in v plies, v < 0 means it loses in -v plies, and 0 is a draw.  This
// differs from kqkr.cpp, which is White-relative; here both sides win often,
// and the symmetric form needs no sign flips anywhere in the induction.
//
// The induction is the general one -- neither side's entries are constrained
// in sign -- so it runs by ply over buckets: wins at depth d are committed,
// their predecessors are re-tested for losses, and losses at depth d have
// their predecessors marked as wins at d+1.  Conversions into the sub-tables
// are read forwards and enter as seeds at whatever depth they name, which is
// why the buckets are keyed on depth rather than swept in strict alternation.
// As everywhere else in this program there is no successor counter: on a
// symmetry-reduced index it would be unsound (README, section 4).
#include "table.hpp"

#include <atomic>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <stdexcept>

namespace kqk {
namespace {

struct Timer {
    std::chrono::steady_clock::time_point t0 = std::chrono::steady_clock::now();
    double s() const {
        return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    }
};

// Accumulates the successors of one position and reports its value.  A move is
// scored by what it does to the *opponent*: if it leaves them lost in k plies,
// I win in k+1; if every move leaves them winning, I lose by the slowest of
// them.  `winNow` is the move that takes the opponent's last king.
struct Acc {
    int best = 0, worst = 0, moves = 0;
    bool anyDraw = false, anyUnknown = false;
    inline void add(int16_t v) {
        ++moves;
        if (v == VC_UNKNOWN) { anyUnknown = true; return; }
        if (v < 0) { int w = -v + 1; if (!best || w < best) best = w; }
        else if (v > 0) { if (v + 1 > worst) worst = v + 1; }
        else anyDraw = true;
    }
    inline void winNow() { ++moves; if (!best || best > 1) best = 1; }
    inline int16_t value() const {
        if (best) return (int16_t)best;
        if (anyUnknown) return VC_UNKNOWN;
        if (!moves || anyDraw) return 0;
        return (int16_t)-worst;
    }
};

constexpr int KFc[8] = { 1, 1, 0, -1, -1, -1, 0, 1 };
constexpr int KRc[8] = { 0, 1, 1, 1, 0, -1, -1, -1 };

inline Sq kstep(const Geometry& g, Sq s, int d) {
    int f = g.file(s) + KFc[d], r = g.rank(s) + KRc[d];
    return g.onBoard(f, r) ? g.sq(f, r) : Sq(-1);
}

} // namespace

// ---------------------------------------------------------------------------
// The three sub-endgames.  All are small -- one king pair, one king triple or
// one king pair and a queen square -- so they are solved by sweeping until
// nothing changes, which needs no frontier bookkeeping at all.
// ---------------------------------------------------------------------------
// The two king-only tables.  K vs K + K is a three-man endgame in its own
// right -- nblk entries, no queen dimension -- so it is separable from the
// four-man table above it, and `--kvkk` builds only this much.
//
// Note on the sweep below.  It stops at the first depth that assigns nothing,
// which is sound here but would not be in general: a value at depth d needs a
// successor at depth d-1, *except* where a conversion seeds one, and the only
// conversion out of K vs K + K is White taking a king, which lands in K vs K.
// Every K vs K value is 0 or 1 -- a lone king cannot force contact with
// another -- so no seed sits deeper than one ply and the depths run
// contiguously from 2 on.  (Checked: sweeping n = 15 to depth 319 rather than
// stopping at 74 changes not one entry.)
void TableKQKKCap::solveKingTables(bool progress) {
    const Geometry& g = geo;
    const U64 nkk = idx3.nkk, nblk = idx.nblk;
    Timer clock;

    // ---- K vs K -----------------------------------------------------------
    kkW.assign(nkk, VC_UNKNOWN);
    kkB.assign(nkk, VC_UNKNOWN);
    for (U64 i = 0; i < nkk; ++i) {
        const Sq wk = idx3.kkWk[i], bk = idx3.kkBk[i];
        if (g.kingsTouch(wk, bk)) { kkW[i] = 1; kkB[i] = 1; }   // whoever moves takes
    }
    for (int d = 2; d < 4000; ++d) {
        bool changed = false;
        for (int side = 0; side < 2; ++side) {
            std::vector<int16_t>& me = side ? kkB : kkW;
            const std::vector<int16_t>& op = side ? kkW : kkB;
            for (U64 i = 0; i < nkk; ++i) {
                if (me[i] != VC_UNKNOWN) continue;
                const Sq wk = idx3.kkWk[i], bk = idx3.kkBk[i];
                Acc ac;
                const Sq from = side ? bk : wk;
                for (int k = 0; k < 8; ++k) {
                    const Sq t = kstep(g, from, k);
                    if (t < 0) continue;
                    const Sq nw = side ? wk : t, nb = side ? t : bk;
                    if (nw == nb) continue;              // capture: settled above
                    const int32_t j = idx3.kkIndexOf(nw, nb);
                    ac.add(j < 0 ? (int16_t)VC_DEAD : op[j]);
                }
                const int16_t v = ac.value();
                if (v != VC_UNKNOWN && (v == d || v == -d)) { me[i] = v; changed = true; }
            }
        }
        if (!changed) break;
    }
    for (U64 i = 0; i < nkk; ++i) {
        if (kkW[i] == VC_UNKNOWN) kkW[i] = 0;
        if (kkB[i] == VC_UNKNOWN) kkB[i] = 0;
    }

    // ---- K vs K + K -------------------------------------------------------
    k3W.assign(nblk, VC_UNKNOWN);
    k3B.assign(nblk, VC_UNKNOWN);
    for (U64 i = 0; i < nblk; ++i) {
        const Sq wk = idx.blkWk[i], a = idx.blkB1[i], b = idx.blkB2[i];
        if (g.kingsTouch(wk, a) || g.kingsTouch(wk, b)) k3B[i] = 1;   // ...KxK ends it
    }
    for (int d = 1; d < 4000; ++d) {
        bool changed = false;
        for (U64 i = 0; i < nblk; ++i) {
            const Sq wk = idx.blkWk[i], a = idx.blkB1[i], b = idx.blkB2[i];
            if (k3W[i] == VC_UNKNOWN) {
                Acc ac;
                for (int k = 0; k < 8; ++k) {
                    const Sq t = kstep(g, wk, k);
                    if (t < 0) continue;
                    if (t == a || t == b) {                       // K x K -> K vs K
                        const Sq rest = (t == a) ? b : a;
                        const int32_t j = idx3.kkIndexOf(t, rest);
                        ac.add(j < 0 ? (int16_t)VC_DEAD : kkB[j]);
                    } else {
                        const int32_t j = idx.blockOfTriple(t, a, b);
                        ac.add(j < 0 ? (int16_t)VC_DEAD : k3B[j]);
                    }
                }
                const int16_t v = ac.value();
                if (v != VC_UNKNOWN && (v == d || v == -d)) { k3W[i] = v; changed = true; }
            }
            if (k3B[i] == VC_UNKNOWN) {
                Acc ac;
                for (int s = 0; s < 2; ++s) {
                    const Sq from = s ? b : a, oth = s ? a : b;
                    for (int k = 0; k < 8; ++k) {
                        const Sq t = kstep(g, from, k);
                        if (t < 0 || t == oth) continue;
                        if (t == wk) { ac.winNow(); continue; }    // ...KxK ends it
                        const int32_t j = idx.blockOfTriple(wk, t, oth);
                        ac.add(j < 0 ? (int16_t)VC_DEAD : k3W[j]);
                    }
                }
                const int16_t v = ac.value();
                if (v != VC_UNKNOWN && (v == d || v == -d)) { k3B[i] = v; changed = true; }
            }
        }
        if (!changed && d > 1) break;
    }
    for (U64 i = 0; i < nblk; ++i) {
        if (k3W[i] == VC_UNKNOWN) k3W[i] = 0;
        if (k3B[i] == VC_UNKNOWN) k3B[i] = 0;
    }

}

// K + Q vs K, the endgame White converts into when he wins a king.
void TableKQKKCap::solveSubTables(bool progress) {
    solveKingTables(progress);
    const Geometry& g = geo;
    const U64 nkk = idx3.nkk;
    const U32 nsq = (U32)g.nsq;
    Timer clock;

    const U64 n3 = idx3.nslots;
    q3W.assign(n3, VC_DEAD);
    q3B.assign(n3, VC_DEAD);
    for (U64 kk = 0; kk < nkk; ++kk) {
        const Sq wk = idx3.kkWk[kk], bk = idx3.kkBk[kk];
        for (U32 q = 0; q < nsq; ++q) {
            const Sq wq = (Sq)q;
            if (wq == wk || wq == bk) continue;
            Sq cfg[MAXWP] = { wq, -1 };
            if (!idx3.cfgIsCanonical((int32_t)kk, cfg)) continue;
            const U64 s = kk * idx3.npc + q;
            q3W[s] = VC_UNKNOWN;
            q3B[s] = VC_UNKNOWN;
            // White takes the black king -- Black's last -- and the game ends.
            if (g.kingsTouch(wk, bk) || g.attacks(Piece::Queen, wq, bk, wk)) q3W[s] = 1;
            if (g.kingsTouch(bk, wk)) q3B[s] = 1;                 // ...KxK ends it
        }
    }
    for (int d = 2; d < 4000; ++d) {
        bool changed = false;
        for (U64 kk = 0; kk < nkk; ++kk) {
            const Sq wk = idx3.kkWk[kk], bk = idx3.kkBk[kk];
            for (U32 q = 0; q < nsq; ++q) {
                const U64 s = kk * idx3.npc + q;
                if (q3W[s] == VC_UNKNOWN) {
                    const Sq wq = (Sq)q;
                    Acc ac;
                    for (int k = 0; k < 8; ++k) {                 // king
                        const Sq t = kstep(g, wk, k);
                        if (t < 0 || t == wq || t == bk) continue;  // bk settled at init
                        Pos p; p.wk = t; p.bk = bk; p.wp[0] = wq;
                        U64 j; ac.add(idx3.slotOf(p, j) ? q3B[j] : (int16_t)VC_DEAD);
                    }
                    forEachMove<Piece::Queen>(g, wq, wk, bk, -1, [&](Sq t) {   // queen
                        Pos p; p.wk = wk; p.bk = bk; p.wp[0] = t;
                        U64 j; ac.add(idx3.slotOf(p, j) ? q3B[j] : (int16_t)VC_DEAD);
                        return true;
                    });
                    const int16_t v = ac.value();
                    if (v != VC_UNKNOWN && (v == d || v == -d)) { q3W[s] = v; changed = true; }
                }
                if (q3B[s] == VC_UNKNOWN) {
                    const Sq wq = (Sq)q;
                    Acc ac;
                    for (int k = 0; k < 8; ++k) {
                        const Sq t = kstep(g, bk, k);
                        if (t < 0 || t == wk) continue;           // KxK settled at init
                        if (t == wq) {                            // ...KxQ -> K vs K
                            const int32_t j = idx3.kkIndexOf(wk, t);
                            ac.add(j < 0 ? (int16_t)VC_DEAD : kkW[j]);
                            continue;
                        }
                        Pos p; p.wk = wk; p.bk = t; p.wp[0] = wq;
                        U64 j; ac.add(idx3.slotOf(p, j) ? q3W[j] : (int16_t)VC_DEAD);
                    }
                    const int16_t v = ac.value();
                    if (v != VC_UNKNOWN && (v == d || v == -d)) { q3B[s] = v; changed = true; }
                }
            }
        }
        if (!changed) break;
    }
    for (U64 i = 0; i < n3; ++i) {
        if (q3W[i] == VC_UNKNOWN) q3W[i] = 0;
        if (q3B[i] == VC_UNKNOWN) q3B[i] = 0;
    }
    if (progress)
        std::fprintf(stderr, "  sub-tables solved in %.2fs\n", clock.s());
}

// ---------------------------------------------------------------------------
// Lookups.  Every capture leaves this table for one of the three above, so a
// conversion is a forward read and never a retraction: a predecessor of a
// four-man position under a capture would have five men.
// ---------------------------------------------------------------------------
int16_t TableKQKKCap::kkValue(Sq wk, Sq bk, bool whiteToMove) const {
    if (wk == bk) return VC_DEAD;
    const int32_t j = idx3.kkIndexOf(wk, bk);
    if (j < 0) return VC_DEAD;
    return whiteToMove ? kkW[j] : kkB[j];
}
int16_t TableKQKKCap::k3Value(Sq wk, Sq a, Sq b, bool whiteToMove) const {
    if (a == b || a == wk || b == wk) return VC_DEAD;
    const int32_t j = idx.blockOfTriple(wk, a, b);
    if (j < 0) return VC_DEAD;
    return whiteToMove ? k3W[j] : k3B[j];
}
int16_t TableKQKKCap::q3Value(Sq wk, Sq wq, Sq bk, bool whiteToMove) const {
    if (wq == wk || wq == bk || wk == bk) return VC_DEAD;
    Pos p; p.wk = wk; p.bk = bk; p.wp[0] = wq;
    U64 s;
    if (!idx3.slotOf(p, s)) return VC_DEAD;
    return whiteToMove ? q3W[s] : q3B[s];
}
int16_t TableKQKKCap::valueAt(const PosKK& p, bool whiteToMove) const {
    if (p.wk < 0 || p.wq < 0 || p.bk1 < 0 || p.bk2 < 0) return VC_DEAD;
    if (p.bk1 == p.bk2 || p.wq == p.wk || p.wq == p.bk1 || p.wq == p.bk2 ||
        p.wk == p.bk1 || p.wk == p.bk2) return VC_DEAD;
    U64 s;
    if (idx.slotOf(p.wk, p.bk1, p.bk2, p.wq, s) < 0) return VC_DEAD;
    return whiteToMove ? w[s] : b[s];
}

namespace {

inline int16_t mainVal(const TableKQKKCap& T, Sq wk, Sq wq, Sq a, Sq b, bool wtm) {
    U64 s;
    if (T.idx.slotOf(wk, a, b, wq, s) < 0) return VC_DEAD;
    return wtm ? T.w[s] : T.b[s];
}

// White to move.  He may step or slide onto a black king, which takes it and
// converts into K + Q vs K; he may not step onto his own queen.
int16_t evalWhite(const TableKQKKCap& T, Sq wk, Sq wq, Sq a, Sq b) {
    const Geometry& g = T.geo;
    Acc ac;
    for (int k = 0; k < 8; ++k) {
        const Sq t = kstep(g, wk, k);
        if (t < 0 || t == wq) continue;
        if (t == a)      ac.add(T.q3Value(t, wq, b, false));
        else if (t == b) ac.add(T.q3Value(t, wq, a, false));
        else             ac.add(mainVal(T, t, wq, a, b, false));
    }
    for (int d = 0; d < 8; ++d) {
        Sq t = wq;
        for (;;) {
            t = kstep(g, t, d);
            if (t < 0 || t == wk) break;                 // off the board, or his king
            if (t == a) { ac.add(T.q3Value(wk, t, b, false)); break; }
            if (t == b) { ac.add(T.q3Value(wk, t, a, false)); break; }
            ac.add(mainVal(T, wk, t, a, b, false));
        }
    }
    return ac.value();
}

// Black to move.  Taking the white king ends the game at once -- White has no
// second king -- and taking the queen converts into K vs K + K.
int16_t evalBlack(const TableKQKKCap& T, Sq wk, Sq wq, Sq a, Sq b) {
    const Geometry& g = T.geo;
    Acc ac;
    for (int s = 0; s < 2; ++s) {
        const Sq from = s ? b : a, oth = s ? a : b;
        for (int k = 0; k < 8; ++k) {
            const Sq t = kstep(g, from, k);
            if (t < 0 || t == oth) continue;
            if (t == wk) { ac.winNow(); continue; }
            if (t == wq) { ac.add(T.k3Value(wk, t, oth, true)); continue; }
            ac.add(mainVal(T, wk, wq, t, oth, true));
        }
    }
    return ac.value();
}

// Retractions.  White's are quiet moves of the king or the queen; Black's are
// quiet moves of either king.  No un-captures, for the reason in the header.
template <class F>
inline void retractWhite(const Geometry& g, Sq wk, Sq wq, Sq a, Sq b, F&& fn) {
    for (int k = 0; k < 8; ++k) {
        const Sq f = kstep(g, wk, k);
        if (f < 0 || f == wq || f == a || f == b) continue;
        fn(f, wq);
    }
    for (int d = 0; d < 8; ++d) {
        Sq t = wq;
        for (;;) {
            t = kstep(g, t, d);
            if (t < 0 || t == wk || t == a || t == b) break;
            fn(wk, t);
        }
    }
}
template <class F>
inline void retractBlack(const Geometry& g, Sq wk, Sq wq, Sq a, Sq b, F&& fn) {
    for (int s = 0; s < 2; ++s) {
        const Sq cur = s ? b : a, oth = s ? a : b;
        for (int k = 0; k < 8; ++k) {
            const Sq f = kstep(g, cur, k);
            if (f < 0 || f == wk || f == wq || f == oth) continue;
            fn(f, oth);
        }
    }
}

} // namespace

// ---------------------------------------------------------------------------
// The four-man table.  Wins and losses are found by ply, in buckets keyed on
// depth: a conversion can name any depth, so the two sides do not alternate in
// lockstep the way they do when only one of them can win.
// ---------------------------------------------------------------------------
void TableKQKKCap::generate(int threads, bool progress) {
    Timer clock;
    solveSubTables(progress);

    const Geometry& g = geo;
    const U32 npc = idx.npc;
    const U64 nslots = idx.nslots;
    w.assign(nslots, VC_DEAD);
    b.assign(nslots, VC_DEAD);

    for (U64 blk = 0; blk < idx.nblk; ++blk) {
        const Sq wk = idx.blkWk[blk], a = idx.blkB1[blk], bb = idx.blkB2[blk];
        const U64 base = blk * npc;
        for (U32 q = 0; q < npc; ++q) {
            const Sq wq = (Sq)q;
            if (wq == wk || wq == a || wq == bb) continue;
            if (!idx.queenIsCanonical(blk, wq)) continue;
            w[base + q] = VC_UNKNOWN;
            b[base + q] = VC_UNKNOWN;
        }
    }

    std::vector<std::vector<U64>> winB(64), lossB(64);
    int maxD = 1;
    auto push = [&](std::vector<std::vector<U64>>& bk, int d, U64 s) {
        if (d <= 0) return;
        if ((size_t)d >= bk.size()) bk.resize((size_t)d + 64);
        bk[d].push_back(s);
        if (d > maxD) maxD = d;
    };

    // Seeds: everything a position can settle from conversions and terminals
    // alone, before any in-table successor is known.
    for (U64 blk = 0; blk < idx.nblk; ++blk) {
        const Sq wk = idx.blkWk[blk], a = idx.blkB1[blk], bb = idx.blkB2[blk];
        const U64 base = blk * npc;
        for (U32 q = 0; q < npc; ++q) {
            if (w[base + q] == VC_DEAD) continue;
            const Sq wq = (Sq)q;
            const int16_t vw = evalWhite(*this, wk, wq, a, bb);
            if (vw != VC_UNKNOWN && vw > 0) push(winB,  vw, (base + q) * 2 + 0);
            if (vw != VC_UNKNOWN && vw < 0) push(lossB, -vw, (base + q) * 2 + 0);
            const int16_t vb = evalBlack(*this, wk, wq, a, bb);
            if (vb != VC_UNKNOWN && vb > 0) push(winB,  vb, (base + q) * 2 + 1);
            if (vb != VC_UNKNOWN && vb < 0) push(lossB, -vb, (base + q) * 2 + 1);
        }
    }

    auto cell = [&](U64 s) -> int16_t& { return (s & 1) ? b[s >> 1] : w[s >> 1]; };
    auto decode = [&](U64 s, Sq& wk, Sq& wq, Sq& a, Sq& bb) {
        const U64 slot = s >> 1;
        const U64 blk = slot / npc;
        wq = (Sq)(slot % npc);
        wk = idx.blkWk[blk]; a = idx.blkB1[blk]; bb = idx.blkB2[blk];
    };

    U64 wins = 0, losses = 0;
    for (int d = 1; d <= maxD; ++d) {
        std::vector<U64> Wd, Ld;
        if ((size_t)d < winB.size()) {
            for (U64 s : winB[d]) if (cell(s) == VC_UNKNOWN) { cell(s) = (int16_t)d; Wd.push_back(s); }
            std::vector<U64>().swap(winB[d]);
        }
        if ((size_t)d < lossB.size()) {
            for (U64 s : lossB[d]) if (cell(s) == VC_UNKNOWN) { cell(s) = (int16_t)-d; Ld.push_back(s); }
            std::vector<U64>().swap(lossB[d]);
        }
        wins += Wd.size(); losses += Ld.size();

        // A loss at d makes every predecessor a win at d+1.
        for (U64 s : Ld) {
            Sq wk, wq, a, bb; decode(s, wk, wq, a, bb);
            auto mark = [&](Sq nwk, Sq nwq, Sq na, Sq nb, int stm) {
                U64 t;
                if (idx.slotOf(nwk, na, nb, nwq, t) < 0) return;
                const U64 st = t * 2 + stm;
                if (cell(st) == VC_UNKNOWN) push(winB, d + 1, st);
            };
            if (s & 1) retractWhite(g, wk, wq, a, bb, [&](Sq f, Sq nq) { mark(f, nq, a, bb, 0); });
            else       retractBlack(g, wk, wq, a, bb, [&](Sq f, Sq oth) { mark(wk, wq, f, oth, 1); });
        }
        // A win at d may complete the case against a predecessor: re-test it.
        for (U64 s : Wd) {
            Sq wk, wq, a, bb; decode(s, wk, wq, a, bb);
            auto test = [&](Sq nwk, Sq nwq, Sq na, Sq nb, int stm) {
                U64 t;
                if (idx.slotOf(nwk, na, nb, nwq, t) < 0) return;
                const U64 st = t * 2 + stm;
                if (cell(st) != VC_UNKNOWN) return;
                Sq cwk, cwq, ca, cb; decode(st, cwk, cwq, ca, cb);
                const int16_t v = stm ? evalBlack(*this, cwk, cwq, ca, cb)
                                      : evalWhite(*this, cwk, cwq, ca, cb);
                if (v != VC_UNKNOWN && v < 0) push(lossB, -v, st);
            };
            if (s & 1) retractWhite(g, wk, wq, a, bb, [&](Sq f, Sq nq) { test(f, nq, a, bb, 0); });
            else       retractBlack(g, wk, wq, a, bb, [&](Sq f, Sq oth) { test(wk, wq, f, oth, 1); });
        }
        if (progress && (!Wd.empty() || !Ld.empty()))
            std::fprintf(stderr, "  ply %3d: %10llu wins, %10llu losses\n", d,
                         (unsigned long long)Wd.size(), (unsigned long long)Ld.size());
    }

    for (U64 i = 0; i < nslots; ++i) {
        if (w[i] == VC_UNKNOWN) w[i] = 0;
        if (b[i] == VC_UNKNOWN) b[i] = 0;
    }
    st.seconds = clock.s();
    if (progress)
        std::fprintf(stderr, "  solved in %.2fs (%llu wins, %llu losses over %d plies)\n",
                     clock.s(), (unsigned long long)wins, (unsigned long long)losses, maxD);
    computeStats(threads);
}

// ---------------------------------------------------------------------------
// Verification.  Every entry of every one of the four tables is recomputed
// from its successors with a move generator written out again here, straight
// down the rules rather than through the solver's open-coded rays and
// retractions, and compared.  Returns the number of mismatches.
// ---------------------------------------------------------------------------
namespace {

int16_t reKK(const TableKQKKCap& T, Sq wk, Sq bk, bool wtm) {
    const Geometry& g = T.geo;
    Acc ac;
    const Sq from = wtm ? wk : bk;
    for (int k = 0; k < 8; ++k) {
        const Sq t = kstep(g, from, k);
        if (t < 0) continue;
        const Sq nw = wtm ? t : wk, nb = wtm ? bk : t;
        if (nw == nb) { ac.winNow(); continue; }        // takes the last king
        ac.add(T.kkValue(nw, nb, !wtm));
    }
    return ac.value();
}
int16_t reKKK(const TableKQKKCap& T, Sq wk, Sq a, Sq b, bool wtm) {
    const Geometry& g = T.geo;
    Acc ac;
    if (wtm) {
        for (int k = 0; k < 8; ++k) {
            const Sq t = kstep(g, wk, k);
            if (t < 0) continue;
            if (t == a)      ac.add(T.kkValue(t, b, false));   // KxK -> K vs K
            else if (t == b) ac.add(T.kkValue(t, a, false));
            else             ac.add(T.k3Value(t, a, b, false));
        }
    } else {
        for (int s = 0; s < 2; ++s) {
            const Sq from = s ? b : a, oth = s ? a : b;
            for (int k = 0; k < 8; ++k) {
                const Sq t = kstep(g, from, k);
                if (t < 0 || t == oth) continue;
                if (t == wk) { ac.winNow(); continue; }
                ac.add(T.k3Value(wk, t, oth, true));
            }
        }
    }
    return ac.value();
}
int16_t reKQK(const TableKQKKCap& T, Sq wk, Sq wq, Sq bk, bool wtm) {
    const Geometry& g = T.geo;
    Acc ac;
    if (wtm) {
        for (int k = 0; k < 8; ++k) {
            const Sq t = kstep(g, wk, k);
            if (t < 0 || t == wq) continue;
            if (t == bk) { ac.winNow(); continue; }            // takes the last king
            ac.add(T.q3Value(t, wq, bk, false));
        }
        for (int d = 0; d < 8; ++d) {
            Sq t = wq;
            for (;;) {
                t = kstep(g, t, d);
                if (t < 0 || t == wk) break;
                if (t == bk) { ac.winNow(); break; }
                ac.add(T.q3Value(wk, t, bk, false));
            }
        }
    } else {
        for (int k = 0; k < 8; ++k) {
            const Sq t = kstep(g, bk, k);
            if (t < 0) continue;
            if (t == wk) { ac.winNow(); continue; }            // ...KxK ends it
            if (t == wq) { ac.add(T.kkValue(wk, t, true)); continue; }
            ac.add(T.q3Value(wk, wq, t, true));
        }
    }
    return ac.value();
}

} // namespace

U64 TableKQKKCap::verify(int threads, bool progress) const {
    const Geometry& g = geo;
    U64 bad = 0, shown = 0;
    auto complain = [&](const char* what, int16_t got, int16_t want) {
        ++bad;
        if (shown++ < 8)
            std::fprintf(stderr, "  %s: stored %d, re-derived %d\n", what, got, want);
    };
    for (U64 i = 0; i < idx3.nkk; ++i) {
        const Sq wk = idx3.kkWk[i], bk = idx3.kkBk[i];
        if (kkW[i] != reKK(*this, wk, bk, true))  complain("K vs K, white to move", kkW[i], reKK(*this, wk, bk, true));
        if (kkB[i] != reKK(*this, wk, bk, false)) complain("K vs K, black to move", kkB[i], reKK(*this, wk, bk, false));
    }
    for (U64 i = 0; i < idx.nblk; ++i) {
        const Sq wk = idx.blkWk[i], a = idx.blkB1[i], b = idx.blkB2[i];
        if (k3W[i] != reKKK(*this, wk, a, b, true))  complain("K vs K+K, white to move", k3W[i], reKKK(*this, wk, a, b, true));
        if (k3B[i] != reKKK(*this, wk, a, b, false)) complain("K vs K+K, black to move", k3B[i], reKKK(*this, wk, a, b, false));
    }
    for (U64 kk = 0; kk < idx3.nkk; ++kk) {
        const Sq wk = idx3.kkWk[kk], bk = idx3.kkBk[kk];
        for (U32 q = 0; q < idx3.npc; ++q) {
            const U64 s = kk * idx3.npc + q;
            if (q3W[s] == VC_DEAD && q3B[s] == VC_DEAD) continue;
            const Sq wq = (Sq)q;
            if (q3W[s] != reKQK(*this, wk, wq, bk, true))  complain("K+Q vs K, white to move", q3W[s], reKQK(*this, wk, wq, bk, true));
            if (q3B[s] != reKQK(*this, wk, wq, bk, false)) complain("K+Q vs K, black to move", q3B[s], reKQK(*this, wk, wq, bk, false));
        }
    }
    for (U64 blk = 0; blk < idx.nblk; ++blk) {
        const Sq wk = idx.blkWk[blk], a = idx.blkB1[blk], bb = idx.blkB2[blk];
        for (U32 q = 0; q < idx.npc; ++q) {
            const U64 s = blk * idx.npc + q;
            if (w[s] == VC_DEAD) continue;
            const Sq wq = (Sq)q;
            const int16_t vw = evalWhite(*this, wk, wq, a, bb);
            const int16_t vb = evalBlack(*this, wk, wq, a, bb);
            if (w[s] != vw) complain("K+Q vs K+K, white to move", w[s], vw);
            if (b[s] != vb) complain("K+Q vs K+K, black to move", b[s], vb);
        }
    }
    (void)threads; (void)g;
    if (progress) std::fprintf(stderr, "  verify: %llu mismatches\n", (unsigned long long)bad);
    return bad;
}

// ---------------------------------------------------------------------------
// Census.
// ---------------------------------------------------------------------------
void TableKQKKCap::computeStats(int threads) {
    (void)threads;
    const Geometry& g = geo;
    const double secs = st.seconds;
    st = KqkkCapStats{};
    st.seconds = secs;
    st.slots = idx.nslots;

    for (U64 i = 0; i < idx3.nkk; ++i) {
        const int orb = NSYM / idx3.kkStabLen[i];
        st.kkLive += orb;
        if (kkW[i] == 0) st.kkDraws += orb;
    }
    for (U64 i = 0; i < idx.nblk; ++i) {
        const int orb = NSYM / idx.blkStabLen[i];
        st.kkkLive += orb;
        if (k3B[i] > 0) st.kkkBlackWins += orb;
        if (k3B[i] > st.kkkDeepest) st.kkkDeepest = k3B[i];
        if (k3W[i] < 0) st.kkkWtmBlackWins += orb;
        else if (k3W[i] == 0) st.kkkWtmDraws += orb;
    }
    for (U64 kk = 0; kk < idx3.nkk; ++kk) {
        const Sq wk = idx3.kkWk[kk], bk = idx3.kkBk[kk];
        for (U32 q = 0; q < idx3.npc; ++q) {
            const U64 s = kk * idx3.npc + q;
            if (q3W[s] == VC_DEAD) continue;
            int fixed = 0;
            for (int sy = 0; sy < NSYM; ++sy)
                if (g.image(sy, wk) == wk && g.image(sy, bk) == bk &&
                    g.image(sy, (Sq)q) == (Sq)q) ++fixed;
            const int orb = fixed ? NSYM / fixed : NSYM;
            st.kqkLive += orb;
            if (q3W[s] > 0) st.kqkWhiteWins += orb;
            if (q3W[s] > st.kqkDeepest) st.kqkDeepest = q3W[s];
            if (q3B[s] < 0)       st.kqkBtmWhiteWins += orb;
            else if (q3B[s] == 0) st.kqkBtmDraws      += orb;
            else                  st.kqkBtmBlackWins  += orb;
        }
    }
    U64 bestW = ~0ull, bestB = ~0ull;
    for (U64 blk = 0; blk < idx.nblk; ++blk) {
        const Sq wk = idx.blkWk[blk], a = idx.blkB1[blk], bb = idx.blkB2[blk];
        for (U32 q = 0; q < idx.npc; ++q) {
            const U64 s = blk * idx.npc + q;
            if (w[s] == VC_DEAD) continue;
            const PosKK p{ wk, (Sq)q, a, bb };
            const U64 orb = (U64)idx.orbitSize(p);
            const int16_t vw = w[s], vb = b[s];
            // Is anything hanging?  A black king attacked by the queen, or one
            // standing beside the white king, means somebody can capture at
            // once and the placement says more about the tempo than about the
            // endgame.
            const bool quiet = !g.attacks(Piece::Queen, (Sq)q, a, wk, bb) &&
                               !g.attacks(Piece::Queen, (Sq)q, bb, wk, a) &&
                               !g.kingsTouch(wk, a) && !g.kingsTouch(wk, bb);
            if (quiet) {
                if (vw > 0) st.qwWin += orb; else if (vw < 0) st.qwLoss += orb; else st.qwDraw += orb;
                if (vb > 0) st.qbWin += orb; else if (vb < 0) st.qbLoss += orb; else st.qbDraw += orb;
            }
            if (vw > 0) { ++st.wWin;  st.fwWin  += orb; } else if (vw < 0) { ++st.wLoss; st.fwLoss += orb; } else { ++st.wDraw; st.fwDraw += orb; }
            if (vb > 0) { ++st.bWin;  st.fbWin  += orb; } else if (vb < 0) { ++st.bLoss; st.fbLoss += orb; } else { ++st.bDraw; st.fbDraw += orb; }
            if (vw > st.maxWhite || (vw == st.maxWhite && s < bestW)) {
                if (vw > 0) { st.maxWhite = vw; st.deepestWhite = p; bestW = s; }
            }
            if (vb > st.maxBlack || (vb == st.maxBlack && s < bestB)) {
                if (vb > 0) { st.maxBlack = vb; st.deepestBlack = p; bestB = s; }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Moves, for probing and for playing a line out.
// ---------------------------------------------------------------------------
void kqkkCapMoves(const TableKQKKCap& t, const PosKK& p, bool whiteToMove,
                  const std::function<void(const PosKK&, CapMove, int16_t)>& fn) {
    const Geometry& g = t.geo;
    if (whiteToMove) {
        for (int k = 0; k < 8; ++k) {
            const Sq to = kstep(g, p.wk, k);
            if (to < 0 || to == p.wq) continue;
            if (to == p.bk1) fn(PosKK{ to, p.wq, -1, p.bk2 }, CapMove::TakesKing,
                                t.q3Value(to, p.wq, p.bk2, false));
            else if (to == p.bk2) fn(PosKK{ to, p.wq, p.bk1, -1 }, CapMove::TakesKing,
                                t.q3Value(to, p.wq, p.bk1, false));
            else fn(PosKK{ to, p.wq, p.bk1, p.bk2 }, CapMove::Quiet,
                    t.valueAt(PosKK{ to, p.wq, p.bk1, p.bk2 }, false));
        }
        for (int d = 0; d < 8; ++d) {
            Sq to = p.wq;
            for (;;) {
                to = kstep(g, to, d);
                if (to < 0 || to == p.wk) break;
                if (to == p.bk1) { fn(PosKK{ p.wk, to, -1, p.bk2 }, CapMove::TakesKing,
                                      t.q3Value(p.wk, to, p.bk2, false)); break; }
                if (to == p.bk2) { fn(PosKK{ p.wk, to, p.bk1, -1 }, CapMove::TakesKing,
                                      t.q3Value(p.wk, to, p.bk1, false)); break; }
                fn(PosKK{ p.wk, to, p.bk1, p.bk2 }, CapMove::Quiet,
                   t.valueAt(PosKK{ p.wk, to, p.bk1, p.bk2 }, false));
            }
        }
        return;
    }
    for (int s = 0; s < 2; ++s) {
        const Sq from = s ? p.bk2 : p.bk1, oth = s ? p.bk1 : p.bk2;
        for (int k = 0; k < 8; ++k) {
            const Sq to = kstep(g, from, k);
            if (to < 0 || to == oth) continue;
            const PosKK q{ p.wk, p.wq, s ? oth : to, s ? to : oth };
            if (to == p.wk) { fn(PosKK{ -1, p.wq, q.bk1, q.bk2 }, CapMove::TakesWhiteKing, -1); continue; }
            if (to == p.wq) { fn(PosKK{ p.wk, -1, q.bk1, q.bk2 }, CapMove::TakesQueen,
                                 t.k3Value(p.wk, q.bk1, q.bk2, true)); continue; }
            fn(q, CapMove::Quiet, t.valueAt(q, true));
        }
    }
}

// ---------------------------------------------------------------------------
// The reference solver: the same four endgames with no symmetry at all, by a
// different algorithm -- sweeping every position ply by ply, rather than
// retracting from a frontier -- and compared placement by placement.  A value
// is taken only on the sweep whose number matches its magnitude: a position
// whose value is computable is not necessarily settled, since a shorter win
// may still be waiting on a successor nobody has resolved yet.  It
// needs n^8 entries, so it is a small-board yardstick; what it checks that a
// self-consistency pass cannot is the index, since it compares every ordered
// placement including the ones the real table reaches only through a symmetry.
// ---------------------------------------------------------------------------
namespace {

struct BruteCap {
    const Geometry& g;
    int nsq;
    std::vector<int16_t> kkW, kkB, k3W, k3B, q3W, q3B, W, B;
    explicit BruteCap(const Geometry& geo) : g(geo), nsq(geo.nsq) {}
    inline int i2(int a, int b) const { return a * nsq + b; }
    inline int i3(int a, int b, int c) const { return (a * nsq + b) * nsq + c; }
    inline U64 i4(int a, int b, int c, int d) const {
        return (((U64)a * nsq + b) * nsq + c) * nsq + d;
    }
    inline Sq st(Sq s, int d) const { return kstep(g, s, d); }

    void solve() {
        // K vs K
        kkW.assign((size_t)nsq * nsq, VC_UNKNOWN);
        kkB.assign((size_t)nsq * nsq, VC_UNKNOWN);
        for (int a = 0; a < nsq; ++a) for (int b = 0; b < nsq; ++b)
            if (a != b && g.kingsTouch(a, b)) { kkW[i2(a,b)] = 1; kkB[i2(a,b)] = 1; }
        for (int d = 2; ; ++d) {
            bool ch = false;
            for (int side = 0; side < 2; ++side) {
                std::vector<int16_t>& me = side ? kkB : kkW;
                const std::vector<int16_t>& op = side ? kkW : kkB;
                for (int a = 0; a < nsq; ++a) for (int b = 0; b < nsq; ++b) {
                    if (a == b || me[i2(a,b)] != VC_UNKNOWN) continue;
                    Acc ac;
                    const Sq from = side ? b : a;
                    for (int k = 0; k < 8; ++k) {
                        const Sq t = st(from, k);
                        if (t < 0) continue;
                        const Sq nw = side ? a : t, nb = side ? t : b;
                        if (nw == nb) continue;              // set at init
                        ac.add(op[i2(nw,nb)]);
                    }
                    const int16_t v = ac.value();
                    if (v != VC_UNKNOWN && (v == d || v == -d)) { me[i2(a,b)] = v; ch = true; }
                }
            }
            if (!ch) break;
        }
        // K vs K + K
        k3W.assign((size_t)nsq*nsq*nsq, VC_UNKNOWN);
        k3B.assign((size_t)nsq*nsq*nsq, VC_UNKNOWN);
        for (int w = 0; w < nsq; ++w) for (int a = 0; a < nsq; ++a) for (int b = 0; b < nsq; ++b)
            if (w != a && w != b && a != b && (g.kingsTouch(w,a) || g.kingsTouch(w,b)))
                k3B[i3(w,a,b)] = 1;
        for (int d = 2; ; ++d) {
            bool ch = false;
            for (int w = 0; w < nsq; ++w) for (int a = 0; a < nsq; ++a) for (int b = 0; b < nsq; ++b) {
                if (w == a || w == b || a == b) continue;
                if (k3W[i3(w,a,b)] == VC_UNKNOWN) {
                    Acc ac;
                    for (int k = 0; k < 8; ++k) {
                        const Sq t = st(w, k);
                        if (t < 0) continue;
                        if (t == a)      ac.add(kkB[i2(t,b)]);
                        else if (t == b) ac.add(kkB[i2(t,a)]);
                        else             ac.add(k3B[i3(t,a,b)]);
                    }
                    const int16_t v = ac.value();
                    if (v != VC_UNKNOWN && (v == d || v == -d)) { k3W[i3(w,a,b)] = v; ch = true; }
                }
                if (k3B[i3(w,a,b)] == VC_UNKNOWN) {
                    Acc ac;
                    for (int s = 0; s < 2; ++s) {
                        const Sq from = s ? b : a, oth = s ? a : b;
                        for (int k = 0; k < 8; ++k) {
                            const Sq t = st(from, k);
                            if (t < 0 || t == oth) continue;
                            if (t == w) continue;            // set at init
                            ac.add(k3W[i3(w,t,oth)]);
                        }
                    }
                    const int16_t v = ac.value();
                    if (v != VC_UNKNOWN && (v == d || v == -d)) { k3B[i3(w,a,b)] = v; ch = true; }
                }
            }
            if (!ch) break;
        }
        // K + Q vs K
        q3W.assign((size_t)nsq*nsq*nsq, VC_UNKNOWN);
        q3B.assign((size_t)nsq*nsq*nsq, VC_UNKNOWN);
        for (int w = 0; w < nsq; ++w) for (int q = 0; q < nsq; ++q) for (int b = 0; b < nsq; ++b) {
            if (w == q || w == b || q == b) continue;
            if (g.kingsTouch(w,b) || g.attacks(Piece::Queen, q, b, w)) q3W[i3(w,q,b)] = 1;
            if (g.kingsTouch(b,w)) q3B[i3(w,q,b)] = 1;
        }
        for (int d = 2; ; ++d) {
            bool ch = false;
            for (int w = 0; w < nsq; ++w) for (int q = 0; q < nsq; ++q) for (int b = 0; b < nsq; ++b) {
                if (w == q || w == b || q == b) continue;
                if (q3W[i3(w,q,b)] == VC_UNKNOWN) {
                    Acc ac;
                    for (int k = 0; k < 8; ++k) {
                        const Sq t = st(w, k);
                        if (t < 0 || t == q || t == b) continue;
                        ac.add(q3B[i3(t,q,b)]);
                    }
                    for (int d = 0; d < 8; ++d) {
                        Sq t = q;
                        for (;;) { t = st(t, d);
                            if (t < 0 || t == w || t == b) break;
                            ac.add(q3B[i3(w,t,b)]); }
                    }
                    const int16_t v = ac.value();
                    if (v != VC_UNKNOWN && (v == d || v == -d)) { q3W[i3(w,q,b)] = v; ch = true; }
                }
                if (q3B[i3(w,q,b)] == VC_UNKNOWN) {
                    Acc ac;
                    for (int k = 0; k < 8; ++k) {
                        const Sq t = st(b, k);
                        if (t < 0 || t == w) continue;       // KxK set at init
                        if (t == q) { ac.add(kkW[i2(w,t)]); continue; }
                        ac.add(q3W[i3(w,q,t)]);
                    }
                    const int16_t v = ac.value();
                    if (v != VC_UNKNOWN && (v == d || v == -d)) { q3B[i3(w,q,b)] = v; ch = true; }
                }
            }
            if (!ch) break;
        }
        // K + Q vs K + K.  This one converts, so a sweep that changes nothing
        // does *not* mean it has converged: a capture can name any depth the
        // sub-tables hold, and the plies in between may be empty.  Sweep to
        // the deepest value any sub-table contains before trusting silence.
        int conv = 0;
        for (const auto* v : { &kkW, &kkB, &k3W, &k3B, &q3W, &q3B })
            for (int16_t x : *v) { const int m = x > 0 ? x : -x;
                                   if (m != VC_UNKNOWN && m != VC_DEAD && m > conv) conv = m; }
        W.assign((size_t)nsq*nsq*nsq*nsq, VC_UNKNOWN);
        B.assign((size_t)nsq*nsq*nsq*nsq, VC_UNKNOWN);
        for (int d = 1; ; ++d) {
            bool ch = false;
            for (int w = 0; w < nsq; ++w) for (int q = 0; q < nsq; ++q)
              for (int a = 0; a < nsq; ++a) for (int b = 0; b < nsq; ++b) {
                if (w==q||w==a||w==b||q==a||q==b||a==b) continue;
                const U64 i = i4(w,q,a,b);
                if (W[i] == VC_UNKNOWN) {
                    Acc ac;
                    for (int k = 0; k < 8; ++k) {
                        const Sq t = st(w, k);
                        if (t < 0 || t == q) continue;
                        if (t == a)      ac.add(q3B[i3(t,q,b)]);
                        else if (t == b) ac.add(q3B[i3(t,q,a)]);
                        else             ac.add(B[i4(t,q,a,b)]);
                    }
                    for (int d = 0; d < 8; ++d) {
                        Sq t = q;
                        for (;;) { t = st(t, d);
                            if (t < 0 || t == w) break;
                            if (t == a) { ac.add(q3B[i3(w,t,b)]); break; }
                            if (t == b) { ac.add(q3B[i3(w,t,a)]); break; }
                            ac.add(B[i4(w,t,a,b)]); }
                    }
                    const int16_t v = ac.value();
                    if (v != VC_UNKNOWN && (v == d || v == -d)) { W[i] = v; ch = true; }
                }
                if (B[i] == VC_UNKNOWN) {
                    Acc ac;
                    for (int s = 0; s < 2; ++s) {
                        const Sq from = s ? b : a, oth = s ? a : b;
                        for (int k = 0; k < 8; ++k) {
                            const Sq t = st(from, k);
                            if (t < 0 || t == oth) continue;
                            if (t == w) { ac.winNow(); continue; }
                            if (t == q) { ac.add(k3W[i3(w,t,oth)]); continue; }
                            ac.add(W[i4(w,q,t,oth)]);
                        }
                    }
                    const int16_t v = ac.value();
                    if (v != VC_UNKNOWN && (v == d || v == -d)) { B[i] = v; ch = true; }
                }
            }
            if (!ch && d > conv + 1) break;
        }
        auto settle = [](std::vector<int16_t>& v){ for (auto& x : v) if (x == VC_UNKNOWN) x = 0; };
        settle(kkW); settle(kkB); settle(k3W); settle(k3B);
        settle(q3W); settle(q3B); settle(W); settle(B);
    }
};

} // namespace

U64 kqkkCapBruteForceCheck(const TableKQKKCap& t, bool progress) {
    BruteCap br(t.geo);
    br.solve();
    const int nsq = t.geo.nsq;
    U64 bad = 0, shown = 0;
    auto cmp = [&](const char* what, int16_t a, int16_t b, const char* pos) {
        if (a == b) return;
        ++bad;
        if (shown++ < 8)
            std::fprintf(stderr, "  brute mismatch %s %s: table %d, brute %d\n", what, pos, a, b);
    };
    char buf[64];
    for (int w = 0; w < nsq; ++w) for (int b = 0; b < nsq; ++b) {
        if (w == b) continue;
        std::snprintf(buf, sizeof buf, "wK %s bK %s", t.geo.name(w).c_str(), t.geo.name(b).c_str());
        cmp("K vs K W", t.kkValue(w, b, true),  br.kkW[br.i2(w,b)], buf);
        cmp("K vs K B", t.kkValue(w, b, false), br.kkB[br.i2(w,b)], buf);
    }
    for (int w = 0; w < nsq; ++w) for (int a = 0; a < nsq; ++a) for (int b = 0; b < nsq; ++b) {
        if (w==a||w==b||a==b) continue;
        std::snprintf(buf, sizeof buf, "wK %s bK %s bK %s", t.geo.name(w).c_str(),
                      t.geo.name(a).c_str(), t.geo.name(b).c_str());
        cmp("K vs K+K W", t.k3Value(w,a,b,true),  br.k3W[br.i3(w,a,b)], buf);
        cmp("K vs K+K B", t.k3Value(w,a,b,false), br.k3B[br.i3(w,a,b)], buf);
    }
    for (int w = 0; w < nsq; ++w) for (int q = 0; q < nsq; ++q) for (int b = 0; b < nsq; ++b) {
        if (w==q||w==b||q==b) continue;
        std::snprintf(buf, sizeof buf, "wK %s wQ %s bK %s", t.geo.name(w).c_str(),
                      t.geo.name(q).c_str(), t.geo.name(b).c_str());
        cmp("K+Q vs K W", t.q3Value(w,q,b,true),  br.q3W[br.i3(w,q,b)], buf);
        cmp("K+Q vs K B", t.q3Value(w,q,b,false), br.q3B[br.i3(w,q,b)], buf);
    }
    for (int w = 0; w < nsq; ++w) for (int q = 0; q < nsq; ++q)
      for (int a = 0; a < nsq; ++a) for (int b = 0; b < nsq; ++b) {
        if (w==q||w==a||w==b||q==a||q==b||a==b) continue;
        const PosKK p{ w, q, a, b };
        std::snprintf(buf, sizeof buf, "wK %s wQ %s bK %s bK %s", t.geo.name(w).c_str(),
                      t.geo.name(q).c_str(), t.geo.name(a).c_str(), t.geo.name(b).c_str());
        cmp("KQKK W", t.valueAt(p, true),  br.W[br.i4(w,q,a,b)], buf);
        cmp("KQKK B", t.valueAt(p, false), br.B[br.i4(w,q,a,b)], buf);
    }
    if (progress)
        std::fprintf(stderr, "  brute force n=%d: %llu mismatches\n", t.n, (unsigned long long)bad);
    return bad;
}

// ---------------------------------------------------------------------------
// On-disk format: a header and the eight arrays, raw.  The census is recomputed
// on load.
// ---------------------------------------------------------------------------
namespace {
constexpr char CAPMAGIC[8] = { 'K','Q','K','K','C','A','P',0 };
struct CapHeader {
    char magic[8];
    U32 version, n, pad0, pad1;
    U64 nkk, nblk, n3, nslots;
};
void putc_(std::FILE* f, const void* p, size_t n) {
    if (std::fwrite(p, 1, n, f) != n) throw std::runtime_error("short write");
}
void getc_(std::FILE* f, void* p, size_t n) {
    if (std::fread(p, 1, n, f) != n) throw std::runtime_error("short read / truncated file");
}
void putVec(std::FILE* f, const std::vector<int16_t>& v) {
    putc_(f, v.data(), v.size() * sizeof(int16_t));
}
void getVec(std::FILE* f, std::vector<int16_t>& v, U64 n) {
    v.assign((size_t)n, 0);
    getc_(f, v.data(), v.size() * sizeof(int16_t));
}
} // namespace

void TableKQKKCap::save(const std::string& path) const {
    std::FILE* f = std::fopen(path.c_str(), "wb");
    if (!f) throw std::runtime_error("cannot open " + path + " for writing");
    try {
        CapHeader h{};
        std::memcpy(h.magic, CAPMAGIC, 8);
        h.version = 1; h.n = (U32)n;
        h.nkk = idx3.nkk; h.nblk = idx.nblk; h.n3 = idx3.nslots; h.nslots = idx.nslots;
        putc_(f, &h, sizeof h);
        putVec(f, kkW); putVec(f, kkB); putVec(f, k3W); putVec(f, k3B);
        putVec(f, q3W); putVec(f, q3B); putVec(f, w);   putVec(f, b);
    } catch (...) { std::fclose(f); throw; }
    std::fclose(f);
}

std::unique_ptr<TableKQKKCap> TableKQKKCap::load(const std::string& path) {
    std::FILE* f = std::fopen(path.c_str(), "rb");
    if (!f) throw std::runtime_error("cannot open " + path);
    std::unique_ptr<TableKQKKCap> t;
    try {
        CapHeader h{};
        getc_(f, &h, sizeof h);
        if (std::memcmp(h.magic, CAPMAGIC, 8) != 0)
            throw std::runtime_error(path + " is not a KQKK capture-rules tablebase");
        if (h.version != 1) throw std::runtime_error("unsupported file version");
        t.reset(new TableKQKKCap((int)h.n));
        if (t->idx.nslots != h.nslots || t->idx3.nkk != h.nkk || t->idx.nblk != h.nblk)
            throw std::runtime_error("file does not match the index it names");
        getVec(f, t->kkW, h.nkk);  getVec(f, t->kkB, h.nkk);
        getVec(f, t->k3W, h.nblk); getVec(f, t->k3B, h.nblk);
        getVec(f, t->q3W, h.n3);   getVec(f, t->q3B, h.n3);
        getVec(f, t->w, h.nslots); getVec(f, t->b, h.nslots);
    } catch (...) { std::fclose(f); throw; }
    std::fclose(f);
    t->computeStats(1);
    return t;
}

} // namespace kqk
