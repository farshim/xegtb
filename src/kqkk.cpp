// kqkk.cpp -- king and queen against TWO black kings.
//
// The variant
// -----------
// Black has two kings instead of one.  They are both royal, they move one at a
// time, and:
//
//   * neither may stand on or beside the white king -- the ordinary rule that
//     kings do not touch, applied to each of them in turn;
//   * they *may* stand beside each other, and beside is all they can do to each
//     other: they are the same colour, so neither attacks the other, and each
//     blocks the queen's rays for the other;
//   * White may never capture, because a king cannot be taken.  The queen's
//     rays stop in front of a black king and she may not land on it.  This is
//     the point of the variant: if White could simply take one king the other
//     would then be an ordinary bare king, and the endgame would be KQK;
//   * Black may take the queen, when she stands beside a black king and the
//     white king does not defend her.  That leaves a lone white king against
//     two black kings, which is a draw -- neither side can even give check --
//     so it is settled before the search starts and never enters the table.
//
// **A mate counts only when both kings are mated at once.**  That is the rule
// the whole table is about, and it is written in one predicate, `restOk`:
//
//   strict (the default)  After Black's move neither king may be left
//     attacked -- the ordinary rule of chess, applied to each king.  Black is
//     checkmated when both kings are attacked and no move of either king
//     escapes; when Black has no move but only one king is attacked, that is
//     stalemate and a draw.  So the position in which one black king is
//     trapped and the other cannot help it is *not* a win: "mate only when
//     both are mated" turns what would be a mate in KQK into a stalemate here.
//
//   loose (--loose)  A black king may stand in check; what Black may not do is
//     leave *both* kings attacked at once.  Same mate and stalemate tests.
//     This is the other reading of "a mate is only counted if both kings are
//     mated" -- that a single check is simply not binding -- and it is one
//     predicate away, so the program computes either.
//
// Since a black king is never beside the white king, the white king attacks
// nothing in any legal position: check always means the queen bears on the
// square, and mate always means she bears on both kings at once, along two
// different rays, with neither king blocking the ray to the other.
//
// What carries over from the rest of the program
// ----------------------------------------------
// All four structural facts that solver.cpp rests on survive, which is why
// this endgame gets the same cheap two-phase induction and the same one-byte
// entries rather than the signed, converting machinery KQKR needs:
//
//   * **Black can never give check.**  A black king may not stand beside the
//     white king, so White is never in check, can never be mated, and every
//     white-to-move entry is a win or a draw.
//   * **White can never capture**, so no position in the table has a
//     predecessor outside it and the unmove generator needs no un-captures.
//   * **A legal capture is an immediate, permanent draw** (K vs KK).
//   * **King and queen both move symmetrically**, so the unmove generator is
//     the move generator run from the destination square.
//
// What does not carry over is the index; see indexkk.hpp.  The block key is
// the king *triple* and the configuration is the queen square alone, because
// Black's second man is a king: interchangeable with the first, and moving on
// Black's turn rather than White's.
//
// As in solver.cpp there is no successor counter -- on a symmetry-reduced
// index an edge between orbits of different size is seen a different number of
// times from its two ends -- so phase B re-tests each candidate by forward
// move generation.  Black has at most sixteen moves here rather than eight,
// which is the only price the second king charges.
#include "table.hpp"

#include <atomic>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <random>
#include <stdexcept>
#include <thread>

namespace kqk {
namespace {

inline U8 aload(const U8* a, U64 i) {
    return std::atomic_ref<U8>(const_cast<U8&>(a[i])).load(std::memory_order_relaxed);
}
inline void astore(U8* a, U64 i, U8 v) {
    std::atomic_ref<U8>(a[i]).store(v, std::memory_order_relaxed);
}
// Claim an unresolved entry, so that two threads reaching it in the same sweep
// -- one retracting a queen move inside the block, one a king move from a
// neighbouring block -- do not both count the same fill.
inline bool aclaim(U8* a, U64 i, U8 v) {
    U8 expect = V_UNKNOWN;
    return std::atomic_ref<U8>(a[i]).compare_exchange_strong(
        expect, v, std::memory_order_relaxed, std::memory_order_relaxed);
}

struct Timer {
    std::chrono::steady_clock::time_point t0 = std::chrono::steady_clock::now();
    double s() const {
        return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    }
};

// ---------------------------------------------------------------------------
// The rules.
// ---------------------------------------------------------------------------

// Is `t` attacked by White?  Only the queen can attack: a black king never
// stands beside the white king, so in a legal position he attacks nothing.
// Her rays are blocked by the white king and by both black kings; `other` is
// whichever black king is not the one being asked about.  A man standing
// exactly on `t` never blocks the ray to `t`, so it does not matter whether a
// moving king's origin is passed as a blocker or not.
inline bool hit(const Geometry& g, Sq wq, Sq t, Sq wk, Sq other) {
    return g.attacks(Piece::Queen, wq, t, wk, other);
}

// May Black leave the two kings standing like this?  The whole of the variant
// in one predicate, and the only place the two rule sets differ.
template <bool STRICT>
inline bool restOk(const Geometry& g, Sq wk, Sq wq, Sq a, Sq b) {
    if constexpr (STRICT) return !hit(g, wq, a, wk, b) && !hit(g, wq, b, wk, a);
    else                  return !hit(g, wq, a, wk, b) || !hit(g, wq, b, wk, a);
}

// Both kings attacked at once -- the shape of a mate, once Black is also shown
// to have no move at all.
inline bool bothInCheck(const Geometry& g, Sq wk, Sq wq, Sq a, Sq b) {
    return hit(g, wq, a, wk, b) && hit(g, wq, b, wk, a);
}

// Is the placement legal with the given side to move?  Four men on four
// distinct squares, neither black king beside the white king, and -- when it is
// White's turn -- Black must not have just left a king it was not allowed to.
template <bool STRICT>
inline bool legalPosKK(const Geometry& g, const PosKK& p, bool wtm) {
    if (p.bk1 == p.bk2) return false;
    if (p.wq == p.wk || p.wq == p.bk1 || p.wq == p.bk2) return false;
    if (g.kingsTouch(p.wk, p.bk1) || g.kingsTouch(p.wk, p.bk2)) return false;
    if (wtm && !restOk<STRICT>(g, p.wk, p.wq, p.bk1, p.bk2)) return false;
    return true;
}

// Every legal black move.  fn(moved, other, capture) gets the two black king
// squares after the move -- `moved` is the king that just moved -- and whether
// it took the queen.  A capture is legal exactly when the white king does not
// defend her, which the kingsTouch test has already decided: if he does defend
// her, the square is barred to a black king like any other square beside him.
template <bool STRICT, class F>
inline void genBlack(const Geometry& g, const PosKK& p, F&& fn) {
    for (int which = 0; which < 2; ++which) {
        const Sq from  = which ? p.bk2 : p.bk1;
        const Sq other = which ? p.bk1 : p.bk2;
        const int f0 = g.file(from), r0 = g.rank(from);
        for (int d = 0; d < 8; ++d) {
            const int f = f0 + KF[d], r = r0 + KR[d];
            if (!g.onBoard(f, r)) continue;
            const Sq t = g.sq(f, r);
            if (t == other) continue;                  // its fellow king stands there
            if (g.kingsTouch(t, p.wk)) continue;       // includes t == p.wk
            if (t == p.wq) { fn(t, other, true); continue; }        // ...KxQ
            if (!restOk<STRICT>(g, p.wk, p.wq, t, other)) continue;
            fn(t, other, false);
        }
    }
}

// Every legal white move.  White is never in check, so no move of his can
// expose anything and there is nothing further to test; and White can never
// capture, kings not being takeable.
template <class F>
inline void genWhiteKK(const Geometry& g, const PosKK& p, F&& fn) {
    const int f0 = g.file(p.wk), r0 = g.rank(p.wk);
    for (int d = 0; d < 8; ++d) {
        const int f = f0 + KF[d], r = r0 + KR[d];
        if (!g.onBoard(f, r)) continue;
        const Sq t = g.sq(f, r);
        if (t == p.wq) continue;                                     // his own queen
        if (g.kingsTouch(t, p.bk1) || g.kingsTouch(t, p.bk2)) continue;
        fn(PosKK{ t, p.wq, p.bk1, p.bk2 });
    }
    forEachMove<Piece::Queen>(g, p.wq, p.wk, p.bk1, p.bk2, [&](Sq t) {
        fn(PosKK{ p.wk, t, p.bk1, p.bk2 });
        return true;
    });
}

// ---------------------------------------------------------------------------
// Retrograde analysis.  Phase A retracts a white move out of a black-to-move
// loss; phase B retracts a black move out of a white-to-move win and re-tests
// the candidate forwards.
// ---------------------------------------------------------------------------
template <bool STRICT>
void generateImpl(TableKQKK& T, int threads, bool progress) {
    const Geometry&   g   = T.geo;
    const IndexKQKK&  idx = T.idx;
    const U32  npc  = idx.npc;
    const U64  nblk = idx.nblk;
    std::vector<U8>& w = T.w;
    std::vector<U8>& b = T.b;
    Timer clock;

    w.assign(idx.nslots, V_DEAD);
    b.assign(idx.nslots, V_DEAD);

    // Dirty-block maps.  A block is one king triple, i.e. npc consecutive
    // entries.  Only blocks that received a value at the previous ply are
    // rescanned, which keeps the long sparse tail of deep plies nearly free.
    std::vector<U8> dirtyB(nblk, 0), dirtyBn(nblk, 0), dirtyW(nblk, 0);
    std::vector<std::vector<U32>> scratch(std::max(1, threads));

    // ---- initialisation ---------------------------------------------------
    // Marks dead slots, finds the mates and the stalemates, and settles every
    // position in which Black can simply take the queen.
    std::atomic<U64> mates{0}, stalemates{0};
    parallelFor(nblk, 64, threads, [&](U64 lo, U64 hi, int) {
        U64 localMates = 0, localStale = 0;
        for (U64 blk = lo; blk < hi; ++blk) {
            const Sq wk = idx.blkWk[blk], b1 = idx.blkB1[blk], b2 = idx.blkB2[blk];
            const U64 base = blk * npc;
            bool blockHasMate = false;
            for (U32 qi = 0; qi < npc; ++qi) {
                const Sq wq = (Sq)qi;
                if (wq == wk || wq == b1 || wq == b2) continue;      // stays V_DEAD
                if (!idx.queenIsCanonical(blk, wq)) continue;        // a duplicate slot
                const PosKK p{ wk, wq, b1, b2 };
                const bool xa = hit(g, wq, b1, wk, b2);
                const bool xb = hit(g, wq, b2, wk, b1);
                // White to move: Black must not have left a king it may not.
                const bool wtmLegal = STRICT ? (!xa && !xb) : !(xa && xb);
                w[base + qi] = wtmLegal ? V_UNKNOWN : V_DEAD;

                int nmoves = 0;
                bool grabsQueen = false;
                genBlack<STRICT>(g, p, [&](Sq, Sq, bool cap) {
                    ++nmoves;
                    if (cap) grabsQueen = true;
                });
                if (grabsQueen)   b[base + qi] = V_DRAW;      // ...KxQ leaves K vs KK
                else if (nmoves)  b[base + qi] = V_UNKNOWN;
                else if (xa && xb) {                          // both mated at once
                    b[base + qi] = 0; ++localMates; blockHasMate = true;
                } else {                                      // at most one mated
                    b[base + qi] = V_DRAW; ++localStale;
                }
            }
            if (blockHasMate) dirtyB[blk] = 1;
        }
        mates.fetch_add(localMates, std::memory_order_relaxed);
        stalemates.fetch_add(localStale, std::memory_order_relaxed);
    });

    if (progress)
        std::fprintf(stderr, "  init: %llu king triples, %llu mates, %llu stalemates, %.2fs\n",
                     (unsigned long long)nblk, (unsigned long long)mates.load(),
                     (unsigned long long)stalemates.load(), clock.s());

    // ---- backward induction -----------------------------------------------
    double tA = 0, tB = 0;
    U32 d = 0;
    for (;;) {
        if (d + 2 > MAX_PLY) {
            std::fprintf(stderr,
                         "error: depth to mate exceeds %d plies on a %dx%d board; "
                         "widen the entry type and rebuild\n", (int)MAX_PLY, T.n, T.n);
            std::exit(2);
        }

        // ---- phase A: losses at ply d make their predecessors wins at d+1 --
        std::fill(dirtyW.begin(), dirtyW.end(), 0);
        const double tp0 = clock.s();
        std::atomic<U64> madeW{0};
        parallelFor(nblk, 32, threads, [&](U64 lo, U64 hi, int) {
            U64 local = 0;
            for (U64 blk = lo; blk < hi; ++blk) {
                if (!dirtyB[blk]) continue;
                const Sq  wk = idx.blkWk[blk], b1 = idx.blkB1[blk], b2 = idx.blkB2[blk];
                const U8* stab = &idx.blkStab[blk * NSYM];
                const int slen = idx.blkStabLen[blk];
                const U64 base = blk * npc;
                U8* const       wb = w.data() + base;
                const U8* const bb = b.data() + base;
                const U8  dv  = (U8)(d + 1);
                const int wkf = g.file(wk), wkr = g.rank(wk);
                bool touched = false;
                for (U32 qi = 0; qi < npc; ++qi) {
                    if (aload(bb, qi) != (U8)d) continue;
                    const Sq wq = (Sq)qi;

                    // Undo a queen move.  She moves symmetrically, so the
                    // squares she could have come from are exactly the squares
                    // she can move to -- the same forEachMove the forward
                    // generator uses, so the two cannot drift apart.  The kings
                    // do not move, so every such predecessor stays in this
                    // block: one contiguous run of memory.
                    forEachMove<Piece::Queen>(g, wq, wk, b1, b2, [&](Sq from) {
                        const U32 c = (slen == 1) ? (U32)from
                                                  : (U32)idx.canonSquare(stab, slen, from);
                        if (aload(wb, c) == V_UNKNOWN && aclaim(wb, c, dv)) {
                            ++local; touched = true;
                        }
                        return true;
                    });

                    // Undo a white king move.  This one does leave the block:
                    // the king is part of the block key.
                    for (int s = 0; s < 8; ++s) {
                        const int f = wkf + KF[s], r = wkr + KR[s];
                        if (!g.onBoard(f, r)) continue;
                        const Sq from = g.sq(f, r);
                        if (from == wq || from == b1 || from == b2) continue;
                        U64 t;
                        const int32_t tblk = idx.slotOf(from, b1, b2, wq, t);
                        if (tblk < 0) continue;        // he cannot have stood there
                        if (aload(w.data(), t) == V_UNKNOWN && aclaim(w.data(), t, dv)) {
                            ++local;
                            astore(dirtyW.data(), (U64)tblk, 1);
                        }
                    }
                }
                if (touched) astore(dirtyW.data(), blk, 1);
            }
            madeW.fetch_add(local, std::memory_order_relaxed);
        });
        tA += clock.s() - tp0;
        if (madeW.load() == 0) break;
        T.st.maxPly = d + 1;

        // ---- phase B: a black-to-move position is lost once every move it
        //      has leads to a white win --------------------------------------
        std::fill(dirtyBn.begin(), dirtyBn.end(), 0);
        const double tp1 = clock.s();
        std::atomic<U64> madeB{0};
        parallelFor(nblk, 32, threads, [&](U64 lo, U64 hi, int tid) {
            U64 local = 0;
            std::vector<U32>& hits = scratch[tid];
            for (U64 blk = lo; blk < hi; ++blk) {
                if (!dirtyW[blk]) continue;
                const Sq wk = idx.blkWk[blk], b1 = idx.blkB1[blk], b2 = idx.blkB2[blk];
                const auto& stabWk = g.triStab[g.triId[wk]];
                const U8* const sw = stabWk.data();
                const int lw = (int)stabWk.size();
                const int32_t* const row = idx.blockRowFor(wk);
                const U8* const wb = w.data() + blk * npc;
                const U8 dv = (U8)(d + 1);

                // The queen squares that were just won.  Sweeping the black
                // king's origin outside and the queen square inside turns the
                // successor lookups into a handful of monotonically advancing
                // streams instead of scattered probes.
                hits.clear();
                for (U32 qi = 0; qi < npc; ++qi)
                    if (aload(wb, qi) == dv) hits.push_back(qi);
                if (hits.empty()) continue;

                for (int which = 0; which < 2; ++which) {
                    const Sq mover = which ? b2 : b1;
                    const Sq other = which ? b1 : b2;
                    const int mf = g.file(mover), mr = g.rank(mover);
                    for (int s = 0; s < 8; ++s) {
                        const int pf = mf + KF[s], pr = mr + KR[s];
                        if (!g.onBoard(pf, pr)) continue;
                        const Sq from = g.sq(pf, pr);      // where that king stood
                        if (from == other) continue;
                        if (g.kingsTouch(from, wk)) continue;   // predecessor illegal

                        // The predecessor's block, and the blocks its own
                        // successors live in, depend only on the kings, not on
                        // the queen -- so resolve them once for the whole sweep
                        // over queen squares.
                        const Sq kings[2] = { from, other };
                        struct Step { Sq to, stay; const U8* base; };
                        Step step[16];
                        int nstep = 0;
                        const bool slow = (lw > 1);
                        int32_t rblk  = -1;
                        U64     rbase = 0;
                        if (!slow) {
                            rblk = row[idx.pairId(from, other)];
                            if (rblk < 0) continue;
                            rbase = (U64)rblk * npc;
                            for (int wi = 0; wi < 2; ++wi) {
                                const Sq mv = kings[wi], st = kings[1 - wi];
                                const int f0 = g.file(mv), r0 = g.rank(mv);
                                for (int t = 0; t < 8; ++t) {
                                    const int tf = f0 + KF[t], tr = r0 + KR[t];
                                    if (!g.onBoard(tf, tr)) continue;
                                    const Sq to = g.sq(tf, tr);
                                    if (to == st) continue;
                                    if (g.kingsTouch(to, wk)) continue;
                                    const int32_t cb = row[idx.pairId(to, st)];
                                    if (cb < 0) continue;
                                    step[nstep++] = { to, st, w.data() + (U64)cb * npc };
                                }
                            }
                        }

                        for (U32 qi : hits) {
                            const Sq wq = (Sq)qi;
                            if (from == wq) continue;    // the queen stands there
                            U64 rslot;
                            if (slow) {
                                const int32_t rk =
                                    idx.slotSameWk(row, sw, lw, from, other, wq, rslot);
                                if (rk < 0) continue;
                                rblk = rk;
                            } else {
                                rslot = rbase + qi;
                            }
                            if (aload(b.data(), rslot) != V_UNKNOWN) continue;

                            bool allWin = true;
                            U8   worst  = 0;
                            int  moves  = 0;
                            if (slow) {
                                const PosKK pp{ wk, wq, from, other };
                                genBlack<STRICT>(g, pp, [&](Sq to, Sq stay, bool cap) {
                                    if (!allWin) return;
                                    if (cap) { allWin = false; return; }
                                    ++moves;
                                    U64 c;
                                    if (idx.slotSameWk(row, sw, lw, to, stay, wq, c) < 0) {
                                        allWin = false; return;
                                    }
                                    const U8 v = aload(w.data(), c);
                                    if (!isDtm(v)) { allWin = false; return; }
                                    if (v > worst) worst = v;
                                });
                            } else {
                                for (int i = 0; i < nstep; ++i) {
                                    const Sq to = step[i].to, stay = step[i].stay;
                                    if (to == wq) { allWin = false; break; }  // ...KxQ
                                    if (!restOk<STRICT>(g, wk, wq, to, stay)) continue;
                                    ++moves;
                                    const U8 v = aload(step[i].base, qi);
                                    if (!isDtm(v)) { allWin = false; break; }
                                    if (v > worst) worst = v;
                                }
                            }
                            if (!allWin || !moves) continue;
                            astore(b.data(), rslot, (U8)(worst + 1));
                            ++local;
                            astore(dirtyBn.data(), (U64)rblk, 1);
                        }
                    }
                }
            }
            madeB.fetch_add(local, std::memory_order_relaxed);
        });
        tB += clock.s() - tp1;

        if (progress)
            std::fprintf(stderr, "  ply %3u: %12llu wins   ply %3u: %12llu losses  (%.2fs)\n",
                         d + 1, (unsigned long long)madeW.load(),
                         d + 2, (unsigned long long)madeB.load(), clock.s());

        if (madeB.load() == 0) break;
        dirtyB.swap(dirtyBn);
        d += 2;
    }

    // Everything still unresolved is drawn.
    parallelFor(idx.nslots, 1u << 16, threads, [&](U64 lo, U64 hi, int) {
        for (U64 i = lo; i < hi; ++i) {
            if (w[i] == V_UNKNOWN) w[i] = V_DRAW;
            if (b[i] == V_UNKNOWN) b[i] = V_DRAW;
        }
    });

    T.st.seconds = clock.s();
    if (progress)
        std::fprintf(stderr, "  solved in %.2fs  (phase A %.2fs, phase B %.2fs)\n",
                     clock.s(), tA, tB);
}

} // namespace

void TableKQKK::generate(int threads, bool progress) {
    if (rules == KkRules::Strict) generateImpl<true>(*this, threads, progress);
    else                          generateImpl<false>(*this, threads, progress);
    computeStats(threads);
}

// ---------------------------------------------------------------------------
// Probing.
// ---------------------------------------------------------------------------
U8 TableKQKK::valueAt(const PosKK& p, bool whiteToMove) const {
    if (p.wk < 0 || p.wq < 0 || p.bk1 < 0 || p.bk2 < 0) return V_DEAD;
    if (p.bk1 == p.bk2) return V_DEAD;
    if (p.wq == p.wk || p.wq == p.bk1 || p.wq == p.bk2) return V_DEAD;
    U64 s;
    if (idx.slotOf(p, s) < 0) return V_DEAD;
    return whiteToMove ? w[s] : b[s];
}

bool TableKQKK::legal(const PosKK& p, bool whiteToMove) const {
    return rules == KkRules::Strict ? legalPosKK<true>(geo, p, whiteToMove)
                                    : legalPosKK<false>(geo, p, whiteToMove);
}

bool TableKQKK::inCheck(const PosKK& p, int which) const {
    return which == 0 ? hit(geo, p.wq, p.bk1, p.wk, p.bk2)
                      : hit(geo, p.wq, p.bk2, p.wk, p.bk1);
}

ProbeResult TableKQKK::probe(const PosKK& p, bool whiteToMove) const {
    ProbeResult r;
    const U8 v = valueAt(p, whiteToMove);
    if (v == V_DEAD)   { r.outcome = Outcome::Illegal; return r; }
    if (v == V_DRAW)   { r.outcome = Outcome::Draw;    return r; }
    r.outcome = whiteToMove ? Outcome::Win : Outcome::Loss;
    r.plies = v;
    r.moves = (v + 1) / 2;
    return r;
}

void kqkkMoves(const TableKQKK& t, const PosKK& p, bool whiteToMove,
               const std::function<void(const PosKK&, bool, U8)>& fn) {
    if (whiteToMove) {
        genWhiteKK(t.geo, p, [&](const PosKK& q) { fn(q, false, t.valueAt(q, false)); });
        return;
    }
    auto walk = [&](auto tag) {
        constexpr bool S = decltype(tag)::value;
        genBlack<S>(t.geo, p, [&](Sq to, Sq stay, bool cap) {
            const PosKK q{ p.wk, cap ? Sq(-1) : p.wq, to, stay };
            fn(q, cap, cap ? (U8)V_DRAW : t.valueAt(q, true));
        });
    };
    if (t.rules == KkRules::Strict) walk(std::true_type{});
    else                            walk(std::false_type{});
}

bool TableKQKK::bestMove(const PosKK& p, bool whiteToMove, PosKK& out, bool& capture) const {
    bool got = false;
    long bestKey = 0;
    kqkkMoves(*this, p, whiteToMove, [&](const PosKK& q, bool cap, U8 v) {
        // Winner: the shortest win it has.  Loser: the longest defence, and a
        // draw ahead of any of them.
        long tier, sub;
        if (whiteToMove) { tier = isDtm(v) ? 0 : 1; sub = isDtm(v) ? v : 0; }
        else             { tier = isDtm(v) ? 1 : 0; sub = isDtm(v) ? (long)(250 - v) : 0; }
        const long key = tier * 1000 + sub;
        if (!got || key < bestKey) { got = true; bestKey = key; out = q; capture = cap; }
    });
    return got;
}

std::vector<PosKK> TableKQKK::principalVariation(const PosKK& p, bool whiteToMove) const {
    std::vector<PosKK> line;
    PosKK cur = p;
    bool wtm = whiteToMove;
    for (int ply = 0; ply < 2 * MAX_PLY + 4; ++ply) {
        const U8 v = valueAt(cur, wtm);
        if (!isDtm(v) || v == 0) break;
        PosKK nxt{};
        bool cap = false;
        if (!bestMove(cur, wtm, nxt, cap) || cap) break;
        line.push_back(nxt);
        cur = nxt;
        wtm = !wtm;
    }
    return line;
}

// ---------------------------------------------------------------------------
// Verification: every entry re-derived from its successors with the forward
// move generator and the full canonicalisation, which is the path the solver's
// fast in-block forms are supposed to agree with.  Returns the number of
// mismatches; zero means the table satisfies the Bellman equations everywhere.
// ---------------------------------------------------------------------------
template <bool STRICT>
static U64 verifyImpl(const TableKQKK& T, int threads, bool progress) {
    const Geometry& g = T.geo;
    const IndexKQKK& idx = T.idx;
    const U32 npc = idx.npc;
    std::atomic<U64> bad{0};
    std::atomic<U64> reported{0};

    parallelFor(idx.nblk, 32, threads, [&](U64 lo, U64 hi, int) {
        U64 local = 0;
        for (U64 blk = lo; blk < hi; ++blk) {
            const Sq wk = idx.blkWk[blk], b1 = idx.blkB1[blk], b2 = idx.blkB2[blk];
            for (U32 qi = 0; qi < npc; ++qi) {
                const U64 slot = blk * npc + qi;
                const Sq wq = (Sq)qi;
                const bool dead = (wq == wk || wq == b1 || wq == b2) ||
                                  !idx.queenIsCanonical(blk, wq);
                const PosKK p{ wk, wq, b1, b2 };
                auto complain = [&](const char* side, int want, int got) {
                    if (reported.fetch_add(1, std::memory_order_relaxed) < 12)
                        std::fprintf(stderr,
                                     "  mismatch %s  wK %s wQ %s bK %s bK %s: want %d, got %d\n",
                                     side, g.name(wk).c_str(), g.name(wq).c_str(),
                                     g.name(b1).c_str(), g.name(b2).c_str(), want, got);
                    ++local;
                };
                if (dead) {
                    if (T.w[slot] != V_DEAD) complain("W(dead)", V_DEAD, T.w[slot]);
                    if (T.b[slot] != V_DEAD) complain("b(dead)", V_DEAD, T.b[slot]);
                    continue;
                }

                // White to move.
                {
                    U8 want;
                    if (!legalPosKK<STRICT>(g, p, true)) want = V_DEAD;
                    else {
                        int best = -1;
                        genWhiteKK(g, p, [&](const PosKK& q) {
                            const U8 v = T.valueAt(q, false);
                            if (isDtm(v) && (best < 0 || v < best)) best = v;
                        });
                        want = best < 0 ? (U8)V_DRAW : (U8)(best + 1);
                    }
                    if (T.w[slot] != want) complain("W", want, T.w[slot]);
                }
                // Black to move.  Every black-to-move placement is legal: Black
                // cannot have been left in a check it was not allowed to leave,
                // since it is White who has just moved.
                {
                    bool allWin = true, anyCap = false;
                    int worst = -1, moves = 0;
                    genBlack<STRICT>(g, p, [&](Sq to, Sq stay, bool cap) {
                        ++moves;
                        if (cap) { anyCap = true; allWin = false; return; }
                        const PosKK q{ wk, wq, to, stay };
                        const U8 v = T.valueAt(q, true);
                        if (!isDtm(v)) { allWin = false; return; }
                        if ((int)v > worst) worst = v;
                    });
                    (void)anyCap;
                    U8 want;
                    if (moves == 0)      want = bothInCheck(g, wk, wq, b1, b2) ? (U8)0 : (U8)V_DRAW;
                    else if (!allWin)    want = V_DRAW;
                    else                 want = (U8)(worst + 1);
                    if (T.b[slot] != want) complain("b", want, T.b[slot]);
                }
            }
        }
        bad.fetch_add(local, std::memory_order_relaxed);
    });
    if (progress)
        std::fprintf(stderr, "  verify: %llu mismatches\n", (unsigned long long)bad.load());
    return bad.load();
}

U64 TableKQKK::verify(int threads, bool progress) const {
    return rules == KkRules::Strict ? verifyImpl<true>(*this, threads, progress)
                                    : verifyImpl<false>(*this, threads, progress);
}

// ---------------------------------------------------------------------------
// Census.  Counts are taken twice: once over canonical slots, one per symmetry
// class, and once weighted by orbit size, which is the whole-board figure.
// ---------------------------------------------------------------------------
template <bool STRICT>
static void statsImpl(TableKQKK& T, int threads) {
    const Geometry& g = T.geo;
    const IndexKQKK& idx = T.idx;
    const U32 npc = idx.npc;
    const int nthreads = std::max(1, threads);

    struct Acc {
        KqkkStats s;
        U64 bestSlot = ~0ull;
        int bestPly = -1;
        PosKK best{};
    };
    std::vector<Acc> acc(nthreads);
    for (auto& a : acc) { a.s.histW.assign(MAX_PLY + 2, 0); a.s.histWFull.assign(MAX_PLY + 2, 0); }

    parallelFor(idx.nblk, 32, nthreads, [&](U64 lo, U64 hi, int tid) {
        Acc& a = acc[tid];
        for (U64 blk = lo; blk < hi; ++blk) {
            const Sq wk = idx.blkWk[blk], b1 = idx.blkB1[blk], b2 = idx.blkB2[blk];
            for (U32 qi = 0; qi < npc; ++qi) {
                const U64 slot = blk * npc + qi;
                const U8 vw = T.w[slot], vb = T.b[slot];
                if (vw == V_DEAD && vb == V_DEAD) continue;
                const Sq wq = (Sq)qi;
                const PosKK p{ wk, wq, b1, b2 };
                const U64 orb = (U64)idx.orbitSize(p);

                if (vw != V_DEAD) {
                    ++a.s.wLive; a.s.fwLive += orb;
                    if (isDtm(vw)) {
                        ++a.s.wWin; a.s.fwWin += orb;
                        ++a.s.histW[vw]; a.s.histWFull[vw] += orb;
                        if ((int)vw > a.bestPly || ((int)vw == a.bestPly && slot < a.bestSlot)) {
                            a.bestPly = vw; a.bestSlot = slot; a.best = p;
                        }
                    } else { ++a.s.wDraw; a.s.fwDraw += orb; }
                }
                if (vb != V_DEAD) {
                    ++a.s.bLive; a.s.fbLive += orb;
                    if (isDtm(vb)) {
                        ++a.s.bLoss; a.s.fbLoss += orb;
                        if (vb == 0) { ++a.s.bMate; a.s.fbMate += orb; }
                    } else {
                        ++a.s.bDraw; a.s.fbDraw += orb;
                        int moves = 0; bool cap = false;
                        genBlack<STRICT>(g, p, [&](Sq, Sq, bool c) { ++moves; if (c) cap = true; });
                        if (moves == 0) {
                            ++a.s.bStale; a.s.fbStale += orb;
                            // Exactly one king attacked: in ordinary chess this
                            // would be mate.  Here it is a draw, and counting
                            // these is counting what the rule costs White.
                            const bool x1 = hit(g, wq, b1, wk, b2);
                            const bool x2 = hit(g, wq, b2, wk, b1);
                            if (x1 != x2) { ++a.s.bStale1; a.s.fbStale1 += orb; }
                        }
                        else if (cap)    { ++a.s.bEnPrise; a.s.fbEnPrise += orb; }
                    }
                }
            }
        }
    });

    KqkkStats& s = T.st;
    const double secs = s.seconds;
    const U32 maxPly = s.maxPly;
    s = KqkkStats{};
    s.seconds = secs;
    s.maxPly = maxPly;
    s.slots = idx.nslots;
    s.histW.assign(MAX_PLY + 2, 0);
    s.histWFull.assign(MAX_PLY + 2, 0);
    int bestPly = -1; U64 bestSlot = ~0ull;
    for (const Acc& a : acc) {
        s.wLive += a.s.wLive; s.wWin += a.s.wWin; s.wDraw += a.s.wDraw;
        s.bLive += a.s.bLive; s.bLoss += a.s.bLoss; s.bDraw += a.s.bDraw;
        s.bMate += a.s.bMate; s.bStale += a.s.bStale; s.bEnPrise += a.s.bEnPrise;
        s.bStale1 += a.s.bStale1; s.fbStale1 += a.s.fbStale1;
        s.fwLive += a.s.fwLive; s.fwWin += a.s.fwWin; s.fwDraw += a.s.fwDraw;
        s.fbLive += a.s.fbLive; s.fbLoss += a.s.fbLoss; s.fbDraw += a.s.fbDraw;
        s.fbMate += a.s.fbMate; s.fbStale += a.s.fbStale; s.fbEnPrise += a.s.fbEnPrise;
        for (size_t i = 0; i < s.histW.size(); ++i) {
            s.histW[i] += a.s.histW[i];
            s.histWFull[i] += a.s.histWFull[i];
        }
        if (a.bestPly > bestPly || (a.bestPly == bestPly && a.bestSlot < bestSlot)) {
            bestPly = a.bestPly; bestSlot = a.bestSlot; s.longest = a.best;
        }
    }
    s.maxPly = bestPly > 0 ? (U32)bestPly : 0;
    s.longestSlot = bestSlot;
}

void TableKQKK::computeStats(int threads) {
    if (rules == KkRules::Strict) statsImpl<true>(*this, threads);
    else                          statsImpl<false>(*this, threads);
}

// ---------------------------------------------------------------------------
// The reference solver: the same endgame with no symmetry reduction, one byte
// per *ordered* placement, single threaded, and by a different algorithm --
// full forward sweeps by ply, with no retraction and no dirty blocks.  It
// needs n^8 bytes per side, so it is a small-board yardstick; what it checks
// is not only the values but the index, since it compares every ordered
// placement including the ones the real table reaches only through a symmetry.
// ---------------------------------------------------------------------------
namespace {

struct Brute {
    const Geometry& g;
    KkRules rules;
    U64 nsq, s1, s2, s3;
    std::vector<U8> w, b;

    Brute(const Geometry& geo, KkRules r) : g(geo), rules(r) {
        nsq = (U64)g.nsq;
        s3 = 1; s2 = nsq; s1 = nsq * nsq;
        w.assign(nsq * nsq * nsq * nsq, V_DEAD);
        b.assign(w.size(), V_DEAD);
    }
    inline U64 index(Sq wk, Sq wq, Sq k1, Sq k2) const {
        return ((U64)wk * nsq + (U64)wq) * nsq * nsq + (U64)k1 * nsq + (U64)k2;
    }
    inline U8 at(const PosKK& p, bool wtm) const {
        return (wtm ? w : b)[index(p.wk, p.wq, p.bk1, p.bk2)];
    }

    template <bool STRICT>
    void solve() {
        const int n = g.nsq;
        for (Sq wk = 0; wk < n; ++wk)
            for (Sq wq = 0; wq < n; ++wq)
                for (Sq k1 = 0; k1 < n; ++k1)
                    for (Sq k2 = 0; k2 < n; ++k2) {
                        const PosKK p{ wk, wq, k1, k2 };
                        if (!legalPosKK<STRICT>(g, p, false)) continue;   // both stay dead
                        const U64 i = index(wk, wq, k1, k2);
                        w[i] = legalPosKK<STRICT>(g, p, true) ? V_UNKNOWN : V_DEAD;
                        int moves = 0; bool cap = false;
                        genBlack<STRICT>(g, p, [&](Sq, Sq, bool c) { ++moves; if (c) cap = true; });
                        if (cap)         b[i] = V_DRAW;
                        else if (moves)  b[i] = V_UNKNOWN;
                        else             b[i] = bothInCheck(g, wk, wq, k1, k2) ? (U8)0 : (U8)V_DRAW;
                    }

        for (U32 d = 1;; d += 2) {
            U64 madeW = 0, madeB = 0;
            for (Sq wk = 0; wk < n; ++wk)
              for (Sq wq = 0; wq < n; ++wq)
                for (Sq k1 = 0; k1 < n; ++k1)
                  for (Sq k2 = 0; k2 < n; ++k2) {
                    const U64 i = index(wk, wq, k1, k2);
                    if (w[i] != V_UNKNOWN) continue;
                    const PosKK p{ wk, wq, k1, k2 };
                    bool won = false;
                    genWhiteKK(g, p, [&](const PosKK& q) {
                        if (won) return;
                        if (b[index(q.wk, q.wq, q.bk1, q.bk2)] == (U8)(d - 1)) won = true;
                    });
                    if (won) { w[i] = (U8)d; ++madeW; }
                  }
            for (Sq wk = 0; wk < n; ++wk)
              for (Sq wq = 0; wq < n; ++wq)
                for (Sq k1 = 0; k1 < n; ++k1)
                  for (Sq k2 = 0; k2 < n; ++k2) {
                    const U64 i = index(wk, wq, k1, k2);
                    if (b[i] != V_UNKNOWN) continue;
                    const PosKK p{ wk, wq, k1, k2 };
                    bool allWin = true; int worst = -1, moves = 0;
                    genBlack<STRICT>(g, p, [&](Sq to, Sq stay, bool c) {
                        if (!allWin) return;
                        if (c) { allWin = false; return; }
                        ++moves;
                        const U8 v = w[index(wk, wq, to, stay)];
                        if (!isDtm(v)) { allWin = false; return; }
                        if ((int)v > worst) worst = v;
                    });
                    if (allWin && moves) { b[i] = (U8)(worst + 1); ++madeB; }
                  }
            if (!madeW && !madeB) break;
        }
        for (U64 i = 0; i < w.size(); ++i) {
            if (w[i] == V_UNKNOWN) w[i] = V_DRAW;
            if (b[i] == V_UNKNOWN) b[i] = V_DRAW;
        }
    }
};

// A deliberately naive attack test: walk the ray one square at a time instead
// of doing arithmetic on the ray parameter.  Geometry::attacks is the fast
// form; this is the independent one the self-check compares it against.
bool naiveQueenAttacks(const Geometry& g, Sq from, Sq to, Sq o0, Sq o1, Sq o2) {
    if (from == to) return false;
    for (int d = 0; d < 8; ++d) {
        int f = g.file(from), r = g.rank(from);
        for (;;) {
            f += DIR_F[d]; r += DIR_R[d];
            if (!g.onBoard(f, r)) break;
            const Sq s = g.sq(f, r);
            if (s == to) return true;
            if (s == o0 || s == o1 || s == o2) break;
        }
    }
    return false;
}

} // namespace

U64 kqkkBruteForceCheck(const TableKQKK& t, bool progress) {
    Brute br(t.geo, t.rules);
    if (t.rules == KkRules::Strict) br.solve<true>(); else br.solve<false>();
    const int n = t.geo.nsq;
    U64 bad = 0, shown = 0;
    for (Sq wk = 0; wk < n; ++wk)
        for (Sq wq = 0; wq < n; ++wq)
            for (Sq k1 = 0; k1 < n; ++k1)
                for (Sq k2 = 0; k2 < n; ++k2) {
                    const PosKK p{ wk, wq, k1, k2 };
                    for (int side = 0; side < 2; ++side) {
                        const bool wtm = side == 0;
                        const U8 a = br.at(p, wtm), c = t.valueAt(p, wtm);
                        if (a == c) continue;
                        ++bad;
                        if (shown++ < 10)
                            std::fprintf(stderr,
                                "  brute mismatch %s  wK %s wQ %s bK %s bK %s: brute %d, table %d\n",
                                wtm ? "W" : "b", t.geo.name(wk).c_str(), t.geo.name(wq).c_str(),
                                t.geo.name(k1).c_str(), t.geo.name(k2).c_str(), (int)a, (int)c);
                    }
                }
    if (progress)
        std::fprintf(stderr, "  brute force n=%d: %llu mismatches\n",
                     t.n, (unsigned long long)bad);
    return bad;
}

// ---------------------------------------------------------------------------
// The two components the small-board brute force cannot reach on a large
// board: the move generator, against a naive one, and the index, against the
// definition of the symmetry class -- a table value must not change under any
// of the eight symmetries of the board, nor under swapping the two black
// kings, which are indistinguishable.
// ---------------------------------------------------------------------------
U64 kqkkSelfCheck(int lo, int hi, U64 trials, bool progress) {
    U64 bad = 0;
    for (int n = lo; n <= hi; ++n) {
        Geometry g(n);
        std::mt19937_64 rng(0x5eed1234u + n);
        std::uniform_int_distribution<int> pick(0, g.nsq - 1);
        TableKQKK t(n);
        t.generate(1, false);
        U64 checked = 0;
        for (U64 it = 0; it < trials; ++it) {
            PosKK p{ pick(rng), pick(rng), pick(rng), pick(rng) };
            if (!t.legal(p, false)) continue;
            ++checked;
            // 1. the attack test against a naive ray walk
            for (int which = 0; which < 2; ++which) {
                const Sq k = which ? p.bk2 : p.bk1, o = which ? p.bk1 : p.bk2;
                const bool fast = t.inCheck(p, which);
                const bool slow = naiveQueenAttacks(g, p.wq, k, p.wk, o, -1);
                if (fast != slow) { ++bad;
                    std::fprintf(stderr, "  n=%d attack test disagrees at wQ %s -> %s\n",
                                 n, g.name(p.wq).c_str(), g.name(k).c_str()); }
            }
            // 2. the value is a class function
            const U8 vw = t.valueAt(p, true), vb = t.valueAt(p, false);
            const PosKK sw{ p.wk, p.wq, p.bk2, p.bk1 };
            if (t.valueAt(sw, true) != vw || t.valueAt(sw, false) != vb) {
                ++bad;
                std::fprintf(stderr, "  n=%d swapping the black kings changes the value\n", n);
            }
            for (int s = 1; s < NSYM; ++s) {
                const PosKK q{ g.image(s, p.wk), g.image(s, p.wq),
                               g.image(s, p.bk1), g.image(s, p.bk2) };
                if (t.valueAt(q, true) != vw || t.valueAt(q, false) != vb) {
                    ++bad;
                    std::fprintf(stderr, "  n=%d symmetry %d changes the value\n", n, s);
                }
            }
        }
        if (progress)
            std::fprintf(stderr, "  n=%2d: %llu placements checked\n",
                         n, (unsigned long long)checked);
    }
    return bad;
}

// ---------------------------------------------------------------------------
// On-disk format.  A fixed header, then the two value arrays, optionally
// run-length encoded; the census is recomputed on load, which costs one linear
// pass and keeps the format to one thing.  The header records the rule set, so
// a strict table can never be read as a loose one.
// ---------------------------------------------------------------------------
namespace {

constexpr char KKMAGIC[8] = { 'K', 'Q', 'K', 'K', 'T', 'B', 0, 0 };
constexpr U32  KKVERSION  = 1;
constexpr U32  KKFLAG_RLE   = 1u << 0;
constexpr U32  KKFLAG_LOOSE = 1u << 1;

struct KKHeader {
    char magic[8];
    U32  version, n, flags, pad;
    U64  nblk, nslots, wBytes, bBytes;
};

void put(std::FILE* f, const void* p, size_t n) {
    if (std::fwrite(p, 1, n, f) != n) throw std::runtime_error("short write");
}
void get(std::FILE* f, void* p, size_t n) {
    if (std::fread(p, 1, n, f) != n) throw std::runtime_error("short read / truncated file");
}

std::vector<U8> rleEnc(const std::vector<U8>& src) {
    std::vector<U8> out;
    out.reserve(src.size() / 8 + 16);
    size_t i = 0;
    while (i < src.size()) {
        const U8 v = src[i];
        size_t j = i + 1;
        while (j < src.size() && src[j] == v) ++j;
        U64 run = j - i;
        out.push_back(v);
        while (run >= 0x80) { out.push_back(U8((run & 0x7F) | 0x80)); run >>= 7; }
        out.push_back(U8(run));
        i = j;
    }
    return out;
}

void rleDec(const std::vector<U8>& src, std::vector<U8>& dst, U64 expect) {
    dst.clear();
    dst.reserve(expect);
    size_t i = 0;
    while (i < src.size()) {
        const U8 v = src[i++];
        U64 run = 0; int sh = 0;
        for (;;) {
            if (i >= src.size()) throw std::runtime_error("corrupt run-length data");
            const U8 c = src[i++];
            run |= (U64)(c & 0x7F) << sh;
            sh += 7;
            if (!(c & 0x80)) break;
        }
        dst.insert(dst.end(), (size_t)run, v);
    }
    if (dst.size() != expect) throw std::runtime_error("run-length data has the wrong length");
}

} // namespace

void TableKQKK::save(const std::string& path, bool rle) const {
    std::FILE* f = std::fopen(path.c_str(), "wb");
    if (!f) throw std::runtime_error("cannot open " + path + " for writing");
    try {
        // Run-length encoding pays handsomely on the other endgames, whose
        // tables hold large drawn regions and dead diagonals.  It does not pay
        // here: a KQKK block is one king triple swept over every queen square,
        // almost all of it won, with the depth changing from one square to the
        // next, so the runs are short and the encoding can come out *larger*
        // than the data.  Encode, compare, and keep whichever is smaller; the
        // header flag records which one was written.
        std::vector<U8> we = rle ? rleEnc(w) : w;
        std::vector<U8> be = rle ? rleEnc(b) : b;
        bool wroteRle = rle;
        if (rle && we.size() + be.size() >= w.size() + b.size()) {
            we = w; be = b; wroteRle = false;
        }
        KKHeader h{};
        std::memcpy(h.magic, KKMAGIC, 8);
        h.version = KKVERSION;
        h.n = (U32)n;
        h.flags = (wroteRle ? KKFLAG_RLE : 0u) |
                  (rules == KkRules::Loose ? KKFLAG_LOOSE : 0u);
        h.nblk = idx.nblk;
        h.nslots = idx.nslots;
        h.wBytes = we.size();
        h.bBytes = be.size();
        put(f, &h, sizeof h);
        put(f, we.data(), we.size());
        put(f, be.data(), be.size());
    } catch (...) { std::fclose(f); throw; }
    std::fclose(f);
}

std::unique_ptr<TableKQKK> TableKQKK::load(const std::string& path) {
    std::FILE* f = std::fopen(path.c_str(), "rb");
    if (!f) throw std::runtime_error("cannot open " + path);
    std::unique_ptr<TableKQKK> t;
    try {
        KKHeader h{};
        get(f, &h, sizeof h);
        if (std::memcmp(h.magic, KKMAGIC, 8) != 0)
            throw std::runtime_error(path + " is not a KQKK tablebase");
        if (h.version != KKVERSION)
            throw std::runtime_error("unsupported KQKK file version");
        t.reset(new TableKQKK((int)h.n,
                              (h.flags & KKFLAG_LOOSE) ? KkRules::Loose : KkRules::Strict));
        if (t->idx.nslots != h.nslots)
            throw std::runtime_error("file does not match the index it names");
        std::vector<U8> we((size_t)h.wBytes), be((size_t)h.bBytes);
        get(f, we.data(), we.size());
        get(f, be.data(), be.size());
        if (h.flags & KKFLAG_RLE) {
            rleDec(we, t->w, h.nslots);
            rleDec(be, t->b, h.nslots);
        } else {
            t->w = std::move(we);
            t->b = std::move(be);
        }
    } catch (...) { std::fclose(f); throw; }
    std::fclose(f);
    t->computeStats(1);
    return t;
}

} // namespace kqk
