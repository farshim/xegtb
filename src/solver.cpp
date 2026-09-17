// solver.cpp -- parallel retrograde analysis producing depth-to-mate.
//
// Structure of the computation
// ----------------------------
// In every endgame this program computes, the value of a position is heavily
// constrained before any search: Black has a lone king, so Black can never
// give check, never mate, and never win.  Therefore every white-to-move entry
// is a win or a draw and every black-to-move entry is a loss or a draw.  The
// backward induction is correspondingly a strict alternation of two sweeps.
//
//   phase A   black-to-move losses at ply d  ->  their white-to-move
//             predecessors are wins at ply d+1
//   phase B   white-to-move wins at ply d+1  ->  a black-to-move predecessor
//             becomes a loss at ply d+2 once *all* of its moves lead to wins
//
// Phase B re-tests the predecessor by forward move generation rather than by
// decrementing a per-position counter of unresolved successors.  The usual
// counter trick is unsound on a symmetry-reduced index: an edge between two
// orbits of different size is seen a different number of times from the two
// ends, so counters would never reach zero for the positions that lie on a
// symmetry axis.  Black has at most eight moves, so re-testing is cheap, and
// it removes the counter array entirely -- the table needs only two bytes per
// symmetry class, one per side to move.
//
// Nothing below is specific to a particular piece.  White's men enter only
// through Geometry (which rays they travel) and through NP, the number of them
// -- the file is templated on that so the one-piece endgames compile to
// exactly the code they had before two-piece ones existed.
//
// Each phase has disjoint read and write sets (phase A reads the black array
// and writes the white one, phase B the other way round), so the only races
// are threads writing the same value to the same byte.  Those are done with
// relaxed atomics.
#include "table.hpp"

#include <atomic>
#include <chrono>
#include <cstdio>
#include <thread>
#include <type_traits>

namespace kqk {

void parallelFor(U64 count, U64 grain, int threads,
                 const std::function<void(U64, U64, int)>& body) {
    if (threads < 1) threads = 1;
    if (grain < 1) grain = 1;
    std::atomic<U64> next{0};
    auto worker = [&](int tid) {
        for (;;) {
            U64 lo = next.fetch_add(grain, std::memory_order_relaxed);
            if (lo >= count) break;
            body(lo, std::min(lo + grain, count), tid);
        }
    };
    std::vector<std::thread> pool;
    pool.reserve(threads > 0 ? threads - 1 : 0);
    for (int t = 1; t < threads; ++t) pool.emplace_back(worker, t);
    worker(0);
    for (auto& th : pool) th.join();
}

namespace {

inline U8 aload(const U8* a, U64 i) {
    return std::atomic_ref<U8>(const_cast<U8&>(a[i])).load(std::memory_order_relaxed);
}
inline void astore(U8* a, U64 i, U8 v) {
    std::atomic_ref<U8>(a[i]).store(v, std::memory_order_relaxed);
}
// Claim an unresolved entry.  Two threads can reach the same entry in the
// same sweep -- from a piece retraction inside the block and a king retraction
// from a neighbouring one -- and both would write the same value, which is
// harmless in itself but would decrement the open-entry counter twice.  The
// exchange makes exactly one of them the writer.
inline bool aclaim(U8* a, U64 i, U8 v) {
    U8 expect = V_UNKNOWN;
    return std::atomic_ref<U8>(a[i]).compare_exchange_strong(
        expect, v, std::memory_order_relaxed, std::memory_order_relaxed);
}
inline U32 aloadU32(const U32* a, U64 i) {
    return std::atomic_ref<U32>(const_cast<U32&>(a[i])).load(std::memory_order_relaxed);
}
inline void asubU32(U32* a, U64 i, U32 v) {
    std::atomic_ref<U32>(a[i]).fetch_sub(v, std::memory_order_relaxed);
}

struct Timer {
    std::chrono::steady_clock::time_point t0 = std::chrono::steady_clock::now();
    double s() const {
        return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    }
};

// Is `t` attacked by White's pieces standing on `cfg`, with the white king the
// only other blocker?  The open-coded form of attackedByPiece() for the hot
// loops, which have the configuration in registers rather than in a Pos.
// `pk` is a local copy of the piece kinds.  Reading them out of Material
// inside the loop would stop the compiler hoisting the load: the atomic stores
// to the value arrays may, as far as it knows, alias the Material.
template <Endgame EG>
inline bool cfgAttacks(const Geometry& g, Sq wk, const Sq* cfg, Sq t) {
    if constexpr (npOf(EG) == 1) return g.attacks(pieceOf(EG, 0), cfg[0], t, wk);
    else if constexpr (npOf(EG) == 3) {
        // All three are knights, so no blocker argument is read; see the note
        // on attackedByPieceT in movegen.hpp.
        for (int i = 0; i < 3; ++i)
            if (g.attacks(pieceOf(EG, i), cfg[i], t, wk)) return true;
        return false;
    }
    else return g.attacks(pieceOf(EG, 0), cfg[0], t, wk, cfg[1]) ||
                g.attacks(pieceOf(EG, 1), cfg[1], t, wk, cfg[0]);
}

template <int NP>
inline bool onCfg(const Sq* cfg, Sq s) {
    if constexpr (NP == 1) return cfg[0] == s;
    else if constexpr (NP == 3) return cfg[0] == s || cfg[1] == s || cfg[2] == s;
    else return cfg[0] == s || cfg[1] == s;
}

// Which of White's pieces stands on `s`, or -1.
template <Endgame EG>
inline int cfgIndexOf(const Sq* cfg, Sq s) {
    if (cfg[0] == s) return 0;
    if constexpr (npOf(EG) >= 2) if (cfg[1] == s) return 1;
    if constexpr (npOf(EG) == 3) if (cfg[2] == s) return 2;
    return -1;
}

// Is White's piece number `captured`, standing on `s`, defended by the other
// one?  If it is, Black cannot take it and the capture is not a move at all.
//
// The white king is deliberately not consulted: every caller has already
// excluded the squares next to it.  That is why the one-piece endgames need
// this at all -- with a single piece nothing can defend it, which is what let
// the original solver treat "the black king steps onto the piece" as a capture
// without further thought.  With two pieces that shortcut is wrong.
template <Endgame EG>
inline bool cfgDefends(const Geometry& g, Sq wk, const Sq* cfg, int captured, Sq s) {
    if constexpr (npOf(EG) == 1) { (void)g; (void)wk; (void)cfg; (void)captured; (void)s;
                                   return false; }
    else if constexpr (npOf(EG) == 3) {
        for (int i = 0; i < 3; ++i)
            if (i != captured && g.attacks(pieceOf(EG, i), cfg[i], s, wk)) return true;
        return false;
    }
    else return captured == 0 ? g.attacks(pieceOf(EG, 1), cfg[1], s, wk)
                              : g.attacks(pieceOf(EG, 0), cfg[0], s, wk);
}

// The value of the position Black reaches by taking White's piece `captured`
// and standing on `to`.  For every endgame but KNNNK the invariant in
// geometry.hpp says the material left cannot mate, so this is the constant
// V_DRAW and the whole call folds away.  KNNNK is the exception: the two
// knights left over can mate, just not by force, so the answer has to be read
// out of the KNNK table for this board.  The position is White to move, and it
// is legal by construction -- Black has just made a legal king move, so he is
// not in check.
template <Endgame EG>
inline U8 captureValue(const Table& T, Sq wk, const Sq* cfg, int captured, Sq to) {
    // Only KNNNK converts under the ordinary rules.  Two more join it under
    // capture rules, for the same reason and by the same mechanism: what is
    // left after the capture is a one-piece endgame with stalemate scored as a
    // loss, and neither K+N vs K nor K+B vs K is uniformly drawn there.  So
    // KNNK reads a KNK table and KBBK reads a KBK one.  Everything else folds
    // to V_DRAW at compile time and pays nothing -- including KBBK itself
    // under the ordinary rules, where T.sub is null and the branch below
    // returns V_DRAW at run time.
    if constexpr (EG != Endgame::KNNNK && EG != Endgame::KNNK &&
                  EG != Endgame::KBBK) {
        (void)T; (void)wk; (void)cfg; (void)captured; (void)to;
        return V_DRAW;
    } else {
        if (!T.sub) return V_DRAW;
        Pos q;
        q.wk = wk;
        q.bk = to;
        int k = 0;
        for (int i = 0; i < npOf(EG); ++i) if (i != captured) q.wp[k++] = cfg[i];
        return T.sub->valueAt(q, /*whiteToMove=*/true);
    }
}

// ---------------------------------------------------------------------------
template <Endgame EG>
void generateImpl(Table& T, int threads, bool progress) {
    constexpr int NP = npOf(EG);
    const Geometry& g = T.geo;
    const Index& idx = T.idx;
    const U32 npc = idx.npc;
    const U64 nkk = idx.nkk;
    ByteArray& w = T.w;
    ByteArray& b = T.b;
    Timer clock;

    w.assign(idx.nslots, V_DEAD);
    b.assign(idx.nslots, V_DEAD);

    // Dirty-block maps.  A block is one king pair, i.e. npc consecutive
    // entries.  Only blocks that received a value at the previous ply need to
    // be rescanned, which keeps the deep, sparse plies almost free.
    std::vector<U8> dirtyB(nkk, 0), dirtyBn(nkk, 0), dirtyW(nkk, 0);
    std::vector<std::vector<U32>> scratch(std::max(1, threads));

    // Number of still-unresolved white-to-move entries per block.  Once a block
    // hits zero it can never gain anything from another piece-retraction sweep,
    // so the sweep can be skipped -- and that is where most of the work would
    // otherwise go, since each piece has O(n) retractions per position.  In the
    // one-piece endgames every legal white-to-move position is a win, so the
    // counters drain completely; in KBBK the same-coloured-bishop
    // configurations never resolve, so they do not, and the optimisation
    // simply stops firing.  Correctness does not depend on it either way.
    std::vector<U32> openW(nkk, 0);

    // ---- initialisation ---------------------------------------------------
    // Marks dead slots, finds mates and stalemates, and settles every position
    // in which Black can simply take one of White's pieces.
    std::atomic<U64> mates{0};
    // Blocks holding a black-to-move loss whose value is not the ply that
    // produced it.  Only a table that CONVERTS can have any: a capture's value
    // comes from a sub-table and may name any depth at all, so phase B can
    // settle a position at ply 40 while the sweep is at ply 2, and the strict
    // alternation -- which assumes the value is always d+2 -- would then never
    // come back for it.  `laterDirty[v * nkk + kk]` says block kk holds
    // something worth revisiting when the sweep reaches ply v.
    //
    // This is the bucketed induction the capture rules needed, in the smallest
    // form that serves a one-way conversion; it is allocated only when there
    // is a sub-table, so the non-converting endgames pay nothing for it.
    const bool converts = (T.sub != nullptr);
    std::vector<U8> laterDirty;
    if (converts) laterDirty.assign((size_t)(MAX_PLY + 2) * nkk, 0);
    std::atomic<U32> maxLater{0};
    auto scheduleAt = [&](U32 v, U64 kk) {
        if (!converts || v > MAX_PLY) return;
        astore(laterDirty.data(), (U64)v * nkk + kk, 1);
        for (U32 cur = maxLater.load(std::memory_order_relaxed);
             cur < v &&
             !maxLater.compare_exchange_weak(cur, v, std::memory_order_relaxed); ) {}
    };
    parallelFor(nkk, 64, threads, [&](U64 lo, U64 hi, int) {
        U64 localMates = 0;
        for (U64 kk = lo; kk < hi; ++kk) {
            Pos p;
            p.wk = idx.kkWk[kk];
            p.bk = idx.kkBk[kk];
            bool blockHasMate = false;
            U64 base = kk * npc;
            U32 open = 0;
            for (U32 pc = 0; pc < npc; ++pc) {
                idx.decode<EG>(pc, p.wp);
                if (!idx.cfgLive<EG>(p.wp, p.wk, p.bk)) continue;        // stays V_DEAD
                if (!idx.cfgIsCanonical<EG>((int32_t)kk, p.wp)) continue;
                bool check = blackInCheckT<EG>(g, p);
                w[base + pc] = check ? V_DEAD : V_UNKNOWN;   // black in check: illegal
                open += !check;

                // Black's moves.  A capture is settled here and now, because
                // its value does not depend on this table: for every endgame
                // but KNNNK it is a draw by the invariant, and for KNNNK it is
                // whatever the KNNK table says.  Everything else is left for
                // the induction.  `escapes` means Black has some move White
                // does not win, which makes the position drawn whatever else
                // is true; `pending` means some move's value is still unknown.
                int nmoves = 0;
                bool escapes = false, pending = false;
                U8 worst = 0;
                genBlackT<EG>(g, p, [&](Sq to, int cap) {
                    ++nmoves;
                    if (cap < 0) { pending = true; return; }
                    U8 v = captureValue<EG>(T, p.wk, p.wp, cap, to);
                    if (!isDtm(v)) escapes = true;
                    else if (v > worst) worst = v;
                });
                if (escapes)         b[base + pc] = V_DRAW;      // piece en prise
                else if (nmoves && !pending) {
                    // Every move Black has is a capture, and every one of them
                    // loses.  Nothing in this table will ever trigger a re-test
                    // of such a position -- its successors all live in the
                    // sub-table -- so it is settled here and its block is
                    // remembered, to be handed to phase A at the right ply.
                    b[base + pc] = (U8)(worst + 1);
                    if (worst + 1 == 0) blockHasMate = true;
                    else scheduleAt((U32)(worst + 1), kk);
                }
                else if (nmoves)     b[base + pc] = V_UNKNOWN;
                else if (check)    { b[base + pc] = 0; ++localMates; blockHasMate = true; }
                else if (T.stalemateLoss) {
                    // Capture rules: Black is not in check and has no chess
                    // move, so every move he does have walks his king onto a
                    // square White can take it from.  He loses, at ply 0, the
                    // same as a mate -- which is the single clause that
                    // separates the capture game from chess for this material.
                    b[base + pc] = 0; blockHasMate = true;
                }
                else                 b[base + pc] = V_DRAW;      // stalemate
            }
            openW[kk] = open;
            if (blockHasMate) dirtyB[kk] = 1;
        }
        mates.fetch_add(localMates, std::memory_order_relaxed);
    });

    if (progress)
        std::fprintf(stderr, "  init: %llu king pairs, %llu mates, %.2fs\n",
                     (unsigned long long)nkk, (unsigned long long)mates.load(), clock.s());

    // ---- backward induction ----------------------------------------------
    double tA = 0, tB = 0;
    U32 d = 0;
    for (;;) {
        if (d + 2 > MAX_PLY) {
            std::fprintf(stderr,
                         "error: depth to mate exceeds %d plies on a %dx%d board; "
                         "widen the entry type and rebuild\n", (int)MAX_PLY, T.n, T.n);
            std::exit(2);
        }
        // Blocks holding a loss whose value is exactly this ply rejoin the
        // dirty set, whether it was settled at init or written out of order by
        // a conversion.  Empty for every table that does not convert.
        if (converts && d <= MAX_PLY)
            for (U64 kk = 0; kk < nkk; ++kk)
                dirtyB[kk] |= laterDirty[(size_t)d * nkk + kk];

        // phase A: losses at ply d push their predecessors to wins at ply d+1
        std::fill(dirtyW.begin(), dirtyW.end(), 0);
        double tp0 = clock.s();
        std::atomic<U64> madeW{0};
        parallelFor(nkk, 32, threads, [&](U64 lo, U64 hi, int) {
            U64 local = 0;
            for (U64 kk = lo; kk < hi; ++kk) {
                if (!dirtyB[kk]) continue;
                const Sq wk = idx.kkWk[kk], bk = idx.kkBk[kk];
                const U8* stab = &idx.kkStab[kk * NSYM];
                const int  slen = idx.kkStabLen[kk];
                const U64  base = kk * npc;
                U8* const  wb = w.data() + base;
                const U8*  bb = b.data() + base;
                const U8   dv = (U8)(d + 1);
                const int  wkf = g.file(wk), wkr = g.rank(wk);
                bool touched = false;
                U32  filled = 0;
                // A private copy of the block's open-entry count.  Other
                // threads may retract a white king move into this block and
                // lower the shared counter without this copy seeing it, which
                // only ever makes the copy an over-estimate -- so reaching
                // zero here really does mean the block is finished, while a
                // stale non-zero value costs nothing but one more sweep.
                U32  blockRemaining = aloadU32(openW.data(), kk);
                bool blockOpen = blockRemaining != 0;
                for (U32 pc = 0; pc < npc; ++pc) {
                    if (aload(bb, pc) != (U8)d) continue;
                    Sq cfg[MAXWP];
                    idx.decode<EG>(pc, cfg);

                    // Undo a move of one of White's pieces.  Every piece here
                    // moves symmetrically, so the squares it could have come
                    // from are exactly the squares it can move to -- which is
                    // why this is the same forEachMove the forward generator
                    // uses, and why the two can never drift apart.  The king
                    // pair does not change, so every such predecessor stays
                    // inside this block: the whole walk touches one contiguous
                    // run of memory.
                    auto retract = [&](auto Ic) {
                        constexpr int I = decltype(Ic)::value;
                        auto put = [&](Sq from) {
                            // Re-encode the configuration with piece I put back
                            // on `from`.  For a single piece that is just the
                            // square, and saying so explicitly is what keeps the
                            // one-piece endgames on the register-only path they
                            // had before two-piece ones existed: going through
                            // the general array form costs a few percent at
                            // n = 32.
                            U32 c;
                            if constexpr (NP == 1) {
                                c = (slen == 1) ? (U32)from
                                                : (U32)idx.canonSquare(stab, slen, from);
                            } else {
                                Sq prev[MAXWP];
                                for (int k = 0; k < NP; ++k) prev[k] = cfg[k];
                                prev[I] = from;
                                c = (slen == 1) ? (U32)idx.encode<EG>(prev)
                                                : idx.canonCfg<EG>(stab, slen, prev);
                            }
                            if (aload(wb, c) == V_UNKNOWN && aclaim(wb, c, dv)) {
                                ++local; ++filled;
                                touched = true;
                                if (--blockRemaining == 0) { blockOpen = false; return false; }
                            }
                            return true;
                        };
                        // Squares the piece could have come from.  forEachMove
                        // takes three occupancies; with three knights the men
                        // in the way are four, so the black king is excluded by
                        // hand -- exact for a jumper, which cannot be blocked.
                        if constexpr (NP == 3) {
                            forEachMove<pieceOf(EG, I)>(g, cfg[I], wk,
                                                        cfg[I == 0 ? 1 : 0],
                                                        cfg[I == 2 ? 1 : 2],
                                                        [&](Sq from) {
                                return from == bk ? true : put(from);
                            });
                        } else {
                            const Sq other = (NP == 2) ? cfg[1 - I] : Sq(-1);
                            forEachMove<pieceOf(EG, I)>(g, cfg[I], wk, bk, other, put);
                        }
                    };
                    if (blockOpen) retract(std::integral_constant<int, 0>{});
                    if constexpr (NP >= 2)
                        if (blockOpen) retract(std::integral_constant<int, 1>{});
                    if constexpr (NP == 3)
                        if (blockOpen) retract(std::integral_constant<int, 2>{});

                    // Undo a white king move.  This one does leave the block.
                    for (int s = 0; s < 8; ++s) {
                        int f = wkf + KF[s], r = wkr + KR[s];
                        if (!g.onBoard(f, r)) continue;
                        Sq from = g.sq(f, r);
                        if (from == bk || onCfg<NP>(cfg, from)) continue;
                        U64 t;
                        int32_t tkk = idx.slotOfKk<EG>(from, bk, cfg, t);
                        if (tkk < 0) continue;
                        if (aload(w.data(), t) == V_UNKNOWN && aclaim(w.data(), t, dv)) {
                            ++local;
                            asubU32(openW.data(), (U64)tkk, 1);
                            astore(dirtyW.data(), (U64)tkk, 1);
                        }
                    }
                }
                if (filled) asubU32(openW.data(), kk, filled);
                if (touched) astore(dirtyW.data(), kk, 1);
            }
            madeW.fetch_add(local, std::memory_order_relaxed);
        });
        tA += clock.s() - tp0;
        if (madeW.load() == 0 && d >= maxLater.load()) break;
        T.st.maxPly = d + 1;

        // phase B: a black-to-move position is lost once every move it has
        // leads to a white win.
        std::fill(dirtyBn.begin(), dirtyBn.end(), 0);
        double tp1 = clock.s();
        std::atomic<U64> madeB{0};
        parallelFor(nkk, 32, threads, [&](U64 lo, U64 hi, int tid) {
            U64 local = 0;
            std::vector<U32>& hits = scratch[tid];
            for (U64 kk = lo; kk < hi; ++kk) {
                if (!dirtyW[kk]) continue;
                const Sq wk = idx.kkWk[kk], bk = idx.kkBk[kk];
                const auto& stabWk = g.triStab[g.triId[wk]];
                const U8* const sw = stabWk.data();
                const int lw = (int)stabWk.size();
                const int32_t* const kkRow = idx.kkRowFor(wk);
                const U8* const wb = w.data() + kk * npc;
                const U8  dv = (U8)(d + 1);

                // Collect the configurations that were just won.  Sweeping them
                // once per black king origin, rather than the other way round,
                // turns the successor lookups into a handful of monotonically
                // advancing streams instead of scattered probes.
                hits.clear();
                for (U32 pc = 0; pc < npc; ++pc)
                    if (aload(wb, pc) == dv) hits.push_back(pc);
                if (hits.empty()) continue;

                const int bkf = g.file(bk), bkr = g.rank(bk);
                for (int s = 0; s < 8; ++s) {
                    int pf = bkf + KF[s], pr = bkr + KR[s];
                    if (!g.onBoard(pf, pr)) continue;
                    const Sq from = g.sq(pf, pr);            // black king before its move
                    if (g.kingsTouch(from, wk)) continue;

                    if (lw > 1) {                            // white king on a symmetry axis
                        for (U32 pc : hits) {
                            Pos pp;
                            pp.wk = wk; pp.bk = from;
                            idx.decode<EG>(pc, pp.wp);
                            if (onCfg<NP>(pp.wp, from)) continue;
                            U64 rslot;
                            int32_t rkk = idx.slotSameWk<EG>(kkRow, sw, lw, from, pp.wp, rslot);
                            if (rkk < 0 || aload(b.data(), rslot) != V_UNKNOWN) continue;
                            bool allWin = true; U8 worst = 0; int moves = 0;
                            genBlackT<EG>(g, pp, [&](Sq to, int cap) {
                                if (!allWin) return;
                                ++moves;
                                if (cap >= 0) {
                                    U8 cv = captureValue<EG>(T, pp.wk, pp.wp, cap, to);
                                    if (!isDtm(cv)) { allWin = false; return; }
                                    if (cv > worst) worst = cv;
                                    return;
                                }
                                U64 c;
                                if (idx.slotSameWk<EG>(kkRow, sw, lw, to, pp.wp, c) < 0) {
                                    allWin = false; return;
                                }
                                U8 v = aload(w.data(), c);
                                if (!isDtm(v)) { allWin = false; return; }
                                if (v > worst) worst = v;
                            });
                            if (!allWin || !moves) continue;
                            astore(b.data(), rslot, (U8)(worst + 1));
                            ++local;
                            if ((U32)(worst + 1) == d + 2) astore(dirtyBn.data(), (U64)rkk, 1);
                            else                           scheduleAt((U32)(worst + 1), (U64)rkk);
                        }
                        continue;
                    }

                    const int32_t rkk = kkRow[from];
                    if (rkk < 0) continue;
                    U8* const rb = b.data() + (U64)rkk * npc;

                    // Successors of that predecessor: the black king steps back
                    // out again.  Their blocks depend only on the square, so
                    // resolve them once for the whole sweep over configurations.
                    Sq  toSq[8];
                    const U8* toBase[8];
                    int nto = 0;
                    for (int t = 0; t < 8; ++t) {
                        int tf = pf + KF[t], tr = pr + KR[t];
                        if (!g.onBoard(tf, tr)) continue;
                        Sq to = g.sq(tf, tr);
                        if (g.kingsTouch(to, wk)) continue;
                        int32_t ck = kkRow[to];
                        if (ck < 0) continue;
                        toSq[nto] = to;
                        toBase[nto] = w.data() + (U64)ck * npc;
                        ++nto;
                    }

                    for (U32 pc : hits) {
                        // Same reason as in phase A: with one piece the
                        // configuration is a square, and keeping it one lets
                        // this loop stay in registers.
                        Sq cfg[MAXWP];
                        if constexpr (NP == 1) cfg[0] = (Sq)pc;
                        else idx.decode<EG>(pc, cfg);
                        if (onCfg<NP>(cfg, from)) continue;   // a piece stands there
                        if (aload(rb, pc) != V_UNKNOWN) continue;
                        bool allWin = true; U8 worst = 0; int moves = 0;
                        for (int i = 0; i < nto; ++i) {
                            Sq to = toSq[i];
                            int cap = cfgIndexOf<EG>(cfg, to);
                            if (cap >= 0) {
                                // Black would be taking that piece.  Legal only
                                // if none of the others defends it; if one does,
                                // this is no move.  What a real capture is worth
                                // is captureValue's business: a draw everywhere
                                // but KNNNK, and a KNNK lookup there.
                                if (cfgDefends<EG>(g, wk, cfg, cap, to)) continue;
                                U8 cv = captureValue<EG>(T, wk, cfg, cap, to);
                                if (!isDtm(cv)) { allWin = false; break; }
                                ++moves;
                                if (cv > worst) worst = cv;
                                continue;
                            }
                            if (cfgAttacks<EG>(g, wk, cfg, to)) continue;   // not a legal move
                            ++moves;
                            U8 v = aload(toBase[i], pc);
                            if (!isDtm(v)) { allWin = false; break; }
                            if (v > worst) worst = v;
                        }
                        if (!allWin || !moves) continue;
                        astore(rb, pc, (U8)(worst + 1));
                        ++local;
                        if ((U32)(worst + 1) == d + 2) astore(dirtyBn.data(), (U64)rkk, 1);
                        else                           scheduleAt((U32)(worst + 1), (U64)rkk);
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

        if (madeB.load() == 0 && d >= maxLater.load()) break;
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

    if (progress)
        std::fprintf(stderr, "  solved in %.2fs  (phase A %.2fs, phase B %.2fs)\n",
                     clock.s(), tA, tB);
}

} // namespace

void Table::generate(int threads, bool progress) {
    switch (mat.eg) {
        case Endgame::KQK:  generateImpl<Endgame::KQK>(*this, threads, progress);  break;
        case Endgame::KRK:  generateImpl<Endgame::KRK>(*this, threads, progress);  break;
        case Endgame::KBBK:
            // Under the ordinary rules ...KxB leaves KBK, a dead draw, and no
            // sub-table is needed.  Under capture rules it leaves KBK with
            // stalemate scored as a loss, which White wins from 7360
            // placements on 8x8 and more on every larger board, so one is.
            if (stalemateLoss && !sub) {
                std::fprintf(stderr, "error: KBBK under capture rules needs a %dx%d "
                                     "KBK table attached before it can be solved\n", n, n);
                std::exit(2);
            }
            generateImpl<Endgame::KBBK>(*this, threads, progress); break;
        case Endgame::KBNK: generateImpl<Endgame::KBNK>(*this, threads, progress); break;
        // KNNK qualifies: the only capture available to Black leaves KNK, and
        // KNK contains no mate on any board size, so the capture really is an
        // immediate draw.  KNNNK does not qualify and is not listed here.
        case Endgame::KNK:  generateImpl<Endgame::KNK>(*this, threads, progress);  break;
        // KBK qualifies for the same reason KNK does: the only capture Black
        // has leaves bare kings.  It exists as an endgame in its own right
        // only because KBBK under capture rules has to read it.
        case Endgame::KBK:  generateImpl<Endgame::KBK>(*this, threads, progress);  break;
        case Endgame::KNNK:
            // Under the ordinary rules ...KxN leaves KNK, which holds no mate
            // on any board, so no sub-table is needed.  Under capture rules it
            // leaves KNK with stalemate scored as a loss, which White wins
            // from 2900 placements on every board from 10x10 up, so one is.
            if (stalemateLoss && !sub) {
                std::fprintf(stderr, "error: KNNK under capture rules needs a %dx%d "
                                     "KNK table attached before it can be solved\n", n, n);
                std::exit(2);
            }
            generateImpl<Endgame::KNNK>(*this, threads, progress);
            break;
        case Endgame::KNNNK:
            if (!sub || sub->mat.eg != Endgame::KNNK || sub->n != n) {
                std::fprintf(stderr, "error: KNNNK needs a %dx%d KNNK table attached "
                                     "before it can be solved\n", n, n);
                std::exit(2);
            }
            generateImpl<Endgame::KNNNK>(*this, threads, progress);
            break;
        default:
            // KQKR: Black is armed, so none of the reasoning this solver rests
            // on applies.  It has its own, in kqkr.cpp.  KNNNK: a knight
            // capture leaves KNNK, which is not always drawn, so it needs a
            // conversion this solver has no notion of; its own is in knnnk.cpp.
            std::fprintf(stderr, "error: %s cannot be solved by this solver; "
                                 "use the kqkr command\n", mat.name());
            std::exit(2);
    }
    computeStats(threads);
}

} // namespace kqk
