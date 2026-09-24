// brute.cpp -- an independent, symmetry-free recomputation of the endgame.
//
// This is the reference implementation, written for obviousness rather than
// speed: one byte per placement per side to move, no symmetry reduction, no
// dirty-block bookkeeping, no retrograde edges, one thread.  Each ply is a
// full forward scan of the whole array using the same move generators the
// rules are written in.  White's pieces are indexed as an *ordered* tuple even
// when they are alike, so every two-bishop position is stored twice, once for
// each way of naming the bishops -- deliberately, because the two copies must
// agree.  (For KBNK the pieces differ, so the ordered tuple is the only
// sensible indexing anyway and there is no duplication.)
//
// It exists to check the parts of the real generator that verify() cannot.
// verify() re-derives every entry from its successors, so it would be equally
// happy with a table that is self-consistent but indexed wrongly -- if the
// canonicalisation mapped two distinct positions onto one slot, both the
// solver and the verifier would read the same corrupted value and agree.  The
// brute force never canonicalises anything, so comparing the two tables
// position by position is a direct test of the D4 reduction and of the
// configuration encoding -- unordered for KBBK, ordered for KBNK -- and
// comparing the whole-board census is a direct test of the orbit-size
// weighting in stats.
#include "table.hpp"

#include <cstdio>

namespace kqk {

BruteForce::BruteForce(const Geometry& geo, Material m, const Table* subTable,
                       bool staleLoss, const Table* subAlt,
                       const Table* const* subFor) : g(geo), mat(m) {
    if (subFor) for (int i = 0; i < MAXWP; ++i) subFor_[i] = subFor[i];
    const int nsq = g.nsq;
    stride1 = (m.np >= 2) ? (U64)nsq : 1;
    stride2 = 1;
    // index() is a mixed radix of the two kings and every white piece, so the
    // array holds nsq^(2 + np) entries.  Spelling that as a loop rather than a
    // conditional is what keeps it right when a piece is added: the two-piece
    // form written out by hand is what a three-piece endgame silently overran.
    U64 total = (U64)nsq * nsq;
    for (int i = 0; i < m.np; ++i) total *= (U64)nsq;
    w.assign(total, V_DEAD);
    b.assign(total, V_DEAD);

    // Enumerate every placement of White's pieces, in order.
    auto forEachCfg = [&](auto&& fn) {
        Sq cfg[MAXWP];
        if (m.np == 1) {
            for (cfg[0] = 0; cfg[0] < nsq; ++cfg[0]) fn(cfg);
        } else if (m.np == 3) {
            for (cfg[0] = 0; cfg[0] < nsq; ++cfg[0])
                for (cfg[1] = 0; cfg[1] < nsq; ++cfg[1]) {
                    if (cfg[1] == cfg[0]) continue;
                    for (cfg[2] = 0; cfg[2] < nsq; ++cfg[2]) {
                        if (cfg[2] == cfg[0] || cfg[2] == cfg[1]) continue;
                        fn(cfg);
                    }
                }
        } else {
            for (cfg[0] = 0; cfg[0] < nsq; ++cfg[0])
                for (cfg[1] = 0; cfg[1] < nsq; ++cfg[1]) {
                    if (cfg[0] == cfg[1]) continue;
                    fn(cfg);
                }
        }
    };

    sub = subTable;
    subAlt_ = subAlt;
    staleLoss_ = staleLoss;
    // What a capture is worth.  A draw for every endgame satisfying the
    // invariant in geometry.hpp; for KNNNK, whatever the KNNK table says about
    // the position Black reaches.  Written out here rather than shared with
    // solver.cpp on purpose: this file exists to disagree with that one if
    // either is wrong.
    auto capValue = [&](const Pos& pos, Sq to, int cap) -> U8 {
        // Two unlike white men leave two different materials behind, so which
        // table answers depends on which man was taken.  Written out here
        // rather than shared with solver.cpp on purpose: this file exists to
        // disagree with that one if either is wrong.
        const Table* s = (cap >= 0 && cap < MAXWP) ? subFor_[cap] : nullptr;
        if (!s) return V_DRAW;
        // The sub-table names its men in its own order, which need not be
        // this one's: a pair of alike men comes first here (KQNNK is N,N,Q)
        // while the two-man tables run strongest first (KQNK is Q,N).  Lay the
        // survivors out to match the table being read, or the probe lands on
        // the entry with those two men exchanged.
        Pos q;
        q.wk = pos.wk;
        q.bk = to;
        Sq  left[MAXWP];
        Piece lp[MAXWP];
        int k = 0;
        for (int i = 0; i < m.np; ++i)
            if (i != cap) { left[k] = pos.wp[i]; lp[k] = m.piece[i]; ++k; }
        bool used[MAXWP] = { false, false, false };
        for (int j = 0; j < k; ++j)
            for (int i = 0; i < k; ++i)
                if (!used[i] && lp[i] == s->mat.piece[j]) { q.wp[j] = left[i]; used[i] = true; break; }
        return s->valueAt(q, true);
    };

    // ---- initialisation: mates, stalemates and immediate captures ---------
    Pos p;
    for (p.wk = 0; p.wk < nsq; ++p.wk)
        for (p.bk = 0; p.bk < nsq; ++p.bk) {
            if (g.kingsTouch(p.wk, p.bk)) continue;
            forEachCfg([&](const Sq* cfg) {
                for (int i = 0; i < m.np; ++i) p.wp[i] = cfg[i];
                for (int i = 0; i < m.np; ++i)
                    if (cfg[i] == p.wk || cfg[i] == p.bk) return;
                U64 i = index(p);
                bool check = blackInCheck(g, m, p);
                w[i] = check ? V_DEAD : V_UNKNOWN;   // Black already in check: illegal

                int moves = 0;
                bool escapes = false, pending = false;
                U8 worst = 0;
                genBlack(g, m, p, [&](Sq to, int cap) {
                    ++moves;
                    if (cap < 0) { pending = true; return; }
                    U8 v = capValue(p, to, cap);
                    if (!isDtm(v)) escapes = true;
                    else if (v > worst) worst = v;
                });
                if (escapes)     b[i] = V_DRAW;      // a capture Black survives
                else if (moves && !pending) b[i] = (U8)(worst + 1);
                else if (moves)  b[i] = V_UNKNOWN;
                else if (check)  b[i] = 0;           // checkmate
                else if (staleLoss) b[i] = 0;        // capture rules: stalemate loses
                else             b[i] = V_DRAW;      // stalemate
            });
        }

    // The deepest value a conversion put into b[] up front.  Positions whose
    // every move is a capture are settled during initialisation, at whatever
    // depth the sub-table gives them, so the depths that exist are not a dense
    // range starting at zero -- they have gaps, and a gap is not the end.  The
    // induction below must keep going until it is past the last of these, or
    // it abandons every seed sitting above the first quiet round.  (The real
    // solver has the same problem and handles it by remembering such blocks
    // and handing them to phase A at the right ply.)
    U8 seedMax = 0;
    for (U64 i = 0; i < b.size(); ++i)
        if (isDtm(b[i]) && b[i] > seedMax) seedMax = b[i];

    // ---- backward induction, one ply at a time ----------------------------
    for (U32 d = 0; d + 2 <= MAX_PLY; d += 2) {
        U64 madeW = 0, madeB = 0;

        // A white-to-move position is won in d+1 as soon as one move reaches a
        // black-to-move position lost in d.  Depths only grow, so the first
        // ply at which that happens is the right one.
        for (p.wk = 0; p.wk < nsq; ++p.wk)
            for (p.bk = 0; p.bk < nsq; ++p.bk) {
                if (g.kingsTouch(p.wk, p.bk)) continue;
                forEachCfg([&](const Sq* cfg) {
                    for (int i = 0; i < m.np; ++i) p.wp[i] = cfg[i];
                    U64 i = index(p);
                    if (w[i] != V_UNKNOWN) return;
                    bool hit = false;
                    genWhite(g, m, p, [&](const Pos& q) {
                        if (b[index(q)] == (U8)d) hit = true;
                    });
                    if (hit) { w[i] = (U8)(d + 1); ++madeW; }
                });
            }

        // A black-to-move position is lost once every move it has runs into a
        // white win; its depth is one more than the most stubborn of them.
        for (p.wk = 0; p.wk < nsq; ++p.wk)
            for (p.bk = 0; p.bk < nsq; ++p.bk) {
                if (g.kingsTouch(p.wk, p.bk)) continue;
                forEachCfg([&](const Sq* cfg) {
                    for (int i = 0; i < m.np; ++i) p.wp[i] = cfg[i];
                    U64 i = index(p);
                    if (b[i] != V_UNKNOWN) return;
                    bool allWin = true;
                    U8 worst = 0;
                    genBlack(g, m, p, [&](Sq t, int cap) {
                        if (!allWin) return;
                        if (cap >= 0) {
                            U8 cv = capValue(p, t, cap);
                            if (!isDtm(cv)) { allWin = false; return; }
                            if (cv > worst) worst = cv;
                            return;
                        }
                        Pos q = p;
                        q.bk = t;
                        U8 v = w[index(q)];
                        if (!isDtm(v)) allWin = false;
                        else if (v > worst) worst = v;
                    });
                    if (allWin) { b[i] = (U8)(worst + 1); ++madeB; }
                });
            }
        // Quiet round: stop only once no seed can still be waiting above d.
        if (!madeW && !madeB && d >= seedMax) break;
    }

    // Whatever never resolved is drawn.
    for (U64 i = 0; i < w.size(); ++i) {
        if (w[i] == V_UNKNOWN) w[i] = V_DRAW;
        if (b[i] == V_UNKNOWN) b[i] = V_DRAW;
    }
}

U64 BruteForce::index(const Pos& p) const {
    U64 i = (U64)p.wk * g.nsq + p.bk;
    for (int k = 0; k < mat.np; ++k) i = i * g.nsq + p.wp[k];
    return i;
}

U8 BruteForce::at(const Pos& p, bool whiteToMove) const {
    U64 i = index(p);
    return whiteToMove ? w[i] : b[i];
}

Stats BruteForce::census() const {
    const int nsq = g.nsq;
    Stats s;
    s.histWFull.assign(MAX_PLY + 2, 0);
    Pos p;
    // Two alike pieces are one position stored twice, so count each unordered
    // configuration once; two unalike pieces are two distinct positions and
    // both must be counted.
    auto forEachCfg = [&](auto&& fn) {
        Sq cfg[MAXWP];
        if (mat.np == 1) {
            for (cfg[0] = 0; cfg[0] < nsq; ++cfg[0]) fn(cfg);
        } else if (mat.np == 3) {
            // Count each PHYSICAL placement once, which depends on which of
            // the three men are interchangeable: all three, the first two, or
            // none.  Counting every three-man material as an unordered triple
            // -- true only of KNNNK -- made this census exactly three times
            // too small for a queen, a queen and a rook.
            const CfgShape sh = cfgShapeOf(mat.eg);
            for (cfg[0] = 0; cfg[0] < nsq; ++cfg[0])
                for (cfg[1] = (sh == CfgShape::TripleOrdered ? 0 : cfg[0] + 1);
                     cfg[1] < nsq; ++cfg[1]) {
                    if (cfg[1] == cfg[0]) continue;
                    for (cfg[2] = (sh == CfgShape::TripleAlike ? cfg[1] + 1 : 0);
                         cfg[2] < nsq; ++cfg[2]) {
                        if (cfg[2] == cfg[0] || cfg[2] == cfg[1]) continue;
                        fn(cfg);
                    }
                }
        } else {
            for (cfg[0] = 0; cfg[0] < nsq; ++cfg[0])
                for (cfg[1] = mat.identical ? cfg[0] + 1 : 0; cfg[1] < nsq; ++cfg[1]) {
                    if (cfg[0] == cfg[1]) continue;
                    fn(cfg);
                }
        }
    };
    for (p.wk = 0; p.wk < nsq; ++p.wk)
        for (p.bk = 0; p.bk < nsq; ++p.bk)
            forEachCfg([&](const Sq* cfg) {
                for (int i = 0; i < mat.np; ++i) p.wp[i] = cfg[i];
                U64 i = index(p);
                U8 vw = w[i], vb = b[i];
                if (vw == V_DEAD && vb == V_DEAD) return;
                if (vw != V_DEAD) {
                    ++s.fwLive;
                    if (isDtm(vw)) {
                        ++s.fwWin;
                        ++s.histWFull[vw];
                        if (vw > s.maxPly) { s.maxPly = vw; s.longest = p; }
                    } else ++s.fwDraw;
                }
                if (vb != V_DEAD) {
                    ++s.fbLive;
                    if (isDtm(vb)) {
                        ++s.fbLoss;
                        // Same split as Table::computeStats: under capture
                        // rules a ply-0 loss is a mate or a stalemate, and only
                        // the check test tells them apart.
                        if (vb == 0) {
                            if (staleLoss_ && !blackInCheck(g, mat, p)) ++s.fbStaleLoss;
                            else                                       ++s.fbMate;
                        }
                    } else {
                        ++s.fbDraw;
                        int moves = 0;
                        bool grab = false;
                        genBlack(g, mat, p, [&](Sq, int cap) { ++moves; grab |= (cap >= 0); });
                        if (grab)        ++s.fbEnPrise;
                        else if (!moves) ++s.fbStale;
                    }
                }
            });
    return s;
}

U64 bruteForceCheck(const Table& t, bool progress) {
    const Geometry& g = t.geo;
    const Material& m = t.mat;
    const int nsq = g.nsq;
    BruteForce bf(g, m, t.sub, t.stalemateLoss, t.subAlt, t.subFor);

    // ---- every placement, both sides to move ------------------------------
    U64 bad = 0, checked = 0;
    int reported = 0;
    Pos p;
    auto describe = [&](const Pos& q) {
        std::string s = "wK=" + g.name(q.wk) + " bK=" + g.name(q.bk);
        for (int i = 0; i < m.np; ++i) s += " " + m.label(i) + "=" + g.name(q.wp[i]);
        return s;
    };
    for (p.wk = 0; p.wk < nsq; ++p.wk)
        for (p.bk = 0; p.bk < nsq; ++p.bk)
            for (p.wp[0] = 0; p.wp[0] < nsq; ++p.wp[0])
                for (p.wp[1] = 0; p.wp[1] < (m.np >= 2 ? nsq : 1); ++p.wp[1])
                for (p.wp[2] = 0; p.wp[2] < (m.np == 3 ? nsq : 1); ++p.wp[2])
                    for (int side = 0; side < 2; ++side) {
                        if (m.np >= 2 && p.wp[0] == p.wp[1]) continue;
                        if (m.np == 3 && (p.wp[0] == p.wp[2] || p.wp[1] == p.wp[2])) continue;
                        bool wtm = side == 0;
                        U8 want = bf.at(p, wtm);
                        U8 got  = t.valueAt(p, wtm);
                        ++checked;
                        if (want == got) continue;
                        ++bad;
                        if (reported++ < 12)
                            std::fprintf(stderr, "  BRUTE MISMATCH %s %s: table=%u brute=%u\n",
                                         describe(p).c_str(), wtm ? "wtm" : "btm", got, want);
                    }

    // ---- the whole-board census -------------------------------------------
    Stats bs = bf.census();
    const Stats& ts = t.st;
    struct { const char* what; U64 table, brute; } cmp[] = {
        { "white-to-move legal", ts.fwLive,    bs.fwLive    },
        { "white-to-move wins",  ts.fwWin,     bs.fwWin     },
        { "white-to-move draws", ts.fwDraw,    bs.fwDraw    },
        { "black-to-move legal", ts.fbLive,    bs.fbLive    },
        { "black-to-move losses",ts.fbLoss,    bs.fbLoss    },
        { "black-to-move draws", ts.fbDraw,    bs.fbDraw    },
        { "checkmates",          ts.fbMate,    bs.fbMate    },
        { "stalemate losses",    ts.fbStaleLoss, bs.fbStaleLoss },
        { "stalemates",          ts.fbStale,   bs.fbStale   },
        { "piece en prise",      ts.fbEnPrise, bs.fbEnPrise },
        { "deepest win (plies)", ts.maxPly,    bs.maxPly    },
    };
    for (auto& c : cmp) {
        if (c.table == c.brute) continue;
        ++bad;
        std::fprintf(stderr, "  BRUTE CENSUS %s: table=%llu brute=%llu\n", c.what,
                     (unsigned long long)c.table, (unsigned long long)c.brute);
    }
    for (size_t q = 0; q < ts.histWFull.size() && q < bs.histWFull.size(); ++q)
        if (ts.histWFull[q] != bs.histWFull[q]) {
            ++bad;
            std::fprintf(stderr, "  BRUTE HISTOGRAM ply %zu: table=%llu brute=%llu\n", q,
                         (unsigned long long)ts.histWFull[q],
                         (unsigned long long)bs.histWFull[q]);
        }

    if (progress)
        std::fprintf(stderr, "  brute force: %llu placements compared, %llu disagreements\n",
                     (unsigned long long)checked, (unsigned long long)bad);
    return bad;
}

} // namespace kqk
