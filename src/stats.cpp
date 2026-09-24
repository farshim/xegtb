// stats.cpp -- census of the finished table, both over symmetry classes and
// over the full board (each class weighted by the size of its D4 orbit, which
// is what published figures count).
#include "table.hpp"

#include <atomic>
#include <mutex>

namespace kqk {

// Black not in check and nothing of White's hanging.  Kept in step with
// sharedQuiet in explore.cpp; if one changes the other must.
static bool statsQuiet(const Table& t, const Pos& p) {
    if (blackInCheck(t.geo, t.mat, p)) return false;
    bool grab = false;
    genBlack(t.geo, t.mat, p, [&](Sq, int cap) { grab |= (cap >= 0); });
    return !grab;
}

void Table::computeStats(int threads, bool quiet) {
    const Geometry& g = geo;
    const U32 npc = idx.npc;
    const bool staleLoss = stalemateLoss;

    Stats total;
    total.slotsPerSide = idx.nslots;
    total.histW.assign(MAX_PLY + 2, 0);
    total.histWFull.assign(MAX_PLY + 2, 0);
    std::mutex mtx;

    parallelFor(idx.nkk, 64, threads, [&](U64 lo, U64 hi, int) {
        Stats loc;
        loc.histW.assign(MAX_PLY + 2, 0);
        loc.histWFull.assign(MAX_PLY + 2, 0);
        for (U64 kk = lo; kk < hi; ++kk) {
            Pos p;
            p.wk = idx.kkWk[kk];
            p.bk = idx.kkBk[kk];
            U64 base = kk * npc;
            for (U32 pc = 0; pc < npc; ++pc) {
                U8 vw = w[base + pc], vb = b[base + pc];
                if (vw == V_DEAD && vb == V_DEAD) continue;
                idx.decode(pc, p.wp);
                U64 orb = (U64)orbitSize(p);
                const bool isQ = quiet && statsQuiet(*this, p);
                if (isQ) {
                    loc.fQuiet += orb;
                    if (vw != V_DEAD) { if (isDtm(vw)) loc.fqwWin += orb; else loc.fqwDraw += orb; }
                    if (vb != V_DEAD) { if (isDtm(vb)) loc.fqbLoss += orb; else loc.fqbDraw += orb; }
                    if (vw != V_DEAD && isDtm(vw) && vw > loc.maxPlyQuiet) {
                        loc.maxPlyQuiet = vw; loc.longestQuiet = p;
                    }
                }

                if (vw != V_DEAD) {
                    ++loc.wLive; loc.fwLive += orb;
                    if (isDtm(vw)) {
                        ++loc.wWin; loc.fwWin += orb;
                        ++loc.histW[vw]; loc.histWFull[vw] += orb;
                        if (vw > loc.maxPly) {
                            loc.maxPly = vw; loc.longest = p;
                            loc.longestSlot = base + pc;
                        }
                    } else { ++loc.wDraw; loc.fwDraw += orb; }
                }
                if (vb != V_DEAD) {
                    ++loc.bLive; loc.fbLive += orb;
                    if (isDtm(vb)) {
                        ++loc.bLoss; loc.fbLoss += orb;
                        if (vb == 0) {
                            // Under capture rules a ply-0 loss is a mate or a
                            // stalemate, and only the check test tells them
                            // apart.  Under the ordinary rules a stalemate is
                            // a draw and never reaches here, so the test costs
                            // nothing and the two counts stay separate.
                            if (staleLoss && !blackInCheck(g, mat, p)) {
                                ++loc.bStaleLoss; loc.fbStaleLoss += orb;
                            } else { ++loc.bMate; loc.fbMate += orb; }
                        }
                    } else {
                        ++loc.bDraw; loc.fbDraw += orb;
                        int moves = 0;
                        bool grab = false;
                        genBlack(g, mat, p, [&](Sq, int cap) { ++moves; grab |= (cap >= 0); });
                        if (grab)        { ++loc.bEnPrise; loc.fbEnPrise += orb; }
                        else if (!moves) { ++loc.bStale;   loc.fbStale   += orb; }
                    }
                }
            }
        }
        std::lock_guard<std::mutex> lk(mtx);
        total.wLive += loc.wLive; total.wWin += loc.wWin; total.wDraw += loc.wDraw;
        total.bLive += loc.bLive; total.bLoss += loc.bLoss; total.bDraw += loc.bDraw;
        total.bMate += loc.bMate; total.bStale += loc.bStale; total.bEnPrise += loc.bEnPrise;
        total.bStaleLoss += loc.bStaleLoss; total.fbStaleLoss += loc.fbStaleLoss;
        total.fwLive += loc.fwLive; total.fwWin += loc.fwWin; total.fwDraw += loc.fwDraw;
        total.fbLive += loc.fbLive; total.fbLoss += loc.fbLoss; total.fbDraw += loc.fbDraw;
        total.fbMate += loc.fbMate; total.fbStale += loc.fbStale; total.fbEnPrise += loc.fbEnPrise;
        total.fQuiet += loc.fQuiet;
        total.fqwWin += loc.fqwWin; total.fqwDraw += loc.fqwDraw;
        total.fqbLoss += loc.fqbLoss; total.fqbDraw += loc.fqbDraw;
        if (loc.maxPlyQuiet > total.maxPlyQuiet) {
            total.maxPlyQuiet = loc.maxPlyQuiet;
            total.longestQuiet = loc.longestQuiet;
        }
        for (size_t i = 0; i < loc.histW.size(); ++i) {
            total.histW[i] += loc.histW[i];
            total.histWFull[i] += loc.histWFull[i];
        }
        // Deterministic tie-break, so two runs produce the same file.
        if (loc.maxPly > total.maxPly ||
            (loc.maxPly == total.maxPly && loc.longestSlot < total.longestSlot)) {
            total.maxPly = loc.maxPly;
            total.longest = loc.longest;
            total.longestSlot = loc.longestSlot;
        }
    });

    total.quietCensus = quiet;
    st = std::move(total);
}

} // namespace kqk
