// probe.cpp -- lookups, optimal move selection and principal variations.
#include "table.hpp"

namespace kqk {

ProbeResult Table::probe(const Pos& p, bool whiteToMove) const {
    ProbeResult r;
    U8 v = valueAt(p, whiteToMove);
    if (v == V_DEAD) return r;                       // Outcome::Illegal
    if (!isDtm(v)) { r.outcome = Outcome::Draw; return r; }
    r.outcome = whiteToMove ? Outcome::Win : Outcome::Loss;
    r.plies = v;
    r.moves = (v + 1) / 2;                           // white moves left until mate
    return r;
}

bool Table::bestMove(const Pos& p, bool whiteToMove, Move& out) const {
    U8 here = valueAt(p, whiteToMove);
    if (here == V_DEAD) return false;
    bool found = false;

    if (whiteToMove) {
        // Winning: shortest mate.  Drawn: any move that keeps the draw and
        // does not hang a piece for nothing.
        int best = -1;
        genWhite(geo, mat, p, [&](const Pos& q) {
            U8 c = valueAt(q, false);
            if (c == V_DEAD) return;
            if (isDtm(here)) {
                if (isDtm(c) && (best < 0 || c < best)) {
                    best = c; out = { q, -1 }; found = true;
                }
            } else if (!found) {
                out = { q, -1 }; found = true;
            }
        });
    } else {
        // Lost: resist as long as possible.  Drawn: take a piece if we can,
        // otherwise any move that holds the draw.
        int best = -1;
        genBlack(geo, mat, p, [&](Sq t, int cap) {
            Pos q = p;
            q.bk = t;
            if (isDtm(here)) {
                if (cap >= 0) return;
                U8 c = valueAt(q, true);
                if (isDtm(c) && c > best) { best = c; out = { q, -1 }; found = true; }
            } else {
                if (cap >= 0) {
                    q.wp[cap] = -1;
                    out = { q, cap }; found = true; best = 1 << 30;
                    return;
                }
                if (best == 1 << 30) return;
                U8 c = valueAt(q, true);
                if (!isDtm(c) && !found) { out = { q, -1 }; found = true; }
            }
        });
    }
    return found;
}

std::vector<Move> Table::principalVariation(const Pos& start, bool whiteToMove) const {
    std::vector<Move> pv;
    Pos p = start;
    U8 v = valueAt(p, whiteToMove);
    if (!isDtm(v)) return pv;                    // only mate lines are forced
    int guard = (int)v + 4;
    while (guard-- > 0) {
        Move m;
        if (!bestMove(p, whiteToMove, m)) break;
        pv.push_back(m);
        p = m.after;
        whiteToMove = !whiteToMove;
        U8 nv = valueAt(p, whiteToMove);
        if (nv == 0) break;                      // mate delivered
        if (!isDtm(nv)) break;
    }
    return pv;
}

} // namespace kqk
