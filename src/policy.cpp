// policy.cpp -- a table-free mating rule for KQK, and its exhaustive scorer.
//
// The rule is a pure function of the position: no tablebase, no memory of the
// game so far, no dependence on the board size.  To score it we build the
// unreduced state graph, fix White's move to whatever the rule says, let Black
// play anything at all, and compute the worst case by backward induction over
// the induced graph.  A position from which the rule never mates -- because
// play cycles, or because the rule runs out of moves -- is a failure and is
// counted.  Every legal placement is scored; nothing is sampled.
#include "table.hpp"

#include <array>
#include <cstring>
#include <vector>

namespace kqk {
namespace {

constexpr U8 P_UNKNOWN = 254, P_FAILED = 255;

// How small the cage has to get before the rule stops steering and simply
// searches out the mate (measured as its semi-perimeter), and how deep that
// search is allowed to go.
constexpr int CAGE_SMALL = 6;
constexpr int MATE_DEPTH = 5;
// How long a 1-wide cage has to be before the king escorts the queen along it
// instead of walking to the corner.
constexpr int STRIP = 7;

// The rule.  Everything it knows is derived from the queen's cage.
struct Rule {
    const Geometry& g;
    Material mat;
    int n, nsq;
    const Table* tb = nullptr;      // only for the oracle control
    bool oracle = false;

    Rule(const Geometry& geo)
        : g(geo), mat(Material::of(Endgame::KQK)), n(geo.n), nsq(geo.nsq) {}

    U64 ix(Sq wk, Sq bk, Sq wq) const { return ((U64)wk * nsq + bk) * nsq + wq; }

    // ---- the cage ---------------------------------------------------------
    // The queen's file and rank cut the board into four rectangles; the black
    // king sits in one of them and cannot cross either line, because the queen
    // attacks every square of both.  (Every square, that is, unless the white
    // king is standing on one of them -- so `sound` below checks the cage
    // really is preserved rather than taking it on trust.)
    bool caged(Sq q, Sq k) const {
        return g.file(q) != g.file(k) && g.rank(q) != g.rank(k);
    }
    void rect(Sq q, Sq k, int& x0, int& x1, int& y0, int& y1) const {
        int qx = g.file(q), qy = g.rank(q), bx = g.file(k), by = g.rank(k);
        if (bx < qx) { x0 = 0; x1 = qx - 1; } else { x0 = qx + 1; x1 = n - 1; }
        if (by < qy) { y0 = 0; y1 = qy - 1; } else { y0 = qy + 1; y1 = n - 1; }
    }
    int area(Sq q, Sq k) const {
        if (!caged(q, k)) return 4 * n * n;
        int x0, x1, y0, y1; rect(q, k, x0, x1, y0, y1);
        return (x1 - x0 + 1) * (y1 - y0 + 1);
    }
    int semiPerim(Sq q, Sq k) const {
        if (!caged(q, k)) return 4 * n;
        int x0, x1, y0, y1; rect(q, k, x0, x1, y0, y1);
        return (x1 - x0 + 1) + (y1 - y0 + 1);
    }
    // The progress measure: cage area, with semi-perimeter to break ties --
    // at equal area a 3x4 cage is a better cage than a 2x6 one.
    long measure(Sq q, Sq k) const {
        if (!caged(q, k)) return (long)(8 * n * n) * 1000;
        int x0, x1, y0, y1; rect(q, k, x0, x1, y0, y1);
        int w = x1 - x0 + 1, h = y1 - y0 + 1;
        return (long)w * h * 1000 + (w + h);
    }
    long rectKey(Sq q, Sq k) const {
        if (!caged(q, k)) return -1;
        int x0, x1, y0, y1; rect(q, k, x0, x1, y0, y1);
        return ((long)x0 * n + x1) * n * n + (long)y0 * n + y1;
    }
    int clampSq(int v) const { return v < 0 ? 0 : (v > n - 1 ? n - 1 : v); }
    // The post the white king walks to.  Normally two squares in from the
    // cage's own board corner, diagonally -- the square you mate from.
    //
    // A long thin cage is the exception, and getting it wrong is what breaks
    // the rule outright.  In a strip the board corner can be at the far end
    // from the black king, so a king that walks to it has achieved nothing;
    // meanwhile the queen cannot advance along the strip, because every square
    // she would advance to stands next to the black king and would simply be
    // taken.  What she needs is an escort, so the post becomes the square
    // beside her next advance: one step back from the strip, one step along it.
    // Like the corner post it is a function of the cage alone.
    Sq post(Sq q, Sq k) const {
        int qx = g.file(q), qy = g.rank(q), bx = g.file(k), by = g.rank(k);
        int cx = bx < qx ? 0 : n - 1, cy = by < qy ? 0 : n - 1;
        int dx = bx < qx ? 1 : -1,    dy = by < qy ? 1 : -1;
        int x0, x1, y0, y1; rect(q, k, x0, x1, y0, y1);
        int w = x1 - x0 + 1, h = y1 - y0 + 1;
        if (w == 1 && h >= STRIP) return g.sq(clampSq(qx + dx), clampSq(qy - dy));
        if (h == 1 && w >= STRIP) return g.sq(clampSq(qx - dx), clampSq(qy + dy));
        return g.sq(clampSq(cx + 2 * dx), clampSq(cy + 2 * dy));
    }
    int cheb(Sq a, Sq b) const {
        int dx = g.file(a) - g.file(b), dy = g.rank(a) - g.rank(b);
        if (dx < 0) dx = -dx; if (dy < 0) dy = -dy; return dx > dy ? dx : dy;
    }
    int manh(Sq a, Sq b) const {
        int dx = g.file(a) - g.file(b), dy = g.rank(a) - g.rank(b);
        if (dx < 0) dx = -dx; if (dy < 0) dy = -dy; return dx + dy;
    }
    // (chebyshev, manhattan) distance from the white king to the post, packed.
    long kdist(Sq wk, Sq q, Sq k) const {
        if (!caged(q, k)) return (long)cheb(wk, k) * 1000 + manh(wk, k);
        Sq t = post(q, k);
        return (long)cheb(wk, t) * 1000 + manh(wk, t);
    }

    // ---- move tests -------------------------------------------------------
    void blackInfo(const Pos& p, int& moves, bool& grabs) const {
        moves = 0; grabs = false;
        genBlack(g, mat, p, [&](Sq, int cap) { ++moves; if (cap >= 0) grabs = true; });
    }
    bool isMate(const Pos& q) const {
        int mv; bool gr; blackInfo(q, mv, gr);
        return mv == 0 && blackInCheck(g, mat, q);
    }
    // A White move is sound when, after it: Black cannot take the queen; Black
    // has a move; the cage is well defined; no black reply changes the cage;
    // and no black reply reaches a square with no move at all.  That last
    // clause matters -- such a square is not stalemate, because it is White to
    // move, but it forces White to open the cage on the next move.
    bool sound(const Pos& q, long rk) const {
        int mv; bool gr; blackInfo(q, mv, gr);
        if (mv == 0 || gr) return false;
        if (!caged(q.wp[0], q.bk)) return false;
        bool ok = true;
        genBlack(g, mat, q, [&](Sq to, int cap) {
            if (!ok || cap >= 0) return;
            if (rectKey(q.wp[0], to) != rk) { ok = false; return; }
            Pos r = q; r.bk = to;
            int m2; bool g2; blackInfo(r, m2, g2);
            if (m2 == 0) ok = false;
        });
        return ok;
    }
    // Forced mate in at most k White moves, over sound moves that never grow
    // the cage.  Cheap: it only runs once the cage is small.
    bool mateIn(const Pos& p, int k, Pos* out, long cap) const {
        bool done = false;
        genWhite(g, mat, p, [&](const Pos& q) {
            if (!done && isMate(q)) { done = true; if (out) *out = q; }
        });
        if (done || k <= 1) return done;
        const long a0 = measure(p.wp[0], p.bk);
        const long lim = cap < a0 ? cap : a0;
        genWhite(g, mat, p, [&](const Pos& q) {
            if (done) return;
            long rk = rectKey(q.wp[0], q.bk);
            if (!sound(q, rk)) return;
            if (measure(q.wp[0], q.bk) > lim) return;
            bool all = true;
            genBlack(g, mat, q, [&](Sq to, int cap2) {
                if (!all) return;
                if (cap2 >= 0) { all = false; return; }
                Pos r = q; r.bk = to;
                if (!mateIn(r, k - 1, nullptr, lim)) all = false;
            });
            if (all) { done = true; if (out) *out = q; }
        });
        return done;
    }
    // How hemmed in Black is -- a tie-break only.
    int squeeze(const Pos& p) const {
        int mv; bool gr; blackInfo(p, mv, gr);
        return 10 * cheb(p.wk, p.bk) + mv;
    }

    // ---- the rule itself --------------------------------------------------
    // `fired` receives which of the six rules produced the move.
    bool choose(const Pos& p, Pos& out, int* fired = nullptr) const {
        if (oracle) {
            Move m;
            if (!tb->bestMove(p, true, m)) return false;
            out = m.after; if (fired) *fired = 0; return true;
        }
        const long a0 = measure(p.wp[0], p.bk);
        const long k0 = kdist(p.wk, p.wp[0], p.bk);
        // 1-2.  Mate, or search the endgame out.  The iterative deepening is
        // essential: at a fixed depth "mate in at most five" can stay true
        // forever while the pieces shuffle.  Taking the smallest k that works
        // forces the bound itself down by one every move.
        if (semiPerim(p.wp[0], p.bk) <= CAGE_SMALL) {
            Pos m;
            for (int k = 1; k <= MATE_DEPTH; ++k)
                if (mateIn(p, k, &m, a0)) {
                    out = m; if (fired) *fired = (k == 1 ? 1 : 2); return true;
                }
        }
        int bestTier = 9; long bestKey = 0; bool found = false;
        genWhite(g, mat, p, [&](const Pos& q) {
            if (bestTier == 0) return;
            if (isMate(q)) { bestTier = 0; out = q; found = true; return; }
            long rk = rectKey(q.wp[0], q.bk);
            if (!sound(q, rk)) return;
            const long a1 = measure(q.wp[0], q.bk);
            const long k1 = kdist(q.wk, q.wp[0], q.bk);
            int tier; long key;
            if (a1 < a0)                  // 3. squeeze
                { tier = 1; key = a1 * 100000 + k1; }
            else if (a1 == a0 && k1 < k0) // 4. walk the king in
                { tier = 2; key = k1; }
            else if (a1 == a0)            // 5. wait
                { tier = 3; key = squeeze(q); }
            else return;                  // never let the cage grow
            if (tier < bestTier || (tier == bestTier && key < bestKey)) {
                bestTier = tier; bestKey = key; out = q; found = true;
            }
        });
        if (found) { if (fired) *fired = bestTier == 0 ? 1 : bestTier + 2; return true; }
        // 6.  Nothing sound: any legal move that neither hangs the queen nor
        // stalemates.  Reached from about one position in three hundred.
        genWhite(g, mat, p, [&](const Pos& q) {
            if (found) return;
            int mv; bool gr; blackInfo(q, mv, gr);
            if (mv == 0 || gr) return;
            out = q; found = true;
        });
        if (found && fired) *fired = 6;
        return found;
    }
};

} // namespace

PolicyScore policyScore(int n, bool oracle, int threads) {
    Geometry g(n);
    Rule R(g);
    const int nsq = g.nsq;
    const U64 N = (U64)nsq * nsq * nsq;

    Table tb(n, Endgame::KQK);
    tb.generate(threads, false);
    R.tb = &tb; R.oracle = oracle;

    std::vector<U8> vW(N, P_UNKNOWN), vB(N, P_UNKNOWN);
    std::vector<int32_t> succ(N, -1);
    std::vector<std::array<U64, 7>> hits(threads);
    for (auto& h : hits) h.fill(0);

    // ---- classify every placement, and precompute the rule's move ---------
    parallelFor((U64)nsq, 1, threads, [&](U64 lo, U64 hi, int tid) {
        Pos p;
        for (U64 wk = lo; wk < hi; ++wk) {
            p.wk = (Sq)wk;
            for (p.bk = 0; p.bk < nsq; ++p.bk) {
                if (g.kingsTouch(p.wk, p.bk)) continue;
                for (p.wp[0] = 0; p.wp[0] < nsq; ++p.wp[0]) {
                    if (p.wp[0] == p.wk || p.wp[0] == p.bk) continue;
                    U64 i = R.ix(p.wk, p.bk, p.wp[0]);
                    int moves; bool grabs; R.blackInfo(p, moves, grabs);
                    bool chk = blackInCheck(g, R.mat, p);
                    if (moves == 0)   vB[i] = chk ? 0 : P_FAILED;  // mate : stalemate
                    else if (grabs)   vB[i] = P_FAILED;            // the queen falls
                    if (chk) { vW[i] = P_FAILED; continue; }       // illegal with wtm
                    Pos q; int fired = 6;
                    if (!R.choose(p, q, &fired)) { vW[i] = P_FAILED; continue; }
                    ++hits[tid][fired == 0 ? 0 : fired - 1];
                    succ[i] = (int32_t)R.ix(q.wk, q.bk, q.wp[0]);
                }
            }
        }
    });

    // ---- backward induction over the induced graph ------------------------
    for (int round = 0; round < 8 * n + 80; ++round) {
        bool changed = false;
        for (U64 i = 0; i < N; ++i)
            if (vW[i] == P_UNKNOWN && succ[i] >= 0) {
                U8 v = vB[succ[i]];
                if (v < P_UNKNOWN) { vW[i] = (U8)(v + 1); changed = true; }
            }
        Pos p;
        for (p.wk = 0; p.wk < nsq; ++p.wk)
        for (p.bk = 0; p.bk < nsq; ++p.bk) {
            if (g.kingsTouch(p.wk, p.bk)) continue;
            for (p.wp[0] = 0; p.wp[0] < nsq; ++p.wp[0]) {
                if (p.wp[0] == p.wk || p.wp[0] == p.bk) continue;
                U64 i = R.ix(p.wk, p.bk, p.wp[0]);
                if (vB[i] != P_UNKNOWN) continue;
                U8 worst = 0; bool all = true;
                genBlack(g, R.mat, p, [&](Sq to, int cap) {
                    if (!all) return;
                    if (cap >= 0) { all = false; return; }
                    U8 v = vW[R.ix(p.wk, to, p.wp[0])];
                    if (v >= P_UNKNOWN) { all = false; return; }
                    if (v > worst) worst = v;
                });
                if (all) { vB[i] = worst; changed = true; }
            }
        }
        if (!changed) break;
    }

    // ---- score ------------------------------------------------------------
    PolicyScore s;
    s.n = n;
    s.optimum = (int)((tb.st.maxPly + 1) / 2);
    for (auto& h : hits) for (int r = 0; r < 7; ++r) s.rule[r] += h[r];
    Pos p;
    for (p.wk = 0; p.wk < nsq; ++p.wk)
    for (p.bk = 0; p.bk < nsq; ++p.bk) {
        if (g.kingsTouch(p.wk, p.bk)) continue;
        for (p.wp[0] = 0; p.wp[0] < nsq; ++p.wp[0]) {
            if (p.wp[0] == p.wk || p.wp[0] == p.bk) continue;
            if (blackInCheck(g, R.mat, p)) continue;
            ++s.positions;
            U8 v = vW[R.ix(p.wk, p.bk, p.wp[0])];
            if (v == P_FAILED)  { if (!s.stuck && !s.cyclic) s.failPos = p; ++s.stuck;  continue; }
            if (v == P_UNKNOWN) { if (!s.stuck && !s.cyclic) s.failPos = p; ++s.cyclic; continue; }
            if (v > s.worst) { s.worst = v; s.worstPos = p; }
        }
    }

    // ---- the worst-case line, or the line that goes wrong -----------------
    {
        Pos c = (s.stuck || s.cyclic) ? s.failPos : s.worstPos;
        const bool failing = (s.stuck || s.cyclic);
        for (int t = 0; t < 4 * n + 40; ++t) {
            Pos q;
            if (!R.choose(c, q)) break;
            s.line.push_back(q);
            s.cage.push_back(R.area(q.wp[0], q.bk));
            int mv; bool gr; R.blackInfo(q, mv, gr);
            if (mv == 0) break;                       // mate
            // Follow the reply that beats the rule: an unresolved successor
            // if the rule fails here, otherwise the slowest resolved one.
            Pos nb = q; int bw = -1; bool tookBad = false;
            genBlack(g, R.mat, q, [&](Sq to, int cap) {
                if (cap >= 0 || tookBad) return;
                Pos r = q; r.bk = to;
                U8 v = vW[R.ix(r.wk, r.bk, r.wp[0])];
                if (failing && v >= P_UNKNOWN) { nb = r; tookBad = true; return; }
                if ((int)v > bw) { bw = (int)v; nb = r; }
            });
            c = nb;
            if (failing && (int)s.line.size() > 3 * n + 24) break;
        }
    }
    return s;
}

} // namespace kqk
