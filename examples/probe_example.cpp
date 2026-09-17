// examples/probe_example.cpp -- using the tablebase as a library.
//
// Builds each endgame in memory and probes it.  Only the Table constructor
// mentions which one; every call after that is identical, because a position
// is always (white king, black king, White's pieces) and the Material says how
// many of the last there are and what they are.
//
//   c++ -std=c++20 -O2 -Isrc examples/probe_example.cpp \
//       src/solver.cpp src/stats.cpp src/verify.cpp src/probe.cpp \
//       src/brute.cpp src/kqkk.cpp src/io.cpp -o probe_example && ./probe_example
#include "table.hpp"

#include <cstdio>
#include <thread>

using namespace kqk;

namespace {

std::string describe(const Geometry& g, const Material& m, const Pos& p) {
    std::string s = "wK=" + g.name(p.wk);
    for (int i = 0; i < m.np; ++i) s += " " + m.label(i) + "=" + g.name(p.wp[i]);
    return s + " bK=" + g.name(p.bk);
}

// A cornered black king on a1, with White's men placed so that each endgame
// gets its characteristic mating net.
struct Case { const char* wk; const char* wp[2]; const char* bk; bool wtm; };

const Case kqkCases[] = {
    { "a1", { "b2", nullptr }, "f5", true  },   // an ordinary winning position
    { "a1", { "c3", nullptr }, "d4", false },   // black to move, the queen is loose
    { "c3", { "b2", nullptr }, "a1", false },   // mate: the queen covers the diagonal
};
const Case krkCases[] = {
    { "a1", { "b2", nullptr }, "f5", true  },
    { "a1", { "c3", nullptr }, "d4", false },
    { "c3", { "b2", nullptr }, "a1", false },   // stalemate: a rook misses a1
};
const Case kbbkCases[] = {
    { "a1", { "b2", "c4" },    "f5", true  },   // opposite colours: a win
    { "a1", { "b2", "d4" },    "f5", true  },   // same colour: a draw, always
    { "c2", { "b2", "c4" },    "a1", false },   // the two-bishop corner mate
};
const Case kbnkCases[] = {
    { "a1", { "e1", "h6" },    "c1", true  },   // the deepest 8x8 position
    { "b1", { "e1", "c2" },    "d1", false },   // the knight defends the bishop,
                                                // so Kxe1 is not a move at all
    { "a1", { "e1", "e3" },    "d1", false },   // here it really is loose: a draw
};

void run(Endgame eg, const Case* cases, int ncases, int n, int threads) {
    Table tb(n, eg);
    tb.generate(threads, /*progress=*/false);
    const Geometry& g = tb.geo;
    const Material& m = tb.mat;

    std::printf("=== %dx%d %s: %llu king pairs, %llu placements each,"
                " deepest win = mate in %u ===\n",
                n, n, m.name(), (unsigned long long)tb.idx.nkk,
                (unsigned long long)tb.idx.npc, (tb.st.maxPly + 1) / 2);

    for (int c = 0; c < ncases; ++c) {
        const Case& t = cases[c];
        Pos p;
        p.wk = g.parse(t.wk);
        p.bk = g.parse(t.bk);
        for (int i = 0; i < m.np; ++i) p.wp[i] = g.parse(t.wp[i]);

        ProbeResult r = tb.probe(p, t.wtm);
        std::printf("  %-34s %s to move -> ", describe(g, m, p).c_str(),
                    t.wtm ? "white" : "black");
        switch (r.outcome) {
            case Outcome::Win:     std::printf("white mates in %d\n", r.moves); break;
            case Outcome::Loss:    std::printf("black is mated in %d\n", r.moves); break;
            case Outcome::Draw:    std::printf("draw\n"); break;
            case Outcome::Illegal: std::printf("illegal position\n"); break;
        }
        Move mv;
        if (r.outcome != Outcome::Illegal && tb.bestMove(p, t.wtm, mv)) {
            std::printf("      best move: ");
            if (t.wtm) {
                if (mv.after.wk != p.wk) std::printf("K%s\n", g.name(mv.after.wk).c_str());
                else for (int i = 0; i < m.np; ++i)
                    if (mv.after.wp[i] != p.wp[i])
                        std::printf("%c%s\n", m.letter(i), g.name(mv.after.wp[i]).c_str());
            } else {
                std::printf("k%s%s\n", mv.captured >= 0 ? "x" : "",
                            g.name(mv.after.bk).c_str());
            }
        }
    }

    // Walk the deepest win in the whole table.
    std::printf("  deepest position: %s, white to move\n",
                describe(g, m, tb.st.longest).c_str());
    auto pv = tb.principalVariation(tb.st.longest, true);
    std::printf("  optimal play takes %zu plies\n\n", pv.size());
}

// KQKK does not share the Table class, because Black has two kings: a position
// is PosKK{wk, wq, bk1, bk2} and the table is TableKQKK.  Everything after the
// constructor reads the same -- probe, bestMove, principalVariation.
struct CaseKK { const char* wk; const char* wq; const char* bk1; const char* bk2; };

const CaseKK kqkkCases[] = {
    { "c3", "c2", "a2", "b1" },   // the queen forks both kings and her king guards her
    { "a1", "b1", "c1", "d1" },   // only one king is mated, so it is a draw
    { "a1", "d4", "d2", "f2" },   // the queen mates both alone, neither king on the rim
};

void runKqkk(int n, int threads, KkRules rules) {
    TableKQKK tb(n, rules);
    tb.generate(threads, /*progress=*/false);
    const Geometry& g = tb.geo;

    std::printf("=== %dx%d KQKK, %s rules: %llu king triples, %llu queen squares each,"
                " deepest win = mate in %u ===\n", n, n, kkRulesName(rules),
                (unsigned long long)tb.idx.nblk, (unsigned long long)tb.idx.npc,
                (tb.st.maxPly + 1) / 2);

    for (const CaseKK& t : kqkkCases) {
        const PosKK p{ g.parse(t.wk), g.parse(t.wq), g.parse(t.bk1), g.parse(t.bk2) };
        // Black to move: these are the positions the rule is about.
        const ProbeResult r = tb.probe(p, /*whiteToMove=*/false);
        std::printf("  wK=%s wQ=%s bK=%s bK=%s  black to move -> ",
                    g.name(p.wk).c_str(), g.name(p.wq).c_str(),
                    g.name(p.bk1).c_str(), g.name(p.bk2).c_str());
        switch (r.outcome) {
            case Outcome::Loss:
                std::printf(r.plies ? "black is mated in %d\n" : "both kings mated\n",
                            r.moves);
                break;
            case Outcome::Draw:    std::printf("draw\n"); break;
            case Outcome::Illegal: std::printf("illegal position\n"); break;
            default:               std::printf("white wins in %d\n", r.moves); break;
        }
    }

    std::printf("  deepest position: wK=%s wQ=%s bK=%s bK=%s, white to move\n",
                g.name(tb.st.longest.wk).c_str(), g.name(tb.st.longest.wq).c_str(),
                g.name(tb.st.longest.bk1).c_str(), g.name(tb.st.longest.bk2).c_str());
    const auto pv = tb.principalVariation(tb.st.longest, true);
    std::printf("  optimal play takes %zu plies\n\n", pv.size());
}

} // namespace

int main() {
    const int threads = (int)std::thread::hardware_concurrency();
    // KBBK is a four-man table, so it gets a smaller board for the same memory.
    run(Endgame::KQK,  kqkCases,  3, 12, threads);
    run(Endgame::KRK,  krkCases,  3, 12, threads);
    run(Endgame::KBBK, kbbkCases, 3, 10, threads);
    run(Endgame::KBNK, kbnkCases, 3,  8, threads);
    // The two readings of "a mate counts only when both kings are mated".
    runKqkk(8, threads, KkRules::Strict);
    runKqkk(8, threads, KkRules::Loose);
    return 0;
}
