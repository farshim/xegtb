// monotone.cpp -- is there a WHITE strategy under which the mating net never
// grows?
//
// Board n x n, K white kings, one black king, capture-the-king rules.
//
// The net.  Free(W) = { squares at Chebyshev distance >= 2 from every white
// king }.  Phi(W,b) = size of the connected component of Free(W) that holds
// the black king, and 0 when the black king stands beside a white king.
//
// Two facts make Phi a clean potential:
//   * Black cannot change it.  A black move goes to a neighbour of b; if that
//     neighbour is free it lies in the same component, so Phi is unchanged,
//     and if it is not free then White captures next move.
//   * Black can never capture while Phi >= 1, because every white king is
//     then at distance >= 2 from him.  So no white king is ever en prise.
//
// The game solved here.  White to move at (W,b) with Phi >= 1.  White must
// play a king move with 1 <= Phi(W',b) <= Phi(W,b): the net may shrink or
// stay, never grow, and never opens (Phi = 0 is forbidden, which is what
// keeps Black from taking anything).  White WINS the moment a move leaves
// Phi(W',b) = 1: the black king's only free square is the one he stands on,
// so his reply puts him beside a white king and White takes him.
//
// GAP(W,b) = the number of White moves needed, worst case, to force the net
// to shrink strictly at least once (or to win outright).  It is computed
// level by level in increasing Phi, and inside a level by rounds, which is
// the usual attractor computation for a reachability game.  max GAP over the
// table is the constant c in "the net shrinks at least every c White moves".
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <string>
#include <thread>
#include <vector>
#include <unordered_map>
using namespace std;
using U8 = uint8_t; using U16 = uint16_t; using U32 = uint32_t; using U64 = uint64_t;

static int n, m, K, NTHR = 8;
static U64 NW;
static vector<U8>  wset;   // NW * K
static vector<U16> PHI;    // NW * m
static vector<U8>  GAP;    // NW * m, 0 = White has no monotone win
static vector<int> nbr, ncnt;
static U64 Cb[512][8];

static inline U64 rankSet(const int* a, int k) { U64 r = 0; for (int i = 0; i < k; ++i) r += Cb[a[i]][i + 1]; return r; }
static bool nextCombo(int* a, int k, int mm) {
    for (int i = 0; i < k; ++i) {
        int lim = (i + 1 < k) ? a[i + 1] : mm;
        if (a[i] + 1 < lim) { ++a[i]; for (int j = 0; j < i; ++j) a[j] = j; return true; }
    }
    return false;
}
static void unrank(U64 r, int k, int* a) {
    for (int i = k - 1; i >= 0; --i) {
        int x = i;
        while (Cb[x + 1][i + 1] <= r) ++x;
        a[i] = x; r -= Cb[x][i + 1];
    }
}
static string sqname(int s) {
    int f = s % n, r = s / n;
    if (n <= 26) return string(1, char('a' + f)) + to_string(r + 1);
    return to_string(f) + "," + to_string(r);
}
static int parseSq(const string& t) {
    if (isalpha((unsigned char)t[0])) return (atoi(t.c_str() + 1) - 1) * n + (t[0] - 'a');
    size_t c = t.find(','); return atoi(t.c_str() + c + 1) * n + atoi(t.c_str());
}
template <class F> static void par(U64 lo, U64 hi, F f) {
    vector<thread> th; U64 chunk = (hi - lo + NTHR - 1) / NTHR;
    for (int i = 0; i < NTHR; ++i) {
        U64 a = min(hi, lo + (U64)i * chunk), b = min(hi, a + chunk);
        if (a < b) th.emplace_back(f, a, b);
    }
    for (auto& t : th) t.join();
}
static inline U8 gapAt(U64 i) { return std::atomic_ref<U8>(GAP[i]).load(memory_order_relaxed); }
static inline void gapSet(U64 i, U8 v) { std::atomic_ref<U8>(GAP[i]).store(v, memory_order_relaxed); }

// Phi for every (white set, square).
static void buildPHI() {
    par(0, NW, [](U64 lo, U64 hi) {
        int a[8];
        unrank(lo, K, a);
        vector<U8> blk(m); vector<int> comp(m), stk(m), csz;
        for (U64 wr = lo; wr < hi; ++wr) {
            for (int i = 0; i < K; ++i) wset[wr * K + i] = (U8)a[i];
            fill(blk.begin(), blk.end(), 0);
            for (int i = 0; i < K; ++i) {
                int f = a[i] % n, r = a[i] / n;
                for (int df = -1; df <= 1; ++df)
                    for (int dr = -1; dr <= 1; ++dr) {
                        int ff = f + df, rr = r + dr;
                        if (ff >= 0 && ff < n && rr >= 0 && rr < n) blk[rr * n + ff] = 1;
                    }
            }
            fill(comp.begin(), comp.end(), -1); csz.clear();
            for (int s = 0; s < m; ++s) {
                if (blk[s] || comp[s] >= 0) continue;
                int id = (int)csz.size(); csz.push_back(0);
                int sp = 0, cnt = 0; stk[sp++] = s; comp[s] = id;
                while (sp) {
                    int x = stk[--sp]; ++cnt;
                    for (int d = 0; d < ncnt[x]; ++d) {
                        int y = nbr[x * 8 + d];
                        if (!blk[y] && comp[y] < 0) { comp[y] = id; stk[sp++] = y; }
                    }
                }
                csz[id] = cnt;
            }
            U64 base = wr * (U64)m;
            for (int s = 0; s < m; ++s) PHI[base + s] = blk[s] ? 0 : (U16)csz[comp[s]];
            if (wr + 1 < hi) nextCombo(a, K, m);
        }
    });
}

// White's moves from (W, b): the new white sets, with Phi(W',b) attached.
struct Cand { U64 wr2; U16 phi2; };
static inline int moves(U64 wr, int b, Cand* out) {
    const U8* W = &wset[wr * K];
    int cnt = 0, a[8];
    for (int j = 0; j < K; ++j) {
        int s = W[j];
        for (int d = 0; d < ncnt[s]; ++d) {
            int dst = nbr[s * 8 + d];
            bool own = false;
            for (int q = 0; q < K; ++q) if (q != j && W[q] == dst) { own = true; break; }
            if (own || dst == b) continue;
            for (int q = 0; q < K; ++q) a[q] = W[q];
            a[j] = dst;
            for (int i = 1; i < K; ++i) { int x = a[i], p = i - 1; while (p >= 0 && a[p] > x) { a[p + 1] = a[p]; --p; } a[p + 1] = x; }
            U64 wr2 = rankSet(a, K);
            out[cnt].wr2 = wr2; out[cnt].phi2 = PHI[wr2 * (U64)m + b]; ++cnt;
        }
    }
    return cnt;
}
// Worst black reply after White plays to wr2 with the king on b:
// 0 if some reply is still unresolved, else the largest GAP among replies
// (a reply that steps beside a white king counts 0 -- White just takes him).
static inline int worstReply(U64 wr2, int b, int cap) {
    int worst = 0;
    for (int d = 0; d < ncnt[b]; ++d) {
        int b2 = nbr[b * 8 + d];
        U64 i = wr2 * (U64)m + b2;
        if (PHI[i] == 0) continue;
        U8 g = gapAt(i);
        if (!g || g > cap) return -1;
        worst = max(worst, (int)g);
    }
    return worst;
}

int main(int argc, char** argv) {
    n = 8; K = 4; string start;
    for (int i = 1; i < argc; ++i) {
        string k = argv[i]; auto v = [&] { return string(argv[++i]); };
        if (k == "-n") n = atoi(v().c_str());
        else if (k == "-K") K = atoi(v().c_str());
        else if (k == "--threads") NTHR = atoi(v().c_str());
        else if (k == "--start") start = v();
    }
    m = n * n;
    for (int x = 0; x < 512; ++x) { Cb[x][0] = 1; for (int k = 1; k < 8; ++k) Cb[x][k] = x ? Cb[x - 1][k - 1] + Cb[x - 1][k] : 0; }
    NW = Cb[m][K];
    nbr.assign((size_t)m * 8, 0); ncnt.assign(m, 0);
    for (int r = 0; r < n; ++r) for (int f = 0; f < n; ++f) {
        int s = r * n + f, c = 0;
        for (int df = -1; df <= 1; ++df) for (int dr = -1; dr <= 1; ++dr) {
            if (!df && !dr) continue;
            int ff = f + df, rr = r + dr;
            if (ff >= 0 && ff < n && rr >= 0 && rr < n) nbr[s * 8 + c++] = rr * n + ff;
        }
        ncnt[s] = c;
    }
    printf("n=%d  K=%d white kings  white sets=%llu  states=%llu  (%.2f GB)\n",
           n, K, (unsigned long long)NW, (unsigned long long)(NW * m),
           (NW * m * 3.0) / 1073741824.0);
    wset.assign(NW * K, 0); PHI.assign(NW * (U64)m, 0);
    buildPHI();
    GAP.assign(NW * (U64)m, 0);

    // States bucketed by Phi, so each level is processed once, in order.
    int maxPhi = 0;
    for (U64 i = 0; i < NW * (U64)m; ++i) maxPhi = max(maxPhi, (int)PHI[i]);
    vector<U64> cnt(maxPhi + 2, 0);
    for (U64 i = 0; i < NW * (U64)m; ++i) ++cnt[PHI[i]];
    vector<U64> off(maxPhi + 2, 0);
    for (int k = 1; k <= maxPhi; ++k) off[k + 1] = off[k] + cnt[k];
    U64 live = off[maxPhi + 1];
    vector<U32> bucket(live);
    { vector<U64> at(off);
      for (U64 i = 0; i < NW * (U64)m; ++i) { int p = PHI[i]; if (p) bucket[at[p]++] = (U32)i; } }
    printf("positions with the black king loose: %llu, largest net %d\n",
           (unsigned long long)live, maxPhi);

    int maxGap = 0;
    for (int k = 1; k <= maxPhi; ++k) {
        U64 lo = off[k], hi = off[k + 1];
        if (lo == hi) continue;
        for (int round = 1; round <= 250; ++round) {
            atomic<U64> chg{0};
            par(lo, hi, [&](U64 a, U64 b) {
                Cand cd[64]; U64 loc = 0;
                for (U64 t = a; t < b; ++t) {
                    U64 i = bucket[t];
                    if (gapAt(i)) continue;
                    U64 wr = i / m; int bs = (int)(i % m);
                    int nc = moves(wr, bs, cd);
                    bool ok = false;
                    for (int c = 0; c < nc && !ok; ++c) {
                        int p2 = cd[c].phi2;
                        if (p2 == 0 || p2 > k) continue;          // opens the net, or grows it
                        if (p2 == 1) { ok = true; break; }        // black is sealed on his square
                        if (round == 1) { if (p2 < k && worstReply(cd[c].wr2, bs, 254) >= 0) ok = true; }
                        else            { if (p2 == k && worstReply(cd[c].wr2, bs, round - 1) >= 0) ok = true; }
                    }
                    if (ok) { gapSet(i, (U8)round); ++loc; }
                }
                chg += loc;
            });
            if (!chg.load()) break;
            maxGap = max(maxGap, round);
        }
    }

    U64 won = 0; vector<U64> hist(260, 0);
    for (U64 t = 0; t < live; ++t) { U8 g = GAP[bucket[t]]; ++hist[g]; if (g) ++won; }
    printf("\nWhite holds a never-growing net in %llu of %llu positions (%.4f%%)\n",
           (unsigned long long)won, (unsigned long long)live, 100.0 * won / live);
    printf("moves needed to force the next shrink: ");
    for (int g = 1; g <= maxGap; ++g) if (hist[g]) printf("[%d] %llu  ", g, (unsigned long long)hist[g]);
    printf("\nlargest gap anywhere: %d\n", maxGap);
    if (hist[0]) {
        printf("positions where the net has to grow: %llu\n", (unsigned long long)hist[0]);
        // where they sit: net size, and how far the black king is from an edge
        vector<U64> byPhi(maxPhi + 2, 0), byEdge(n, 0);
        U64 shown = 0;
        for (U64 t = 0; t < live; ++t) {
            U64 i = bucket[t]; if (GAP[i]) continue;
            int bs = (int)(i % m); ++byPhi[PHI[i]];
            int f = bs % n, r = bs / n;
            ++byEdge[min(min(f, n - 1 - f), min(r, n - 1 - r))];
            if (shown < 6) {
                const U8* W = &wset[(i / m) * K];
                printf("      example:");
                for (int q = 0; q < K; ++q) printf(" K%s", sqname(W[q]).c_str());
                printf(" k%s   net %d\n", sqname(bs).c_str(), (int)PHI[i]);
                ++shown;
            }
        }
        printf("      by net size: ");
        for (int k = 1; k <= maxPhi; ++k) if (byPhi[k]) printf("[net %d] %llu  ", k, (unsigned long long)byPhi[k]);
        printf("\n      black king's distance to the nearest edge: ");
        for (int d = 0; d < n / 2; ++d) if (byEdge[d]) printf("[%d] %llu  ", d, (unsigned long long)byEdge[d]);
        printf("\n");
    }

    if (!start.empty()) {
        vector<int> sq; string t;
        for (char c : start + ",") { if (c == ',') { if (!t.empty()) sq.push_back(parseSq(t)); t.clear(); } else t += c; }
        int a[8]; for (int i = 0; i < K; ++i) a[i] = sq[i];
        sort(a, a + K);
        int b = sq[K];
        U64 wr = rankSet(a, K);
        printf("\nstart:");
        for (int i = 0; i < K; ++i) printf(" K%s", sqname(a[i]).c_str());
        printf(" k%s -- net %d, gap %d\n", sqname(b).c_str(), (int)PHI[wr * (U64)m + b], (int)GAP[wr * (U64)m + b]);
        // Worst case over EVERY black defence, not just one line.  White plays
        // the DP's own witness move: at gap g he either shrinks the net (g = 1)
        // or holds it with a move whose every reply has gap <= g-1.  So the
        // pair (net, gap) falls lexicographically at every White move and the
        // strategy graph is acyclic.  tourDepth = worst-case White moves left.
        {
            vector<pair<U64,int>> stk; stk.push_back({wr, b});
            unordered_map<U64,int> memo;      // state -> worst-case white moves
            unordered_map<U64,int> worstGap;
            auto witness = [&](U64 w0, int b0) -> U64 {
                int k0 = PHI[w0 * (U64)m + b0], g0 = GAP[w0 * (U64)m + b0];
                Cand cd[64]; int nc = moves(w0, b0, cd);
                for (int c = 0; c < nc; ++c) {
                    int p2 = cd[c].phi2;
                    if (p2 == 0 || p2 > k0) continue;
                    if (p2 == 1) return cd[c].wr2;
                    if (g0 == 1) { if (p2 < k0 && worstReply(cd[c].wr2, b0, 254) >= 0) return cd[c].wr2; }
                    else         { if (p2 == k0 && worstReply(cd[c].wr2, b0, g0 - 1) >= 0) return cd[c].wr2; }
                }
                return (U64)-1;
            };
            // iterative post-order over the reachable strategy graph
            vector<pair<U64,int>> order; vector<char> mark;
            vector<pair<U64,int>> work; work.push_back({wr, b});
            unordered_map<U64,char> seen;
            while (!work.empty()) {
                auto [w0, b0] = work.back(); work.pop_back();
                U64 id = w0 * (U64)m + b0;
                if (seen.count(id)) continue;
                seen[id] = 1; order.push_back({w0, b0});
                U64 w1 = witness(w0, b0);
                if (w1 == (U64)-1) continue;
                if (PHI[w1 * (U64)m + b0] == 1) continue;
                for (int d = 0; d < ncnt[b0]; ++d) {
                    int b2 = nbr[b0 * 8 + d];
                    if (PHI[w1 * (U64)m + b2] == 0) continue;
                    work.push_back({w1, b2});
                }
            }
            printf("\nstrategy reaches %llu positions; solving each for its worst case\n",
                   (unsigned long long)order.size());
            // relax until stable (the graph is a DAG, so this converges fast)
            for (int pass = 0; pass < 100000; ++pass) {
                bool chg = false;
                for (auto it = order.rbegin(); it != order.rend(); ++it) {
                    U64 w0 = it->first; int b0 = it->second, id0 = 0;
                    U64 id = w0 * (U64)m + b0;
                    U64 w1 = witness(w0, b0);
                    int val;
                    if (w1 == (U64)-1) val = 0;
                    else if (PHI[w1 * (U64)m + b0] == 1) val = 1;
                    else {
                        val = 0;
                        for (int d = 0; d < ncnt[b0]; ++d) {
                            int b2 = nbr[b0 * 8 + d];
                            if (PHI[w1 * (U64)m + b2] == 0) continue;
                            auto f = memo.find(w1 * (U64)m + b2);
                            val = max(val, f == memo.end() ? 0 : f->second);
                        }
                        val += 1;
                    }
                    (void)id0;
                    if (memo[id] != val) { memo[id] = val; chg = true; }
                }
                if (!chg) break;
            }
            int mg = 0;
            for (auto& [w0, b0] : order) mg = max(mg, (int)GAP[w0 * (U64)m + b0]);
            printf("worst case from the start: %d white moves, net %d down to 1, "
                   "worst wait between shrinks %d\n",
                   memo[wr * (U64)m + b], (int)PHI[wr * (U64)m + b], mg);
        }
        // One line played out, with Black holding out as long as the table allows.
        int ply = 0; int prev = PHI[wr * (U64)m + b];
        printf("%4s  %-14s %5s\n", "ply", "move", "net");
        printf("%4d  %-14s %5d\n", 0, "(start)", prev);
        while (ply < 4000) {
            int k = PHI[wr * (U64)m + b];
            Cand cd[64]; int nc = moves(wr, b, cd);
            int bestC = -1, bestScore = 1 << 30;
            for (int c = 0; c < nc; ++c) {
                int p2 = cd[c].phi2;
                if (p2 == 0 || p2 > k) continue;
                int score;
                if (p2 == 1) score = -1000000;
                else {
                    int w = worstReply(cd[c].wr2, b, 254);
                    if (w < 0) continue;
                    score = p2 * 1000 + w;            // shrink hardest, then leave Black least room
                }
                if (score < bestScore) { bestScore = score; bestC = c; }
            }
            if (bestC < 0) { printf("      no monotone move\n"); break; }
            U64 wr2 = cd[bestC].wr2;
            // name the white move
            const U8* Wa = &wset[wr * K]; const U8* Wb = &wset[wr2 * K];
            int from = -1, to = -1;
            for (int i = 0; i < K; ++i) { bool f = false; for (int j = 0; j < K; ++j) if (Wb[j] == Wa[i]) f = true; if (!f) from = Wa[i]; }
            for (int i = 0; i < K; ++i) { bool f = false; for (int j = 0; j < K; ++j) if (Wa[j] == Wb[i]) f = true; if (!f) to = Wb[i]; }
            ++ply;
            printf("%4d  K%-4s-%-7s %5d\n", ply, sqname(from).c_str(), sqname(to).c_str(), (int)cd[bestC].phi2);
            wr = wr2;
            if (cd[bestC].phi2 == 1) { printf("      net closed: every black move steps beside a white king\n"); break; }
            // Black's turn: the reply with the largest gap, i.e. the most stubborn.
            int bb = -1, bw = -1;
            for (int d = 0; d < ncnt[b]; ++d) {
                int b2 = nbr[b * 8 + d]; U64 i2 = wr * (U64)m + b2;
                if (PHI[i2] == 0) continue;
                int g = gapAt(i2); if (g > bw) { bw = g; bb = b2; }
            }
            if (bb < 0) { printf("      every black move walks into the capture\n"); break; }
            int bfrom = b; b = bb; ++ply;
            printf("%4d  k%-4s-%-7s %5d\n", ply, sqname(bfrom).c_str(), sqname(b).c_str(), (int)PHI[wr * (U64)m + b]);
        }
    }
    return 0;
}
