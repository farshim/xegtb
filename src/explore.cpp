// explore.cpp -- the per-endgame adapters behind the browser explorer, and the
// catalogue of configurations it offers.
//
// Each adapter does three things and nothing else: turn a placement into a
// list of men, turn a table entry into a White-relative value, and walk the
// legal moves pricing each one.  Every one of those walks goes through the
// move generator the endgame's own solver and verifier already share --
// `genWhite`/`genBlack`, `kqkrMoves`, `kqkbbMoves`, `kqkkMoves`,
// `kqkkCapMoves`, `TableKings::moves`, `TableMixed::moves` -- so the browser
// can never show a move the tables were not built from.  Nothing here reasons
// about how a piece moves.
//
// The opening position is the one thing computed rather than looked up.  The
// deepest win a table holds is frequently one where something is already
// hanging, which makes a poor thing to open on: the position reads as a puzzle
// with the answer given away, and its "best move" is a capture.  So each
// adapter scans for the deepest win from a QUIET placement -- no capture
// available to either side, nobody in check -- and falls back, in order, to
// the deepest win from any placement and then to any quiet placement at all.
// The scan is monotone: the quiet test runs only on a position already deeper
// than the best quiet one so far, so it fires a handful of times over a table.
#include "explore.hpp"
#include "general.hpp"

#include <dirent.h>
#include <sys/stat.h>

#include <map>
#include <set>

#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cctype>
#include <functional>
#include <cstring>

#include "table.hpp"
#include "movegen.hpp"

namespace kqk {
namespace {

// ---------------------------------------------------------------------------
// Small shared pieces.
// ---------------------------------------------------------------------------

// White's men take an upper-case letter, Black's a lower-case one, as the
// multi-royal endgames already print them.
inline char sideLetter(char piece, bool white) {
    return white ? piece : char(piece | 32);
}

std::string sanOf(const Geometry& g, char piece, bool white, Sq from, Sq to, bool cap) {
    std::string s(1, sideLetter(piece, white));
    s += g.name(from);
    s += cap ? 'x' : '-';
    s += g.name(to);
    return s;
}

// Plies to "mate in N", counted the way probe.cpp counts it: the number of
// moves the winner still has to play.
inline int movesOf(int plies) { return (plies + 1) / 2; }

Val mkVal(Val::Kind k, int plies, bool mating) {
    Val v;
    v.kind = k;
    v.plies = (k == Val::Draw || k == Val::Illegal) ? 0 : plies;
    char buf[128];
    switch (k) {
        case Val::Illegal: v.text = "not a legal position"; break;
        case Val::Draw:    v.text = "Draw"; break;
        default: {
            const char* who = (k == Val::WhiteWins) ? "White" : "Black";
            const int mv = movesOf(v.plies);
            if (mating)
                std::snprintf(buf, sizeof buf, "%s wins -- mate in %d (%d %s)",
                              who, mv, v.plies, v.plies == 1 ? "ply" : "plies");
            else
                std::snprintf(buf, sizeof buf, "%s wins in %d %s (%d %s)",
                              who, v.plies, v.plies == 1 ? "ply" : "plies",
                              mv, mv == 1 ? "move" : "moves");
            v.text = buf;
            break;
        }
    }
    return v;
}

// A signed entry that is relative to the side to move -- the convention of
// kings.cpp, mixed.cpp and kqkkcap.cpp -- read as a White-relative value.
Val moverRelative(int16_t v, bool wtm, bool mating) {
    const int wrel = wtm ? v : -v;
    if (wrel == 0) return mkVal(Val::Draw, 0, mating);
    const int plies = v < 0 ? -v : v;
    return mkVal(wrel > 0 ? Val::WhiteWins : Val::BlackWins, plies, mating);
}

// The White-relative signed encoding of kqkr.cpp and kqkbb.cpp: v > 0 is White
// mating in v - 1 plies, v < 0 Black mating in -v - 1.
Val whiteRelativeSigned(int16_t v) {
    if (v == VK_DEAD || v == VK_UNKNOWN) return mkVal(Val::Illegal, 0, true);
    if (v == VK_DRAW) return mkVal(Val::Draw, 0, true);
    if (v > 0) return mkVal(Val::WhiteWins, v - 1, true);
    return mkVal(Val::BlackWins, -v - 1, true);
}

// Find one man of a colour and letter in a view, removing it from `left`.
// Returns -1 when there is none, which is how a captured man is detected.
Sq take(std::vector<Man>& left, char color, char piece) {
    for (size_t i = 0; i < left.size(); ++i)
        if (left[i].color == color && left[i].piece == piece) {
            Sq s = left[i].sq;
            left.erase(left.begin() + (long)i);
            return s;
        }
    return -1;
}

// ---------------------------------------------------------------------------
// The store: solve once, keep the file, load it next time.
// ---------------------------------------------------------------------------
// Every load here is wrapped the same way -- try the file, and on ANY failure
// fall through to solving.  A store is a cache and a cache that cannot be
// re-derived is not a cache; the one thing that must never happen is a board
// drawn from a file whose header did not check out.
//
// The names follow the convention the README's examples set for `gen -o`, so
// a directory filled by the command line is a directory this reads.  Where a
// configuration has no equivalent command -- the capture readings, the loose
// KQKK -- the rule set goes into the stem before the board size, since a
// store keyed on material alone would hand back a table built under the
// wrong rules.
bool fileExists(const std::string& path) {
    struct stat st;
    return stat(path.c_str(), &st) == 0 && (st.st_mode & S_IFREG);
}

double secondsSince(const std::chrono::steady_clock::time_point& t0) {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
}

// What a table of this endgame is called, so that the chain KNNNK -> KNNK ->
// KNK stores each link under its own name rather than the top one's.
std::string sharedStem(Endgame eg, bool capture, int n) {
    std::string s = Material::of(eg).name();
    for (char& c : s) c = (char)(c >= 'A' && c <= 'Z' ? c - 'A' + 'a' : c);
    if (capture) s += "cap";
    return s + std::to_string(n);
}

std::string joinPath(const std::string& dir, const std::string& stem, const std::string& ext) {
    return dir + "/" + stem + "." + ext;
}

// Reports what happened, on stderr, because the browser cannot show it and a
// person watching a card take twenty seconds deserves to know whether it is
// reading or solving.
// What the loaders did while the engine now being built was built.  The
// server answers one request at a time, so a plain counter reset before
// construction and read after it is enough; nothing here is re-entrant.
struct Tally { int loaded = 0, solved = 0; };
Tally g_tally;

void note(const char* what, const std::string& name, double secs, bool wrote) {
    if (std::strcmp(what, "loaded") == 0 || std::strcmp(what, "mapped") == 0) ++g_tally.loaded;
    else ++g_tally.solved;
    if (secs < 0) std::fprintf(stderr, "    %s %s\n", what, name.c_str());
    else std::fprintf(stderr, "    %s %s in %.2fs%s\n", what, name.c_str(), secs,
                      wrote ? ", saved" : "");
    std::fflush(stderr);
}

// Solve or load one shared-solver table, and the chain below it.  The chain
// has to be attached before `generate`, so the two paths differ in more than
// which call fills the arrays.
std::unique_ptr<Table> sharedTable(Endgame eg, bool capture, int n, int threads,
                                   const Store& store, std::unique_ptr<Table>& chainOut);

std::unique_ptr<Table> loadSharedFile(const std::string& path, Endgame eg, bool capture, int n) {
    try {
        auto t = Table::load(path);
        if (t->n != n || t->mat.eg != eg || t->stalemateLoss != capture) return nullptr;
        return t;
    } catch (...) {
        return nullptr;
    }
}

std::unique_ptr<Table> sharedTable(Endgame eg, bool capture, int n, int threads,
                                   const Store& store, std::unique_ptr<Table>& chainOut) {
    const std::string stem = sharedStem(eg, capture, n);
    std::string ext = Material::of(eg).name();
    for (char& c : ext) c = (char)(c >= 'A' && c <= 'Z' ? c - 'A' + 'a' : c);
    const std::string path = store.dir.empty() ? std::string() : joinPath(store.dir, stem, ext);

    if (!path.empty() && fileExists(path)) {
        const auto t0 = std::chrono::steady_clock::now();
        if (auto t = loadSharedFile(path, eg, capture, n)) {
            // A loaded table still needs its conversion chain, which is a
            // table of its own and comes out of the store the same way.  The
            // three old cases are kept because they can be LOADED rather than
            // solved; anything else -- the two- and three-man materials added
            // since, where every capture converts -- falls through to
            // attachSubTable, which solves them.  Those are small beside the
            // table they hang off, so the cost is slight and the alternative
            // is a table that prices a capture as a draw when it is a win.
            chainOut = nullptr;
            Endgame need;
            bool has = true;
            if (eg == Endgame::KNNNK)                     need = Endgame::KNNK;
            else if (eg == Endgame::KNNK && capture)      need = Endgame::KNK;
            else if (eg == Endgame::KBBK && capture)      need = Endgame::KBK;
            else has = false;
            if (has) {
                std::unique_ptr<Table> deeper;
                auto sub = sharedTable(need, capture, n, threads, store, deeper);
                if (deeper) sub->keepAlive = std::move(deeper);
                t->sub = sub.get();
                for (int i = 0; i < t->mat.np; ++i) t->subFor[i] = t->sub;
                chainOut = std::move(sub);
            } else if (t->mat.np >= 2) {
                chainOut = attachSubTable(*t, threads, false);
            }
            note("loaded", stem, secondsSince(t0), false);
            return t;
        }
        std::fprintf(stderr, "    %s is there but would not load; solving instead\n", stem.c_str());
    }

    const auto t0 = std::chrono::steady_clock::now();
    auto t = std::make_unique<Table>(n, eg);
    t->stalemateLoss = capture;
    chainOut = attachSubTable(*t, threads, false);
    t->generate(threads, false);
    t->computeStats(threads);
    const double secs = secondsSince(t0);
    bool wrote = false;
    if (!path.empty() && secs >= store.minSeconds) {
        try { t->save(path, store.rle); wrote = true; }
        catch (const std::exception& e) {
            std::fprintf(stderr, "    could not write %s: %s\n", path.c_str(), e.what());
        }
    }
    note("solved", stem, secs, wrote);
    return t;
}

// The same three steps for a table type whose load and save are members and
// whose construction takes no chain: one template rather than five copies.
template <class T, class Make, class Fill>
std::unique_ptr<T> storedTable(const std::string& path, const std::string& stem,
                               const Store& store, Make make, Fill fill) {
    if (!path.empty() && fileExists(path)) {
        const auto t0 = std::chrono::steady_clock::now();
        try {
            auto t = T::load(path);
            if (t) { note("loaded", stem, secondsSince(t0), false); return t; }
        } catch (...) { }
        std::fprintf(stderr, "    %s is there but would not load; solving instead\n", stem.c_str());
    }
    const auto t0 = std::chrono::steady_clock::now();
    auto t = make();
    fill(*t);
    const double secs = secondsSince(t0);
    bool wrote = false;
    if (!path.empty() && secs >= store.minSeconds) {
        try { t->save(path, store.rle); wrote = true; }
        catch (const std::exception& e) {
            std::fprintf(stderr, "    could not write %s: %s\n", path.c_str(), e.what());
        }
    }
    note("solved", stem, secs, wrote);
    return t;
}

// ---------------------------------------------------------------------------
// The shared solver: a bare black king against a white king and one, two or
// three men.  `Table` also serves as the continuation of KQKR's ...QxR, so the
// four operations are free functions rather than methods.
// ---------------------------------------------------------------------------

View sharedView(const Table& t, const Pos& p, bool wtm) {
    View v;
    v.wtm = wtm;
    v.men.push_back({ 'w', 'K', p.wk });
    for (int i = 0; i < t.mat.np; ++i)
        v.men.push_back({ 'w', t.mat.letter(i), p.wp[i] });
    v.men.push_back({ 'b', 'K', p.bk });
    return v;
}

Val sharedValue(const Table& t, const Pos& p, bool wtm) {
    const U8 raw = t.valueAt(p, wtm);
    if (raw == V_DEAD) return mkVal(Val::Illegal, 0, true);
    if (!isDtm(raw)) return mkVal(Val::Draw, 0, true);
    Val v = mkVal(Val::WhiteWins, raw, true);
    if (raw == 0) {
        // Black to move and lost in no plies: mate, or -- under capture rules,
        // where a side with no move loses rather than draws -- stalemate.
        v.terminal = blackInCheck(t.geo, t.mat, p) ? "checkmate"
                   : "stalemate -- a loss under capture rules";
    }
    return v;
}

bool sharedQuiet(const Table& t, const Pos& p) {
    if (blackInCheck(t.geo, t.mat, p)) return false;
    bool grab = false;
    genBlack(t.geo, t.mat, p, [&](Sq, int cap) { grab |= (cap >= 0); });
    return !grab;                      // White can never capture here
}

// The placement Black's capture leaves.  The surviving men close up, so which
// slot a man ends in says nothing about what it is -- after ...KxB in KBNK the
// knight is wp[0] -- and anything naming them has to be told what went.
// The position Black's capture leads to, laid out for the table that answers
// it -- which is `sub`, and not necessarily this one's order.
//
// A three-man material with a pair of alike men names the pair first and the
// odd man last (KRNNK is N,N,R) while the two-man tables run strongest first
// (KRNK is R,N), so carrying the survivors across in the parent's order probes
// the sub-table with its two men exchanged: a different entry, and usually an
// illegal one.  The solver, the verifier and the brute force each had this
// same bug and were each fixed; this was the fourth copy, and the one the
// browser reads, which is why KRBNK showed "...KxR" as an illegal position and
// KRRNK priced it sixteen plies out.
Pos sharedAfterCapture(const Table& t, const Pos& p, Sq to, int cap,
                       const Table* sub = nullptr) {
    Pos r;
    r.wk = p.wk;
    r.bk = to;
    Sq   left[MAXWP];
    Piece lp[MAXWP];
    int k = 0;
    for (int i = 0; i < t.mat.np; ++i)
        if (i != cap) { left[k] = p.wp[i]; lp[k] = t.mat.piece[i]; ++k; }
    if (!sub) { for (int i = 0; i < k; ++i) r.wp[i] = left[i]; return r; }
    bool used[MAXWP] = { false, false, false };
    for (int j = 0; j < k; ++j)
        for (int i = 0; i < k; ++i)
            if (!used[i] && lp[i] == sub->mat.piece[j]) { r.wp[j] = left[i]; used[i] = true; break; }
    return r;
}

// The men left over, with each survivor keeping its own letter.
View sharedViewAfterCapture(const Table& t, const Pos& r, int cap, bool wtm) {
    View v;
    v.wtm = wtm;
    v.men.push_back({ 'w', 'K', r.wk });
    int k = 0;
    for (int i = 0; i < t.mat.np; ++i)
        if (i != cap) v.men.push_back({ 'w', t.mat.letter(i), r.wp[k++] });
    v.men.push_back({ 'b', 'K', r.bk });
    return v;
}

std::vector<MoveOut> sharedMoves(const Table& t, const Pos& p, bool wtm) {
    std::vector<MoveOut> out;
    if (t.valueAt(p, wtm) == V_DEAD) return out;
    if (wtm) {
        genWhite(t.geo, t.mat, p, [&](const Pos& q) {
            MoveOut m;
            // Exactly one man moved; find it rather than having the generator
            // say so, which keeps this independent of the generator's shape.
            if (q.wk != p.wk) { m.from = p.wk; m.to = q.wk; m.san = sanOf(t.geo, 'K', true, p.wk, q.wk, false); }
            else for (int i = 0; i < t.mat.np; ++i)
                if (q.wp[i] != p.wp[i]) {
                    m.from = p.wp[i]; m.to = q.wp[i];
                    m.san = sanOf(t.geo, t.mat.letter(i), true, p.wp[i], q.wp[i], false);
                    break;
                }
            m.after = sharedView(t, q, false);
            m.val = sharedValue(t, q, false);
            out.push_back(std::move(m));
        });
        return out;
    }
    genBlack(t.geo, t.mat, p, [&](Sq to, int cap) {
        MoveOut m;
        m.from = p.bk; m.to = to; m.capture = (cap >= 0);
        m.san = sanOf(t.geo, 'K', false, p.bk, to, cap >= 0);
        if (cap < 0) {
            Pos q = p; q.bk = to;
            m.after = sharedView(t, q, true);
            m.val = sharedValue(t, q, true);
        } else {
            // Which man was taken decides which table answers.  `t.sub` is the
            // one-table spelling kept for the endgames that have only one
            // conversion; with three white men there are up to three different
            // ones, and reading the wrong one is not a rounding error -- it is
            // another position's value.
            const Table* sub = (cap >= 0 && cap < MAXWP) ? t.subFor[cap] : nullptr;
            const Pos r = sharedAfterCapture(t, p, to, cap, sub);
            if (sub) {
                // What is left can still mate: its table gives the value and
                // play goes on there.
                m.after = sharedView(*sub, r, true);
                m.val = sharedValue(*sub, r, true);
                m.note = std::string("takes a man: ") + sub->mat.name() + " is left";
            } else {
                m.after = sharedViewAfterCapture(t, r, cap, true);
                m.val = mkVal(Val::Draw, 0, true);
                m.val.terminal = "draw -- what is left cannot mate";
                m.playable = false;
                m.note = "takes a man, and the rest cannot mate";
            }
        }
        out.push_back(std::move(m));
    });
    return out;
}

class SharedEngine : public Engine {
public:
    SharedEngine(int n, Endgame eg, bool capture, int threads, const Store& store) {
        t_ = sharedTable(eg, capture, n, threads, store, chain_);
    }

    const Geometry& geo() const override { return t_->geo; }
    std::string material() const override { return t_->mat.name(); }

    // Which table of the chain a placement belongs to: the one holding exactly
    // these men.  Null when Black has taken enough that nothing is left.
    //
    // Matching on the piece COUNT alone, down the single `sub` chain, is what
    // this did, and it is right only while a material has one conversion.  A
    // three-man material has up to three different ones -- KRBNK loses its
    // rook into KBNK, its bishop into KRNK and its knight into KRBK, all with
    // two men left -- so the count picks whichever table happened to be linked
    // and the letters then fail to match.  That is what made the explorer
    // refuse to replay its own move after a capture.  The search is over the
    // whole conversion graph and compares the men themselves.
    const Table* tableFor(const View& v) const {
        std::vector<char> want;
        for (const Man& m : v.men) if (m.color == 'w' && m.piece != 'K') want.push_back(m.piece);
        std::sort(want.begin(), want.end());
        std::vector<const Table*> seen{ t_.get() };
        for (size_t i = 0; i < seen.size(); ++i) {
            const Table* t = seen[i];
            if (!t) continue;
            std::vector<char> have;
            for (int j = 0; j < t->mat.np; ++j) have.push_back(t->mat.letter(j));
            std::sort(have.begin(), have.end());
            if (have == want) return t;
            auto push = [&](const Table* x) {
                if (x && std::find(seen.begin(), seen.end(), x) == seen.end()) seen.push_back(x);
            };
            for (int j = 0; j < t->mat.np && j < MAXWP; ++j) push(t->subFor[j]);
            push(t->sub);
            push(t->subAlt);
        }
        return nullptr;
    }

    bool toPos(const View& v, const Table& t, Pos& p, std::string& err) const {
        std::vector<Man> left = v.men;
        p.wk = take(left, 'w', 'K');
        p.bk = take(left, 'b', 'K');
        if (p.wk < 0 || p.bk < 0) { err = "both kings must be on the board"; return false; }
        for (int i = 0; i < t.mat.np; ++i) {
            p.wp[i] = take(left, 'w', t.mat.letter(i));
            if (p.wp[i] < 0) { err = "White's men do not match this endgame"; return false; }
        }
        if (!left.empty()) { err = "too many men for this endgame"; return false; }
        return true;
    }

    bool accept(View& v, std::string& err) const override {
        const Table* t = tableFor(v);
        if (!t) { err = "no table holds this material"; return false; }
        Pos p;
        if (!toPos(v, *t, p, err)) return false;
        v = sharedView(*t, p, v.wtm);
        return true;
    }

    Val value(const View& v) const override {
        const Table* t = tableFor(v);
        if (!t) { Val r = mkVal(Val::Draw, 0, true);
                  r.terminal = "draw -- what is left cannot mate"; return r; }
        Pos p; std::string err;
        if (!toPos(v, *t, p, err)) return mkVal(Val::Illegal, 0, true);
        return sharedValue(*t, p, v.wtm);
    }

    std::vector<MoveOut> moves(const View& v) const override {
        const Table* t = tableFor(v);
        Pos p; std::string err;
        if (!t || !toPos(v, *t, p, err)) return {};
        return sharedMoves(*t, p, v.wtm);
    }

    bool quiet(const View& v) const override {
        const Table* t = tableFor(v);
        Pos p; std::string err;
        if (!t || !toPos(v, *t, p, err)) return false;
        return sharedQuiet(*t, p);
    }

    View start(std::string& note) const override {
        const Table& t = *t_;
        const Index& idx = t.idx;
        Pos bestQuiet{}, bestAny{}, anyQuiet{};
        int bq = -1, ba = -1;
        bool haveQuiet = false;
        Pos p;
        for (U64 kk = 0; kk < idx.nkk; ++kk) {
            p.wk = idx.kkWk[kk];
            p.bk = idx.kkBk[kk];
            const U64 base = kk * idx.npc;
            for (U32 pc = 0; pc < idx.npc; ++pc) {
                const U8 raw = t.w[base + pc];
                if (raw == V_DEAD) continue;
                idx.decode(pc, p.wp);
                if (!idx.cfgLive(p.wp, p.wk, p.bk)) continue;
                if (!idx.cfgIsCanonical((int32_t)kk, p.wp)) continue;
                if (isDtm(raw)) {
                    if ((int)raw > ba) { ba = raw; bestAny = p; }
                    if ((int)raw > bq && sharedQuiet(t, p)) { bq = raw; bestQuiet = p; }
                } else if (!haveQuiet && sharedQuiet(t, p)) {
                    anyQuiet = p; haveQuiet = true;
                }
            }
        }
        if (bq >= 0) { note = "the deepest win White has from a quiet position"; return sharedView(t, bestQuiet, true); }
        if (ba >= 0) { note = "the deepest win White has -- no quiet position reaches it"; return sharedView(t, bestAny, true); }
        if (haveQuiet) { note = "a quiet position; White has no win anywhere on this board"; return sharedView(t, anyQuiet, true); }
        note = "no legal position found";
        return View{};
    }

private:
    std::unique_ptr<Table> t_;
    std::unique_ptr<Table> chain_;   // owns the conversion chain, if any
};

// ---------------------------------------------------------------------------
// KQKR and KQKB: Black is armed.  White's ...QxR leaves KQK, which this engine
// goes on playing in; Black's ...RxQ leaves the rook against a bare white king,
// which is the KRK table read with the colours swapped, and the explorer stops
// there rather than turning the board round.
// ---------------------------------------------------------------------------
class KqkrEngine : public Engine {
public:
    KqkrEngine(int n, Endgame eg, bool capture, int threads, const Store& store) {
        // "kqkr8" for the mating reading, "kqkrcap8" for the capture one.  The
        // rule set has to be in the NAME: the same material is a different
        // game under each, and without the marker the two tables would want
        // the same file and one would be served as the other.  The shared
        // solver has spelled it this way all along.
        std::string ext = Material::of(eg).name();
        for (char& c : ext) c = (char)(c >= 'A' && c <= 'Z' ? c - 'A' + 'a' : c);
        const std::string lower = ext + (capture ? "cap" : "") + std::to_string(n);
        t_ = storedTable<TableKQKR>(
            store.dir.empty() ? std::string() : joinPath(store.dir, lower, ext), lower, store,
            [&] {
                auto t = std::make_unique<TableKQKR>(n, eg);
                t->stalemateLoss = capture;
                return t;
            },
            [&](TableKQKR& t) { t.generate(threads, false); });
        t_->stalemateLoss = capture;
        // The two conversions are tables of their own, so they come out of the
        // store on their own terms rather than riding along in this file --
        // and under the capture rules they are the capture readings too.
        // What White's capture leaves is White's OWN man against a bare king,
        // which is KQK only when White has a queen.  Handing a rook-vs-rook
        // table the KQK conversion valued RxR as though the rook were a queen,
        // and the play-out check in tests/run_tests.sh section 22 caught it:
        // the depth jumped from 33 plies to 16 in one move.
        t_->convQ = sharedTable(bareEndgameOf(whitePieceOf(eg)), capture, n, threads,
                                store, chainQ_);
        t_->convB = sharedTable(subEndgame(eg), capture, n, threads, store, chainB_);
        bl_ = blackPieceOf(eg);
        wl_ = whitePieceOf(eg);
    }

    const Geometry& geo() const override { return t_->geo; }
    std::string material() const override { return t_->mat.name(); }

    View mkView(const Pos& p, bool wtm) const {
        View v; v.wtm = wtm;
        v.men.push_back({ 'w', 'K', p.wk });
        v.men.push_back({ 'w', pieceLetter(wl_), p.wp[0] });
        v.men.push_back({ 'b', 'K', p.bk });
        v.men.push_back({ 'b', pieceLetter(bl_), p.wp[1] });
        return v;
    }

    // Both captures leave three men.  White's leaves KQK, which convQ holds;
    // Black's leaves Black's man against a bare white king.
    bool isKqk(const View& v) const {
        int bm = 0;
        for (const Man& m : v.men) if (m.color == 'b' && m.piece != 'K') ++bm;
        return bm == 0;
    }

    bool toPos(const View& v, Pos& p, std::string& err) const {
        std::vector<Man> left = v.men;
        p.wk = take(left, 'w', 'K');
        p.bk = take(left, 'b', 'K');
        p.wp[0] = take(left, 'w', pieceLetter(wl_));
        p.wp[1] = take(left, 'b', pieceLetter(bl_));
        if (p.wk < 0 || p.bk < 0) { err = "both kings must be on the board"; return false; }
        if (!left.empty()) { err = "too many men for this endgame"; return false; }
        return true;
    }

    bool accept(View& v, std::string& err) const override {
        Pos p;
        if (!toPos(v, p, err)) return false;
        if (isKqk(v)) {
            if (p.wp[0] < 0) { err = "nothing is left to play"; return false; }
            Pos q; q.wk = p.wk; q.bk = p.bk; q.wp[0] = p.wp[0];
            v = sharedView(*t_->convQ, q, v.wtm);
            return true;
        }
        if (p.wp[0] < 0) { err = "the explorer stops when the queen falls"; return false; }
        v = mkView(p, v.wtm);
        return true;
    }

    Val value(const View& v) const override {
        Pos p; std::string err;
        if (!toPos(v, p, err)) return mkVal(Val::Illegal, 0, true);
        if (isKqk(v)) {
            Pos q; q.wk = p.wk; q.bk = p.bk; q.wp[0] = p.wp[0];
            return sharedValue(*t_->convQ, q, v.wtm);
        }
        Val r = whiteRelativeSigned(t_->valueAt(p, v.wtm));
        if (r.plies == 0 && r.kind != Val::Draw && r.kind != Val::Illegal)
            r.terminal = "checkmate";
        return r;
    }

    std::vector<MoveOut> moves(const View& v) const override {
        Pos p; std::string err;
        if (!toPos(v, p, err)) return {};
        if (isKqk(v)) {
            Pos q; q.wk = p.wk; q.bk = p.bk; q.wp[0] = p.wp[0];
            return sharedMoves(*t_->convQ, q, v.wtm);
        }
        std::vector<MoveOut> out;
        const Geometry& g = t_->geo;
        kqkrMoves(*t_, p, v.wtm, [&](const Pos& q, bool cap, int16_t val) {
            MoveOut m;
            m.capture = cap;
            m.val = whiteRelativeSigned(val);
            if (v.wtm) {
                if (q.wk != p.wk) { m.from = p.wk; m.to = q.wk;
                                    m.san = sanOf(g, 'K', true, p.wk, q.wk, cap); }
                else              { m.from = p.wp[0]; m.to = q.wp[0];
                                    m.san = sanOf(g, pieceLetter(wl_), true, p.wp[0], q.wp[0], cap); }
            } else {
                if (q.bk != p.bk) { m.from = p.bk; m.to = q.bk;
                                    m.san = sanOf(g, 'K', false, p.bk, q.bk, cap); }
                else              { m.from = p.wp[1]; m.to = q.wp[1];
                                    m.san = sanOf(g, pieceLetter(bl_), false, p.wp[1], q.wp[1], cap); }
            }
            if (cap && v.wtm) {
                // ...QxR: KQK is left, and the mate usually happens there.
                Pos r; r.wk = q.wk; r.bk = q.bk; r.wp[0] = q.wp[0];
                m.after = sharedView(*t_->convQ, r, false);
                m.note = "takes Black's man: KQK is left";
            } else if (cap) {
                // ...RxQ: the rook against a bare white king, which is KRK with
                // the colours swapped.  Shown, valued, but not played on.
                m.after.wtm = true;
                m.after.men.push_back({ 'w', 'K', q.wk });
                m.after.men.push_back({ 'b', 'K', q.bk });
                m.after.men.push_back({ 'b', pieceLetter(bl_), q.wp[1] });
                m.playable = false;
                m.note = std::string("takes the queen: ") + t_->convB->mat.name() +
                         " with the colours swapped, which the explorer does not turn round";
            } else {
                m.after = mkView(q, !v.wtm);
            }
            out.push_back(std::move(m));
        });
        return out;
    }

    bool quiet(const View& v) const override {
        Pos p; std::string err;
        if (!toPos(v, p, err)) return false;
        if (isKqk(v)) {
            Pos q; q.wk = p.wk; q.bk = p.bk; q.wp[0] = p.wp[0];
            return sharedQuiet(*t_->convQ, q);
        }
        // Nothing hanging and nobody in check.  Both halves are needed here in
        // a way they are not where Black is bare: with Black armed a
        // white-to-move position may well be one where Black has just given
        // check, and a position whose only legal move is a forced reply is a
        // poor one to open the explorer on.
        if (kqkrBlackChecked(t_->geo, wl_, p.wk, p.bk, p.wp[0], p.wp[1])) return false;
        if (kqkrWhiteChecked(t_->geo, bl_, p.wk, p.bk, p.wp[0], p.wp[1])) return false;
        for (int s = 0; s < 2; ++s) {
            bool grab = false;
            kqkrMoves(*t_, p, s == 0, [&](const Pos&, bool cap, int16_t) { grab |= cap; });
            if (grab) return false;
        }
        return true;
    }

    View start(std::string& note) const override {
        const Index& idx = t_->idx;
        Pos bestQuiet{}, bestAny{}, anyQuiet{};
        int bq = -1, ba = -1;
        bool haveQuiet = false;
        Pos p;
        for (U64 kk = 0; kk < idx.nkk; ++kk) {
            p.wk = idx.kkWk[kk];
            p.bk = idx.kkBk[kk];
            const U64 base = kk * idx.npc;
            for (U32 pc = 0; pc < idx.npc; ++pc) {
                const int16_t raw = t_->w[base + pc];
                if (raw == VK_DEAD || raw == VK_UNKNOWN) continue;
                idx.decode(pc, p.wp);
                if (!idx.cfgLive(p.wp, p.wk, p.bk)) continue;
                if (!idx.cfgIsCanonical((int32_t)kk, p.wp)) continue;
                if (raw > 0) {
                    const int plies = raw - 1;
                    if (plies > ba) { ba = plies; bestAny = p; }
                    if (plies > bq) {
                        View v = mkView(p, true);
                        if (quiet(v)) { bq = plies; bestQuiet = p; }
                    }
                } else if (!haveQuiet) {
                    View v = mkView(p, true);
                    if (quiet(v)) { anyQuiet = p; haveQuiet = true; }
                }
            }
        }
        if (bq >= 0) { note = "the deepest win White has from a quiet position"; return mkView(bestQuiet, true); }
        if (ba >= 0) { note = "the deepest win White has -- no quiet position reaches it"; return mkView(bestAny, true); }
        if (haveQuiet) { note = "a quiet position; White has no win anywhere on this board"; return mkView(anyQuiet, true); }
        note = "no legal position found";
        return View{};
    }

private:
    std::unique_ptr<TableKQKR> t_;
    std::unique_ptr<Table> chainQ_, chainB_;   // conversion chains, if any
    Piece bl_ = Piece::Rook;    // Black's man
    Piece wl_ = Piece::Queen;   // White's, now that it is not always a queen
};

// ---------------------------------------------------------------------------
// KQKBB: five men.  White's QxB leaves KQKB, which this engine goes on playing
// in through a KQKR engine over the sub-table; Black's ...BxQ leaves two
// bishops against a bare king, KBBK with the colours swapped, and stops.
// ---------------------------------------------------------------------------
class KqkbbEngine : public Engine {
public:
    KqkbbEngine(int n, int threads, const Store& store) {
        const std::string stem = "kqkbb" + std::to_string(n);
        t_ = storedTable<TableKQKBB>(
            store.dir.empty() ? std::string() : joinPath(store.dir, stem, "kqkbb"), stem, store,
            [&] { return std::make_unique<TableKQKBB>(n); },
            [&](TableKQKBB& t) { t.generate(threads, false); });
        // Its two conversions, and the KQKB one's own two, all through the
        // store.  buildSubTables only builds what is still null, so filling
        // them here leaves it nothing to do.
        const std::string bstem = "kqkb" + std::to_string(n);
        t_->kqkb = storedTable<TableKQKR>(
            store.dir.empty() ? std::string() : joinPath(store.dir, bstem, "kqkb"), bstem, store,
            [&] { return std::make_unique<TableKQKR>(n, Endgame::KQKB); },
            [&](TableKQKR& t) { t.generate(threads, false); });
        t_->kbbk = sharedTable(Endgame::KBBK, false, n, threads, store, chainBB_);
        t_->kqkb->convQ = sharedTable(Endgame::KQK, false, n, threads, store, chainQ_);
        t_->kqkb->convB = sharedTable(Endgame::KBK, false, n, threads, store, chainB_);
        t_->buildSubTables(threads, false);
    }

    const Geometry& geo() const override { return t_->geo; }
    std::string material() const override { return "KQKBB"; }

    View mkView(const PosBB& p, bool wtm) const {
        View v; v.wtm = wtm;
        v.men.push_back({ 'w', 'K', p.wk });
        v.men.push_back({ 'w', 'Q', p.wq });
        v.men.push_back({ 'b', 'K', p.bk });
        if (p.b1 >= 0) v.men.push_back({ 'b', 'B', p.b1 });
        if (p.b2 >= 0) v.men.push_back({ 'b', 'B', p.b2 });
        return v;
    }

    int bishops(const View& v) const {
        int c = 0;
        for (const Man& m : v.men) if (m.color == 'b' && m.piece == 'B') ++c;
        return c;
    }

    bool toPos(const View& v, PosBB& p, std::string& err) const {
        std::vector<Man> left = v.men;
        p.wk = take(left, 'w', 'K');
        p.wq = take(left, 'w', 'Q');
        p.bk = take(left, 'b', 'K');
        p.b1 = take(left, 'b', 'B');
        p.b2 = take(left, 'b', 'B');
        if (p.wk < 0 || p.bk < 0) { err = "both kings must be on the board"; return false; }
        if (!left.empty()) { err = "too many men for this endgame"; return false; }
        return true;
    }

    // One bishop left: the position belongs to the KQKB sub-table, which is a
    // TableKQKR and has a Pos of its own.
    bool toSub(const PosBB& p, Pos& q) const {
        q.wk = p.wk; q.bk = p.bk; q.wp[0] = p.wq;
        q.wp[1] = p.b1 >= 0 ? p.b1 : p.b2;
        return q.wp[1] >= 0 && q.wp[0] >= 0;
    }

    bool accept(View& v, std::string& err) const override {
        PosBB p;
        if (!toPos(v, p, err)) return false;
        if (p.wq < 0) { err = "the explorer stops when the queen falls"; return false; }
        const int nb = bishops(v);
        if (nb == 2) { v = mkView(p, v.wtm); return true; }
        if (nb == 1) { Pos q; toSub(p, q); v = subView(q, v.wtm); return true; }
        Pos q; q.wk = p.wk; q.bk = p.bk; q.wp[0] = p.wq;
        v = sharedView(*t_->kqkb->convQ, q, v.wtm);
        return true;
    }

    View subView(const Pos& q, bool wtm) const {
        View v; v.wtm = wtm;
        v.men.push_back({ 'w', 'K', q.wk });
        v.men.push_back({ 'w', 'Q', q.wp[0] });
        v.men.push_back({ 'b', 'K', q.bk });
        v.men.push_back({ 'b', 'B', q.wp[1] });
        return v;
    }

    Val value(const View& v) const override {
        PosBB p; std::string err;
        if (!toPos(v, p, err)) return mkVal(Val::Illegal, 0, true);
        const int nb = bishops(v);
        if (nb == 2) {
            Val r = whiteRelativeSigned(t_->valueAt(p, v.wtm));
            if (r.plies == 0 && (r.kind == Val::WhiteWins || r.kind == Val::BlackWins))
                r.terminal = "checkmate";
            return r;
        }
        if (nb == 1) { Pos q; toSub(p, q); return whiteRelativeSigned(t_->kqkb->valueAt(q, v.wtm)); }
        Pos q; q.wk = p.wk; q.bk = p.bk; q.wp[0] = p.wq;
        return sharedValue(*t_->kqkb->convQ, q, v.wtm);
    }

    std::vector<MoveOut> moves(const View& v) const override {
        PosBB p; std::string err;
        if (!toPos(v, p, err)) return {};
        const int nb = bishops(v);
        if (nb == 1) {
            // KQKB, which a KQKR-shaped walk already knows how to price.
            Pos q; toSub(p, q);
            std::vector<MoveOut> out;
            const Geometry& g = t_->geo;
            kqkrMoves(*t_->kqkb, q, v.wtm, [&](const Pos& r, bool cap, int16_t val) {
                MoveOut m;
                m.capture = cap;
                m.val = whiteRelativeSigned(val);
                if (v.wtm) {
                    if (r.wk != q.wk) { m.from = q.wk; m.to = r.wk; m.san = sanOf(g, 'K', true, q.wk, r.wk, cap); }
                    else              { m.from = q.wp[0]; m.to = r.wp[0]; m.san = sanOf(g, 'Q', true, q.wp[0], r.wp[0], cap); }
                } else {
                    if (r.bk != q.bk) { m.from = q.bk; m.to = r.bk; m.san = sanOf(g, 'K', false, q.bk, r.bk, cap); }
                    else              { m.from = q.wp[1]; m.to = r.wp[1]; m.san = sanOf(g, 'B', false, q.wp[1], r.wp[1], cap); }
                }
                if (cap && v.wtm) {
                    Pos s; s.wk = r.wk; s.bk = r.bk; s.wp[0] = r.wp[0];
                    m.after = sharedView(*t_->kqkb->convQ, s, false);
                    m.note = "takes the last bishop: KQK is left";
                } else if (cap) {
                    m.after.wtm = true;
                    m.after.men.push_back({ 'w', 'K', r.wk });
                    m.after.men.push_back({ 'b', 'K', r.bk });
                    m.after.men.push_back({ 'b', 'B', r.wp[1] });
                    m.playable = false;
                    m.note = "takes the queen: a bishop against a bare king, a draw";
                } else {
                    m.after = subView(r, !v.wtm);
                }
                out.push_back(std::move(m));
            });
            return out;
        }
        if (nb == 0) {
            Pos q; q.wk = p.wk; q.bk = p.bk; q.wp[0] = p.wq;
            return sharedMoves(*t_->kqkb->convQ, q, v.wtm);
        }
        std::vector<MoveOut> out;
        const Geometry& g = t_->geo;
        kqkbbMoves(*t_, p, v.wtm, [&](const PosBB& q, bool cap, int16_t val) {
            MoveOut m;
            m.capture = cap;
            m.val = whiteRelativeSigned(val);
            if (v.wtm) {
                if (q.wk != p.wk) { m.from = p.wk; m.to = q.wk; m.san = sanOf(g, 'K', true, p.wk, q.wk, cap); }
                else              { m.from = p.wq; m.to = q.wq; m.san = sanOf(g, 'Q', true, p.wq, q.wq, cap); }
            } else if (q.bk != p.bk) {
                m.from = p.bk; m.to = q.bk; m.san = sanOf(g, 'K', false, p.bk, q.bk, cap);
            } else {
                // A bishop moved.  The pair is unordered and the index sorts
                // it, so name the move by the square that left and the one
                // that arrived rather than by a slot.
                Sq from = -1, to = -1;
                const Sq a[2] = { p.b1, p.b2 }, b[2] = { q.b1, q.b2 };
                for (int i = 0; i < 2; ++i) {
                    if (a[i] >= 0 && a[i] != b[0] && a[i] != b[1]) from = a[i];
                    if (b[i] >= 0 && b[i] != a[0] && b[i] != a[1]) to = b[i];
                }
                m.from = from; m.to = to;
                m.san = sanOf(g, 'B', false, from, to, cap);
            }
            if (cap && v.wtm) {
                Pos r; toSub(q, r);
                m.after = subView(r, false);
                m.note = "takes a bishop: KQKB is left";
            } else if (cap) {
                m.after.wtm = true;
                m.after.men.push_back({ 'w', 'K', q.wk });
                m.after.men.push_back({ 'b', 'K', q.bk });
                if (q.b1 >= 0) m.after.men.push_back({ 'b', 'B', q.b1 });
                if (q.b2 >= 0) m.after.men.push_back({ 'b', 'B', q.b2 });
                m.playable = false;
                m.note = "takes the queen: two bishops against a bare king, "
                         "which is KBBK with the colours swapped";
            } else {
                m.after = mkView(q, !v.wtm);
            }
            out.push_back(std::move(m));
        });
        return out;
    }

    bool quiet(const View& v) const override {
        PosBB p; std::string err;
        if (!toPos(v, p, err)) return false;
        if (bishops(v) != 2) return false;
        if (kqkbbBlackChecked(t_->geo, p.wk, p.bk, p.wq, p.b1, p.b2)) return false;
        if (kqkbbWhiteChecked(t_->geo, p.wk, p.bk, p.wq, p.b1, p.b2)) return false;
        for (int s = 0; s < 2; ++s) {
            bool grab = false;
            kqkbbMoves(*t_, p, s == 0, [&](const PosBB&, bool cap, int16_t) { grab |= cap; });
            if (grab) return false;
        }
        return true;
    }

    View start(std::string& note) const override {
        const IndexKQKBB& idx = t_->idx;
        PosBB bestQuiet{}, bestAny{}, anyQuiet{};
        int bq = -1, ba = -1;
        bool haveQuiet = false;
        PosBB p;
        for (U64 kk = 0; kk < idx.nkk; ++kk) {
            p.wk = idx.kkWk[kk];
            p.bk = idx.kkBk[kk];
            const U64 base = kk * idx.npc;
            for (U32 pc = 0; pc < idx.npc; ++pc) {
                const int16_t raw = t_->w[base + pc];
                if (raw == VK_DEAD || raw == VK_UNKNOWN) continue;
                idx.decode(pc, p.wq, p.b1, p.b2);
                if (!idx.cfgIsCanonical((int32_t)kk, p.wq, p.b1, p.b2)) continue;
                if (raw > 0) {
                    const int plies = raw - 1;
                    if (plies > ba) { ba = plies; bestAny = p; }
                    if (plies > bq) {
                        View v = mkView(p, true);
                        if (quiet(v)) { bq = plies; bestQuiet = p; }
                    }
                } else if (!haveQuiet) {
                    View v = mkView(p, true);
                    if (quiet(v)) { anyQuiet = p; haveQuiet = true; }
                }
            }
        }
        if (bq >= 0) { note = "the deepest win White has from a quiet position"; return mkView(bestQuiet, true); }
        if (ba >= 0) { note = "the deepest win White has -- no quiet position reaches it"; return mkView(bestAny, true); }
        if (haveQuiet) { note = "a quiet position; White has no win anywhere on this board"; return mkView(anyQuiet, true); }
        note = "no legal position found";
        return View{};
    }

private:
    std::unique_ptr<TableKQKBB> t_;
    std::unique_ptr<Table> chainBB_, chainQ_, chainB_;
};

// ---------------------------------------------------------------------------
// KQKK under the mating rules: a queen against two black kings.  ...KxQ is an
// immediate draw and leaves no table, so it is shown and not played on.
// ---------------------------------------------------------------------------
class KqkkEngine : public Engine {
public:
    KqkkEngine(int n, KkRules rules, int threads, const Store& store) {
        const std::string stem =
            std::string("kqkk") + (rules == KkRules::Loose ? "loose" : "") + std::to_string(n);
        t_ = storedTable<TableKQKK>(
            store.dir.empty() ? std::string() : joinPath(store.dir, stem, "kqkk"), stem, store,
            [&] { return std::make_unique<TableKQKK>(n, rules); },
            [&](TableKQKK& t) { t.generate(threads, false); t.computeStats(threads); });
        // The header carries the rule set, so a loose file can never be read
        // as a strict one -- but it can be handed back for the wrong one of
        // the two if the name collided, which is why the name says so too.
        if (t_->rules != rules)
            throw std::runtime_error("the stored KQKK table is under the other rule set");
    }

    const Geometry& geo() const override { return t_->geo; }
    std::string material() const override { return "KQKK"; }

    View mkView(const PosKK& p, bool wtm) const {
        View v; v.wtm = wtm;
        v.men.push_back({ 'w', 'K', p.wk });
        if (p.wq >= 0) v.men.push_back({ 'w', 'Q', p.wq });
        if (p.bk1 >= 0) v.men.push_back({ 'b', 'K', p.bk1 });
        if (p.bk2 >= 0) v.men.push_back({ 'b', 'K', p.bk2 });
        return v;
    }

    bool toPos(const View& v, PosKK& p, std::string& err) const {
        std::vector<Man> left = v.men;
        p.wk = take(left, 'w', 'K');
        p.wq = take(left, 'w', 'Q');
        p.bk1 = take(left, 'b', 'K');
        p.bk2 = take(left, 'b', 'K');
        if (p.wk < 0 || p.bk1 < 0 || p.bk2 < 0) { err = "three kings and a queen, please"; return false; }
        if (p.wq < 0) { err = "the explorer stops when the queen falls"; return false; }
        if (!left.empty()) { err = "too many men for this endgame"; return false; }
        return true;
    }

    bool accept(View& v, std::string& err) const override {
        PosKK p;
        if (!toPos(v, p, err)) return false;
        v = mkView(p, v.wtm);
        return true;
    }

    Val value(const View& v) const override {
        PosKK p; std::string err;
        if (!toPos(v, p, err)) return mkVal(Val::Illegal, 0, true);
        const U8 raw = t_->valueAt(p, v.wtm);
        if (raw == V_DEAD) return mkVal(Val::Illegal, 0, true);
        if (!isDtm(raw)) return mkVal(Val::Draw, 0, true);
        Val r = mkVal(Val::WhiteWins, raw, true);
        if (raw == 0) r.terminal = "both black kings are mated at once";
        return r;
    }

    std::vector<MoveOut> moves(const View& v) const override {
        PosKK p; std::string err;
        if (!toPos(v, p, err)) return {};
        if (t_->valueAt(p, v.wtm) == V_DEAD) return {};
        std::vector<MoveOut> out;
        const Geometry& g = t_->geo;
        kqkkMoves(*t_, p, v.wtm, [&](const PosKK& q, bool tookQueen, U8 val) {
            MoveOut m;
            m.capture = tookQueen;
            if (v.wtm) {
                if (q.wk != p.wk) { m.from = p.wk; m.to = q.wk; m.san = sanOf(g, 'K', true, p.wk, q.wk, false); }
                else              { m.from = p.wq; m.to = q.wq; m.san = sanOf(g, 'Q', true, p.wq, q.wq, false); }
            } else {
                // One of the two black kings moved; the index may have swapped
                // them, so name the move by the square vacated and the one
                // arrived at.
                const Sq a[2] = { p.bk1, p.bk2 }, b[2] = { q.bk1, q.bk2 };
                Sq from = -1, to = -1;
                for (int i = 0; i < 2; ++i) {
                    if (a[i] != b[0] && a[i] != b[1]) from = a[i];
                    if (b[i] >= 0 && b[i] != a[0] && b[i] != a[1]) to = b[i];
                }
                if (tookQueen) to = p.wq;
                m.from = from; m.to = to;
                m.san = sanOf(g, 'K', false, from, to, tookQueen);
            }
            if (tookQueen) {
                m.after = mkView(q, !v.wtm);
                m.val = mkVal(Val::Draw, 0, true);
                m.val.terminal = "draw -- a king cannot mate two";
                m.playable = false;
                m.note = "takes the queen, and a bare king cannot mate";
            } else {
                m.after = mkView(q, !v.wtm);
                m.val = isDtm(val) ? mkVal(Val::WhiteWins, val, true) : mkVal(Val::Draw, 0, true);
            }
            out.push_back(std::move(m));
        });
        return out;
    }

    bool quiet(const View& v) const override {
        PosKK p; std::string err;
        if (!toPos(v, p, err)) return false;
        if (t_->inCheck(p, 0) || t_->inCheck(p, 1)) return false;
        bool grab = false;
        kqkkMoves(*t_, p, false, [&](const PosKK&, bool took, U8) { grab |= took; });
        return !grab;
    }

    View start(std::string& note) const override {
        const IndexKQKK& idx = t_->idx;
        PosKK bestQuiet{}, bestAny{}, anyQuiet{};
        int bq = -1, ba = -1;
        bool haveQuiet = false;
        for (U64 blk = 0; blk < idx.nblk; ++blk) {
            PosKK p;
            p.wk = idx.blkWk[blk]; p.bk1 = idx.blkB1[blk]; p.bk2 = idx.blkB2[blk];
            for (U32 q = 0; q < idx.npc; ++q) {
                p.wq = (Sq)q;
                const U8 raw = t_->valueAt(p, true);
                if (raw == V_DEAD) continue;
                View v = mkView(p, true);
                if (isDtm(raw)) {
                    if ((int)raw > ba) { ba = raw; bestAny = p; }
                    if ((int)raw > bq && quiet(v)) { bq = raw; bestQuiet = p; }
                } else if (!haveQuiet && quiet(v)) { anyQuiet = p; haveQuiet = true; }
            }
        }
        if (bq >= 0) { note = "the deepest win White has from a quiet position"; return mkView(bestQuiet, true); }
        if (ba >= 0) { note = "the deepest win White has -- no quiet position reaches it"; return mkView(bestAny, true); }
        if (haveQuiet) { note = "a quiet position; White has no win anywhere on this board"; return mkView(anyQuiet, true); }
        note = "no legal position found";
        return View{};
    }

private:
    std::unique_ptr<TableKQKK> t_;
};

// ---------------------------------------------------------------------------
// KQKK under the capture rules: no check, no mate, both sides can win, and
// material falls.  Every conversion is inside the same object, so play goes on
// all the way down to bare kings.
// ---------------------------------------------------------------------------
class KqkkCapEngine : public Engine {
public:
    KqkkCapEngine(int n, int threads, const Store& store) {
        const std::string stem = "kqkkcap" + std::to_string(n);
        // TableKQKKCap::save takes no encoding flag, so this one wrapper has a
        // save of its own rather than the shared template's.
        const std::string path =
            store.dir.empty() ? std::string() : joinPath(store.dir, stem, "kqkkcap");
        if (!path.empty() && fileExists(path)) {
            const auto t0 = std::chrono::steady_clock::now();
            try {
                t_ = TableKQKKCap::load(path);
                if (t_ && t_->n == n) {
                    t_->computeStats(threads);
                    note("loaded", stem, secondsSince(t0), false);
                    return;
                }
                t_.reset();
            } catch (...) { t_.reset(); }
            std::fprintf(stderr, "    %s is there but would not load; solving instead\n",
                         stem.c_str());
        }
        const auto t0 = std::chrono::steady_clock::now();
        t_ = std::make_unique<TableKQKKCap>(n);
        t_->generate(threads, false);
        t_->computeStats(threads);
        const double secs = secondsSince(t0);
        bool wrote = false;
        if (!path.empty() && secs >= store.minSeconds) {
            try { t_->save(path); wrote = true; }
            catch (const std::exception& e) {
                std::fprintf(stderr, "    could not write %s: %s\n", path.c_str(), e.what());
            }
        }
        note("solved", stem, secs, wrote);
    }

    const Geometry& geo() const override { return t_->geo; }
    std::string material() const override { return "KQKK"; }

    View mkView(const PosKK& p, bool wtm) const {
        View v; v.wtm = wtm;
        if (p.wk >= 0) v.men.push_back({ 'w', 'K', p.wk });
        if (p.wq >= 0) v.men.push_back({ 'w', 'Q', p.wq });
        if (p.bk1 >= 0) v.men.push_back({ 'b', 'K', p.bk1 });
        if (p.bk2 >= 0) v.men.push_back({ 'b', 'K', p.bk2 });
        return v;
    }

    bool toPos(const View& v, PosKK& p, std::string& err) const {
        std::vector<Man> left = v.men;
        p.wk = take(left, 'w', 'K');
        p.wq = take(left, 'w', 'Q');
        p.bk1 = take(left, 'b', 'K');
        p.bk2 = take(left, 'b', 'K');
        if (!left.empty()) { err = "too many men for this endgame"; return false; }
        if (p.wk < 0 && p.bk1 < 0) { err = "nothing left on the board"; return false; }
        return true;
    }

    // The value of any material in the lattice, mover-relative.
    int16_t raw(const PosKK& p, bool wtm) const {
        const int nb = (p.bk1 >= 0) + (p.bk2 >= 0);
        if (p.wk < 0) return 0;                       // Black has already won
        if (nb == 0) return 0;                        // White has already won
        if (p.wq >= 0 && nb == 2) return t_->valueAt(p, wtm);
        const Sq bk = p.bk1 >= 0 ? p.bk1 : p.bk2;
        if (p.wq >= 0) return t_->q3Value(p.wk, p.wq, bk, wtm);
        if (nb == 2)   return t_->k3Value(p.wk, p.bk1, p.bk2, wtm);
        return t_->kkValue(p.wk, bk, wtm);
    }

    bool accept(View& v, std::string& err) const override {
        PosKK p;
        if (!toPos(v, p, err)) return false;
        v = mkView(p, v.wtm);
        return true;
    }

    Val value(const View& v) const override {
        PosKK p; std::string err;
        if (!toPos(v, p, err)) return mkVal(Val::Illegal, 0, false);
        const int nb = (p.bk1 >= 0) + (p.bk2 >= 0);
        if (p.wk < 0) { Val r = mkVal(Val::BlackWins, 0, false);
                        r.text = "Black has won -- the white king has fallen";
                        r.terminal = "the white king has fallen"; return r; }
        if (nb == 0)  { Val r = mkVal(Val::WhiteWins, 0, false);
                        r.text = "White has won -- both black kings have fallen";
                        r.terminal = "both black kings have fallen"; return r; }
        const int16_t x = raw(p, v.wtm);
        if (x == VC_DEAD || x == VC_UNKNOWN) return mkVal(Val::Illegal, 0, false);
        return moverRelative(x, v.wtm, false);
    }

    std::vector<MoveOut> moves(const View& v) const override {
        PosKK p; std::string err;
        if (!toPos(v, p, err)) return {};
        std::vector<MoveOut> out;
        const Geometry& g = t_->geo;
        kqkkCapMoves(*t_, p, v.wtm, [&](const PosKK& q, CapMove kind, int16_t) {
            MoveOut m;
            m.capture = (kind != CapMove::Quiet);
            if (v.wtm) {
                if (q.wk != p.wk) { m.from = p.wk; m.to = q.wk; m.san = sanOf(g, 'K', true, p.wk, q.wk, m.capture); }
                else              { m.from = p.wq; m.to = q.wq; m.san = sanOf(g, 'Q', true, p.wq, q.wq, m.capture); }
                if (m.capture) {
                    // A white man took a black king: the destination is the
                    // square that king stood on, which q no longer records.
                    m.to = (p.bk1 >= 0 && q.bk1 < 0) ? p.bk1 : p.bk2;
                    m.san = sanOf(g, q.wk != p.wk ? 'K' : 'Q', true, m.from, m.to, true);
                }
            } else {
                const Sq a[2] = { p.bk1, p.bk2 }, b[2] = { q.bk1, q.bk2 };
                Sq from = -1, to = -1;
                for (int i = 0; i < 2; ++i) {
                    if (a[i] >= 0 && a[i] != b[0] && a[i] != b[1]) from = a[i];
                    if (b[i] >= 0 && b[i] != a[0] && b[i] != a[1]) to = b[i];
                }
                if (kind == CapMove::TakesWhiteKing) to = p.wk;
                else if (kind == CapMove::TakesQueen) to = p.wq;
                m.from = from; m.to = to;
                m.san = sanOf(g, 'K', false, from, to, m.capture);
            }
            m.after = mkView(q, !v.wtm);
            m.val = value(m.after);
            const int nb = (q.bk1 >= 0) + (q.bk2 >= 0);
            if (q.wk < 0)      { m.playable = false; m.note = "takes the white king, and that is the game"; }
            else if (nb == 0)  { m.playable = false; m.note = "takes the last black king, and that is the game"; }
            else if (kind == CapMove::TakesQueen) m.note = "takes the queen: kings alone from here";
            else if (kind == CapMove::TakesKing)  m.note = "takes a king; the other one still has to be caught";
            out.push_back(std::move(m));
        });
        return out;
    }

    bool quiet(const View& v) const override {
        PosKK p; std::string err;
        if (!toPos(v, p, err)) return false;
        if (p.wk < 0 || p.bk1 < 0 || p.bk2 < 0 || p.wq < 0) return false;
        for (int s = 0; s < 2; ++s) {
            bool grab = false;
            kqkkCapMoves(*t_, p, s == 0,
                         [&](const PosKK&, CapMove k, int16_t) { grab |= (k != CapMove::Quiet); });
            if (grab) return false;
        }
        return true;
    }

    View start(std::string& note) const override {
        const IndexKQKK& idx = t_->idx;
        PosKK bestQuiet{}, bestAny{}, anyQuiet{};
        int bq = -1, ba = -1;
        bool haveQuiet = false;
        for (U64 blk = 0; blk < idx.nblk; ++blk) {
            PosKK p;
            p.wk = idx.blkWk[blk]; p.bk1 = idx.blkB1[blk]; p.bk2 = idx.blkB2[blk];
            for (U32 q = 0; q < idx.npc; ++q) {
                p.wq = (Sq)q;
                const int16_t x = t_->valueAt(p, true);
                if (x == VC_DEAD || x == VC_UNKNOWN) continue;
                View v = mkView(p, true);
                if (x > 0) {
                    if (x > ba) { ba = x; bestAny = p; }
                    if (x > bq && quiet(v)) { bq = x; bestQuiet = p; }
                } else if (!haveQuiet && quiet(v)) { anyQuiet = p; haveQuiet = true; }
            }
        }
        if (bq >= 0) { note = "the deepest win White has from a quiet position"; return mkView(bestQuiet, true); }
        if (ba >= 0) { note = "the deepest win White has -- no quiet position reaches it"; return mkView(bestAny, true); }
        if (haveQuiet) { note = "a quiet position; White has no win anywhere on this board"; return mkView(anyQuiet, true); }
        note = "no legal position found";
        return View{};
    }

private:
    std::unique_ptr<TableKQKKCap> t_;
};

// ---------------------------------------------------------------------------
// W white men against B black men, capture rules, one kind of man a side.
// ---------------------------------------------------------------------------
class KingsEngine : public Engine {
public:
    KingsEngine(int n, int W, int B, int pw, int pb, int threads, const Store& store)
        : g_(n), W_(W), B_(B), pw_(pw), pb_(pb) {
        t_ = std::make_unique<TableKings>(n, W, B, pw, pb);
        // This family brought its own store to the party: `TableKings::store`
        // maps any table of the lattice already on disk and writes back the
        // ones it solves, per table rather than per configuration.  That is
        // strictly better than anything wrapped around the outside of it --
        // KKK vs KK reuses the KK vs K it shares with every other row -- so
        // the only thing to do here is point it at the directory.
        const auto t0 = std::chrono::steady_clock::now();
        if (!store.dir.empty()) t_->store(store.dir, false);
        t_->generate(threads, false);
        // The census is NOT taken here.  It walks the whole lattice, and for
        // tables that came off a store that walk is a random-access pass over
        // a mapped file on an external drive -- 83 s for 3K vs 2N on 9 x 9,
        // where solving the thing from cold takes a fraction of that, which
        // made a store on a slow drive SLOWER than no store at all.  Nothing
        // but start() reads it, and a request that names a position never
        // calls start(), so it waits until something asks.
        threads_ = threads;
        char name[64];
        std::snprintf(name, sizeof name, "%d%c vs %d%c on %d x %d",
                      W, capPieceLetter(pw), B, capPieceLetter(pb), n, n);
        // One note per table of the lattice rather than one for the lot: the
        // whole question is whether the drive was used, and "solved or mapped"
        // answered it with a shrug.
        int mapped = 0, built = 0;
        t_->tableCounts(mapped, built);
        for (int i = 0; i < mapped; ++i) g_tally.loaded++;
        for (int i = 0; i < built; ++i) g_tally.solved++;
        char what[64];
        std::snprintf(what, sizeof what, "%s %d of %d tables of",
                      built == 0 ? "mapped" : mapped == 0 ? "solved" : "mapped",
                      built == 0 ? mapped : mapped == 0 ? built : mapped, mapped + built);
        std::fprintf(stderr, "    %s %s in %.2fs\n", what, name, secondsSince(t0));
        std::fflush(stderr);
    }

    const Geometry& geo() const override { return g_; }
    std::string material() const override {
        return std::string(W_, capPieceLetter(pw_)) + " vs " + std::string(B_, capPieceLetter(pb_));
    }

    View mkView(const std::vector<Sq>& W, const std::vector<Sq>& B, bool wtm) const {
        View v; v.wtm = wtm;
        for (Sq s : W) v.men.push_back({ 'w', capPieceLetter(pw_), s });
        for (Sq s : B) v.men.push_back({ 'b', capPieceLetter(pb_), s });
        return v;
    }

    bool split(const View& v, std::vector<Sq>& W, std::vector<Sq>& B, std::string& err) const {
        W.clear(); B.clear();
        for (const Man& m : v.men) {
            if (m.color == 'w' && m.piece == capPieceLetter(pw_)) W.push_back(m.sq);
            else if (m.color == 'b' && m.piece == capPieceLetter(pb_)) B.push_back(m.sq);
            else { err = "this configuration has no such man"; return false; }
        }
        if ((int)W.size() > W_ || (int)B.size() > B_) { err = "too many men"; return false; }
        std::sort(W.begin(), W.end());
        std::sort(B.begin(), B.end());
        return true;
    }

    bool accept(View& v, std::string& err) const override {
        std::vector<Sq> W, B;
        if (!split(v, W, B, err)) return false;
        if (W.empty() || B.empty()) { err = "the game is already over"; return false; }
        v = mkView(W, B, v.wtm);
        return true;
    }

    Val value(const View& v) const override {
        std::vector<Sq> W, B; std::string err;
        if (!split(v, W, B, err)) return mkVal(Val::Illegal, 0, false);
        if (W.empty()) { Val r = mkVal(Val::BlackWins, 0, false);
                         r.text = "Black has won -- White has nothing left";
                         r.terminal = "White has nothing left"; return r; }
        if (B.empty()) { Val r = mkVal(Val::WhiteWins, 0, false);
                         r.text = "White has won -- Black has nothing left";
                         r.terminal = "Black has nothing left"; return r; }
        return moverRelative(t_->probe(W, B, v.wtm), v.wtm, false);
    }

    std::vector<MoveOut> moves(const View& v) const override {
        std::vector<Sq> W, B; std::string err;
        if (!split(v, W, B, err) || W.empty() || B.empty()) return {};
        std::vector<MoveOut> out;
        for (const KingsMove& k : t_->moves(W, B, v.wtm)) {
            MoveOut m;
            m.from = k.from; m.to = k.to; m.capture = k.capture;
            m.san = sanOf(g_, v.wtm ? capPieceLetter(pw_) : capPieceLetter(pb_),
                          v.wtm, k.from, k.to, k.capture);
            m.after = mkView(k.W, k.B, !v.wtm);
            m.val = value(m.after);
            if (k.ends) {
                m.playable = false;
                m.note = v.wtm ? "takes Black's last man, and that is the game"
                               : "takes White's last man, and that is the game";
            } else if (k.capture) {
                m.note = "a capture: the game goes on with less material";
            }
            out.push_back(std::move(m));
        }
        return out;
    }

    bool quiet(const View& v) const override {
        std::vector<Sq> W, B; std::string err;
        if (!split(v, W, B, err) || W.empty() || B.empty()) return false;
        return t_->quiet(W, B);
    }

    // The census, taken once and only when something needs it.
    const KingsStats& stats() const {
        if (!censused_) { t_->census(threads_, false); censused_ = true; }
        return t_->stats();
    }

    View start(std::string& note) const override {
        if (skipScan) {
            std::vector<Sq> W, B;
            for (int i = 0; i < W_; ++i) W.push_back((Sq)i);
            for (int i = 0; i < B_; ++i) B.push_back((Sq)(W_ + i));
            note = "White wins nothing on this board, which the statistics already "
                   "record; an arbitrary placement rather than a scan of the table";
            return mkView(W, B, true);
        }
        const KingsStats& s = stats();
        auto cut = [&](const std::vector<Sq>& p, std::vector<Sq>& W, std::vector<Sq>& B) {
            W.assign(p.begin(), p.begin() + W_);
            B.assign(p.begin() + W_, p.end());
        };
        std::vector<Sq> W, B;
        if (s.deepestWhiteQuiet > 0 && (int)s.posWhiteQuiet.size() == W_ + B_) {
            cut(s.posWhiteQuiet, W, B);
            note = "the deepest win White has from a quiet position";
            return mkView(W, B, true);
        }
        if (s.deepestWhite > 0 && (int)s.posWhite.size() == W_ + B_) {
            cut(s.posWhite, W, B);
            note = "the deepest win White has -- no quiet position reaches it";
            return mkView(W, B, true);
        }
        // White outnumbered is an ordinary configuration in this lattice --
        // one man against two is generated as readily as three against one --
        // and there White has nothing to show.  Opening on Black's deepest win
        // is the same question asked of the other side; before this the page
        // answered 404 for a table that was sitting on the drive.
        if (s.deepestBlackQuiet > 0 && (int)s.posBlackQuiet.size() == W_ + B_) {
            cut(s.posBlackQuiet, W, B);
            note = "White has no win here; the deepest win BLACK has from a quiet position";
            return mkView(W, B, false);
        }
        if (s.deepestBlack > 0 && (int)s.posBlack.size() == W_ + B_) {
            cut(s.posBlack, W, B);
            note = "White has no win here; the deepest win Black has";
            return mkView(W, B, false);
        }
        // Neither side wins anywhere -- every position of this material is
        // drawn, which is itself a result.  Any placement shows it.
        if (g_.nsq >= W_ + B_) {
            W.clear(); B.clear();
            for (int i = 0; i < W_; ++i) W.push_back((Sq)i);
            for (int i = 0; i < B_; ++i) B.push_back((Sq)(W_ + i));
            note = "neither side wins anywhere on this board; an arbitrary placement";
            return mkView(W, B, true);
        }
        note = "no win found on this board";
        return View{};
    }

private:
    Geometry g_;
    int W_, B_, pw_, pb_;
    int threads_ = 1;
    mutable bool censused_ = false;
    std::unique_ptr<TableKings> t_;
};

// ---------------------------------------------------------------------------
// Two unlike white men against one black man, capture rules.
// ---------------------------------------------------------------------------
class MixedEngine : public Engine {
public:
    // No store: this one has no on-disk form, and does not need one.  It is
    // the unreduced solver, so its tables are eight times the size of the
    // reduced ones -- and it solves a board in hundredths of a second, which
    // is less than reading the file back would cost.
    MixedEngine(int n, int p0, int p1, int pb, int threads, const Store& store)
        : g_(n), p0_(p0), p1_(p1), pb_(pb) {
        t_ = std::make_unique<TableMixed>(n, p0, p1, pb);
        // Same bargain as the kings lattice above: point it at the store and a
        // configuration already on the drive opens instead of being re-solved.
        const auto t0 = std::chrono::steady_clock::now();
        t_->generate(threads, store.dir);
        char name[64];
        std::snprintf(name, sizeof name, "%c%c vs %c on %d x %d", capPieceLetter(p0),
                      capPieceLetter(p1), capPieceLetter(pb), n, n);
        note(t_->fromStore() ? "loaded" : "solved", name, secondsSince(t0), false);
    }

    const Geometry& geo() const override { return g_; }
    std::string material() const override {
        return std::string(1, capPieceLetter(p0_)) + capPieceLetter(p1_) + " vs " +
               capPieceLetter(pb_);
    }

    View mkView(Sq w0, Sq w1, Sq b, bool wtm) const {
        View v; v.wtm = wtm;
        if (w0 >= 0) v.men.push_back({ 'w', capPieceLetter(p0_), w0 });
        if (w1 >= 0) v.men.push_back({ 'w', capPieceLetter(p1_), w1 });
        if (b >= 0)  v.men.push_back({ 'b', capPieceLetter(pb_), b });
        return v;
    }

    bool split(const View& v, Sq& w0, Sq& w1, Sq& b, std::string& err) const {
        std::vector<Man> left = v.men;
        w0 = take(left, 'w', capPieceLetter(p0_));
        // The two white men may be of the same kind when this table is run as
        // the cross-check on the reduced solver, so the second lookup has to
        // come after the first has taken its man out.
        w1 = take(left, 'w', capPieceLetter(p1_));
        b  = take(left, 'b', capPieceLetter(pb_));
        if (!left.empty()) { err = "this configuration has no such man"; return false; }
        return true;
    }

    bool accept(View& v, std::string& err) const override {
        Sq w0, w1, b;
        if (!split(v, w0, w1, b, err)) return false;
        if (b < 0 || (w0 < 0 && w1 < 0)) { err = "the game is already over"; return false; }
        v = mkView(w0, w1, b, v.wtm);
        return true;
    }

    Val value(const View& v) const override {
        Sq w0, w1, b; std::string err;
        if (!split(v, w0, w1, b, err)) return mkVal(Val::Illegal, 0, false);
        if (b < 0) { Val r = mkVal(Val::WhiteWins, 0, false);
                     r.text = "White has won -- Black has nothing left";
                     r.terminal = "Black has nothing left"; return r; }
        if (w0 < 0 && w1 < 0) { Val r = mkVal(Val::BlackWins, 0, false);
                                r.text = "Black has won -- White has nothing left";
                                r.terminal = "White has nothing left"; return r; }
        return moverRelative(t_->probe(w0, w1, b, v.wtm), v.wtm, false);
    }

    std::vector<MoveOut> moves(const View& v) const override {
        Sq w0, w1, b; std::string err;
        if (!split(v, w0, w1, b, err)) return {};
        std::vector<MoveOut> out;
        for (const MixedMove& k : t_->moves(w0, w1, b, v.wtm)) {
            MoveOut m;
            m.from = k.from; m.to = k.to; m.capture = k.capture;
            const char letter = v.wtm ? capPieceLetter(k.mover == 0 ? p0_ : p1_)
                                      : capPieceLetter(pb_);
            m.san = sanOf(g_, letter, v.wtm, k.from, k.to, k.capture);
            m.after = mkView(k.w0, k.w1, k.b, !v.wtm);
            m.val = value(m.after);
            if (k.ends) {
                m.playable = false;
                m.note = "takes the last man, and that is the game";
            } else if (k.capture) {
                m.note = "a capture: the game goes on with less material";
            }
            out.push_back(std::move(m));
        }
        return out;
    }

    bool quiet(const View& v) const override {
        Sq w0, w1, b; std::string err;
        if (!split(v, w0, w1, b, err)) return false;
        if (w0 < 0 || w1 < 0 || b < 0) return false;
        return t_->quiet(w0, w1, b);
    }

    View start(std::string& note) const override {
        Sq w0 = -1, w1 = -1, b = -1;
        int plies = 0;
        if (t_->deepestQuiet(w0, w1, b, plies)) {
            note = "the deepest win White has from a quiet position";
            return mkView(w0, w1, b, true);
        }
        // The same fallbacks every other adapter has, which this one was
        // missing: a board can be too small to hold a quiet placement at all
        // -- on 3 x 3 a queen bears on every square -- and the page then had
        // nothing to open on and answered 404 for a table sitting on the
        // drive.
        if (t_->deepestAny(w0, w1, b, plies)) {
            note = "no quiet win on this board; the deepest win from any placement";
            return mkView(w0, w1, b, true);
        }
        if (g_.n * g_.n >= 3) {
            note = "White has no win on this board; an arbitrary placement";
            return mkView(0, 1, 2, true);
        }
        note = "nothing to show on a board this small";
        return View{};
    }

private:
    Geometry g_;
    int p0_, p1_, pb_;
    std::unique_ptr<TableMixed> t_;
};

// ---------------------------------------------------------------------------
// The catalogue.
// ---------------------------------------------------------------------------

Family shared(const char* id, const char* label, const char* title, const char* blurb,
              Endgame eg, bool capture, int maxN, int defN = 8) {
    Family f;
    f.id = id; f.label = label; f.title = title; f.blurb = blurb;
    // The page groups by rule set first, so the heading here names the SHAPE
    // of the endgame and not the rules again.  Both readings of a bare black
    // king sit under the same heading, one in each half of the page.
    f.group = "A bare black king";
    f.rules = capture ? "capture" : "mate";
    f.kind = Family::Shared;
    f.arg[0] = (int)eg; f.arg[1] = capture ? 1 : 0;
    f.minN = 3; f.maxN = maxN; f.defN = defN;
    return f;
}

std::vector<Family> buildCatalogue() {
    std::vector<Family> c;

    // Group 1: Black has a lone king -- the shared solver.
    c.push_back(shared("kqk", "KQK", "King and queen against king",
                       "The simplest of them, and the one the 8x8 figures are checked against.",
                       Endgame::KQK, false, 20));
    c.push_back(shared("krk", "KRK", "King and rook against king",
                       "A rook is a queen restricted to the four orthogonal rays.",
                       Endgame::KRK, false, 20));
    c.push_back(shared("kbbk", "KBBK", "King and two bishops against king",
                       "Two like pieces, so a configuration is an unordered pair. "
                       "Same-coloured bishops never mate.",
                       Endgame::KBBK, false, 14));
    c.push_back(shared("kbnk", "KBNK", "King, bishop and knight against king",
                       "The deep one: mate in 33 on 8x8, and the only endgame whose "
                       "depths outgrow a one-byte entry before its table outgrows memory.",
                       Endgame::KBNK, false, 13));
    c.push_back(shared("knk", "KNK", "King and knight against king",
                       "No mate exists anywhere. Every position is drawn, which is "
                       "itself a result the solver computes rather than assumes.",
                       Endgame::KNK, false, 20));
    c.push_back(shared("knnk", "KNNK", "King and two knights against king",
                       "Two knights cannot force mate, but they can mate: the table "
                       "holds wins in one.",
                       Endgame::KNNK, false, 12));
    c.push_back(shared("knnnk", "KNNNK", "King and three knights against king",
                       "Three alike, so a configuration is an unordered triple -- and "
                       "the first endgame here whose captures convert rather than draw.",
                       Endgame::KNNNK, false, 9, 7));
    c.push_back(shared("kbk", "KBK", "King and bishop against king",
                       "A dead draw under the mating rules, and there only as what "
                       "KQKB's ...BxQ leaves.",
                       Endgame::KBK, false, 20));

    // Group 2: Black is armed.
    {
        Family f;
        f.id = "kqkr"; f.label = "KQKR"; f.title = "King and queen against king and rook";
        f.group = "Black is armed"; f.rules = "mate";
        f.blurb = "Signed entries: Black's ...RxQ leaves a bare white king, so this "
                  "table has wins, draws and losses. Converts into KQK and KRK.";
        f.kind = Family::Kqkr; f.arg[0] = (int)Endgame::KQKR;
        // 12 rather than 11: this is a four-man table, so it grows as m^4 and
        // 12 x 12 is under 200 MB.  The old ceiling was caution, not a limit.
        f.minN = 3; f.maxN = 12; f.defN = 8;
        c.push_back(f);
        f.id = "kqkb"; f.label = "KQKB"; f.title = "King and queen against king and bishop";
        f.blurb = "The same solver with Black's man on the diagonals, and what KQKBB "
                  "converts into when White takes a bishop.";
        f.arg[0] = (int)Endgame::KQKB;
        c.push_back(f);

        // The capture readings, which go to the general solver.  These two were
        // written before the other eight and had their own rows here; the
        // reason for moving them is the reason given at the loop below, and it
        // applies to all ten equally.  Missing these two because they were
        // spelled out separately is exactly the kind of thing a sweep over the
        // loop alone does not catch: the eight moved, these stayed, and the
        // store went on filling with kqkr files.
        {
            Family gf;
            gf.group = "Black is armed"; gf.rules = "capture";
            gf.kind = Family::General;
            gf.minN = 3; gf.maxN = 11; gf.defN = 8;
            gf.blurb = "A king is an ordinary man under these rules, and a side is "
                       "beaten when its last one is taken -- by anything, the other "
                       "king included.";
            gf.id = "kqkr-capture"; gf.label = "KQKR (capture)";
            gf.title = "King and queen against king and rook, capture rules";
            gf.arg[0] = (int)Piece::Queen; gf.arg[1] = (int)Piece::Rook;
            c.push_back(gf);
            gf.id = "kqkb-capture"; gf.label = "KQKB (capture)";
            gf.title = "King and queen against king and bishop, capture rules";
            gf.arg[0] = (int)Piece::Queen; gf.arg[1] = (int)Piece::Bishop;
            c.push_back(gf);
        }

        // The rest of one white man against one black man.  KQKR and KQKB
        // were written because KQKBB needed them; generalising that solver
        // from "White has a queen" to "White has a man" completes the set,
        // and with the colour mirror these sixteen tables answer every
        // four-man endgame in which both sides are armed.
        struct Row { Endgame eg; const char* id; const char* label; const char* blurb; };
        static const Row rows[] = {
            { Endgame::KQKQ, "kqkq", "KQKQ",
              "Queen against queen: the first endgame here that is a real fight, "
              "with wins for both sides and draws between them." },
            { Endgame::KQKN, "kqkn", "KQKN",
              "A queen against a knight, which cannot be driven off a square it "
              "does not stand next to." },
            { Endgame::KRKR, "krkr", "KRKR",
              "Rook against rook: drawn in ordinary chess, and on a small board "
              "not always." },
            { Endgame::KRKB, "krkb", "KRKB",
              "The textbook fortress draw at 8 x 8, and the board size is the "
              "variable the textbook does not have." },
            { Endgame::KRKN, "krkn", "KRKN",
              "Rook against knight, where the defence is to keep the knight "
              "beside its king." },
            { Endgame::KBKB, "kbkb", "KBKB",
              "Bishop against bishop, and neither can mate: every win is a "
              "capture of a man that was already hanging." },
            { Endgame::KBKN, "kbkn", "KBKN",
              "Bishop against knight, the same way -- the table is almost all "
              "draws, which is itself the result." },
            { Endgame::KNKN, "knkn", "KNKN",
              "Knight against knight. Nothing can be forced at all; the table "
              "exists to say so exactly." },
        };
        for (const Row& r : rows) {
            Family g;
            g.kind = Family::Kqkr;
            g.group = "Black is armed";
            g.minN = 3; g.maxN = 12; g.defN = 8;
            g.id = r.id; g.label = r.label;
            g.title = std::string(Material::of(r.eg).have());
            g.title[0] = (char)std::toupper((unsigned char)g.title[0]);
            g.blurb = r.blurb; g.rules = "mate";
            g.arg[0] = (int)r.eg; g.arg[1] = 0;
            c.push_back(g);
            // The capture reading goes to the general solver, not to this one.
            // kqkr.cpp is built on chess legality: its kings may not stand
            // beside each other and neither may be captured.  Under these
            // rules both sides hold a king and either may take the other's,
            // which is not a detail -- against the stated rule its capture
            // tables missed 57% of the placements outright and disagreed on
            // 84,932 of the verdicts they did give.  Its ordinary-rules tables
            // are exact on every placement and keep the family above.
            g.id = std::string(r.id) + "-capture";
            g.label = std::string(r.label) + " (capture)";
            g.title += ", capture rules";
            g.rules = "capture";
            g.blurb = "The same men under the capture rules: a king is an ordinary "
                      "man here, and a side is beaten when its last one is taken.";
            g.kind = Family::General;
            g.arg[0] = (int)whitePieceOf(r.eg);
            g.arg[1] = (int)blackPieceOf(r.eg);
            g.maxN = 11;      // the general solver's index is unreduced
            c.push_back(g);
            g.kind = Family::Kqkr;   // restore for the next row
            g.maxN = 12;
        }
    }
    {
        Family f;
        f.id = "kqkbb"; f.label = "KQKBB"; f.title = "King and queen against king and two bishops";
        f.group = "Black is armed"; f.rules = "mate";
        f.blurb = "Five men, and the first endgame here in which the armed side is the "
                  "one with two like pieces. Converts twice over.";
        f.kind = Family::Kqkbb;
        // Five men, so it grows as m^5: 238 MB at 8 x 8, 2.3 GB at 10 x 10
        // and about 7 GB at 11 x 11.  The ceiling is where a board stops
        // fitting in memory rather than where it stops being interesting.
        f.minN = 3; f.maxN = 11; f.defN = 6;
        c.push_back(f);
    }

    // Group 3: two black kings.
    {
        Family f;
        f.id = "kqkk"; f.label = "KQKK"; f.title = "King and queen against two black kings";
        f.group = "Two black kings"; f.rules = "mate";
        f.blurb = "The two black kings may stand beside each other but not beside the "
                  "white king, and a mate counts only when both are mated at once.";
        f.kind = Family::Kqkk; f.arg[0] = (int)KkRules::Strict;
        f.minN = 4; f.maxN = 12; f.defN = 8;
        c.push_back(f);
        f.id = "kqkk-loose"; f.label = "KQKK (loose)";
        f.title = "King and queen against two black kings, the loose reading";
        f.blurb = "The same material under the other reading of the rule: Black may "
                  "not leave BOTH kings attacked at once, rather than either.";
        f.arg[0] = (int)KkRules::Loose;
        c.push_back(f);
    }
    {
        Family f;
        f.id = "kqkk-capture"; f.label = "KQKK (capture)";
        f.title = "King and queen against two black kings, capture rules";
        f.group = "Two black kings"; f.rules = "capture";
        f.blurb = "Every king an ordinary capturable man, no check and no mate, the "
                  "game won by taking the opponent's last. The one endgame here that "
                  "Black can win.";
        f.kind = Family::KqkkCap;
        // 3 x 3 is a real board for this material: four men on nine squares,
        // and under the capture rules there is no adjacency rule to violate.
        // The solver has always accepted it; only this line said otherwise.
        f.minN = 3; f.maxN = 9; f.defN = 8;
        c.push_back(f);
    }

    // Group 4: kings only, capture rules.
    {
        struct Row { int W, B; const char* label; const char* blurb; int maxN; int defN; };
        static const Row rows[] = {
            { 1, 1, "K vs K", "Two kings and nothing else. Whoever is to move with the "
                              "kings already touching takes the other.", 20, 8 },
            { 2, 1, "KK vs K", "The table the whole lattice turns on.", 16, 8 },
            { 3, 1, "KKK vs K", "Three white kings hunting one.", 12, 8 },
            { 4, 1, "KKKK vs K", "Four against one.", 9, 8 },
            { 2, 2, "KK vs KK", "Even material, and a real fight.", 12, 8 },
            { 3, 2, "KKK vs KK", "The headline table: White must take both of Black's "
                                 "kings, Black all of White's.", 10, 8 },
            { 4, 2, "KKKK vs KK", "The largest of the lattice, and much the slowest "
                                  "to build: 8 x 8 takes about three quarters of a minute.", 8, 6 },
        };
        for (const Row& r : rows) {
            Family f;
            char id[64];
            std::snprintf(id, sizeof id, "kings-%d-%d-king-king", r.W, r.B);
            f.id = id; f.label = r.label;
            f.title = std::string(r.label) + " under capture rules";
            f.group = "Like pieces, the conversion lattice"; f.rules = "capture";
            f.blurb = r.blurb;
            f.kind = Family::Kings;
            f.arg[0] = r.W; f.arg[1] = r.B; f.arg[2] = CP_KING; f.arg[3] = CP_KING;
            f.minN = 3; f.maxN = r.maxN; f.defN = std::min(r.defN, r.maxN);
            c.push_back(f);
        }
    }
    {
        Family f;
        f.id = "kings-2-1-rook-rook"; f.label = "RR vs R";
        f.title = "Two white rooks against one black rook, capture rules";
        f.group = "Like pieces, the conversion lattice"; f.rules = "capture";
        f.blurb = "The same lattice with the king's step swapped for a rook's ray: the "
                  "symmetry reduction does not care which man is on the board.";
        f.kind = Family::Kings;
        f.arg[0] = 2; f.arg[1] = 1; f.arg[2] = CP_ROOK; f.arg[3] = CP_ROOK;
        f.minN = 3; f.maxN = 12; f.defN = 8;
        c.push_back(f);
        f.id = "kings-2-1-knight-knight"; f.label = "NN vs N";
        f.title = "Two white knights against one black knight, capture rules";
        f.blurb = "Knights jump, so nothing can be blocked and nothing defends by "
                  "standing in the way.";
        f.arg[2] = CP_KNIGHT; f.arg[3] = CP_KNIGHT;
        c.push_back(f);
    }

    // Group 5: two unlike white men.
    {
        struct Row { int p0, p1, pb; const char* id; const char* label; const char* blurb; };
        static const Row rows[] = {
            { CP_KING, CP_QUEEN, CP_KNIGHT, "mixed-king-queen-knight", "KQ vs N",
              "A king and a queen against a knight. Black's capture branches on WHICH "
              "white man it takes, which is what this solver has that the kings one "
              "cannot express." },
            { CP_KING, CP_ROOK, CP_KNIGHT, "mixed-king-rook-knight", "KR vs N",
              "The same with a rook, whose rays a third man can block." },
            { CP_KING, CP_QUEEN, CP_KING, "mixed-king-queen-king", "KQ vs K",
              "King and queen against a bare king under the capture rules rather than "
              "the mating ones -- the same material as KQK, a different game." },
        };
        for (const Row& r : rows) {
            Family f;
            f.id = r.id; f.label = r.label;
            f.title = std::string(r.label) + " under capture rules";
            f.group = "Two unlike white men"; f.rules = "capture";
            f.blurb = r.blurb;
            f.kind = Family::Mixed;
            f.arg[0] = r.p0; f.arg[1] = r.p1; f.arg[2] = r.pb;
            f.minN = 3; f.maxN = 12; f.defN = 8;
            c.push_back(f);
        }
    }

    // Group 6: the capture readings of two mate-rule endgames, which are real
    // results rather than curiosities: ...KxB leaves K+B vs K, which under
    // these rules a bare king does not always survive.
    c.push_back(shared("kbbk-capture", "KBBK (capture)",
                       "King and two bishops against king, capture rules",
                       "Stalemate is a loss here, so ...KxB converts into the K+B vs K "
                       "capture table rather than into a draw.",
                       Endgame::KBBK, true, 12));
    c.push_back(shared("kbk-capture", "KBK (capture)",
                       "King and bishop against king, capture rules",
                       "A dead draw under the mating rules; under these a lone bishop "
                       "and king can take a cornered king's last square away.",
                       Endgame::KBK, true, 16));
    // Two white men against a bare black king, the seven the shared solver
    // did not have.  Every one of them converts: unlike KBBK, where ...KxB
    // leaves a dead draw, taking one man here leaves material that still
    // wins, so the value has to be looked up rather than assumed.
    {
        struct Row { Endgame eg; const char* id; const char* label; const char* blurb; };
        static const Row rows[] = {
            { Endgame::KQQK, "kqqk", "KQQK", "Two queens, and the fastest mate here." },
            { Endgame::KQRK, "kqrk", "KQRK", "Queen and rook. Taking the queen leaves KRK "
              "and taking the rook leaves KQK -- two different tables, which is what this "
              "solver could not express until now." },
            { Endgame::KQBK, "kqbk", "KQBK", "Queen and bishop against a bare king." },
            { Endgame::KQNK, "kqnk", "KQNK", "Queen and knight; the knight is the man "
              "Black's king can most easily reach." },
            { Endgame::KRRK, "krrk", "KRRK", "Two rooks: the ladder mate, and on a wide "
              "board the ladder has further to walk." },
            { Endgame::KRBK, "krbk", "KRBK", "Rook and bishop." },
            { Endgame::KRNK, "krnk", "KRNK", "Rook and knight." },
        };
        for (const Row& r : rows) {
            c.push_back(shared(r.id, r.label, Material::of(r.eg).have(), r.blurb,
                               r.eg, false, 8));
            c.push_back(shared((std::string(r.id) + "-capture").c_str(),
                               (std::string(r.label) + " (capture)").c_str(),
                               Material::of(r.eg).have(),
                               "The same men with stalemate scored as a loss.",
                               r.eg, true, 8));
        }
    }

    // Three white men against a bare black king: the nineteen the index
    // could not hold until it learned two more shapes.  Every one of them
    // converts twice over -- take a man and two are left, take another and
    // one is -- so the chain runs three deep.
    {
        static const Endgame threes[] = {
            Endgame::KQQQK,
            Endgame::KQQRK,
            Endgame::KQQBK,
            Endgame::KQQNK,
            Endgame::KQRRK,
            Endgame::KQRBK,
            Endgame::KQRNK,
            Endgame::KQBBK,
            Endgame::KQBNK,
            Endgame::KQNNK,
            Endgame::KRRRK,
            Endgame::KRRBK,
            Endgame::KRRNK,
            Endgame::KRBBK,
            Endgame::KRBNK,
            Endgame::KRNNK,
            Endgame::KBBBK,
            Endgame::KBBNK,
            Endgame::KBNNK
        };
        for (Endgame eg : threes) {
            std::string id = Material::of(eg).name();
            for (char& c : id) c = (char)(c >= 'A' && c <= 'Z' ? c - 'A' + 'a' : c);
            const std::string label = Material::of(eg).name();
            c.push_back(shared(id.c_str(), label.c_str(), Material::of(eg).have(),
                               "Three men against a bare king, and a capture leaves "
                               "two that still win: the value of every capture is "
                               "looked up rather than assumed.",
                               eg, false, 8));
            c.push_back(shared((id + "-capture").c_str(), (label + " (capture)").c_str(),
                               Material::of(eg).have(),
                               "The same three men with stalemate scored as a loss.",
                               eg, true, 8));
        }
    }

    // The other six readings, which were being generated and measured long
    // before anything listed them: their tables were on the drive under names
    // the loader knew and the catalogue did not, so the one place they could
    // not be looked at was the browser.  The figures quoted are this store's
    // own, from the 8 x 8 row of stats.csv.
    c.push_back(shared("kqk-capture", "KQK (capture)",
                       "King and queen against king, capture rules",
                       "With one king a side the capture rules come to a single change: "
                       "stalemate is a loss rather than a draw. It is enough to win from "
                       "every placement with the move on 8 x 8, the longest in 15 plies "
                       "against the mating table's 19.",
                       Endgame::KQK, true, 20));
    c.push_back(shared("krk-capture", "KRK (capture)",
                       "King and rook against king, capture rules",
                       "Also won from every placement with the move on 8 x 8, and at 31 "
                       "plies it takes twice as long as the queen.",
                       Endgame::KRK, true, 20));
    c.push_back(shared("knk-capture", "KNK (capture)",
                       "King and knight against king, capture rules",
                       "Under the mating rules every position of this material is drawn. "
                       "With stalemate a loss, 1.4% of placements with the move are won "
                       "on 8 x 8: a king and knight can take a cornered king's last "
                       "square away, just almost never.",
                       Endgame::KNK, true, 20));
    c.push_back(shared("knnk-capture", "KNNK (capture)",
                       "King and two knights against king, capture rules",
                       "Two knights cannot force mate. They can force stalemate: 99.4% of "
                       "placements with the move are won on 8 x 8, the deepest in 51 plies.",
                       Endgame::KNNK, true, 12));
    c.push_back(shared("knnnk-capture", "KNNNK (capture)",
                       "King and three knights against king, capture rules",
                       "The third knight closes the gap -- every placement with the move "
                       "is won on 8 x 8 -- and a knight Black takes converts into the "
                       "two-knight capture table rather than into a draw.",
                       Endgame::KNNNK, true, 12, 7));
    c.push_back(shared("kbnk-capture", "KBNK (capture)",
                       "King, bishop and knight against king, capture rules",
                       "The mating version is the deep one at 33 moves on 8 x 8; with "
                       "stalemate a loss the same two men win 99.5% of placements with "
                       "the move, the deepest in 37 plies.",
                       Endgame::KBNK, true, 13));
    return c;
}

int capPieceFromName(const std::string& t, bool& ok) {
    ok = true;
    if (t == "king")   return CP_KING;
    if (t == "rook")   return CP_ROOK;
    if (t == "knight") return CP_KNIGHT;
    if (t == "bishop") return CP_BISHOP;
    if (t == "queen")  return CP_QUEEN;
    ok = false;
    return CP_KING;
}

std::vector<std::string> split(const std::string& s, char sep) {
    std::vector<std::string> out;
    std::string cur;
    for (char c : s) {
        if (c == sep) { out.push_back(cur); cur.clear(); }
        else cur += c;
    }
    out.push_back(cur);
    return out;
}

} // namespace

const std::vector<Family>& familyCatalogue() {
    static const std::vector<Family> c = buildCatalogue();
    return c;
}

bool familyById(const std::string& id, Family& out) {
    for (const Family& f : familyCatalogue())
        if (f.id == id) { out = f; return true; }

    // Not listed, but possibly still addressable.  `kings-W-B-white-black` and
    // `mixed-w1-w2-black` name configurations the catalogue does not bother to
    // show; they answer exactly as a listed one would.
    const std::vector<std::string> t = split(id, '-');
    if (t.size() == 5 && t[0] == "kings") {
        bool ok1, ok2;
        const int W = std::atoi(t[1].c_str()), B = std::atoi(t[2].c_str());
        const int pw = capPieceFromName(t[3], ok1), pb = capPieceFromName(t[4], ok2);
        if (!ok1 || !ok2 || W < 1 || W > 4 || B < 1 || B > 2) return false;
        out = Family{};
        out.id = id;
        out.label = std::string(W, capPieceLetter(pw)) + " vs " + std::string(B, capPieceLetter(pb));
        out.title = out.label + " under capture rules";
        out.group = "Like pieces, the conversion lattice"; out.rules = "capture";
        out.blurb = "Addressed by id rather than listed in the catalogue.";
        out.kind = Family::Kings;
        out.arg[0] = W; out.arg[1] = B; out.arg[2] = pw; out.arg[3] = pb;
        // The tables of this lattice are kept per table in the --tb store and
        // the engine above maps them, so a board that has been generated opens
        // at once rather than being rebuilt.  The ceiling is therefore what has
        // been generated, not what is cheap to solve from cold.
        out.minN = 3; out.maxN = 14; out.defN = 8;
        return true;
    }
    if (t.size() == 4 && t[0] == "mixed") {
        bool ok1, ok2, ok3;
        const int p0 = capPieceFromName(t[1], ok1);
        const int p1 = capPieceFromName(t[2], ok2);
        const int pb = capPieceFromName(t[3], ok3);
        if (!ok1 || !ok2 || !ok3) return false;
        // mixed.cpp will happily run two LIKE white men -- that is how it
        // cross-checks the reduced solver -- but the explorer cannot name the
        // survivor once one of them has been taken, and a board that says
        // "a rook" without saying which rook is worse than no board.  The
        // kings family covers like men with an index that does not care.
        if (p0 == p1) return false;
        out = Family{};
        out.id = id;
        out.label = std::string(1, capPieceLetter(p0)) + capPieceLetter(p1) + " vs " + capPieceLetter(pb);
        out.title = out.label + " under capture rules";
        out.group = "Two unlike white men"; out.rules = "capture";
        out.blurb = "Addressed by id rather than listed in the catalogue.";
        out.kind = Family::Mixed;
        out.arg[0] = p0; out.arg[1] = p1; out.arg[2] = pb;
        out.minN = 3; out.maxN = 12; out.defN = 8;
        return true;
    }
    return false;
}

// The name a configuration's own table takes in a store.  The conversions it
// pulls in have names of their own, from sharedStem; this is the top of the
// pile, and it is what the catalogue's "on disk" mark looks for.
std::string storeStem(const Family& f, int n) {
    switch (f.kind) {
        case Family::Shared:  return sharedStem((Endgame)f.arg[0], f.arg[1] != 0, n);
        case Family::Kqkr: {
            std::string s = Material::of((Endgame)f.arg[0]).name();
            for (char& c : s) c = (char)(c >= 'A' && c <= 'Z' ? c - 'A' + 'a' : c);
            return s + (f.arg[1] != 0 ? "cap" : "") + std::to_string(n);
        }
        case Family::Kqkbb:   return "kqkbb" + std::to_string(n);
        case Family::Kqkk:    return std::string("kqkk") +
                                     ((KkRules)f.arg[0] == KkRules::Loose ? "loose" : "") +
                                     std::to_string(n);
        case Family::KqkkCap: return "kqkkcap" + std::to_string(n);
        // The kings lattice keeps a file per table rather than per
        // configuration, under names kings.cpp chooses, and mixed keeps none.
        case Family::Kings:
        case Family::Mixed:   return std::string();
    }
    return std::string();
}

std::string storeExt(const Family& f) {
    switch (f.kind) {
        case Family::Shared: {
            std::string s = Material::of((Endgame)f.arg[0]).name();
            for (char& c : s) c = (char)(c >= 'A' && c <= 'Z' ? c - 'A' + 'a' : c);
            return s;
        }
        case Family::Kqkr: {
            std::string s = Material::of((Endgame)f.arg[0]).name();
            for (char& c : s) c = (char)(c >= 'A' && c <= 'Z' ? c - 'A' + 'a' : c);
            return s;
        }
        case Family::Kqkbb:   return "kqkbb";
        case Family::Kqkk:    return "kqkk";
        case Family::KqkkCap: return "kqkkcap";
        default:              return std::string();
    }
}

// The switch, wrapped by buildEngine so that the tally is read in one place.

// ---------------------------------------------------------------------------
// The general solver, as an explorer engine.  See src/general.cpp.
//
// It serves materials nothing else here can answer, and it serves the ten
// capture-rules materials that kqkr.cpp used to, because kqkr.cpp's capture
// reading is not the rule this variant actually has: both sides hold a king
// there, so either may take the other's, and a solver built on chess legality
// cannot express that.  Its ORDINARY-rules tables are exact and keep those
// families.
//
// No store.  The unreduced index makes a table eight times the size of a
// reduced one, and these solve in well under a second on the boards the
// catalogue offers them at, so a file would cost more to read than to rebuild.
class GeneralEngine : public Engine {
public:
    GeneralEngine(const GenMat& m, int n, int threads, const Store& store)
        : g_(n), mat_(m) {
        const int cap = TableGen::maxMenFor(n);
        if (m.men() > cap)
            throw std::runtime_error("this board is too large for the unreduced "
                                     "index the general solver uses");
        GenCounts c;
        t_ = genSolve(mat_, n, threads, cache_, false, store.dir, &c, store.minSeconds);
        if (!t_) throw std::runtime_error("nothing to solve for this material");
        for (int i = 0; i < c.loaded; ++i) note("loaded", mat_.name(), -1, false);
        for (int i = 0; i < c.solved; ++i) note("solved", mat_.name(), -1, false);
    }

    const Geometry& geo() const override { return g_; }
    std::string material() const override { return mat_.name(); }

    // Which table of the chain holds exactly these men.  A capture leaves this
    // material for a smaller one, and the explorer walks on into it, so a
    // placement with fewer men than the root is a position and not an error --
    // it simply lives in another table.  Everything the chain built is in the
    // cache, keyed by material, so the search is over that.
    const TableGen* tableFor(const View& v, std::vector<Man>* ordered) const {
        std::vector<char> w, b;
        for (const Man& m : v.men) (m.color == 'w' ? w : b).push_back(m.piece);
        std::sort(w.begin(), w.end());
        std::sort(b.begin(), b.end());
        for (const auto& kv : cache_) {
            const TableGen* t = kv.second.get();
            if (!t) continue;
            std::vector<char> tw, tb;
            for (U8 pc : t->mat.w) tw.push_back(capPieceLetter(pc));
            for (U8 pc : t->mat.b) tb.push_back(capPieceLetter(pc));
            std::sort(tw.begin(), tw.end());
            std::sort(tb.begin(), tb.end());
            if (tw != w || tb != b) continue;
            if (!ordered) return t;
            // Lay the men out in that material's own order.
            std::vector<Man> got = v.men, out;
            auto take = [&](char colour, int kind) {
                for (size_t i = 0; i < got.size(); ++i) {
                    if (got[i].sq < 0 || got[i].color != colour) continue;
                    if (got[i].piece != capPieceLetter(kind)) continue;
                    out.push_back(got[i]); got[i].sq = -1; return true;
                }
                return false;
            };
            bool ok = true;
            for (U8 pc : t->mat.w) if (!take('w', pc)) { ok = false; break; }
            if (ok) for (U8 pc : t->mat.b) if (!take('b', pc)) { ok = false; break; }
            if (!ok) continue;
            *ordered = out;
            return t;
        }
        return nullptr;
    }

    bool accept(View& v, std::string& err) const override {
        std::vector<Man> out;
        const TableGen* t = tableFor(v, &out);
        if (!t) { err = "no table holds this material"; return false; }
        Sq sq[8];
        for (size_t i = 0; i < out.size(); ++i) {
            sq[i] = out[i].sq;
            if (sq[i] < 0 || sq[i] >= g_.nsq) { err = "a man is off the board"; return false; }
        }
        if (!genLegal(*t, sq, v.wtm ? 0 : 1)) { err = "not a legal position"; return false; }
        v.men = out;
        return true;
    }

    Val value(const View& v) const override {
        const TableGen* t = tableFor(v, nullptr);
        if (!t) return Val{};
        Sq sq[8];
        toSquares(v, sq);
        const int stm = v.wtm ? 0 : 1;
        if (!genLegal(*t, sq, stm)) return Val{};
        // Through the table's OWN ranking, never `idx` directly: with the D4
        // reduction on, `idx` is not the ranking the values were stored under
        // and `rank` is what maps a placement to its canonical slot.
        U64 slot;
        if (!t->rank(sq, slot)) return Val{};
        return valOf(t->v[stm][(size_t)slot], v.wtm, genMoveList(*t, sq, stm).empty());
    }

    bool quiet(const View& v) const override {
        const TableGen* t = tableFor(v, nullptr);
        if (!t) return false;
        Sq sq[8];
        toSquares(v, sq);
        return genQuiet(*t, sq);
    }

    std::vector<MoveOut> moves(const View& v) const override {
        std::vector<MoveOut> out;
        const TableGen* t = tableFor(v, nullptr);
        if (!t) return out;
        Sq sq[8];
        toSquares(v, sq);
        const int stm = v.wtm ? 0 : 1;
        if (!genLegal(*t, sq, stm)) return out;
        for (const GenMove& mv : genMoveList(*t, sq, stm)) {
            MoveOut M;
            M.from    = sq[mv.mover];
            M.to      = mv.to;
            M.capture = mv.cap >= 0;
            bool ends = false;
            const int16_t u = genValueAfter(*t, sq, stm, mv, ends);
            M.playable = !ends;
            // The board after the move, with the captured man removed.
            View a;
            a.wtm = !v.wtm;
            for (int i = 0; i < t->mat.men(); ++i) {
                if (i == mv.cap) continue;
                Man man = v.men[(size_t)i];
                if (i == mv.mover) man.sq = mv.to;
                a.men.push_back(man);
            }
            M.after = a;
            // `u` is stated for whoever moves next, which is the other side.
            M.val = valOf(u, !v.wtm, false);
            if (ends) {
                M.val.terminal = v.wtm ? "white wins -- black has no king left"
                                       : "black wins -- white has no king left";
                if (!mat_.alive(capturedSideMen(mv), v.wtm ? mat_.royalB : mat_.royalW))
                    M.val.terminal = v.wtm ? "white wins -- black has nothing left"
                                           : "black wins -- white has nothing left";
                M.note = "the game ends here";
            }
            const Man& mover = v.men[(size_t)mv.mover];
            char pl = mover.piece;
            if (mover.color == 'b') pl = (char)(pl - 'A' + 'a');
            M.san = std::string(1, pl) + g_.name(M.from) + (M.capture ? "x" : "-") + g_.name(M.to);
            out.push_back(M);
        }
        return out;
    }

    View start(std::string& note) const override {
        // `slots()` and `unrank`, not `idx`: under the reduction the table has
        // an eighth as many slots as the plain product, so walking `idx.nslots`
        // ran off the end of the value array outright.
        const U64 N = t_->slots();
        Sq sq[8];
        int bq = -1, ba = -1;
        std::vector<Sq> bestQuiet, bestAny, anyLegal;
        for (U64 i = 0; i < N; ++i) {
            t_->unrank(i, sq);
            const int16_t val = t_->v[0][(size_t)i];
            if (val == VC_DEAD) continue;
            if (anyLegal.empty()) anyLegal.assign(sq, sq + mat_.men());
            if (val <= 0) continue;                    // White to move, White wins
            if (val > ba) { ba = val; bestAny.assign(sq, sq + mat_.men()); }
            if (val > bq && genQuiet(*t_, sq)) { bq = val; bestQuiet.assign(sq, sq + mat_.men()); }
        }
        if (bq >= 0) { note = "the deepest win White has from a quiet position"; return viewOf(bestQuiet); }
        if (ba >= 0) { note = "the deepest win White has (no quiet one exists on this board)"; return viewOf(bestAny); }
        note = "White has no win on this board; an arbitrary legal position";
        return viewOf(anyLegal);
    }

private:
    Geometry g_;
    GenMat   mat_;
    mutable GenCache cache_;
    const TableGen* t_ = nullptr;

    void toSquares(const View& v, Sq* sq) const {
        for (int i = 0; i < mat_.men(); ++i) sq[i] = v.men[(size_t)i].sq;
    }
    std::vector<U8> capturedSideMen(const GenMove&) const { return {}; }

    bool noMoves(const Sq* sq, int stm) const {
        return genMoveList(*t_, sq, stm).empty();
    }

    View viewOf(const std::vector<Sq>& sq) const {
        View v;
        v.wtm = true;
        size_t i = 0;
        for (U8 pc : mat_.w) { v.men.push_back(Man{ 'w', capPieceLetter(pc), sq[i] }); ++i; }
        for (U8 pc : mat_.b) { v.men.push_back(Man{ 'b', capPieceLetter(pc), sq[i] }); ++i; }
        return v;
    }

    // The table speaks in plies-plus-one relative to whoever is to move; the
    // front end wants plies relative to White.
    Val valOf(int16_t raw, bool wtm, bool stuck) const {
        Val out;
        if (raw == VC_DEAD) return out;                       // Illegal
        if (raw == 0) {
            out.kind = Val::Draw;
            out.text = "Drawn";
            if (stuck) out.terminal = "stalemate -- no legal move, which is a draw here";
            return out;
        }
        const bool moverWins = raw > 0;
        const int plies = (raw > 0 ? raw : -raw) - 1;
        const bool white = moverWins == wtm;
        out.kind  = white ? Val::WhiteWins : Val::BlackWins;
        out.plies = plies;
        char buf[128];
        std::snprintf(buf, sizeof buf, "%s wins -- mate in %d (%d plies)",
                      white ? "White" : "Black", (plies + 1) / 2, plies);
        out.text = buf;
        if (plies == 0) out.terminal = white ? "black's last king has fallen"
                                             : "white's last king has fallen";
        return out;
    }
};

static std::unique_ptr<Engine> buildEngineInner(const Family& f, int n, int threads,
                                                std::string& err, const Store& store);

std::unique_ptr<Engine> buildEngine(const Family& f, int n, int threads, std::string& err,
                                    const Store& store) {
    if (n < f.minN || n > f.maxN) {
        err = "board size out of range for this configuration";
        return nullptr;
    }
    g_tally = Tally{};
    std::unique_ptr<Engine> made = buildEngineInner(f, n, threads, err, store);
    if (made) {
        char s[96];
        if (g_tally.solved == 0 && g_tally.loaded > 0)
            std::snprintf(s, sizeof s, "loaded %d table%s from the store",
                          g_tally.loaded, g_tally.loaded == 1 ? "" : "s");
        else if (g_tally.loaded == 0)
            std::snprintf(s, sizeof s, "solved %d table%s here",
                          g_tally.solved, g_tally.solved == 1 ? "" : "s");
        else
            std::snprintf(s, sizeof s, "loaded %d table%s, solved %d here",
                          g_tally.loaded, g_tally.loaded == 1 ? "" : "s", g_tally.solved);
        made->source = s;
    }
    return made;
}

static std::unique_ptr<Engine> buildEngineInner(const Family& f, int n, int threads,
                                                std::string& err, const Store& store) {
    try {
        switch (f.kind) {
            case Family::Shared:
                return std::make_unique<SharedEngine>(n, (Endgame)f.arg[0], f.arg[1] != 0,
                                                      threads, store);
            case Family::Kqkr:
                return std::make_unique<KqkrEngine>(n, (Endgame)f.arg[0], f.arg[1] != 0,
                                                    threads, store);
            case Family::Kqkbb:
                return std::make_unique<KqkbbEngine>(n, threads, store);
            case Family::Kqkk:
                return std::make_unique<KqkkEngine>(n, (KkRules)f.arg[0], threads, store);
            case Family::KqkkCap:
                return std::make_unique<KqkkCapEngine>(n, threads, store);
            case Family::Kings:
                return std::make_unique<KingsEngine>(n, f.arg[0], f.arg[1], f.arg[2], f.arg[3],
                                                     threads, store);
            case Family::Mixed:
                return std::make_unique<MixedEngine>(n, f.arg[0], f.arg[1], f.arg[2],
                                                     threads, store);
            case Family::General: {
                // arg[0]/arg[1] are Piece codes for White's and Black's man,
                // each standing beside a king.
                auto toCap = [](int p) {
                    return p == (int)Piece::Queen  ? CP_QUEEN : p == (int)Piece::Rook   ? CP_ROOK
                         : p == (int)Piece::Bishop ? CP_BISHOP : CP_KNIGHT;
                };
                GenMat m;
                m.w.push_back(CP_KING); m.w.push_back((U8)toCap(f.arg[0]));
                m.b.push_back(CP_KING); m.b.push_back((U8)toCap(f.arg[1]));
                m.capture = (f.rules == "capture");
                m.royalW = m.royalB = true;
                m.sort();
                return std::make_unique<GeneralEngine>(m, n, threads, store);
            }
        }
    } catch (const std::exception& e) {
        err = e.what();
        return nullptr;
    }
    err = "unknown configuration";
    return nullptr;
}


// ---------------------------------------------------------------------------
// What a store holds.
// ---------------------------------------------------------------------------
//
// Three naming schemes meet in one directory, because three solvers write into
// it and each names a file after what it computed rather than after some
// scheme imposed from above:
//
//   KKKvNN-n9.tb   the kings lattice: the material spelled out in piece
//                  letters, White's then Black's, and the board.  One file per
//                  TABLE, so a configuration is present only when every table
//                  its captures convert into is present too.
//   KQvN-n8.mx     mixed: two unlike white men against one black one.  One
//                  file per configuration -- it holds the two one-man tables
//                  as well, so it stands alone.
//   kbnkcap12.kbnk the shared solver and the armed ones, named by
//                  storeStem/storeExt above, which is where the loader looks.
//
// Reading the directory rather than the catalogue is what makes the page
// honest.  The catalogue lists 28 configurations somebody wrote a sentence
// about; a store filled by a sweep holds hundreds, and every one of them opens
// instantly if the page will only admit that it is there.
namespace {

int capPieceFromLetter(char c, bool& ok) {
    ok = true;
    switch (c) {
        case 'K': return CP_KING;
        case 'R': return CP_ROOK;
        case 'N': return CP_KNIGHT;
        case 'B': return CP_BISHOP;
        case 'Q': return CP_QUEEN;
    }
    ok = false;
    return CP_KING;
}

// A run of one repeated piece letter: "KKK" -> 3 kings.  The lattice's names
// are two such runs either side of a 'v', and 'v' is lower case precisely so
// that it can never be mistaken for one of the five upper-case letters.
bool pieceRun(const std::string& s, size_t a, size_t b, int& count, int& piece) {
    if (b <= a || b - a > 4) return false;
    bool ok;
    piece = capPieceFromLetter(s[a], ok);
    if (!ok) return false;
    for (size_t i = a + 1; i < b; ++i)
        if (s[i] != s[a]) return false;
    count = (int)(b - a);
    return true;
}

// "KKKvNN-n9.tb" with ext ".tb".  False for every name that is not this shape,
// including the other two schemes' names and anything a user dropped in.
bool parseShapeName(const std::string& name, const char* ext,
                    int& W, int& B, int& pw, int& pb, int& n) {
    const size_t elen = std::strlen(ext);
    if (name.size() < elen || name.compare(name.size() - elen, elen, ext) != 0) return false;
    const std::string stem = name.substr(0, name.size() - elen);
    const size_t v = stem.find('v');
    const size_t d = stem.rfind("-n");
    if (v == std::string::npos || d == std::string::npos || d < v) return false;
    if (!pieceRun(stem, 0, v, W, pw)) return false;
    if (!pieceRun(stem, v + 1, d, B, pb)) return false;
    if (d + 2 >= stem.size()) return false;
    for (size_t i = d + 2; i < stem.size(); ++i)
        if (stem[i] < '0' || stem[i] > '9') return false;
    n = std::atoi(stem.c_str() + d + 2);
    return n >= 2 && n <= 64;
}

struct ShapeKey {
    int W, B, pw, pb;
    bool operator<(const ShapeKey& o) const {
        if (pw != o.pw) return pw < o.pw;
        if (pb != o.pb) return pb < o.pb;
        if (W != o.W) return W < o.W;
        return B < o.B;
    }
};
struct MixKey {
    int p0, p1, pb;
    bool operator<(const MixKey& o) const {
        if (p0 != o.p0) return p0 < o.p0;
        if (p1 != o.p1) return p1 < o.p1;
        return pb < o.pb;
    }
};

// One board of one lattice configuration, with the size of the file.
using Boards = std::map<int, unsigned long long>;

struct Inventory {
    std::map<ShapeKey, Boards> tb;
    std::map<MixKey, Boards>   mx;
    std::map<std::string, unsigned long long> byName;   // everything else
    int files = 0;
    unsigned long long bytes = 0;
};

Inventory readDir(const std::string& dir) {
    Inventory inv;
    DIR* d = opendir(dir.c_str());
    if (!d) return inv;
    while (const dirent* e = readdir(d)) {
        const std::string name = e->d_name;
        if (name.empty() || name[0] == '.') continue;
        // A .part is a write in progress: the loader will never open one and
        // neither does this.
        if (name.size() > 5 && name.compare(name.size() - 5, 5, ".part") == 0) continue;
        struct stat st;
        if (stat((dir + "/" + name).c_str(), &st) != 0 || !S_ISREG(st.st_mode)) continue;
        const unsigned long long sz = (unsigned long long)st.st_size;
        ++inv.files;
        inv.bytes += sz;
        int W, B, pw, pb, n;
        if (parseShapeName(name, ".tb", W, B, pw, pb, n)) {
            inv.tb[ShapeKey{ W, B, pw, pb }][n] = sz;
        } else if (parseShapeName(name, ".mx", W, B, pw, pb, n)) {
            // Mixed spells its two white men out as they are, so the "run"
            // reading only holds when they are alike; the general case is two
            // letters that differ.  Re-read the stem for that.
            const std::string stem = name.substr(0, name.size() - 3);
            const size_t v = stem.find('v');
            bool ok0, ok1;
            if (v == 2) {
                const int p0 = capPieceFromLetter(stem[0], ok0);
                const int p1 = capPieceFromLetter(stem[1], ok1);
                if (ok0 && ok1) inv.mx[MixKey{ p0, p1, pb }][n] = sz;
            }
        } else {
            // Not a shape name, but possibly two unlike men: "KQvN-n8.mx".
            const size_t e2 = name.rfind(".mx");
            if (e2 != std::string::npos && e2 + 3 == name.size()) {
                const std::string stem = name.substr(0, e2);
                const size_t v = stem.find('v');
                const size_t dd = stem.rfind("-n");
                bool ok0, ok1, ok2;
                if (v == 2 && dd != std::string::npos && dd == v + 2) {
                    const int p0 = capPieceFromLetter(stem[0], ok0);
                    const int p1 = capPieceFromLetter(stem[1], ok1);
                    const int pbb = capPieceFromLetter(stem[3], ok2);
                    const int nn = std::atoi(stem.c_str() + dd + 2);
                    if (ok0 && ok1 && ok2 && nn >= 2 && nn <= 64)
                        inv.mx[MixKey{ p0, p1, pbb }][nn] = sz;
                }
            }
            inv.byName[name] = sz;
        }
    }
    closedir(d);
    return inv;
}

// A lattice configuration is on a board when EVERY table it can convert into
// is on that board too: White taking one of Black's men leaves (W, B-1), Black
// taking one of White's leaves (W-1, B), and the explorer maps all of them at
// once.  Reporting the top table alone would promise a board that then stalls
// rebuilding the ones under it, which is exactly the lie this scan exists to
// stop telling.
std::vector<int> latticeBoards(const Inventory& inv, int W, int B, int pw, int pb) {
    std::vector<int> out;
    const auto top = inv.tb.find(ShapeKey{ W, B, pw, pb });
    if (top == inv.tb.end()) return out;
    for (const auto& kv : top->second) {
        const int n = kv.first;
        bool whole = true;
        for (int w = 1; w <= W && whole; ++w)
            for (int b = 1; b <= B && whole; ++b) {
                const auto it = inv.tb.find(ShapeKey{ w, b, pw, pb });
                if (it == inv.tb.end() || !it->second.count(n)) whole = false;
            }
        if (whole) out.push_back(n);
    }
    return out;
}

// The boards a catalogue family has files for, by the name its own loader
// would open.  The range is deliberately wider than the family's stated
// maximum: a table generated before a ceiling was lowered is still a table.
void namedBoards(const Family& f, const Inventory& inv, StoreEntry& e) {
    const std::string ext = storeExt(f);
    if (ext.empty()) return;
    for (int n = 2; n <= 40; ++n) {
        const std::string stem = storeStem(f, n);
        if (stem.empty()) continue;
        const auto it = inv.byName.find(stem + "." + ext);
        if (it == inv.byName.end()) continue;
        e.boards.push_back(n);
        e.bytes += it->second;
        ++e.files;
    }
}

void fillLattice(const Inventory& inv, const Family& f, StoreEntry& e) {
    e.boards = latticeBoards(inv, f.arg[0], f.arg[1], f.arg[2], f.arg[3]);
    const auto it = inv.tb.find(ShapeKey{ f.arg[0], f.arg[1], f.arg[2], f.arg[3] });
    if (it == inv.tb.end()) return;
    for (int n : e.boards) {
        const auto b = it->second.find(n);
        if (b != it->second.end()) { e.bytes += b->second; ++e.files; }
    }
}

void fillMixed(const Inventory& inv, const Family& f, StoreEntry& e) {
    const auto it = inv.mx.find(MixKey{ f.arg[0], f.arg[1], f.arg[2] });
    if (it == inv.mx.end()) return;
    for (const auto& kv : it->second) {
        e.boards.push_back(kv.first);
        e.bytes += kv.second;
        ++e.files;
    }
}

} // namespace

// ---------------------------------------------------------------------------
// The whole space of materials, solved or not.
// ---------------------------------------------------------------------------
namespace {

// Multisets of `k` men drawn from `alphabet`, in the alphabet's order, so that
// "KRR" comes out once and "KRR" reordered never does.  Material is a bag of
// men; two rooks are two rooks whichever you name first.
void multisets(const std::string& alphabet, int k, std::vector<std::string>& out,
               std::string cur = "", size_t start = 0) {
    if ((int)cur.size() == k) { out.push_back(cur); return; }
    for (size_t i = start; i < alphabet.size(); ++i)
        multisets(alphabet, k, out, cur + alphabet[i], i);
}

// The shared solver's eight endgames, keyed by White's men with the king
// dropped: "Q" is KQK, "BN" is KBNK.  Anything not here has no solver, which
// is most of the space -- KRR vs K and KRKBB are perfectly ordinary chess
// endgames that nothing in this repository can compute.
bool sharedEndgameFor(const std::string& whiteMen, Endgame& eg) {
    static const struct { const char* men; Endgame eg; } t[] = {
        { "Q", Endgame::KQK }, { "R", Endgame::KRK }, { "B", Endgame::KBK },
        { "N", Endgame::KNK }, { "BB", Endgame::KBBK }, { "BN", Endgame::KBNK },
        { "NN", Endgame::KNNK }, { "NNN", Endgame::KNNNK },
        { "QQ", Endgame::KQQK }, { "QR", Endgame::KQRK }, { "QB", Endgame::KQBK },
        { "QN", Endgame::KQNK }, { "RR", Endgame::KRRK }, { "RB", Endgame::KRBK },
        { "RN", Endgame::KRNK },
        { "QQQ", Endgame::KQQQK },
        { "QQR", Endgame::KQQRK },
        { "QQB", Endgame::KQQBK },
        { "QQN", Endgame::KQQNK },
        { "QRR", Endgame::KQRRK },
        { "QRB", Endgame::KQRBK },
        { "QRN", Endgame::KQRNK },
        { "QBB", Endgame::KQBBK },
        { "QBN", Endgame::KQBNK },
        { "QNN", Endgame::KQNNK },
        { "RRR", Endgame::KRRRK },
        { "RRB", Endgame::KRRBK },
        { "RRN", Endgame::KRRNK },
        { "RBB", Endgame::KRBBK },
        { "RBN", Endgame::KRBNK },
        { "RNN", Endgame::KRNNK },
        { "BBB", Endgame::KBBBK },
        { "BBN", Endgame::KBBNK },
        { "BNN", Endgame::KBNNK },
    };
    for (const auto& e : t)
        if (whiteMen == e.men) { eg = e.eg; return true; }
    return false;
}

// Which of the three families a capture-rules material belongs to, in the
// terms the game is actually played in: whether each side has a king to lose.
const char* captureGroup(const std::string& w, const std::string& b) {
    const size_t wk = (size_t)std::count(w.begin(), w.end(), 'K');
    const size_t bk = (size_t)std::count(b.begin(), b.end(), 'K');
    if (wk == 0 || bk == 0)
        return "No king: one side has none, and loses when its last man goes";
    if (wk > 1 || bk > 1)
        return "Several kings: a side is beaten only when every one of them has fallen";
    return "One king each: the same shape as chess, won by taking the king";
}

const std::vector<int>* boardsOf(const StoreScan& scan, const std::string& id) {
    if (id.empty()) return nullptr;
    for (const StoreEntry& e : scan.entries)
        if (e.id == id) return &e.boards;
    return nullptr;
}

} // namespace

std::vector<MaterialRow> coverage(bool capture, int maxMen, const StoreScan& scan) {
    std::vector<MaterialRow> out;
    const std::string PIECES = "QRBN";        // the men besides a king
    const std::string ALL    = "KQRBN";

    if (!capture) {
        // Normal chess: one king a side, always, and between 0 and 3 other men
        // for White, 0 and 2 for Black.
        for (int wp = 0; wp <= 3; ++wp)
            for (int bp = 0; bp <= 2; ++bp) {
                if (2 + wp + bp > maxMen) continue;
                std::vector<std::string> ws, bs;
                multisets(PIECES, wp, ws);
                multisets(PIECES, bp, bs);
                for (const std::string& w : ws)
                    for (const std::string& b : bs) {
                        MaterialRow r;
                        r.white = "K" + w; r.black = "K" + b;
                        r.label = r.white + r.black;
                        r.men = 2 + wp + bp;
                        Endgame eg;
                        if (b.empty() && sharedEndgameFor(w, eg)) {
                            r.supported = true;
                            r.id = Material::of(eg).name();
                            for (char& c : r.id)
                                c = (char)(c >= 'A' && c <= 'Z' ? c - 'A' + 'a' : c);
                            r.group = "A bare black king";
                        } else if (w.size() == 1 && b.size() == 1) {
                            // One man a side: the armed solver, if the pair is
                            // one of the ten it holds.  The other six are the
                            // colour mirror of one of those and are marked as
                            // such further down.
                            for (int k = 0; k < NUM_ENDGAMES; ++k) {
                                const Endgame e = (Endgame)k;
                                if (!blackArmed(e)) continue;
                                if (pieceLetter(whitePieceOf(e)) != w[0] ||
                                    pieceLetter(blackPieceOf(e)) != b[0]) continue;
                                r.supported = true;
                                r.id = Material::of(e).name();
                                for (char& ch : r.id)
                                    ch = (char)(ch >= 'A' && ch <= 'Z' ? ch - 'A' + 'a' : ch);
                                break;
                            }
                            r.group = "Black is armed";
                        } else if (w == "Q" && b == "BB") {
                            r.supported = true; r.id = "kqkbb"; r.group = "Black is armed";
                        } else {
                            r.group = b.empty() ? "A bare black king" : "Black is armed";
                        }
                        if (const std::vector<int>* bd = boardsOf(scan, r.id)) r.boards = *bd;
                        out.push_back(std::move(r));
                    }
            }
    } else {
        // Capture rules: no king is required and none is privileged, so the
        // space is every bag of men on each side.
        for (int wn = 1; wn <= 4; ++wn)
            for (int bn = 1; bn <= 2; ++bn) {
                if (wn + bn > maxMen) continue;
                std::vector<std::string> ws, bs;
                multisets(ALL, wn, ws);
                multisets(ALL, bn, bs);
                for (const std::string& w : ws)
                    for (const std::string& b : bs) {
                        MaterialRow r;
                        r.white = w; r.black = b;
                        r.label = w + " vs " + b;
                        r.men = wn + bn;
                        r.group = captureGroup(w, b);
                        const bool likeW = w.find_first_not_of(w[0]) == std::string::npos;
                        const bool likeB = b.find_first_not_of(b[0]) == std::string::npos;
                        char id[96];
                        if (likeW && likeB) {
                            bool o1, o2;
                            const int pw = capPieceFromLetter(w[0], o1);
                            const int pb = capPieceFromLetter(b[0], o2);
                            if (o1 && o2) {
                                std::snprintf(id, sizeof id, "kings-%d-%d-%s-%s",
                                              wn, bn, capPieceName(pw), capPieceName(pb));
                                r.supported = true; r.id = id;
                            }
                        } else if (wn == 2 && bn == 1) {
                            // Two unlike white men against one: the mixed solver.
                            bool o0, o1, o2;
                            const int p0 = capPieceFromLetter(w[0], o0);
                            const int p1 = capPieceFromLetter(w[1], o1);
                            const int pb = capPieceFromLetter(b[0], o2);
                            if (o0 && o1 && o2) {
                                std::snprintf(id, sizeof id, "mixed-%s-%s-%s",
                                              capPieceName(p0), capPieceName(p1),
                                              capPieceName(pb));
                                r.supported = true; r.id = id;
                            }
                        }
                        // The mating solvers read under the capture rules reach
                        // shapes neither lattice does: three and four unlike
                        // white men against a bare king, and a king and queen
                        // against an ARMED king.  With one king a side those
                        // rules come to "stalemate loses", which is a flag on
                        // the same solver rather than a solver of its own.
                        if (!r.supported) {
                            Endgame eg;
                            if (b == "K" && w.size() >= 2 && w[0] == 'K' &&
                                sharedEndgameFor(w.substr(1), eg)) {
                                r.id = Material::of(eg).name();
                                for (char& c : r.id)
                                    c = (char)(c >= 'A' && c <= 'Z' ? c - 'A' + 'a' : c);
                                r.id += "-capture";
                                r.supported = true;
                            } else if (w.size() == 2 && b.size() == 2 &&
                                       w[0] == 'K' && b[0] == 'K') {
                                // One king and one man a side: the armed
                                // solver again, read with stalemate a loss.
                                for (int k = 0; k < NUM_ENDGAMES; ++k) {
                                    const Endgame e = (Endgame)k;
                                    if (!blackArmed(e)) continue;
                                    if (pieceLetter(whitePieceOf(e)) != w[1] ||
                                        pieceLetter(blackPieceOf(e)) != b[1]) continue;
                                    std::string nm = Material::of(e).name();
                                    for (char& ch : nm)
                                        ch = (char)(ch >= 'A' && ch <= 'Z' ? ch - 'A' + 'a' : ch);
                                    r.id = nm + "-capture";
                                    r.supported = true;
                                    break;
                                }
                            } else if (w == "KQ" && b == "KK") {
                                r.id = "kqkk-capture"; r.supported = true;
                            }
                        }
                        if (const std::vector<int>* bd = boardsOf(scan, r.id)) r.boards = *bd;
                        out.push_back(std::move(r));
                    }
            }
    }
    // ONE ROW PER MATERIAL, not two.
    //
    // A material and its colour reflection are the same endgame: with no pawns
    // the rules are symmetric, so K+B vs K and K vs K+B are one table read two
    // ways, and listing both says the collection is twice the size it is.  The
    // side with more men is written as White, and between equal counts the
    // stronger men are; that is also the orientation the tables were built in,
    // so the canonical row is nearly always the one that is solved.
    {
        auto strength = [](char c) {
            return c == 'Q' ? 5 : c == 'R' ? 4 : c == 'B' ? 3 : c == 'N' ? 2 : 1;
        };
        auto rank = [&](const std::string& men) {
            std::vector<int> v;
            for (char c : men) v.push_back(strength(c));
            std::sort(v.begin(), v.end(), std::greater<int>());
            return v;
        };
        std::vector<MaterialRow> keep;
        keep.reserve(out.size());
        for (MaterialRow& r : out) {
            if (r.white.size() != r.black.size()) {
                if (r.white.size() < r.black.size()) continue;   // its mirror is kept
            } else {
                const std::vector<int> a = rank(r.white), b = rank(r.black);
                if (a < b) continue;                             // ditto
            }
            keep.push_back(std::move(r));
        }
        out = std::move(keep);
    }

    // A material nothing here solves may still be one of these tables seen
    // from the other side.  With no pawns the rules are colour-symmetric, so
    // K vs KB is K+B vs K reflected, and the answer is already on the drive:
    // it is the same table, read with the sides exchanged.  Listing those as
    // "no solver" was wrong -- it says a question cannot be answered when the
    // answer is sitting in a file.
    {
        std::map<std::pair<std::string, std::string>, const MaterialRow*> have;
        for (const MaterialRow& r : out)
            if (r.supported) have[{ r.white, r.black }] = &r;
        for (MaterialRow& r : out) {
            if (r.supported) continue;
            auto it = have.find({ r.black, r.white });
            if (it == have.end()) continue;
            r.mirror = true;
            r.mirrorOf = it->second->label;
            r.id = it->second->id;
            r.boards = it->second->boards;
        }
    }

    std::sort(out.begin(), out.end(), [](const MaterialRow& a, const MaterialRow& b) {
        if (a.group != b.group) return a.group < b.group;
        if (a.men != b.men) return a.men < b.men;
        const bool ka = a.supported || a.mirror, kb = b.supported || b.mirror;
        if (ka != kb) return ka > kb;
        if (a.supported != b.supported) return a.supported > b.supported;
        return a.label < b.label;
    });
    return out;
}

std::vector<int> storeBoards(const Family& f, const std::string& dir) {
    if (dir.empty()) return {};
    const Inventory inv = readDir(dir);
    StoreEntry e;
    switch (f.kind) {
        case Family::Kings: fillLattice(inv, f, e); break;
        case Family::Mixed: fillMixed(inv, f, e); break;
        default:            namedBoards(f, inv, e); break;
    }
    return e.boards;
}

StoreScan scanStore(const std::string& dir) {
    StoreScan out;
    out.dir = dir;
    if (dir.empty()) return out;
    const Inventory inv = readDir(dir);
    out.filesTotal = inv.files;
    out.bytesTotal = inv.bytes;

    // The catalogue first, in its own order, so that the configurations
    // somebody wrote a sentence about stay at the top of the page.
    std::set<ShapeKey> seenShape;
    std::set<MixKey>   seenMix;
    for (const Family& f : familyCatalogue()) {
        StoreEntry e;
        e.id = f.id; e.label = f.label; e.title = f.title;
        e.group = f.group; e.rules = f.rules; e.listed = true;
        switch (f.kind) {
            case Family::Kings:
                fillLattice(inv, f, e);
                seenShape.insert(ShapeKey{ f.arg[0], f.arg[1], f.arg[2], f.arg[3] });
                break;
            case Family::Mixed:
                fillMixed(inv, f, e);
                seenMix.insert(MixKey{ f.arg[0], f.arg[1], f.arg[2] });
                break;
            default:
                namedBoards(f, inv, e);
                break;
        }
        if (!e.boards.empty()) out.entries.push_back(std::move(e));
    }

    // Then everything the sweep wrote that nobody listed, addressed by the
    // structured ids familyById already understands.
    for (const auto& kv : inv.tb) {
        const ShapeKey& k = kv.first;
        if (seenShape.count(k)) continue;
        if (k.W < 1 || k.W > 4 || k.B < 1 || k.B > 2) continue;
        char id[80];
        std::snprintf(id, sizeof id, "kings-%d-%d-%s-%s", k.W, k.B,
                      capPieceName(k.pw), capPieceName(k.pb));
        StoreEntry e;
        e.id = id;
        e.label = std::string(k.W, capPieceLetter(k.pw)) + " vs " +
                  std::string(k.B, capPieceLetter(k.pb));
        e.title = e.label + " under capture rules";
        e.group = "Like pieces, the conversion lattice"; e.rules = "capture";
        Family f{};
        f.kind = Family::Kings;
        f.arg[0] = k.W; f.arg[1] = k.B; f.arg[2] = k.pw; f.arg[3] = k.pb;
        fillLattice(inv, f, e);
        if (!e.boards.empty()) out.entries.push_back(std::move(e));
    }
    for (const auto& kv : inv.mx) {
        const MixKey& k = kv.first;
        if (seenMix.count(k)) continue;
        // Two LIKE white men is a configuration the lattice already holds and
        // the explorer cannot name: once one of them is taken there is no way
        // to say which survived.  mixed.cpp solves them anyway, as its
        // cross-check against the reduced solver, and those files are counted
        // in the totals but are not a configuration to click on.
        if (k.p0 == k.p1) continue;
        char id[80];
        std::snprintf(id, sizeof id, "mixed-%s-%s-%s",
                      capPieceName(k.p0), capPieceName(k.p1), capPieceName(k.pb));
        StoreEntry e;
        e.id = id;
        e.label = std::string(1, capPieceLetter(k.p0)) + capPieceLetter(k.p1) +
                  " vs " + capPieceLetter(k.pb);
        e.title = e.label + " under capture rules";
        e.group = "Two unlike white men"; e.rules = "capture";
        Family f{};
        f.kind = Family::Mixed;
        f.arg[0] = k.p0; f.arg[1] = k.p1; f.arg[2] = k.pb;
        fillMixed(inv, f, e);
        if (!e.boards.empty()) out.entries.push_back(std::move(e));
    }
    return out;
}

} // namespace kqk
