// serve.cpp -- `egtb serve`: a local web server for looking at the tables.
//
// The tables are the interesting thing here and a terminal is a poor way to
// look at one.  This serves a board in a browser instead: pick a
// configuration, slide the board size, and see every legal move with its
// depth to mate beside it, the way an online tablebase does.
//
// It is deliberately the smallest server that can do that.  No framework, no
// dependency, no threads beyond the ones the solvers already use: one socket,
// one request at a time, and a handful of routes.  Everything it knows about
// chess it asks explore.cpp for, and everything explore.cpp knows it asks the
// tables for, so the whole thing is a projection of the solvers rather than a
// second implementation of them.
//
// Three routes:
//
//   GET /api/families                     the catalogue, generated from
//                                         explore.cpp -- add a configuration
//                                         there and it appears here
//   GET /api/coverage?rules=&men=         every material there is under one
//                                         rule set, marked solved, solvable or
//                                         out of reach of every solver here
//   GET /api/store                        everything the --tables store holds,
//                                         read from the directory: the
//                                         hundreds of configurations a sweep
//                                         wrote that nobody listed
//   GET /api/position?family=&n=&pos=&stm=  a position, its value, and every
//                                         legal move with the value it leads to
//   GET /<anything else>                  a file under the web root
//
// Requests are ANSWERED one at a time on purpose.  Building a table takes
// between no time at all and half a minute depending on the configuration and
// the board, and a request that is building is a request that is working; the
// browser shows that it is waiting.  Serialising also means the engine cache
// below needs no locking of its own.
//
// Connections are ACCEPTED concurrently, which is a different thing and not
// optional.  Browsers open speculative connections and then send nothing down
// them -- Chrome pre-connects on hover, Safari on typing -- and an accept loop
// that read the request before accepting the next connection would sit in
// read() on one of those until it timed out, with the real requests queued
// behind it.  So each connection gets a detached thread, reads its request
// there, and only then takes the lock that serialises the answering.
//
// SECURITY: the listening socket is bound to 127.0.0.1 and nothing else, the
// static root is resolved once and every path is checked against it, and there
// is no route that writes anything.  It is a viewer for a local process, not a
// service.
#include "explore.hpp"

#include <arpa/inet.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <unistd.h>

#include <algorithm>
#include <cctype>
#include <cerrno>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <memory>
#include <set>
#include <atomic>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

#include "table.hpp"

namespace kqk {
namespace {

// ---------------------------------------------------------------------------
// JSON, written out rather than built up.
// ---------------------------------------------------------------------------
class Jw {
public:
    void beginObj() { sep(); s_ += '{'; need_ = false; }
    void endObj()   { s_ += '}'; need_ = true; }
    void beginArr() { sep(); s_ += '['; need_ = false; }
    void endArr()   { s_ += ']'; need_ = true; }
    void key(const char* k) { sep(); quote(k); s_ += ':'; need_ = false; }
    void str(const std::string& v) { sep(); quote(v); need_ = true; }
    void num(long long v) { sep(); s_ += std::to_string(v); need_ = true; }
    void boolean(bool v)  { sep(); s_ += v ? "true" : "false"; need_ = true; }

    void kv(const char* k, const std::string& v) { key(k); str(v); }
    void kv(const char* k, const char* v)        { key(k); str(v); }
    void kv(const char* k, long long v)          { key(k); num(v); }
    void kv(const char* k, int v)                { key(k); num(v); }
    void kv(const char* k, bool v)               { key(k); boolean(v); }

    const std::string& out() const { return s_; }

private:
    void sep() { if (need_) s_ += ','; }
    void quote(const std::string& v) {
        s_ += '"';
        for (unsigned char c : v) {
            switch (c) {
                case '"':  s_ += "\\\""; break;
                case '\\': s_ += "\\\\"; break;
                case '\n': s_ += "\\n";  break;
                case '\r': s_ += "\\r";  break;
                case '\t': s_ += "\\t";  break;
                default:
                    if (c < 0x20) { char b[8]; std::snprintf(b, sizeof b, "\\u%04x", c); s_ += b; }
                    else s_ += (char)c;
            }
        }
        s_ += '"';
        need_ = true;
    }
    std::string s_;
    bool need_ = false;
};

// ---------------------------------------------------------------------------
// Positions on the wire.
// ---------------------------------------------------------------------------
// "wKa1,wQb2,bKf5": colour, piece letter, square, in the family's own order.
// Readable on purpose -- it is what appears in the browser's address bar, and
// it is what a bug report can be pasted from.  Squares are algebraic while
// n <= 26, which is why the explorer stops there; past it a square is written
// "file,rank" and the comma would need escaping for no gain, a 27-square board
// being past what anyone wants to look at.
std::string posString(const Geometry& g, const View& v) {
    std::string s;
    for (const Man& m : v.men) {
        if (!s.empty()) s += ',';
        s += m.color;
        s += m.piece;
        s += g.name(m.sq);
    }
    return s;
}

bool parsePos(const Geometry& g, const std::string& spec, bool wtm, View& out, std::string& err) {
    out = View{};
    out.wtm = wtm;
    std::string tok;
    std::vector<std::string> toks;
    for (char c : spec + ",") {
        if (c == ',') { if (!tok.empty()) toks.push_back(tok); tok.clear(); }
        else tok += c;
    }
    for (const std::string& t : toks) {
        if (t.size() < 3) { err = "cannot read '" + t + "' as a man"; return false; }
        Man m;
        m.color = (char)(t[0] | 32);
        m.piece = (char)(t[1] & ~32);
        if (m.color != 'w' && m.color != 'b') { err = "a man is 'w' or 'b'"; return false; }
        if (!std::strchr("KQRBN", m.piece)) { err = "unknown piece letter"; return false; }
        m.sq = g.parse(t.substr(2));
        if (m.sq < 0) { err = "square '" + t.substr(2) + "' is not on the board"; return false; }
        out.men.push_back(m);
    }
    if (out.men.empty()) { err = "no men given"; return false; }
    return true;
}

const char* valKind(Val::Kind k) {
    switch (k) {
        case Val::WhiteWins: return "white";
        case Val::BlackWins: return "black";
        case Val::Draw:      return "draw";
        default:             return "illegal";
    }
}

// The same value from the mover's point of view, which is what a move list is
// sorted and coloured by.
const char* forMover(const Val& v, bool wtm) {
    if (v.kind == Val::Draw) return "draw";
    if (v.kind == Val::Illegal) return "illegal";
    const bool white = (v.kind == Val::WhiteWins);
    return white == wtm ? "win" : "loss";
}

void writeVal(Jw& j, const Val& v, bool moverIsWhite) {
    j.beginObj();
    j.kv("kind", valKind(v.kind));
    j.kv("mover", forMover(v, moverIsWhite));
    j.kv("plies", v.plies);
    j.kv("moves", (v.plies + 1) / 2);
    j.kv("text", v.text);
    j.kv("terminal", v.terminal);
    j.endObj();
}

void writeMen(Jw& j, const Geometry& g, const View& v) {
    j.key("men");
    j.beginArr();
    for (const Man& m : v.men) {
        j.beginObj();
        j.kv("c", std::string(1, m.color));
        j.kv("p", std::string(1, m.piece));
        j.kv("sq", g.name(m.sq));
        j.kv("f", g.file(m.sq));
        j.kv("r", g.rank(m.sq));
        j.endObj();
    }
    j.endArr();
}

// ---------------------------------------------------------------------------
// Ordering a move list the way a tablebase front end does: the moves that win
// fastest first, then the draws, then the losses that last longest.
// ---------------------------------------------------------------------------
int moveRank(const MoveOut& m, bool moverIsWhite) {
    const char* o = forMover(m.val, moverIsWhite);
    if (!std::strcmp(o, "win"))  return 0;
    if (!std::strcmp(o, "draw")) return 1;
    if (!std::strcmp(o, "loss")) return 2;
    return 3;
}

void sortMoves(std::vector<MoveOut>& mv, bool moverIsWhite) {
    std::stable_sort(mv.begin(), mv.end(), [&](const MoveOut& a, const MoveOut& b) {
        const int ra = moveRank(a, moverIsWhite), rb = moveRank(b, moverIsWhite);
        if (ra != rb) return ra < rb;
        if (ra == 0) return a.val.plies < b.val.plies;      // win sooner
        if (ra == 2) return a.val.plies > b.val.plies;      // lose later
        return a.san < b.san;
    });
}

// ---------------------------------------------------------------------------
// The engine cache.  A build costs seconds, and moving the board-size slider
// asks for a different one each time, so the last few are kept.
// ---------------------------------------------------------------------------
class Cache {
public:
    explicit Cache(size_t cap) : cap_(cap) {}

    Engine* get(const Family& f, int n, int threads, const Store& store, std::string& err) {
        const std::string key = f.id + "/" + std::to_string(n);
        for (size_t i = 0; i < e_.size(); ++i)
            if (e_[i].key == key) {
                Entry hit = std::move(e_[i]);
                e_.erase(e_.begin() + (long)i);
                e_.push_back(std::move(hit));
                return e_.back().eng.get();
            }
        std::fprintf(stderr, "  %s on %d x %d:\n", f.id.c_str(), n, n);
        std::fflush(stderr);
        auto eng = buildEngine(f, n, threads, err, store);
        if (!eng) { std::fprintf(stderr, "    %s\n", err.c_str()); return nullptr; }
        if (e_.size() >= cap_) e_.erase(e_.begin());
        e_.push_back(Entry{ key, std::move(eng) });
        return e_.back().eng.get();
    }

private:
    struct Entry { std::string key; std::unique_ptr<Engine> eng; };
    std::vector<Entry> e_;
    size_t cap_;
};

// ---------------------------------------------------------------------------
// HTTP.
// ---------------------------------------------------------------------------
struct Req {
    std::string path;
    std::map<std::string, std::string> q;
};

std::string urlDecode(const std::string& s) {
    std::string out;
    for (size_t i = 0; i < s.size(); ++i) {
        if (s[i] == '+') out += ' ';
        else if (s[i] == '%' && i + 2 < s.size()) {
            auto hex = [](char c) -> int {
                if (c >= '0' && c <= '9') return c - '0';
                if (c >= 'a' && c <= 'f') return c - 'a' + 10;
                if (c >= 'A' && c <= 'F') return c - 'A' + 10;
                return -1;
            };
            const int a = hex(s[i + 1]), b = hex(s[i + 2]);
            if (a >= 0 && b >= 0) { out += (char)(a * 16 + b); i += 2; }
            else out += s[i];
        } else out += s[i];
    }
    return out;
}

bool parseRequest(const std::string& head, Req& r) {
    const size_t sp1 = head.find(' ');
    if (sp1 == std::string::npos) return false;
    if (head.compare(0, sp1, "GET") != 0) return false;
    const size_t sp2 = head.find(' ', sp1 + 1);
    if (sp2 == std::string::npos) return false;
    std::string target = head.substr(sp1 + 1, sp2 - sp1 - 1);
    const size_t qm = target.find('?');
    if (qm == std::string::npos) { r.path = urlDecode(target); return true; }
    r.path = urlDecode(target.substr(0, qm));
    std::string qs = target.substr(qm + 1);
    size_t i = 0;
    while (i < qs.size()) {
        size_t amp = qs.find('&', i);
        if (amp == std::string::npos) amp = qs.size();
        std::string kvp = qs.substr(i, amp - i);
        const size_t eq = kvp.find('=');
        if (eq != std::string::npos)
            r.q[urlDecode(kvp.substr(0, eq))] = urlDecode(kvp.substr(eq + 1));
        i = amp + 1;
    }
    return true;
}

void sendAll(int fd, const char* p, size_t n) {
    while (n) {
        const ssize_t k = write(fd, p, n);
        if (k <= 0) return;
        p += k; n -= (size_t)k;
    }
}

void respond(int fd, int code, const char* status, const char* type, const std::string& body) {
    char head[512];
    const int k = std::snprintf(head, sizeof head,
                                "HTTP/1.1 %d %s\r\n"
                                "Content-Type: %s\r\n"
                                "Content-Length: %zu\r\n"
                                "Cache-Control: no-store\r\n"
                                "Connection: close\r\n\r\n",
                                code, status, type, body.size());
    sendAll(fd, head, (size_t)k);
    sendAll(fd, body.data(), body.size());
}

void sendJson(int fd, const std::string& body)  { respond(fd, 200, "OK", "application/json; charset=utf-8", body); }

void sendError(int fd, int code, const char* status, const std::string& msg) {
    Jw j;
    j.beginObj();
    j.kv("error", msg);
    j.endObj();
    respond(fd, code, status, "application/json; charset=utf-8", j.out());
}

const char* mimeOf(const std::string& path) {
    const size_t dot = path.rfind('.');
    const std::string ext = dot == std::string::npos ? "" : path.substr(dot);
    if (ext == ".html") return "text/html; charset=utf-8";
    if (ext == ".js")   return "text/javascript; charset=utf-8";
    if (ext == ".css")  return "text/css; charset=utf-8";
    if (ext == ".svg")  return "image/svg+xml";
    if (ext == ".json") return "application/json; charset=utf-8";
    if (ext == ".png")  return "image/png";
    if (ext == ".ico")  return "image/x-icon";
    return "application/octet-stream";
}

bool readFile(const std::string& path, std::string& out) {
    std::FILE* f = std::fopen(path.c_str(), "rb");
    if (!f) return false;
    char buf[65536];
    size_t k;
    out.clear();
    while ((k = std::fread(buf, 1, sizeof buf, f)) > 0) out.append(buf, k);
    std::fclose(f);
    return true;
}

// ---------------------------------------------------------------------------
// The routes.
// ---------------------------------------------------------------------------
struct Server {
    std::string root;
    std::string tablesDir;
    // The statistics file written by `kings --stats-csv`.  Read, never
    // written, and re-read on every request so that a sweep running beside
    // the server shows up on the page as it goes.
    std::string statsPath;
    Store store;
    int threads = 1;
    Cache cache{ 6 };

    // What the store holds, read from the directory.  Kept between requests
    // because a directory with thousands of files in it on a USB drive is not
    // free to read, and refreshed when the directory's own mtime moves --
    // which is exactly when a table lands, since every writer here builds a
    // .part and renames it.  The time-based refresh is the backstop for a
    // filesystem whose directory mtime does not move the way it should.
    StoreScan scan;
    time_t scanDirMtime = 0;
    std::chrono::steady_clock::time_point scanAt{};
    bool scanned = false;

    struct StatRow {
        std::string cfg, wp, bp, posAny, posQuiet;
        int n = 0, w = 0, b = 0;
        long long positions = 0, quietPositions = 0;
        int deepAny = 0, deepQuiet = 0;
        double winPct = 0, qWinPct = 0;
        bool alwaysWhite = false, haveQuiet = false;
    };

    // Everything the pages are built from, computed once and kept until the
    // thing it was computed from changes.
    //
    // Before this, every page load re-read the whole statistics file -- nearly
    // a megabyte, three thousand rows -- parsed it, and recomputed the summary
    // and the findings from scratch; and opening any board did it AGAIN, to
    // look up one opening position.  None of that changes between requests.
    // It changes when a sweep writes another table, and the refresh below is
    // what notices.
    std::vector<StatRow> statRowsCache;
    time_t statsMtime = 0;
    long long statsSize = -1;
    bool statsLoaded = false;
    // The finished JSON of the routes whose answer is a pure function of the
    // two things above.  Keyed by what went into it, so a stale key is simply
    // a miss rather than a wrong answer.
    std::map<std::string, std::string> jsonCache;
    unsigned dataVersion = 0;     // bumped when the store or the statistics move

    // The same cache, kept on the LOCAL disk so that it survives a restart.
    //
    // The store lives on an external drive, and when that drive is slow --
    // this one took twenty minutes to list three thousand files after a stall
    // -- a freshly started server has nothing to show until the scan finishes.
    // It has no business recomputing any of it anyway: what a sweep measured
    // last week is still what it measured.  So the finished answers and a
    // mirror of the statistics file are written here, read back at startup,
    // and replaced only when the drive says something changed.
    std::string cacheDir;

    // The build that wrote the cache.  An answer is a function of the data AND
    // of the code that shaped it, so a rebuilt binary must not serve what the
    // previous one computed: the enumeration changed shape once already, and
    // the old JSON was served for a route whose answer had halved.
    static const char* buildId() { return __DATE__ " " __TIME__; }

    std::string cachePath(const std::string& name) const {
        return cacheDir.empty() ? std::string() : cacheDir + "/" + name;
    }
    static bool readFileInto(const std::string& path, std::string& out) {
        std::FILE* f = std::fopen(path.c_str(), "rb");
        if (!f) return false;
        char buf[65536];
        size_t got;
        out.clear();
        while ((got = std::fread(buf, 1, sizeof buf, f)) > 0) out.append(buf, got);
        std::fclose(f);
        return true;
    }
    static void writeFileFrom(const std::string& path, const std::string& data) {
        if (path.empty()) return;
        // Written beside itself and renamed, so a reader never sees half of it.
        const std::string tmp = path + ".part";
        std::FILE* f = std::fopen(tmp.c_str(), "wb");
        if (!f) return;
        std::fwrite(data.data(), 1, data.size(), f);
        std::fclose(f);
        std::rename(tmp.c_str(), path.c_str());
    }

    // What the last run left behind: the statistics as they were, and the
    // finished JSON of each route.  Nothing here is trusted over the drive --
    // the first background refresh replaces all of it -- it is what the pages
    // show in the meantime.
    void loadCache() {
        if (cacheDir.empty()) return;
        std::string mirror;
        if (readFileInto(cachePath("stats.csv"), mirror)) {
            statRowsCache = parseStats(mirror);
            statsLoaded = !statRowsCache.empty();
            // The mtime and size recorded are the DRIVE's, from the stamp file,
            // so an unchanged drive does not trigger a re-read.
            std::string stamp;
            if (readFileInto(cachePath("stats.stamp"), stamp)) {
                long long mt = 0, sz = -1;
                if (std::sscanf(stamp.c_str(), "%lld %lld", &mt, &sz) == 2) {
                    statsMtime = (time_t)mt;
                    statsSize = sz;
                }
            }
        }
        std::string stampedBy;
        readFileInto(cachePath("build.stamp"), stampedBy);
        if (stampedBy != buildId()) {
            // A different binary wrote this.  Keep the statistics mirror --
            // that is the drive's data, not ours -- and drop the answers.
            std::fprintf(stderr, "  cache: written by another build, recomputing\n");
            writeFileFrom(cachePath("build.stamp"), buildId());
            return;
        }
        for (const char* k : { "store", "interesting", "coverage:m5", "coverage:c5",
                               "coverage:m6", "coverage:c6" }) {
            std::string js;
            if (readFileInto(cachePath(std::string("r-") + k + ".json"), js) && !js.empty())
                jsonCache.emplace(std::string(k) + "@0", std::move(js));
        }
        if (!jsonCache.empty() || statsLoaded)
            std::fprintf(stderr, "  cache: %zu answers and %zu statistics rows from the "
                                 "last run\n", jsonCache.size(), statRowsCache.size());
    }
    void saveCacheEntry(const std::string& key, const std::string& json) const {
        writeFileFrom(cachePath("r-" + key + ".json"), json);
    }

    // The scan runs OFF the request path, on a thread of its own.
    //
    // It used to run inline, which was fine until the drive holding the store
    // went slow: listing its three thousand files took twenty minutes at the
    // worst of it, and because this server answers one request at a time by
    // design, every page in the browser waited on that listing.  Reading a
    // single table stayed fast throughout -- 0.2 s -- so the boards themselves
    // were never the problem; only the enumeration was.  Now a request takes
    // whatever scan has last completed, empty if none has, and kicks off a
    // refresh in the background if one is not already running.  A page that
    // says "nothing on disk yet" for a few seconds is a great deal better than
    // a page that never loads.
    std::mutex scanLock;
    std::atomic<bool> scanning{ false };

    const StoreScan& inventory() {
        if (tablesDir.empty()) return scan;
        bool stale = !scanned;
        if (!stale) {
            struct stat st;
            const bool haveStat = stat(tablesDir.c_str(), &st) == 0;
            const auto now = std::chrono::steady_clock::now();
            stale = (haveStat && st.st_mtime != scanDirMtime) ||
                    std::chrono::duration_cast<std::chrono::seconds>(now - scanAt).count() > 120;
        }
        if (stale && !scanning.exchange(true)) {
            std::thread([this] {
                // The statistics FIRST.  They are one file and read in a
                // fraction of a second; the store is three thousand and on a
                // sick drive takes twenty minutes.  Doing them in this order
                // means the summary and the findings appear at once instead of
                // waiting behind an enumeration they have nothing to do with.
                struct stat ss;
                const bool haveStats = !statsPath.empty() && stat(statsPath.c_str(), &ss) == 0;
                std::vector<StatRow> rows;
                std::string raw;
                const bool statsMoved =
                    haveStats && (ss.st_mtime != statsMtime || (long long)ss.st_size != statsSize);
                if (statsMoved) {
                    rows = loadStats(&raw);
                    // Mirrored locally, with the drive's own mtime and size
                    // beside it, so the next run can read the statistics
                    // without waiting on the drive at all.
                    writeFileFrom(cachePath("stats.csv"), raw);
                    char stamp[64];
                    std::snprintf(stamp, sizeof stamp, "%lld %lld",
                                  (long long)ss.st_mtime, (long long)ss.st_size);
                    writeFileFrom(cachePath("stats.stamp"), stamp);
                }
                if (statsMoved) {
                    std::lock_guard<std::mutex> lk(scanLock);
                    statRowsCache = std::move(rows);
                    statsMtime = ss.st_mtime;
                    statsSize = (long long)ss.st_size;
                    statsLoaded = true;
                    ++dataVersion;
                    jsonCache.clear();
                }

                // Now the slow half.
                struct stat st;
                const bool haveStat = stat(tablesDir.c_str(), &st) == 0;
                StoreScan fresh = scanStore(tablesDir);
                {
                    std::lock_guard<std::mutex> lk(scanLock);
                    scan = std::move(fresh);
                    scanDirMtime = haveStat ? st.st_mtime : 0;
                    scanAt = std::chrono::steady_clock::now();
                    scanned = true;
                    ++dataVersion;
                    jsonCache.clear();     // everything derived from them is stale
                }
                scanning = false;
            }).detach();
        }
        std::lock_guard<std::mutex> lk(scanLock);
        return scan;
    }

    // The boards one family has files for, out of the cached scan rather than
    // by re-reading the directory per family: /api/families asks this
    // twenty-eight times in a row.
    const StoreEntry* entryFor(const std::string& id) {
        for (const StoreEntry& e : inventory().entries)
            if (e.id == id) return &e;
        return nullptr;
    }

    // A catalogue ceiling says how big a board is worth solving from cold --
    // KQKBB stops at 8 because 9 takes minutes.  It has nothing to say about a
    // board already sitting on the drive, and refusing to open one because a
    // constant written before the sweep says 8 is the page disagreeing with
    // its own storage.  So the ceiling rises to whatever has been generated.
    // It never falls: a configuration with no files still solves on demand
    // exactly as it did.
    void widenToStore(Family& f) {
        const StoreEntry* e = entryFor(f.id);
        if (e && !e->boards.empty() && e->boards.back() > f.maxN) f.maxN = e->boards.back();
    }

    void families(int fd) {
        Jw j;
        j.beginObj();
        j.kv("tablesDir", tablesDir);
        j.key("families");
        j.beginArr();
        for (const Family& cf : familyCatalogue()) {
            Family f = cf;
            widenToStore(f);
            j.beginObj();
            j.kv("id", f.id);
            j.kv("label", f.label);
            j.kv("title", f.title);
            j.kv("group", f.group);
            j.kv("rules", f.rules);
            j.kv("blurb", f.blurb);
            j.kv("minN", f.minN);
            j.kv("maxN", f.maxN);
            j.kv("defN", f.defN);
            j.key("generated");
            j.beginArr();
            // Exactly the boards the loader would find, taken from the scan of
            // the directory.  That now covers the kings lattice and mixed as
            // well, which used to report nothing here because they name their
            // files themselves: ten of these twenty-eight cards claimed an
            // empty store while sitting on a drive full of their tables.  For
            // the lattice a board counts only when every table it converts
            // into is there too -- see scanStore.
            if (const StoreEntry* e = entryFor(f.id))
                for (int n : e->boards) j.num(n);
            j.endArr();
            j.endObj();
        }
        j.endArr();
        j.endObj();
        sendJson(fd, j.out());
    }

    // ---- the interesting positions ---------------------------------------
    // Read back out of the statistics file the solver writes with
    // --stats-csv.  Nothing is solved to answer this: the whole point is that
    // the home page can show a real position from every configuration that has
    // been measured without building a single table, which it could not
    // possibly do in the time a page load allows.
    //
    // What makes a position interesting is decided by the statistics rather
    // than by taste, and there are four things worth surfacing, in this order:
    //
    //  1. A material that is won often but never from a quiet placement.  That
    //     is the sharpest thing the quiet census found: every win needs a man
    //     already standing where it can be taken, so the "win" is an artifact
    //     of the position rather than a property of the material.
    //  2. The deepest win that starts from a quiet placement -- the hardest
    //     genuine problem, as opposed to the deepest win outright, which is
    //     usually one where something already hangs and gives the answer away.
    //  3. A material won from every placement either way.
    //  4. The deepest win outright, as a fallback when nothing above fires.

    static std::vector<std::string> csvSplit(const std::string& line) {
        std::vector<std::string> out;
        std::string cur;
        bool inQ = false;
        for (char c : line) {
            if (c == '"') { inQ = !inQ; continue; }
            if (c == ',' && !inQ) { out.push_back(cur); cur.clear(); continue; }
            cur += c;
        }
        out.push_back(cur);
        return out;
    }

    // Reading the file and understanding it are separate, so that the copy
    // kept locally can be parsed without going near the drive again.
    std::vector<StatRow> loadStats(std::string* rawOut = nullptr) const {
        std::vector<StatRow> rows;
        if (statsPath.empty()) return rows;
        std::string all;
        if (!readFileInto(statsPath, all)) return rows;
        if (rawOut) *rawOut = all;
        return parseStats(all);
    }

    static std::vector<StatRow> parseStats(const std::string& all) {
        std::vector<StatRow> rows;
        std::vector<std::string> lines;
        {
            std::string cur;
            for (char c : all) { if (c == '\n') { lines.push_back(cur); cur.clear(); } else if (c != '\r') cur += c; }
            if (!cur.empty()) lines.push_back(cur);
        }
        if (lines.empty()) return rows;
        std::map<std::string, int> col;
        {
            std::vector<std::string> h = csvSplit(lines[0]);
            for (size_t i = 0; i < h.size(); ++i) col[h[i]] = (int)i;
        }
        auto need = [&](const char* k) { return col.count(k) ? col[k] : -1; };
        // A file written by an older build is simply not used, rather than
        // half read into fields that do not mean what they are called.
        if (need("config") < 0 || need("deepest_white_quiet_pos") < 0) return rows;

        for (size_t li = 1; li < lines.size(); ++li) {
            std::vector<std::string> v = csvSplit(lines[li]);
            if ((int)v.size() <= need("deepest_white_quiet_pos")) continue;
            auto get = [&](const char* k) -> std::string {
                int i = need(k); return (i >= 0 && i < (int)v.size()) ? v[i] : std::string();
            };
            auto num = [&](const char* k) -> double {
                const std::string s = get(k);
                if (s.empty() || s == "na") return 0;
                return std::atof(s.c_str());
            };
            StatRow r;
            r.cfg = get("config"); r.wp = get("white_piece"); r.bp = get("black_piece");
            r.n = (int)num("n"); r.w = (int)num("w"); r.b = (int)num("b");
            r.positions = (long long)num("positions");
            r.haveQuiet = get("quiet_positions") != "na" && !get("quiet_positions").empty();
            r.quietPositions = (long long)num("quiet_positions");
            r.deepAny = (int)num("deepest_white"); r.deepQuiet = (int)num("deepest_white_quiet");
            r.winPct = num("wtm_win_pct"); r.qWinPct = num("q_wtm_win_pct");
            r.alwaysWhite = get("always_win_white") == "1";
            r.posAny = get("deepest_white_pos"); r.posQuiet = get("deepest_white_quiet_pos");
            if (r.n > 0 && r.w > 0 && r.b > 0) rows.push_back(r);
        }
        return rows;
    }

    // The parsed statistics, as of the last refresh.  Never reads the disk:
    // the refresh above does that, off the request path.
    // A snapshot, because the refresh thread replaces the vector underneath.
    // Copying one row out under the lock is cheap; handing out a reference to
    // a vector another thread is about to move from is not.
    bool statsRowFor(const std::string& id, int n, StatRow& out) {
        inventory();
        std::lock_guard<std::mutex> lk(scanLock);
        for (const StatRow& r : statRowsCache)
            if (r.n == n && famIdOf(r) == id) { out = r; return true; }
        return false;
    }

    // An answer that depends only on the store and the statistics.  `build`
    // runs once per key per version and its JSON is kept.
    template <class F>
    const std::string& cachedJson(const std::string& key, F&& build) {
        inventory();
        std::lock_guard<std::mutex> lk(scanLock);
        const std::string k = key + "@" + std::to_string(dataVersion);
        auto it = jsonCache.find(k);
        if (it != jsonCache.end()) return it->second;
        // A version that has not been computed yet falls back to whatever the
        // last run left, so a restart shows the collection at once instead of
        // an empty page while the drive is enumerated.
        std::string js = build();
        const bool empty = js.find("\"configurations\":0") != std::string::npos ||
                           js.find("\"rows\":0") != std::string::npos;
        if (empty) {
            auto old = jsonCache.find(key + "@0");
            if (old != jsonCache.end() && old->second.size() > js.size()) return old->second;
            // Nothing worth keeping: the scan has not finished yet, and an
            // empty answer written over a good one would make the next start
            // worse rather than better.
            return jsonCache.emplace(k, std::move(js)).first->second;
        }
        saveCacheEntry(key, js);
        return jsonCache.emplace(k, std::move(js)).first->second;
    }

    // The catalogue id that opens the configuration a statistics row measured.
    // A mixed row carries its two unlike white men in one column as
    // "king+bishop", and is addressed as mixed-w1-w2-black rather than by the
    // kings lattice's shape; the plus is what distinguishes them, nothing else
    // in the schema does.  A shared-solver row is addressed by the endgame
    // name in lower case -- "kbnk", "kbk-capture" -- which is exactly the
    // config column folded down.
    // Which rule set a statistics row was measured under.  The kings lattice
    // and the mixed solver only ever play capture rules; the shared and armed
    // solvers play both, and say which in the name -- "KBBK" against
    // "KBBK-capture".  The page keeps the two apart everywhere it shows them,
    // because the same material is a different game under each and quoting a
    // depth without the rule set says nothing.
    static const char* rulesOf(const StatRow& r) {
        if (r.wp != "shared" && r.wp != "armed") return "capture";
        const std::string tail = "-capture";
        const bool cap = r.cfg.size() > tail.size() &&
                         r.cfg.compare(r.cfg.size() - tail.size(), tail.size(), tail) == 0;
        return cap ? "capture" : "mate";
    }

    static std::string famIdOf(const StatRow& r) {
        char fam[128];
        const size_t plus = r.wp.find('+');
        if (r.wp == "shared" || r.wp == "armed") {
            std::string id = r.cfg;
            for (char& c : id) c = (char)std::tolower((unsigned char)c);
            return id;
        }
        if (plus != std::string::npos)
            std::snprintf(fam, sizeof fam, "mixed-%s-%s-%s",
                          r.wp.substr(0, plus).c_str(),
                          r.wp.substr(plus + 1).c_str(), r.bp.c_str());
        else
            std::snprintf(fam, sizeof fam, "kings-%d-%d-%s-%s",
                          r.w, r.b, r.wp.c_str(), r.bp.c_str());
        return fam;
    }

    // The position to open a configuration on, taken from the statistics file
    // rather than from the table.
    //
    // The engines find it by scanning: the deepest win from a quiet placement,
    // over every placement there is.  That scan is what a census costs, and on
    // a table mapped from an external drive it is the single slowest thing the
    // server does -- 83 s for one kings board, against a fraction of that to
    // solve the same table from scratch in memory.  But the scan has already
    // been done once, by the sweep that generated the table, and its answer is
    // sitting in two columns of stats.csv.  So look there first and hand the
    // engine the position; it then has no reason to census at all.
    //
    // The file is authority for nothing: the position is parsed and validated
    // against the engine like any position from a URL, and a row that does not
    // match is simply not used.
    bool startFromStats(const std::string& id, int n, const Geometry& g,
                        const Engine& eng, View& v, std::string& note) {
        if (statsPath.empty()) return false;
        StatRow r;
        if (statsRowFor(id, n, r)) {
            const bool quiet = !r.posQuiet.empty();
            const std::string& spec = quiet ? r.posQuiet : r.posAny;
            if (spec.empty()) {
                // The row exists and carries no position, which for these
                // rows means one thing: White wins nothing here.  Scanning the
                // table would rediscover exactly that, and on the big boards
                // it takes tens of minutes -- BBB vs QQ on 12 x 12 did not
                // answer inside twenty.  The engine is told to skip it.
                if (r.deepAny == 0 && r.positions > 20000000) eng.skipScan = true;
                return false;
            }
            std::string err;
            if (!parsePos(g, spec, true, v, err)) return false;
            if (!eng.accept(v, err)) return false;
            note = quiet ? "the deepest win White has from a quiet position"
                         : "the deepest win White has -- no quiet position reaches it";
            note += " (from the statistics file, so the table itself was not scanned)";
            return true;
        }
        return false;
    }

    void interesting(int fd) {
        sendJson(fd, cachedJson("interesting", [this] { return interestingJson(); }));
    }

    std::string interestingJson() {
        const std::vector<StatRow>& rows = statRowsCache;

        // What one material does ACROSS boards, which is where most of the
        // interesting results live.  A single row says how deep a win is on
        // one board; the sequence says whether the depth grows with the board,
        // stops growing, or -- the result nobody expects -- falls.
        struct Agg {
            const StatRow* peak = nullptr;       // deepest win of any board
            const StatRow* last = nullptr;       // largest board measured
            const StatRow* quiet = nullptr;      // deepest quiet win
            const StatRow* rev = nullptr;        // won often, never from quiet
            const StatRow* always = nullptr;     // won from every placement
            const StatRow* modest = nullptr;     // the largest board up to 8 x 8
            int boards = 0, lo = 0, hi = 0;
            long long maxPositions = 0;
            bool everWon = false;
        };
        std::map<std::string, Agg> agg;
        for (const StatRow& r : rows) {
            if (r.positions <= 0) continue;
            Agg& a = agg[r.cfg];
            ++a.boards;
            if (!a.lo || r.n < a.lo) a.lo = r.n;
            if (r.n > a.hi) a.hi = r.n;
            if (r.positions > a.maxPositions) a.maxPositions = r.positions;
            if (r.deepAny > 0) a.everWon = true;
            if (!a.peak || r.deepAny > a.peak->deepAny) a.peak = &r;
            if (!a.last || r.n > a.last->n) a.last = &r;
            // A card that names no position makes the explorer scan for one,
            // and that scan is the expensive thing on a big mapped table.  So
            // such a card opens a board that is still substantial and cheap to
            // scan rather than the largest one measured.
            if (r.n <= 8 && (!a.modest || r.n > a.modest->n)) a.modest = &r;
            if (r.deepQuiet > 0 && !r.posQuiet.empty() &&
                (!a.quiet || r.deepQuiet > a.quiet->deepQuiet)) a.quiet = &r;
            if (r.haveQuiet && r.positions >= 100000 && r.winPct > 5.0 &&
                r.qWinPct < 0.0001 && !r.posAny.empty() &&
                (!a.rev || r.positions > a.rev->positions)) a.rev = &r;
            if (r.alwaysWhite && r.positions >= 100000 && r.deepAny > 0 &&
                !r.posAny.empty() && (!a.always || r.deepAny > a.always->deepAny))
                a.always = &r;
        }

        // A card to show: a position, the board it is on, and why it is here.
        // `pos` may be empty, which means "open this configuration and let the
        // explorer choose" -- the only sensible thing for a material White
        // never wins, where there is no winning position to point at.
        struct Pick {
            const StatRow* r = nullptr;
            std::string kind, why, pos;
            double score = 0;
        };

        // Five findings rather than twelve readings of one.  Before this the
        // page filled with twelve copies of the deepest-quiet tier, because
        // that tier outranks the others and there are hundreds of rows in it;
        // the results that are actually surprising never reached the page at
        // all.  Each category is drawn from its own best rows, and they are
        // interleaved below.
        std::vector<Pick> deep, shrink, reversal, never, always;
        char why[420];
        for (const auto& kv : agg) {
            const Agg& a = kv.second;

            if (a.quiet) {
                std::snprintf(why, sizeof why,
                    "the deepest win that begins with nothing hanging: %d plies "
                    "(%d outright, over %lld placements)",
                    a.quiet->deepQuiet, a.quiet->deepAny, (long long)a.quiet->positions);
                deep.push_back({ a.quiet, "deepest", why, a.quiet->posQuiet,
                                 (double)a.quiet->deepQuiet });
            }

            // The depth peaks on a middle board and falls away on the bigger
            // ones.  Room to run is room to be chased into: past some size the
            // losing side has nowhere left that is far from everything.
            if (a.peak && a.last && a.boards >= 5 && a.peak->deepAny > 0 &&
                a.peak->n <= a.hi - 2 && a.last->deepAny * 2 < a.peak->deepAny &&
                !a.peak->posAny.empty()) {
                std::snprintf(why, sizeof why,
                    "deepest on %d x %d at %d plies, and only %d on %d x %d -- "
                    "the bigger board makes the win SHORTER",
                    a.peak->n, a.peak->n, a.peak->deepAny,
                    a.last->deepAny, a.last->n, a.last->n);
                shrink.push_back({ a.peak, "shrinks", why,
                                   a.peak->posQuiet.empty() ? a.peak->posAny : a.peak->posQuiet,
                                   (double)(a.peak->deepAny - a.last->deepAny) });
            }

            if (a.rev) {
                std::snprintf(why, sizeof why,
                    "won from %.1f%% of %lld placements but from none that are quiet -- "
                    "every win needs a man already standing where it can be taken",
                    a.rev->winPct, (long long)a.rev->positions);
                reversal.push_back({ a.rev, "reversal", why, a.rev->posAny,
                                     (double)a.rev->positions });
            }

            // White never wins it anywhere.  There is no position to point at,
            // so the card opens the configuration and lets the explorer show
            // what it finds -- which, since it now falls back to Black, is
            // Black's deepest win.
            if (!a.everWon && a.boards >= 4 && a.maxPositions >= 100000 && a.last) {
                std::snprintf(why, sizeof why,
                    "White does not win this material on ANY board measured, %d x %d "
                    "through %d x %d, over %lld placements at the largest",
                    a.lo, a.lo, a.hi, a.hi, (long long)a.last->positions);
                never.push_back({ a.modest ? a.modest : a.last, "never", why,
                                  std::string(), (double)a.maxPositions });
            }

            if (a.always) {
                std::snprintf(why, sizeof why,
                    "White wins from every one of the %lld placements, either side to "
                    "move; deepest %d plies",
                    (long long)a.always->positions, a.always->deepAny);
                always.push_back({ a.always, "always", why, a.always->posAny,
                                   (double)a.always->deepAny });
            }
        }

        auto top = [](std::vector<Pick>& v) {
            std::sort(v.begin(), v.end(),
                      [](const Pick& x, const Pick& y) { return x.score > y.score; });
        };
        top(deep); top(shrink); top(reversal); top(never); top(always);

        // Quotas, taken a round at a time so the page opens on a mixture
        // rather than on a run of one kind.  A category with nothing in it
        // gives its places up to the others.
        struct Quota { std::vector<Pick>* v; size_t want; size_t used; };
        Quota quotas[] = { { &shrink, 3, 0 }, { &deep, 3, 0 }, { &reversal, 2, 0 },
                           { &never, 2, 0 }, { &always, 2, 0 } };
        std::vector<Pick> picks;
        std::set<std::string> seen;
        for (size_t round = 0; round < 3; ++round)
            for (Quota& q : quotas) {
                if (q.used >= q.want) continue;
                for (Pick& p : *q.v)
                    if (seen.insert(p.r->cfg).second) { picks.push_back(p); ++q.used; break; }
            }
        // Anything left over goes to the deepest, so a thin store still fills
        // the section.
        for (Pick& p : deep) {
            if (picks.size() >= 12) break;
            if (seen.insert(p.r->cfg).second) picks.push_back(p);
        }

        // A summary of everything measured so far, so the page can say what
        // the collection actually contains rather than only showing twelve
        // positions out of it.  Counted here rather than in the browser because
        // the statistics file is the server's to read and is already parsed.
        std::map<std::string, long long> famRows;
        long long mateRows = 0, captureRows = 0;
        long long totalPositions = 0;
        int minN = 1 << 30, maxN = 0, deepest = 0;
        std::string deepestCfg; int deepestN = 0;
        std::set<std::string> alwaysWon;
        for (const StatRow& r : rows) {
            const std::string fam = r.wp.find('+') != std::string::npos ? "mixed"
                                  : r.wp == "shared" ? "normal chess"
                                  : r.wp == "armed"  ? "normal chess (armed)"
                                                     : "capture lattice";
            ++famRows[fam];
            if (std::string(rulesOf(r)) == "capture") ++captureRows; else ++mateRows;
            totalPositions += r.positions;
            if (r.n < minN) minN = r.n;
            if (r.n > maxN) maxN = r.n;
            if (r.deepAny > deepest) { deepest = r.deepAny; deepestCfg = r.cfg; deepestN = r.n; }
            if (r.alwaysWhite) alwaysWon.insert(r.cfg);
        }

        Jw j;
        j.beginObj();
        j.kv("statsFile", statsPath);
        j.key("summary");
        j.beginObj();
        j.kv("rows", (long long)rows.size());
        j.kv("configurations", (long long)agg.size());
        j.kv("positions", totalPositions);
        j.kv("minN", rows.empty() ? 0 : minN);
        j.kv("maxN", maxN);
        j.kv("deepest", deepest);
        j.kv("deepestConfig", deepestCfg);
        j.kv("deepestN", deepestN);
        j.kv("alwaysWon", (long long)alwaysWon.size());
        j.kv("mateRows", mateRows);
        j.kv("captureRows", captureRows);
        // The three counts the findings below are drawn from, so the page can
        // say how many there are rather than only showing a handful.
        j.kv("shrinking", (long long)shrink.size());
        j.kv("neverWon", (long long)never.size());
        j.kv("reversals", (long long)reversal.size());
        j.key("families");
        j.beginArr();
        for (const auto& kv : famRows) {
            j.beginObj(); j.kv("name", kv.first); j.kv("rows", kv.second); j.endObj();
        }
        j.endArr();
        j.endObj();
        j.key("positions");
        j.beginArr();
        for (const Pick& p : picks) {
            // Never offer a card the explorer cannot open.  The statistics
            // file holds rows for readings the catalogue does not carry --
            // KQKR under capture rules is measured but has no family, and its
            // table would collide with the mating one's file name if it did
            // -- and a card linking to an id that resolves to nothing is a
            // 404 with a picture on it.
            const std::string id = famIdOf(*p.r);
            Family probe;
            if (!familyById(id, probe)) continue;
            j.beginObj();
            j.kv("family", id);
            j.kv("config", p.r->cfg);
            j.kv("rules", rulesOf(*p.r));
            j.kv("n", p.r->n);
            j.kv("kind", p.kind);
            j.kv("pos", p.pos);
            j.kv("stm", "w");
            j.kv("why", p.why);
            j.kv("deepest", p.r->deepAny);
            j.kv("deepestQuiet", p.r->deepQuiet);
            j.kv("positions", p.r->positions);
            j.endObj();
        }
        j.endArr();
        j.endObj();
        return j.out();
    }

    // ---- the inventory --------------------------------------------------
    // Everything in the store, whether or not the catalogue lists it.  A sweep
    // writes hundreds of configurations the catalogue never mentions, and
    // every one of them opens in the explorer by its structured id; this is
    // how the page finds out they exist.
    void inventoryRoute(int fd) {
        sendJson(fd, cachedJson("store", [this] { return inventoryJson(); }));
    }

    std::string inventoryJson() {
        const StoreScan& sc = scan;
        Jw j;
        j.beginObj();
        j.kv("dir", sc.dir);
        j.kv("files", (long long)sc.filesTotal);
        j.kv("bytes", (long long)sc.bytesTotal);
        long long boards = 0;
        for (const StoreEntry& e : sc.entries) boards += (long long)e.boards.size();
        j.kv("configurations", (long long)sc.entries.size());
        j.kv("boards", boards);
        j.key("entries");
        j.beginArr();
        for (const StoreEntry& e : sc.entries) {
            j.beginObj();
            j.kv("id", e.id);
            j.kv("label", e.label);
            j.kv("title", e.title);
            j.kv("group", e.group);
            j.kv("rules", e.rules);
            j.kv("listed", e.listed);
            j.kv("files", e.files);
            j.kv("bytes", (long long)e.bytes);
            j.key("boards");
            j.beginArr();
            for (int n : e.boards) j.num(n);
            j.endArr();
            j.endObj();
        }
        j.endArr();
        j.endObj();
        return j.out();
    }

    // ---- the whole space -------------------------------------------------
    // Every material there is under one rule set, marked with what is known
    // about it: solved and on the drive, or not solvable here at all.  The
    // catalogue and the store can only ever say what exists; this says what
    // does not, which is the larger part and the honest part.
    void coverageRoute(int fd, const Req& r) {
        auto arg = [&](const char* k, const std::string& dflt) {
            auto it = r.q.find(k);
            return it == r.q.end() ? dflt : it->second;
        };
        const bool capture = arg("rules", "capture") != "mate";
        int men = std::atoi(arg("men", "5").c_str());
        if (men < 2 || men > 6) men = 5;
        sendJson(fd, cachedJson(std::string("coverage:") + (capture ? "c" : "m") +
                                std::to_string(men),
                                [this, capture, men] { return coverageJson(capture, men); }));
    }

    std::string coverageJson(bool capture, int men) {
        const std::vector<MaterialRow> rows = coverage(capture, men, scan);

        long long stored = 0, solvable = 0, boards = 0, mirrors = 0;
        for (const MaterialRow& m : rows) {
            if (!m.boards.empty()) ++stored;
            if (m.supported) ++solvable;
            if (m.mirror) ++mirrors;
            boards += (long long)m.boards.size();
        }
        Jw j;
        j.beginObj();
        j.kv("rules", capture ? "capture" : "mate");
        j.kv("maxMen", men);
        j.kv("materials", (long long)rows.size());
        j.kv("supported", solvable);
        j.kv("stored", stored);
        j.kv("mirrors", mirrors);
        j.kv("boards", boards);
        j.key("rows");
        j.beginArr();
        for (const MaterialRow& m : rows) {
            j.beginObj();
            j.kv("label", m.label);
            j.kv("white", m.white);
            j.kv("black", m.black);
            j.kv("group", m.group);
            j.kv("men", m.men);
            j.kv("id", m.id);
            j.kv("supported", m.supported);
            j.kv("mirror", m.mirror);
            j.kv("mirrorOf", m.mirrorOf);
            j.key("boards");
            j.beginArr();
            for (int n : m.boards) j.num(n);
            j.endArr();
            j.endObj();
        }
        j.endArr();
        j.endObj();
        return j.out();
    }

    void position(int fd, const Req& r) {
        auto arg = [&](const char* k, const std::string& dflt) {
            auto it = r.q.find(k);
            return it == r.q.end() ? dflt : it->second;
        };
        Family f;
        if (!familyById(arg("family", "kqk"), f)) {
            sendError(fd, 404, "Not Found", "no such configuration");
            return;
        }
        widenToStore(f);
        int n = std::atoi(arg("n", std::to_string(f.defN)).c_str());
        if (n < f.minN || n > f.maxN) {
            sendError(fd, 400, "Bad Request",
                      "board size must be between " + std::to_string(f.minN) +
                      " and " + std::to_string(f.maxN) + " for " + f.label);
            return;
        }
        std::string err;
        Engine* eng = cache.get(f, n, threads, store, err);
        if (!eng) { sendError(fd, 500, "Internal Server Error", err); return; }
        const Geometry& g = eng->geo();

        View v;
        std::string note;
        const std::string spec = arg("pos", "");
        if (spec.empty()) {
            // Only the kings lattice takes its opening position from the
            // statistics.  It is the one family whose scan is expensive -- the
            // others load and scan in under two seconds -- and where several
            // placements tie at the deepest depth, the sweep and the explorer
            // pick different ones.  Both are correct and the depth is the
            // same, but there is no reason to change which position the other
            // families have always shown.
            if (f.kind != Family::Kings || !startFromStats(f.id, n, g, *eng, v, note))
                v = eng->start(note);
            eng->skipScan = false;
            if (v.men.empty()) {
                sendError(fd, 404, "Not Found", "nothing to show for this configuration");
                return;
            }
        } else {
            const std::string stm = arg("stm", "w");
            if (!parsePos(g, spec, stm != "b", v, err)) {
                sendError(fd, 400, "Bad Request", err);
                return;
            }
            if (!eng->accept(v, err)) { sendError(fd, 400, "Bad Request", err); return; }
        }

        const Val val = eng->value(v);
        std::vector<MoveOut> mv = eng->moves(v);
        sortMoves(mv, v.wtm);

        Jw j;
        j.beginObj();
        j.kv("family", f.id);
        j.kv("label", f.label);
        j.kv("title", f.title);
        j.kv("group", f.group);
        j.kv("rules", f.rules);
        j.kv("blurb", f.blurb);
        j.kv("material", eng->material());
        // Where the tables behind this answer came from, so that a claim that
        // the board was read off the drive can be checked one configuration at
        // a time rather than inferred from how long it took.
        j.kv("source", eng->source);
        j.kv("minN", f.minN);
        j.kv("maxN", f.maxN);
        // Which board sizes are already files.  The slider offers every size
        // the configuration is defined for, and most of them are solved on
        // demand; saying which are on the drive is the difference between a
        // board that opens and a board that takes a minute.
        j.key("onDisk");
        j.beginArr();
        if (const StoreEntry* e = entryFor(f.id))
            for (int b : e->boards) j.num(b);
        j.endArr();
        j.kv("n", n);
        j.kv("stm", v.wtm ? "w" : "b");
        j.kv("pos", posString(g, v));
        j.kv("note", note);
        j.kv("quiet", eng->quiet(v));
        writeMen(j, g, v);
        j.key("value");
        writeVal(j, val, v.wtm);
        j.key("moves");
        j.beginArr();
        for (const MoveOut& m : mv) {
            j.beginObj();
            j.kv("san", m.san);
            j.kv("from", m.from >= 0 ? g.name(m.from) : std::string("-"));
            j.kv("to", m.to >= 0 ? g.name(m.to) : std::string("-"));
            j.kv("ff", m.from >= 0 ? g.file(m.from) : -1);
            j.kv("fr", m.from >= 0 ? g.rank(m.from) : -1);
            j.kv("tf", m.to >= 0 ? g.file(m.to) : -1);
            j.kv("tr", m.to >= 0 ? g.rank(m.to) : -1);
            j.kv("cap", m.capture);
            j.kv("playable", m.playable);
            j.kv("note", m.note);
            j.kv("pos", posString(g, m.after));
            j.kv("stm", m.after.wtm ? "w" : "b");
            j.key("value");
            // The value of the position after the move, still read from the
            // point of view of the side that made it -- that is what a move
            // list means by "this move wins in eight".
            writeVal(j, m.val, v.wtm);
            j.endObj();
        }
        j.endArr();
        j.endObj();
        sendJson(fd, j.out());
    }

    void statics(int fd, const Req& r) {
        std::string rel = r.path == "/" ? "/index.html" : r.path;
        if (rel.find("..") != std::string::npos) {
            sendError(fd, 403, "Forbidden", "no");
            return;
        }
        const std::string path = root + rel;
        std::string body;
        if (!readFile(path, body)) {
            respond(fd, 404, "Not Found", "text/plain; charset=utf-8",
                    "no such file: " + rel + "\n(the web root is " + root + ")\n");
            return;
        }
        respond(fd, 200, "OK", mimeOf(path), body);
    }

    // Read the request, then answer it under the lock.  A connection that
    // never says anything -- a browser's pre-connect -- costs this one thread
    // and the receive timeout, and holds nothing anyone else wants.
    void handle(int fd) {
        timeval tv{};
        tv.tv_sec = 10;
        setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);

        std::string head;
        char buf[4096];
        while (head.find("\r\n\r\n") == std::string::npos && head.size() < 65536) {
            const ssize_t k = read(fd, buf, sizeof buf);
            if (k <= 0) break;
            head.append(buf, (size_t)k);
        }
        if (head.empty()) return;               // said nothing; nothing to answer

        Req r;
        if (!parseRequest(head, r)) {
            respond(fd, 400, "Bad Request", "text/plain", "GET only\n");
            return;
        }
        std::lock_guard<std::mutex> lk(answering);
        if (r.path == "/api/families") families(fd);
        else if (r.path == "/api/interesting") interesting(fd);
        else if (r.path == "/api/store") inventoryRoute(fd);
        else if (r.path == "/api/coverage") coverageRoute(fd, r);
        else if (r.path == "/api/position") position(fd, r);
        else statics(fd, r);
    }

    std::mutex answering;
};

// Where the HTML lives.  `--root` wins; otherwise the obvious places, so that
// running the binary from the source tree just works.
std::string findRoot(const std::string& given) {
    if (!given.empty()) return given;
    const char* env = getenv("EGTB_WEB");
    if (env && *env) return env;
    const char* tries[] = { "web", "./web", "../web" };
    for (const char* t : tries) {
        struct stat st;
        if (stat((std::string(t) + "/index.html").c_str(), &st) == 0) return t;
    }
    return "web";
}

} // namespace

int runServe(int argc, char** argv, int threads) {
    int port = 8080;
    std::string root, tables = "artifacts/tables", statsFile, cacheDirArg;
    bool readOnly = false;
    double minSeconds = 2.0;
    for (int i = 0; i < argc; ++i) {
        const std::string k = argv[i];
        auto val = [&]() { return (i + 1 < argc) ? std::string(argv[++i]) : std::string(); };
        if      (k == "--port" || k == "-p") port = std::atoi(val().c_str());
        else if (k == "--root")   root = val();
        else if (k == "--tables") tables = val();
        else if (k == "--stats")  statsFile = val();
        else if (k == "--cache")  cacheDirArg = val();
        else if (k == "--no-tables") tables.clear();
        else if (k == "--read-only") readOnly = true;
        else if (k == "--save-over") minSeconds = std::atof(val().c_str());
        else {
            std::fprintf(stderr, "serve: unknown option %s\n", k.c_str());
            return 2;
        }
    }

    Server s;
    s.root = findRoot(root);
    s.tablesDir = tables;
    s.statsPath = statsFile;
    // Where the answers are kept between runs.  Local by default and beside
    // the web root, never on the drive the store is on -- the whole point is
    // to be able to answer without touching that drive.
    s.cacheDir = cacheDirArg.empty() ? std::string(".egtb-cache") : cacheDirArg;
    if (s.cacheDir != "-") {
        ::mkdir(s.cacheDir.c_str(), 0755);
        s.loadCache();
    } else {
        s.cacheDir.clear();
    }
    s.store.dir = tables;
    // --read-only reads the store and never adds to it, for a directory that
    // is full, shared, or on a drive that should not be written.
    s.store.minSeconds = readOnly ? 1e18 : minSeconds;
    s.threads = threads;

    // A store directory is never created.  On an external drive the missing
    // case is usually the drive not being mounted, and creating the path would
    // quietly put a few hundred megabytes on the boot disk under a mount point
    // instead -- where it would also shadow the real store once the drive came
    // back.  So: say so, and run without a store rather than half of one.
    if (!tables.empty()) {
        struct stat dst;
        if (stat(tables.c_str(), &dst) != 0 || !S_ISDIR(dst.st_mode)) {
            std::fprintf(stderr,
                         "serve: '%s' is not a directory, so nothing will be loaded or kept.\n"
                         "       Create it, point --tables somewhere that exists (is the drive\n"
                         "       mounted?), or pass --no-tables to say you meant it.\n",
                         tables.c_str());
            s.tablesDir.clear();
            s.store.dir.clear();
        }
    }

    struct stat st;
    if (stat((s.root + "/index.html").c_str(), &st) != 0)
        std::fprintf(stderr, "serve: warning: no index.html under '%s'; "
                             "pass --root DIR to say where web/ is\n", s.root.c_str());

    const int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) { std::perror("socket"); return 1; }
    int one = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);

    sockaddr_in a{};
    a.sin_family = AF_INET;
    a.sin_port = htons((uint16_t)port);
    a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);   // local only, never the network
    if (bind(fd, (sockaddr*)&a, sizeof a) < 0) {
        std::fprintf(stderr, "serve: cannot bind port %d: %s\n", port, std::strerror(errno));
        close(fd);
        return 1;
    }
    if (listen(fd, 16) < 0) { std::perror("listen"); close(fd); return 1; }

    // --port 0 asks the kernel for a free one, which is how the test suite
    // starts a server without picking a port that might be in use.
    sockaddr_in bound{};
    socklen_t blen = sizeof bound;
    if (getsockname(fd, (sockaddr*)&bound, &blen) == 0) port = ntohs(bound.sin_port);

    std::printf("egtb serve: http://127.0.0.1:%d/   (web root %s, tables %s%s)\n",
                port, s.root.c_str(), s.tablesDir.empty() ? "(none)" : s.tablesDir.c_str(),
                s.tablesDir.empty() ? "" : (readOnly ? ", read only" : ", read and write"));
    std::printf("%zu configurations; ctrl-C to stop.\n", familyCatalogue().size());
    std::fflush(stdout);

    for (;;) {
        const int c = accept(fd, nullptr, nullptr);
        if (c < 0) continue;
        std::thread([&s, c] { s.handle(c); close(c); }).detach();
    }
}

} // namespace kqk
