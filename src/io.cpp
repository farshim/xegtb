// io.cpp -- on-disk format.
//
// Layout: a fixed header, the census, then the two value arrays.  Entries are
// bytes, so a plain run-length encoding over (value, varint count) pairs is
// both fast and effective -- dead slots, drawn regions and equal-depth shells
// all form long runs.
#include "table.hpp"

#include <cstdio>
#include <cstring>
#include <stdexcept>

namespace kqk {
namespace {

constexpr char MAGIC[8]   = { 'K', 'Q', 'K', 'T', 'B', 0, 0, 0 };
constexpr U32  VERSION    = 3;
constexpr U32  FLAG_RLE   = 1u << 0;

// Version history.  A reader accepts all of them; a writer emits the current
// one.  Older files hold one-piece endgames only, which is why the endgame
// could live in a flag bit before there was a field for it.
//   1  KQK only.
//   2  adds FLAG_ROOK for KRK.
//   3  adds an explicit endgame field and a second longest-position square,
//      for endgames with two white pieces.
constexpr U32  FLAG_ROOK  = 1u << 1;   // versions 1-2 only

// The version-3 header is the older one plus a suffix, so a reader can take
// the first sizeof(HeaderV12) bytes of any file and then decide whether there
// is more to come.  New fields must keep going on the end for that to hold.
struct HeaderV12 {
    char magic[8];
    U32  version, n, flags, histLen;
    U64  nkk, nslots, wBytes, bBytes;
    U32  maxPly; int32_t lwk, lbk, lwp0;
};

struct Header {
    HeaderV12 v12;
    U32       endgame;    // new in version 3
    int32_t   lwp1;       // new in version 3; -1 when White has one piece
};

static_assert(sizeof(Header) == sizeof(HeaderV12) + 8,
              "the version-3 header must be the version-1/2 header plus a suffix");

void put(std::FILE* f, const void* p, size_t n) {
    if (std::fwrite(p, 1, n, f) != n) throw std::runtime_error("short write");
}
void get(std::FILE* f, void* p, size_t n) {
    if (std::fread(p, 1, n, f) != n) throw std::runtime_error("short read / truncated file");
}
void putU64(std::vector<U8>& v, U64 x) { for (int i = 0; i < 8; ++i) v.push_back(U8(x >> (8 * i))); }

std::vector<U8> rleEncode(const U8* src, U64 n) {
    std::vector<U8> out;
    out.reserve((size_t)(n / 8 + 16));
    U64 i = 0;
    while (i < n) {
        U8 v = src[i];
        U64 j = i + 1;
        while (j < n && src[j] == v) ++j;
        U64 run = j - i;
        out.push_back(v);
        while (run >= 0x80) { out.push_back(U8((run & 0x7F) | 0x80)); run >>= 7; }
        out.push_back(U8(run));
        i = j;
    }
    return out;
}

void rleDecode(const std::vector<U8>& src, ByteArray& dst, U64 expect) {
    dst.resize(expect);
    U64 at = 0;
    size_t i = 0;
    while (i < src.size()) {
        U8 v = src[i++];
        U64 run = 0; int sh = 0;
        for (;;) {
            if (i >= src.size()) throw std::runtime_error("corrupt run-length stream");
            U8 c = src[i++];
            run |= U64(c & 0x7F) << sh;
            if (!(c & 0x80)) break;
            sh += 7;
        }
        if (at + run > expect) throw std::runtime_error("run-length stream is too long");
        std::memset(dst.data() + at, v, (size_t)run);
        at += run;
    }
    if (at != expect) throw std::runtime_error("run-length stream has the wrong length");
}

} // namespace

void Table::save(const std::string& path, bool rle) const {
    std::FILE* f = std::fopen(path.c_str(), "wb");
    if (!f) throw std::runtime_error("cannot open " + path + " for writing");

    std::vector<U8> wp, bp;
    if (rle) { wp = rleEncode(w.data(), w.size()); bp = rleEncode(b.data(), b.size()); }

    Header h{};
    std::memcpy(h.v12.magic, MAGIC, 8);
    h.v12.version = VERSION;
    h.v12.n = (U32)n;
    h.v12.flags = rle ? FLAG_RLE : 0;
    h.v12.histLen = (U32)st.histW.size();
    h.v12.nkk = idx.nkk;
    h.v12.nslots = idx.nslots;
    h.v12.wBytes = rle ? wp.size() : w.size();
    h.v12.bBytes = rle ? bp.size() : b.size();
    h.v12.maxPly = st.maxPly;
    h.v12.lwk = st.longest.wk;
    h.v12.lbk = st.longest.bk;
    h.v12.lwp0 = st.longest.wp[0];
    h.endgame = (U32)mat.eg;
    h.lwp1 = st.longest.wp[1];

    std::vector<U8> census;
    for (U64 x : { st.wLive, st.wWin, st.wDraw, st.bLive, st.bLoss, st.bDraw,
                   st.bMate, st.bStale, st.bEnPrise, st.fwLive, st.fwWin, st.fwDraw,
                   st.fbLive, st.fbLoss, st.fbDraw, st.fbMate, st.fbStale, st.fbEnPrise })
        putU64(census, x);
    for (U64 x : st.histW) putU64(census, x);
    for (U64 x : st.histWFull) putU64(census, x);

    try {
        put(f, &h, sizeof h);
        U64 cbytes = census.size();
        put(f, &cbytes, sizeof cbytes);
        put(f, census.data(), census.size());
        put(f, rle ? wp.data() : w.data(), (size_t)h.v12.wBytes);
        put(f, rle ? bp.data() : b.data(), (size_t)h.v12.bBytes);
    } catch (...) { std::fclose(f); throw; }
    std::fclose(f);
}

std::unique_ptr<Table> Table::load(const std::string& path) {
    std::FILE* f = std::fopen(path.c_str(), "rb");
    if (!f) throw std::runtime_error("cannot open " + path);
    Header h{};
    try {
        // Versions 1 and 2 have a shorter header, so read that much first and
        // only then decide whether there is a suffix to follow.
        get(f, &h.v12, sizeof h.v12);
        if (std::memcmp(h.v12.magic, MAGIC, 8) != 0)
            throw std::runtime_error("not a tablebase produced by this program");
        if (h.v12.version == 1 || h.v12.version == 2) {
            h.endgame = (U32)((h.v12.flags & FLAG_ROOK) ? Endgame::KRK : Endgame::KQK);
            h.lwp1 = -1;
        } else if (h.v12.version == VERSION) {
            get(f, &h.endgame, sizeof h - sizeof h.v12);
        } else {
            throw std::runtime_error("unsupported tablebase version");
        }
        if (h.endgame >= (U32)NUM_ENDGAMES)
            throw std::runtime_error("unknown endgame in header");

        auto t = std::make_unique<Table>((int)h.v12.n, (Endgame)h.endgame);
        if (t->idx.nkk != h.v12.nkk || t->idx.nslots != h.v12.nslots)
            throw std::runtime_error("index geometry does not match the file");

        U64 cbytes = 0;
        get(f, &cbytes, sizeof cbytes);
        std::vector<U8> census(cbytes);
        get(f, census.data(), cbytes);
        const U8* c = census.data();
        auto rdU64 = [&]() { U64 x = 0; for (int i = 0; i < 8; ++i) x |= U64(*c++) << (8 * i); return x; };
        Stats& s = t->st;
        s.slotsPerSide = h.v12.nslots;
        s.wLive = rdU64(); s.wWin = rdU64(); s.wDraw = rdU64();
        s.bLive = rdU64(); s.bLoss = rdU64(); s.bDraw = rdU64();
        s.bMate = rdU64(); s.bStale = rdU64(); s.bEnPrise = rdU64();
        s.fwLive = rdU64(); s.fwWin = rdU64(); s.fwDraw = rdU64();
        s.fbLive = rdU64(); s.fbLoss = rdU64(); s.fbDraw = rdU64();
        s.fbMate = rdU64(); s.fbStale = rdU64(); s.fbEnPrise = rdU64();
        s.histW.resize(h.v12.histLen); s.histWFull.resize(h.v12.histLen);
        for (U32 i = 0; i < h.v12.histLen; ++i) s.histW[i] = rdU64();
        for (U32 i = 0; i < h.v12.histLen; ++i) s.histWFull[i] = rdU64();
        s.maxPly = h.v12.maxPly;
        s.longest.wk = h.v12.lwk;
        s.longest.bk = h.v12.lbk;
        s.longest.wp[0] = h.v12.lwp0;
        s.longest.wp[1] = h.lwp1;

        const U64 ns = h.v12.nslots;
        std::vector<U8> raw;
        if (h.v12.flags & FLAG_RLE) {
            raw.resize(h.v12.wBytes); get(f, raw.data(), raw.size()); rleDecode(raw, t->w, ns);
            raw.resize(h.v12.bBytes); get(f, raw.data(), raw.size()); rleDecode(raw, t->b, ns);
        } else {
            t->w.resize(ns); get(f, t->w.data(), (size_t)ns);
            t->b.resize(ns); get(f, t->b.data(), (size_t)ns);
        }
        std::fclose(f);
        return t;
    } catch (...) { std::fclose(f); throw; }
}

} // namespace kqk
