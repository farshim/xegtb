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

// Version 3 onwards.  The capture rules change what the SAME material is
// worth -- a stalemate is a loss there, so KBBK and KBK have wins where the
// mating rules have draws -- and nothing else in the header distinguishes the
// two, so without this a capture table and a mating table of one endgame are
// the same file.  Adding a flag bit rather than a field keeps the rule the
// format was designed around: staying compatible is appending, and every file
// written before this one has the bit clear, which reads as the mating rules
// it was in fact built under.
constexpr U32  FLAG_CAPTURE = 1u << 2;

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
    h.v12.flags = (rle ? FLAG_RLE : 0u) | (stalemateLoss ? FLAG_CAPTURE : 0u);
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
        t->stalemateLoss = (h.v12.flags & FLAG_CAPTURE) != 0;
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

// ---------------------------------------------------------------------------
// The signed tables: KQKR / KQKB, and KQKBB.
//
// These had no on-disk form at all until the browser explorer wanted one.
// Both are two `int16_t` arrays over a dense index, so one header and one
// codec serve them; what differs is which index has to be rebuilt to read
// them back, which is why the header names the kind and the endgame and the
// reader checks the slot count it computes against the one on the file.
//
// The run length encoding is over VALUES rather than bytes.  A byte-wise pass
// over little-endian `int16_t` would break every run in two -- the low byte of
// a depth changes while the high byte does not -- and these tables are mostly
// long stretches of the same thing: dead slots, drawn regions, and the shells
// of equal depth that retrograde analysis lays down.  On KQKBB at n = 8 it
// takes 238 MB down to a few per cent of that.
//
// What is NOT stored is the census: `st` comes back zeroed, because the
// explorer scans the values itself and nothing else loads these.  A caller
// that wants the figures must generate rather than load.
// ---------------------------------------------------------------------------
namespace {

constexpr char SMAGIC[8] = { 'K', 'Q', 'K', 'S', 'T', 'B', 0, 0 };
constexpr U32  SVERSION  = 1;
constexpr U32  SFLAG_RLE     = 1u << 0;
constexpr U32  SFLAG_CAPTURE = 1u << 1;

enum : U32 { SKIND_KQKR = 0, SKIND_KQKBB = 1 };

struct SHeader {
    char magic[8];
    U32  version, kind, n, flags;
    U32  endgame;            // meaningful for SKIND_KQKR
    U32  pad;
    U64  nslots, wBytes, bBytes;
};

std::vector<U8> rle16Encode(const std::vector<int16_t>& v) {
    std::vector<U8> out;
    out.reserve(v.size() / 4 + 16);
    size_t i = 0;
    while (i < v.size()) {
        const int16_t x = v[i];
        size_t j = i + 1;
        while (j < v.size() && v[j] == x) ++j;
        U64 run = j - i;
        const uint16_t u = (uint16_t)x;
        out.push_back(U8(u & 0xFF));
        out.push_back(U8(u >> 8));
        while (run >= 0x80) { out.push_back(U8((run & 0x7F) | 0x80)); run >>= 7; }
        out.push_back(U8(run));
        i = j;
    }
    return out;
}

void rle16Decode(const std::vector<U8>& src, std::vector<int16_t>& dst, U64 expect) {
    dst.assign((size_t)expect, 0);
    U64 at = 0;
    size_t i = 0;
    while (i < src.size()) {
        if (i + 1 >= src.size()) throw std::runtime_error("corrupt run-length stream");
        const uint16_t u = (uint16_t)(src[i] | (src[i + 1] << 8));
        i += 2;
        U64 run = 0; int sh = 0;
        for (;;) {
            if (i >= src.size()) throw std::runtime_error("corrupt run-length stream");
            const U8 c = src[i++];
            run |= U64(c & 0x7F) << sh;
            if (!(c & 0x80)) break;
            sh += 7;
        }
        if (at + run > expect) throw std::runtime_error("run-length stream is too long");
        for (U64 k = 0; k < run; ++k) dst[(size_t)(at + k)] = (int16_t)u;
        at += run;
    }
    if (at != expect) throw std::runtime_error("run-length stream is too short");
}

// Both savers are the same five steps over different members.
void saveSigned(const std::string& path, const SHeader& proto,
                const std::vector<int16_t>& w, const std::vector<int16_t>& b, bool rle) {
    std::FILE* f = std::fopen(path.c_str(), "wb");
    if (!f) throw std::runtime_error("cannot open " + path + " for writing");
    try {
        std::vector<U8> we, be;
        bool wroteRle = rle;
        if (rle) {
            we = rle16Encode(w);
            be = rle16Encode(b);
            // As in kqkk.cpp: encode, compare, and keep whichever is smaller,
            // rather than assuming the encoding pays.
            if (we.size() + be.size() >= 2 * (w.size() + b.size())) wroteRle = false;
        }
        SHeader h = proto;
        std::memcpy(h.magic, SMAGIC, 8);
        h.version = SVERSION;
        h.flags = (h.flags & ~SFLAG_RLE) | (wroteRle ? SFLAG_RLE : 0u);
        h.nslots = w.size();
        h.wBytes = wroteRle ? we.size() : w.size() * 2;
        h.bBytes = wroteRle ? be.size() : b.size() * 2;
        put(f, &h, sizeof h);
        if (wroteRle) { put(f, we.data(), we.size()); put(f, be.data(), be.size()); }
        else          { put(f, w.data(), w.size() * 2); put(f, b.data(), b.size() * 2); }
    } catch (...) { std::fclose(f); throw; }
    std::fclose(f);
}

// Reads the header and the two arrays; the caller has already built the index
// and says how many slots it expects, which is the check that the file belongs
// to the table being filled.
void loadSigned(const std::string& path, U32 kind, U64 nslots, SHeader& h,
                std::vector<int16_t>& w, std::vector<int16_t>& b) {
    std::FILE* f = std::fopen(path.c_str(), "rb");
    if (!f) throw std::runtime_error("cannot open " + path);
    try {
        get(f, &h, sizeof h);
        if (std::memcmp(h.magic, SMAGIC, 8) != 0)
            throw std::runtime_error("not a signed tablebase produced by this program");
        if (h.version != SVERSION) throw std::runtime_error("unsupported tablebase version");
        if (h.kind != kind)        throw std::runtime_error("that file holds a different endgame");
        if (h.nslots != nslots)    throw std::runtime_error("index geometry does not match the file");
        if (h.flags & SFLAG_RLE) {
            std::vector<U8> raw((size_t)h.wBytes);
            get(f, raw.data(), raw.size()); rle16Decode(raw, w, nslots);
            raw.resize((size_t)h.bBytes);
            get(f, raw.data(), raw.size()); rle16Decode(raw, b, nslots);
        } else {
            if (h.wBytes != nslots * 2 || h.bBytes != nslots * 2)
                throw std::runtime_error("truncated tablebase");
            w.resize((size_t)nslots); get(f, w.data(), (size_t)nslots * 2);
            b.resize((size_t)nslots); get(f, b.data(), (size_t)nslots * 2);
        }
    } catch (...) { std::fclose(f); throw; }
    std::fclose(f);
}

} // namespace

void TableKQKR::save(const std::string& path, bool rle) const {
    SHeader h{};
    h.kind = SKIND_KQKR;
    h.n = (U32)n;
    h.endgame = (U32)mat.eg;
    h.flags = stalemateLoss ? SFLAG_CAPTURE : 0u;
    saveSigned(path, h, w, b, rle);
}

std::unique_ptr<TableKQKR> TableKQKR::load(const std::string& path) {
    // The endgame decides the index, so the header has to be read before the
    // table can be built -- unlike Table::load, where one peek does both.
    SHeader peek{};
    {
        std::FILE* f = std::fopen(path.c_str(), "rb");
        if (!f) throw std::runtime_error("cannot open " + path);
        try { get(f, &peek, sizeof peek); } catch (...) { std::fclose(f); throw; }
        std::fclose(f);
    }
    if (std::memcmp(peek.magic, SMAGIC, 8) != 0)
        throw std::runtime_error("not a signed tablebase produced by this program");
    // Any of the one-against-one endgames: the header records which, and the
    // format is the same for all of them.  It used to name the only two that
    // existed, which quietly refused every table added since.
    if (peek.endgame >= (U32)NUM_ENDGAMES || !blackArmed((Endgame)peek.endgame))
        throw std::runtime_error("unknown endgame in header");
    auto t = std::make_unique<TableKQKR>((int)peek.n, (Endgame)peek.endgame);
    t->stalemateLoss = (peek.flags & SFLAG_CAPTURE) != 0;
    SHeader h{};
    loadSigned(path, SKIND_KQKR, t->idx.nslots, h, t->w, t->b);
    return t;
}

void TableKQKBB::save(const std::string& path, bool rle) const {
    SHeader h{};
    h.kind = SKIND_KQKBB;
    h.n = (U32)n;
    saveSigned(path, h, w, b, rle);
}

std::unique_ptr<TableKQKBB> TableKQKBB::load(const std::string& path) {
    SHeader peek{};
    {
        std::FILE* f = std::fopen(path.c_str(), "rb");
        if (!f) throw std::runtime_error("cannot open " + path);
        try { get(f, &peek, sizeof peek); } catch (...) { std::fclose(f); throw; }
        std::fclose(f);
    }
    if (std::memcmp(peek.magic, SMAGIC, 8) != 0)
        throw std::runtime_error("not a signed tablebase produced by this program");
    auto t = std::make_unique<TableKQKBB>((int)peek.n);
    SHeader h{};
    loadSigned(path, SKIND_KQKBB, t->idx.nslots, h, t->w, t->b);
    return t;
}

} // namespace kqk
