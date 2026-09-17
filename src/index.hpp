// index.hpp -- symmetry-reduced, dense indexing of positions in which Black
// has a bare king and White has a king plus one or two long-range pieces.
//
// A position is (white king, black king, White's piece configuration, side to
// move).  The two side-to-move halves are stored as two separate flat arrays,
// each of nkk * npc bytes, so that all configurations of White's pieces for
// one king pair form one contiguous block.  That is what makes the retrograde
// pass cache friendly: undoing a move of a white piece never leaves the
// current block.
//
// A *piece configuration* is
//   one piece    : the square it stands on, so npc = n^2;
//   two alike    : the unordered pair of squares they stand on (KBBK), so
//                  npc = n^2 (n^2 - 1) / 2;
//   two unalike  : the ordered pair (KBNK), so npc = n^4, of which the n^2
//                  diagonal entries are dead;
//   three alike   : the unordered triple (KNNNK), so npc = C(n^2, 3).
// Two bishops are indistinguishable, so storing their ordered pair would
// double the table and give every position a twin saying the same thing.  A
// bishop and a knight are not, so there the order carries information and the
// encoding is the plain mixed-radix one -- which needs no tables at all, and
// wastes only the 1-in-n^2 diagonal.  Three like knights are the same argument
// once more: storing their ordered triple would multiply the table by six.
//
// The canonical representative of a position is obtained by applying the
// element of D4 that puts the white king into the fundamental triangle and,
// among the remaining choices, minimises the pair (black king, configuration).
// The index itself does not depend on *which* pieces White has, only on how
// many and whether they are alike.
#pragma once

#include "geometry.hpp"

namespace kqk {

struct Pos {
    Sq wk = -1, bk = -1;
    Sq wp[MAXWP] = { -1, -1, -1 }; // White's non-king pieces; wp[i] unused when i >= np
};

class Index {
public:
    const Geometry& g;
    Material mat;

    // kkOf[triId(wk) * nsq + bk] is the king-pair index, or -1 when the pair
    // is illegal or not canonical.
    std::vector<int32_t> kkOf;
    std::vector<Sq>      kkWk, kkBk;   // decode, per king-pair index

    // Residual stabiliser of each king pair: the elements of D4 fixing both
    // kings.  Stored flat, 8 slots per pair.  For all but O(n^2) of the pairs
    // this is just the identity.
    std::vector<U8>      kkStab;       // NSYM entries per pair
    std::vector<U8>      kkStabLen;

    // Unordered-pair codec, built only for two like pieces.
    // pairId(a, b) = pairBase[a] + b for a < b.
    std::vector<int32_t> pairBase;
    std::vector<Sq>      pairA, pairB;   // decode, per configuration

    // Unordered-triple codec, built only for three like pieces.
    // tripId(a, b, c) = tripBase[a * nsq + b] + c for a < b < c.
    std::vector<int32_t> tripBase;
    std::vector<Sq>      tripA, tripB, tripC;

    U64 nkk    = 0;   // number of king-pair indices
    U32 npc    = 0;   // piece configurations per king pair
    U64 nslots = 0;   // nkk * npc -- entries per side-to-move array

    // `allowTouch` keeps king pairs that stand next to each other.  They are
    // illegal under the ordinary rules and excluded by default; the KQKK
    // capture variant needs them, because there a king beside a king is not
    // illegal, only capturable.  See kqkkcap.cpp.
    bool allowTouch = false;

    Index(const Geometry& geo, Material m, bool touchOk = false)
        : g(geo), mat(m), allowTouch(touchOk) { build(); }

    inline U64 slot(int32_t kk, U32 pc) const { return (U64)kk * npc + pc; }
    inline int32_t kkOfPair(Sq wkTri, Sq bk) const {
        return kkOf[(size_t)g.triId[wkTri] * g.nsq + bk];
    }

    // ---- piece-configuration codec ----------------------------------------
    // Like pieces are held in ascending order everywhere, so that one placement
    // has one encoding.  Sorting is a network rather than a loop: three
    // compare-exchanges settle three squares, and the two-piece case folds to
    // one.  Every site that normalises a configuration calls this, so they
    // cannot drift apart.
    template <Endgame EG>
    static inline void sortCfg(Sq* c) {
        if constexpr (identicalOf(EG)) {
            auto cx = [](Sq& x, Sq& y) { if (x > y) { Sq t = x; x = y; y = t; } };
            cx(c[0], c[1]);
            if constexpr (npOf(EG) == 3) { cx(c[1], c[2]); cx(c[0], c[1]); }
        }
    }

    template <Endgame EG>
    inline void decode(U32 pc, Sq out[MAXWP]) const {
        if constexpr (npOf(EG) == 1)        out[0] = (Sq)pc;
        else if constexpr (npOf(EG) == 3)   { out[0] = tripA[pc]; out[1] = tripB[pc]; out[2] = tripC[pc]; }
        else if constexpr (identicalOf(EG)) { out[0] = pairA[pc]; out[1] = pairB[pc]; }
        else { out[0] = (Sq)(pc / g.nsq); out[1] = (Sq)(pc % g.nsq); }
    }
    // Dispatched through KQK_DISPATCH rather than a switch of its own: a
    // hand-written switch with a `default` silently sends a new endgame to
    // whichever case happens to sit there, and one that did exactly that --
    // routing two like knights through the unlike-pair code -- is what made
    // every KNNK orbit come out too large.  The macro has no default.
    inline void decode(U32 pc, Sq out[MAXWP]) const {
#define CALL(EG) decode<EG>(pc, out)
        KQK_DISPATCH(mat.eg, CALL)
#undef CALL
    }

    // Encode a configuration, normalising the order for like pieces.  Returns
    // -1 when the squares coincide, which is not a configuration.
    template <Endgame EG>
    inline int32_t encode(const Sq* s) const {
        if constexpr (npOf(EG) == 1) return s[0];
        else if constexpr (npOf(EG) == 3) {
            Sq c[3] = { s[0], s[1], s[2] };
            sortCfg<EG>(c);
            if (c[0] == c[1] || c[1] == c[2]) return -1;
            return tripBase[(size_t)c[0] * g.nsq + c[1]] + c[2];
        } else if constexpr (identicalOf(EG)) {
            Sq a = s[0], b = s[1];
            if (a == b) return -1;
            if (a > b) { Sq t = a; a = b; b = t; }
            return pairBase[a] + b;
        } else {
            if (s[0] == s[1]) return -1;
            return s[0] * g.nsq + s[1];
        }
    }
    inline int32_t encode(const Sq* s) const {
#define CALL(EG) encode<EG>(s)
        KQK_DISPATCH(mat.eg, CALL)
#undef CALL
    }

    // Configurations are compared square by square; for like pieces both sides
    // are already sorted, so this is a plain lexicographic test.
    template <Endgame EG>
    static inline int cmpCfg(const Sq* a, const Sq* b) {
        for (int i = 0; i < npOf(EG); ++i)
            if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
        return 0;
    }

    // Apply a symmetry to a configuration and re-normalise it.  Only like
    // pieces get sorted: for a bishop and a knight the slots are not
    // interchangeable, and swapping them would name a different position.
    template <Endgame EG>
    inline void mapCfg(int sym, const Sq* in, Sq* out) const {
        for (int i = 0; i < npOf(EG); ++i) out[i] = g.image(sym, in[i]);
        sortCfg<EG>(out);
    }

    // ---- canonicalisation --------------------------------------------------
    // Canonical representative of an arbitrary (possibly non-canonical)
    // placement.  The squares need not be distinct; that is checked by the
    // caller.  The scalar form is the primitive: the retrograde inner loop
    // already holds the squares in registers, and making it build a Pos just
    // to take its address costs measurably.
    template <Endgame EG>
    inline void canonical(Sq wk, Sq bk, const Sq* wp,
                          Sq& oWk, Sq& oBk, Sq* oCfg) const {
        const U8* gs = &g.canonSym[(size_t)wk * NSYM];
        const int len = g.canonSymLen[wk];
        oWk = g.image(gs[0], wk);
        oBk = g.image(gs[0], bk);
        mapCfg<EG>(gs[0], wp, oCfg);
        for (int i = 1; i < len; ++i) {
            Sq b = g.image(gs[i], bk), cfg[MAXWP];
            mapCfg<EG>(gs[i], wp, cfg);
            if (b < oBk || (b == oBk && cmpCfg<EG>(cfg, oCfg) < 0)) {
                oBk = b;
                for (int k = 0; k < npOf(EG); ++k) oCfg[k] = cfg[k];
            }
        }
    }
    template <Endgame EG>
    inline Pos canonical(const Pos& p) const {
        Pos best;
        canonical<EG>(p.wk, p.bk, p.wp, best.wk, best.bk, best.wp);
        return best;
    }
    inline Pos canonical(const Pos& p) const {
#define CALL(EG) canonical<EG>(p)
        KQK_DISPATCH(mat.eg, CALL)
#undef CALL
    }

    // Slot for an arbitrary placement.  Returns the king-pair index, or -1
    // when the pair is illegal (kings touching or coincident).  Callers that
    // need the enclosing block get it back without an integer division.
    template <Endgame EG>
    inline int32_t slotOfKk(Sq wk, Sq bk, const Sq* wp, U64& out) const {
        Sq cWk, cBk, cCfg[MAXWP];
        canonical<EG>(wk, bk, wp, cWk, cBk, cCfg);
        int32_t kk = kkOfPair(cWk, cBk);
        if (kk < 0) return -1;
        int32_t pc = encode<EG>(cCfg);
        if (pc < 0) return -1;
        out = slot(kk, (U32)pc);
        return kk;
    }
    template <Endgame EG>
    inline int32_t slotOfKk(const Pos& p, U64& out) const {
        return slotOfKk<EG>(p.wk, p.bk, p.wp, out);
    }
    inline int32_t slotOfKk(const Pos& p, U64& out) const {
#define CALL(EG) slotOfKk<EG>(p, out)
        KQK_DISPATCH(mat.eg, CALL)
#undef CALL
    }
    inline bool slotOf(const Pos& p, U64& out) const { return slotOfKk(p, out) >= 0; }

    // Canonical king-pair index of an arbitrary pair, or -1.  The capture
    // variant needs the king pair on its own, without a piece to go with it.
    inline int32_t kkIndexOf(Sq wk, Sq bk) const {
        const U8* gs = &g.canonSym[(size_t)wk * NSYM];
        const int len = g.canonSymLen[wk];
        Sq best = g.image(gs[0], bk);
        for (int i = 1; i < len; ++i) {
            Sq t = g.image(gs[i], bk);
            if (t < best) best = t;
        }
        return kkOfPair(g.image(gs[0], wk), best);
    }

    // Row of the king-pair table for one white king square, so that a lookup
    // keyed only on the black king costs a single indexed load.
    inline const int32_t* kkRowFor(Sq wkTri) const {
        return &kkOf[(size_t)g.triId[wkTri] * g.nsq];
    }

    // Fast path used while expanding a block: the white king is already in the
    // triangle and unchanged, so only the stabiliser of wk has to be tried.
    // `stab`/`len` describe Stab(wk), obtained from triStab.
    template <Endgame EG>
    inline int32_t slotSameWk(const int32_t* kkRow, const U8* stab, int len,
                              Sq bk, const Sq* wp, U64& out) const {
        Sq bb = bk, bc[MAXWP];
        for (int k = 0; k < npOf(EG); ++k) bc[k] = wp[k];
        sortCfg<EG>(bc);
        for (int i = 1; i < len; ++i) {           // element 0 is the identity
            Sq b = g.image(stab[i], bk), cfg[MAXWP];
            mapCfg<EG>(stab[i], wp, cfg);
            if (b < bb || (b == bb && cmpCfg<EG>(cfg, bc) < 0)) {
                bb = b;
                for (int k = 0; k < npOf(EG); ++k) bc[k] = cfg[k];
            }
        }
        int32_t kk = kkRow[bb];
        if (kk < 0) return -1;
        int32_t pc = encode<EG>(bc);
        if (pc < 0) return -1;
        out = slot(kk, (U32)pc);
        return kk;
    }

    // Fastest path: both kings unchanged and already canonical, only White's
    // pieces move.  Stays inside the current block.
    //
    // With a single piece the configuration *is* a square, so it gets a scalar
    // form: the retrograde inner loop then never has to put it in memory.
    inline Sq canonSquare(const U8* stab, int len, Sq s) const {
        Sq best = s;
        for (int i = 1; i < len; ++i) {
            Sq q = g.image(stab[i], s);
            if (q < best) best = q;
        }
        return best;
    }

    template <Endgame EG>
    inline U32 canonCfg(const U8* stab, int len, const Sq* wp) const {
        if constexpr (npOf(EG) == 1) return (U32)canonSquare(stab, len, wp[0]);
        else {
            Sq best[MAXWP];
            mapCfg<EG>(0, wp, best);              // element 0 is the identity
            for (int i = 1; i < len; ++i) {
                Sq cfg[MAXWP];
                mapCfg<EG>(stab[i], wp, cfg);
                if (cmpCfg<EG>(cfg, best) < 0)
                    for (int k = 0; k < npOf(EG); ++k) best[k] = cfg[k];
            }
            return (U32)encode<EG>(best);
        }
    }

    // Is the configuration invariant under this symmetry?  Used for orbit
    // sizes, where like pieces make the configuration a set rather than a
    // tuple, so the images have to be re-sorted before comparing.
    template <Endgame EG>
    inline bool cfgFixedByT(int sym, const Sq* wp) const {
        Sq cfg[MAXWP], cur[MAXWP];
        for (int i = 0; i < npOf(EG); ++i) cur[i] = wp[i];
        sortCfg<EG>(cur);                    // the same normalisation mapCfg applies
        mapCfg<EG>(sym, wp, cfg);
        for (int i = 0; i < npOf(EG); ++i) if (cfg[i] != cur[i]) return false;
        return true;
    }
    inline bool cfgFixedBy(int sym, const Sq* wp) const {
#define CALL(EG) cfgFixedByT<EG>(sym, wp)
        KQK_DISPATCH(mat.eg, CALL)
#undef CALL
    }

    // Is this a real configuration for this king pair -- every man on a
    // distinct square?  The ordered-pair encoding has n^2 slots whose two
    // squares coincide, and those denote nothing; leaving them live lets the
    // solver read a phantom position in which one piece both gives check and
    // covers its own flight squares, and retract winning moves out of it.
    // Every caller that decides whether a slot is alive must use this.
    template <Endgame EG>
    inline bool cfgLive(const Sq* cfg, Sq wk, Sq bk) const {
        for (int i = 0; i < npOf(EG); ++i)
            if (cfg[i] == wk || cfg[i] == bk) return false;
        if constexpr (npOf(EG) == 2)
            if (cfg[0] == cfg[1]) return false;
        return true;
    }
    inline bool cfgLive(const Sq* cfg, Sq wk, Sq bk) const {
#define CALL(EG) cfgLive<EG>(cfg, wk, bk)
        KQK_DISPATCH(mat.eg, CALL)
#undef CALL
    }

    // Is this the canonical configuration for the given king pair?  Slots that
    // fail this are duplicates of another slot and are marked dead so that the
    // solver never expands the same position twice.
    template <Endgame EG>
    inline bool cfgIsCanonical(int32_t kk, const Sq* wp) const {
        int len = kkStabLen[kk];
        if (len == 1) return true;
        const U8* stab = &kkStab[(size_t)kk * NSYM];
        for (int i = 1; i < len; ++i) {
            Sq cfg[MAXWP];
            mapCfg<EG>(stab[i], wp, cfg);
            if (cmpCfg<EG>(cfg, wp) < 0) return false;
        }
        return true;
    }
    inline bool cfgIsCanonical(int32_t kk, const Sq* wp) const {
#define CALL(EG) cfgIsCanonical<EG>(kk, wp)
        KQK_DISPATCH(mat.eg, CALL)
#undef CALL
    }

private:
    void build() {
        const int nsq = g.nsq;
        kkOf.assign(g.triSq.size() * nsq, -1);
        for (size_t t = 0; t < g.triSq.size(); ++t) {
            Sq wk = g.triSq[t];
            const auto& st = g.triStab[t];
            for (Sq bk = 0; bk < nsq; ++bk) {
                if (allowTouch ? (bk == wk) : g.kingsTouch(wk, bk)) continue;
                // Keep only the smallest black king square in its orbit under
                // the stabiliser of the white king.
                bool canon = true;
                for (size_t i = 1; i < st.size(); ++i)
                    if (g.image(st[i], bk) < bk) { canon = false; break; }
                if (!canon) continue;
                kkOf[t * nsq + bk] = (int32_t)kkWk.size();
                kkWk.push_back(wk);
                kkBk.push_back(bk);
            }
        }
        nkk = kkWk.size();

        if (mat.np == 1) {
            npc = (U32)nsq;
        } else if (!mat.identical) {
            // Ordered pair, mixed radix.  The n^2 entries with both pieces on
            // one square are dead, which is a 1-in-n^2 waste and buys a codec
            // with no tables and no division on the hot path.
            npc = (U32)((U64)nsq * nsq);
        } else if (mat.np == 3) {
            // Unordered triples, counted out once so that the base table and
            // the decode tables cannot disagree about the numbering.
            tripBase.assign((size_t)nsq * nsq, -1);
            U64 id = 0;
            for (Sq a = 0; a < nsq; ++a)
                for (Sq b = a + 1; b < nsq; ++b) {
                    tripBase[(size_t)a * nsq + b] = (int32_t)(id - (U64)(b + 1));
                    id += (U64)(nsq - 1 - b);
                }
            npc = (U32)id;                       // = C(nsq, 3)
            tripA.resize(npc); tripB.resize(npc); tripC.resize(npc);
            for (Sq a = 0; a < nsq; ++a)
                for (Sq b = a + 1; b < nsq; ++b)
                    for (Sq c = b + 1; c < nsq; ++c) {
                        int32_t t = tripBase[(size_t)a * nsq + b] + c;
                        tripA[t] = a; tripB[t] = b; tripC[t] = c;
                    }
        } else {
            npc = (U32)((U64)nsq * (nsq - 1) / 2);
            pairBase.resize(nsq);
            pairA.resize(npc);
            pairB.resize(npc);
            for (Sq a = 0; a < nsq; ++a)
                pairBase[a] = (int32_t)((U64)a * nsq - (U64)a * (a + 1) / 2) - a - 1;
            for (Sq a = 0; a < nsq; ++a)
                for (Sq b = a + 1; b < nsq; ++b) {
                    int32_t id = pairBase[a] + b;
                    pairA[id] = a;
                    pairB[id] = b;
                }
        }
        nslots = nkk * (U64)npc;

        kkStab.assign(nkk * NSYM, 0xFF);
        kkStabLen.assign(nkk, 1);
        for (U64 kk = 0; kk < nkk; ++kk) {
            Sq wk = kkWk[kk], bk = kkBk[kk];
            int len = 0;
            for (int s = 0; s < NSYM; ++s)
                if (g.image(s, wk) == wk && g.image(s, bk) == bk)
                    kkStab[kk * NSYM + len++] = (U8)s;
            kkStabLen[kk] = (U8)len;   // element 0 is the identity
        }
    }
};

} // namespace kqk
