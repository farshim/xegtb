// indexkk.hpp -- symmetry-reduced, dense indexing for KQKK: a white king and
// queen against *two* black kings.
//
// Why this endgame cannot share index.hpp
// ---------------------------------------
// Every other endgame here keys a block on the king *pair* (white king, black
// king) and puts White's men in the configuration, which is what makes the
// retrograde pass cache friendly: undoing a move of a white piece never
// changes the king pair, so phase A walks one contiguous run of memory.
//
// KQKK cannot use that layout, because Black's second man is a king.  It is
// interchangeable with the first, and it moves on Black's turn rather than
// White's.  Forcing it into the configuration slot would give every position
// two indices saying the same thing -- the ordered pair of a thing with
// itself -- and would put a man that moves on Black's turn inside the block
// that phase A is trying to keep still.
//
// So the block key is the king *triple*
//
//     (white king in the fundamental triangle, unordered pair of black kings)
//
// and the configuration is the queen square alone, npc = n^2.  Both desirable
// properties come back: the two black kings are unordered at the level of the
// index, so the table holds one entry per genuine position and not two, and
// undoing a queen move still never leaves the block.  What moves out of the
// block instead is a black king move, which is phase B's business, exactly as
// a black king move leaves the block in solver.cpp.
//
// The legality rule the triple enumerates is the one that defines this
// variant: **neither black king may stand on or beside the white king** -- the
// ordinary rule that kings do not touch, applied to each black king in turn --
// **while the two black kings may stand beside each other**, since they are
// not each other's enemies.
//
// Sizes.  With t = |triangle| ~ n^2/8 white king squares and n^2 (n^2 - 1) / 2
// unordered black king pairs, a table is about n^8 / 16 entries per side to
// move, half of it in each of the two arrays.  That is the same order as the
// two-white-piece endgames and it grows the same way: 8 x 8 is 848 640 entries
// per side, 16 x 16 is 292 million.
#pragma once

#include "geometry.hpp"

namespace kqk {

// A KQKK placement.  The two black kings are interchangeable; nothing outside
// the index cares which is which, and the index sorts them itself.
struct PosKK {
    Sq wk = -1, wq = -1, bk1 = -1, bk2 = -1;
};

class IndexKQKK {
public:
    const Geometry& g;

    // Unordered-pair codec over squares: pairId(a, b) = pairBase[a] + b, a < b.
    std::vector<int32_t> pairBase;
    U64 npair = 0;

    // blockOf[triId(wk) * npair + pairId(b1, b2)] is the block index, or -1
    // when the triple is illegal -- a black king on or beside the white king --
    // or when it is not the canonical representative of its orbit.
    std::vector<int32_t> blockOf;
    std::vector<Sq>      blkWk, blkB1, blkB2;   // decode, per block; blkB1 < blkB2

    // Residual stabiliser of each triple: the elements of D4 that fix the white
    // king and map the black pair to itself, as a set.  Element 0, the
    // identity, is always present and always first.  For all but O(n^2) of the
    // blocks this is the identity alone.
    std::vector<U8> blkStab;                     // NSYM entries per block
    std::vector<U8> blkStabLen;

    U64 nblk   = 0;     // number of canonical king triples
    U32 npc    = 0;     // queen squares per block, = n^2
    U64 nslots = 0;     // nblk * npc -- entries per side-to-move array

    // `allowTouch` keeps triples in which a black king stands beside the white
    // king.  Under the mating rules those are illegal; under the capture rules
    // of kqkkcap.cpp they are legal and merely losing, so the table needs them.
    bool allowTouch = false;

    explicit IndexKQKK(const Geometry& geo, bool touchOk = false)
        : g(geo), allowTouch(touchOk) { build(); }

    inline U64 slot(int32_t blk, U32 q) const { return (U64)blk * npc + q; }
    inline int32_t pairIdSorted(Sq a, Sq b) const { return pairBase[a] + b; }   // a < b
    inline int32_t pairId(Sq a, Sq b) const {
        return a < b ? pairBase[a] + b : pairBase[b] + a;
    }
    // Row of the block table for one white king square, so a lookup keyed only
    // on the black pair costs a single indexed load.  Valid only for a white
    // king already inside the fundamental triangle.
    inline const int32_t* blockRowFor(Sq wkTri) const {
        return &blockOf[(size_t)g.triId[wkTri] * npair];
    }

    // Smallest image of a square under a stabiliser.
    inline Sq canonSquare(const U8* stab, int len, Sq s) const {
        Sq best = s;
        for (int i = 1; i < len; ++i) {
            Sq q = g.image(stab[i], s);
            if (q < best) best = q;
        }
        return best;
    }

    // ---- canonicalisation --------------------------------------------------
    // Slot of an arbitrary placement.  Returns the block index, or -1 when the
    // placement is not a legal canonical triple; the queen is not checked
    // against the kings here, the caller does that.
    //
    // Two stages.  First carry the white king into the triangle and, among the
    // elements that do so, take the one minimising the sorted pair of black
    // kings; then reduce the queen under whatever symmetry of that triple is
    // left.  Splitting it this way is what makes the block key independent of
    // where the queen stands, which phase A depends on.
    inline int32_t slotOf(Sq wk, Sq b1, Sq b2, Sq wq, U64& out) const {
        if (b1 == b2) return -1;
        const U8* gs  = &g.canonSym[(size_t)wk * NSYM];
        const int len = g.canonSymLen[wk];
        Sq ba = -1, bb = -1;
        int bg = 0;
        for (int i = 0; i < len; ++i) {
            Sq a = g.image(gs[i], b1), b = g.image(gs[i], b2);
            if (a > b) { Sq t = a; a = b; b = t; }
            if (i == 0 || a < ba || (a == ba && b < bb)) { ba = a; bb = b; bg = gs[i]; }
        }
        // Every element that carries the white king into the triangle carries
        // it to the same square, the triangle meeting each orbit once.
        int32_t blk = blockOf[(size_t)g.triId[g.image(bg, wk)] * npair + pairBase[ba] + bb];
        if (blk < 0) return -1;
        Sq q = g.image(bg, wq);
        const int slen = blkStabLen[blk];
        if (slen > 1) q = canonSquare(&blkStab[(size_t)blk * NSYM], slen, q);
        out = slot(blk, (U32)q);
        return blk;
    }
    inline int32_t slotOf(const PosKK& p, U64& out) const {
        return slotOf(p.wk, p.bk1, p.bk2, p.wq, out);
    }

    // The block alone, for the king triple without a queen -- which is what
    // K vs K + K is.  Same canonicalisation as slotOf, minus the queen.
    inline int32_t blockOfTriple(Sq wk, Sq b1, Sq b2) const {
        if (b1 == b2) return -1;
        const U8* gs  = &g.canonSym[(size_t)wk * NSYM];
        const int len = g.canonSymLen[wk];
        Sq ba = -1, bb = -1;
        for (int i = 0; i < len; ++i) {
            Sq a = g.image(gs[i], b1), b = g.image(gs[i], b2);
            if (a > b) { Sq t = a; a = b; b = t; }
            if (i == 0 || a < ba || (a == ba && b < bb)) { ba = a; bb = b; }
        }
        return blockOf[(size_t)g.triId[g.image(gs[0], wk)] * npair + pairBase[ba] + bb];
    }

    // Fast path for phase B: the white king has not moved and is already in the
    // triangle, so only its stabiliser -- `stab`, `len`, from triStab -- has to
    // be tried.  When that is the identity alone, which is the overwhelmingly
    // common case, this is one sort and one indexed load.
    inline int32_t slotSameWk(const int32_t* row, const U8* stab, int len,
                              Sq b1, Sq b2, Sq wq, U64& out) const {
        Sq ba = b1, bb = b2;
        if (ba > bb) { Sq t = ba; ba = bb; bb = t; }
        int bg = 0;
        for (int i = 1; i < len; ++i) {
            Sq a = g.image(stab[i], b1), b = g.image(stab[i], b2);
            if (a > b) { Sq t = a; a = b; b = t; }
            if (a < ba || (a == ba && b < bb)) { ba = a; bb = b; bg = stab[i]; }
        }
        int32_t blk = row[pairBase[ba] + bb];
        if (blk < 0) return -1;
        Sq q = bg ? g.image(bg, wq) : wq;
        const int slen = blkStabLen[blk];
        if (slen > 1) q = canonSquare(&blkStab[(size_t)blk * NSYM], slen, q);
        out = slot(blk, (U32)q);
        return blk;
    }

    // Is this slot's queen square the canonical one for its block?  Slots that
    // fail this name the same position as another slot and are marked dead, so
    // that the solver never expands one position twice.
    inline bool queenIsCanonical(U64 blk, Sq q) const {
        const int len = blkStabLen[blk];
        if (len == 1) return true;
        const U8* stab = &blkStab[(size_t)blk * NSYM];
        for (int i = 1; i < len; ++i)
            if (g.image(stab[i], q) < q) return false;
        return true;
    }

    // Number of board placements in this position's symmetry class.  The two
    // black kings being interchangeable, a symmetry that swaps them fixes the
    // position.
    int orbitSize(const PosKK& p) const {
        int fixed = 0;
        for (int s = 0; s < NSYM; ++s) {
            if (g.image(s, p.wk) != p.wk) continue;
            if (g.image(s, p.wq) != p.wq) continue;
            Sq a = g.image(s, p.bk1), b = g.image(s, p.bk2);
            if ((a == p.bk1 && b == p.bk2) || (a == p.bk2 && b == p.bk1)) ++fixed;
        }
        return fixed ? NSYM / fixed : NSYM;
    }

private:
    void build() {
        const int nsq = g.nsq;
        npair = (U64)nsq * (nsq - 1) / 2;
        pairBase.resize(nsq);
        for (Sq a = 0; a < nsq; ++a)
            pairBase[a] = (int32_t)((U64)a * nsq - (U64)a * (a + 1) / 2) - a - 1;

        blockOf.assign(g.triSq.size() * npair, -1);
        for (size_t t = 0; t < g.triSq.size(); ++t) {
            const Sq wk = g.triSq[t];
            const auto& st = g.triStab[t];
            int32_t* row = &blockOf[t * npair];
            for (Sq a = 0; a < nsq; ++a) {
                if (allowTouch ? (a == wk) : g.kingsTouch(wk, a)) continue;
                for (Sq b = a + 1; b < nsq; ++b) {
                    if (allowTouch ? (b == wk) : g.kingsTouch(wk, b)) continue;
                    // Keep only the smallest sorted pair in the orbit under the
                    // stabiliser of the white king.
                    bool canon = true;
                    for (size_t i = 1; i < st.size(); ++i) {
                        Sq ia = g.image(st[i], a), ib = g.image(st[i], b);
                        if (ia > ib) { Sq x = ia; ia = ib; ib = x; }
                        if (ia < a || (ia == a && ib < b)) { canon = false; break; }
                    }
                    if (!canon) continue;
                    row[pairBase[a] + b] = (int32_t)blkWk.size();
                    blkWk.push_back(wk);
                    blkB1.push_back(a);
                    blkB2.push_back(b);
                }
            }
        }
        nblk   = blkWk.size();
        npc    = (U32)nsq;
        nslots = nblk * (U64)npc;

        blkStab.assign(nblk * NSYM, 0xFF);
        blkStabLen.assign(nblk, 1);
        for (U64 k = 0; k < nblk; ++k) {
            const Sq wk = blkWk[k], a = blkB1[k], b = blkB2[k];
            int len = 0;
            for (int s = 0; s < NSYM; ++s) {
                if (g.image(s, wk) != wk) continue;
                Sq ia = g.image(s, a), ib = g.image(s, b);
                if ((ia == a && ib == b) || (ia == b && ib == a))
                    blkStab[k * NSYM + len++] = (U8)s;
            }
            blkStabLen[k] = (U8)len;   // element 0 is the identity
        }
    }
};

} // namespace kqk
