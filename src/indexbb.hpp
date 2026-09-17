// indexbb.hpp -- symmetry-reduced, dense indexing for KQKBB: a white king and
// queen against a black king and *two* bishops.
//
// Why this endgame cannot share index.hpp
// ---------------------------------------
// index.hpp keys a block on the king pair and puts the non-king men in the
// configuration, which is exactly right here -- but its codec knows only four
// shapes: one man, an ordered pair, an unordered pair, an unordered triple.
// KQKBB is none of them.  Its three non-king men are a queen and two
// interchangeable bishops, so the configuration is a square *and* an unordered
// pair, and the codec is the product of the two:
//
//     pc = wq * npair + pairId(b1, b2),      npc = n^2 * n^2 (n^2 - 1) / 2
//
// Storing the bishops as an ordered pair instead would double the table and
// give every position a twin saying the same thing; storing all three men as
// an unordered triple would confuse the queen with a bishop and lose the
// position outright.
//
// What the layout buys.  The block key is the king pair, so *both* kinds of
// non-king move -- White's queen and Black's bishops -- stay inside one
// contiguous run of memory when they are retracted.  Only a king move leaves
// the block.  That is one better than every other endgame here, where the
// enemy's only man is its king.
//
// Sizes.  With t = |triangle| ~ n^2/8 white king squares this is about
// n^10 / 16 entries per side to move: 60 million at 8 x 8, 580 million at
// 10 x 10, 3.7 billion at 12 x 12.  Two signed arrays at two bytes an entry
// make the last of those 14 GiB, which is the wall this endgame runs into
// long before it runs out of patience.
#pragma once

#include "geometry.hpp"

namespace kqk {

// A KQKBB placement.  The two bishops are interchangeable; nothing outside the
// index cares which is which, and the index sorts them itself.
struct PosBB {
    Sq wk = -1, wq = -1, bk = -1, b1 = -1, b2 = -1;
};

class IndexKQKBB {
public:
    const Geometry& g;

    // ---- the block: a canonical king pair ---------------------------------
    // kkOf[triId(wk) * nsq + bk] is the king-pair index, or -1 when the pair
    // is illegal or not canonical.  Built exactly as index.hpp builds it; the
    // two must agree, because the KQKB table this endgame converts into is
    // indexed by the other one.
    std::vector<int32_t> kkOf;
    std::vector<Sq>      kkWk, kkBk;

    // Residual stabiliser of each king pair: the elements of D4 fixing both
    // kings.  For all but O(n^2) of the pairs this is the identity alone.
    std::vector<U8> kkStab;        // NSYM entries per pair
    std::vector<U8> kkStabLen;

    // ---- the configuration: a queen square and an unordered bishop pair ----
    std::vector<int32_t> pairBase;         // pairId(a, b) = pairBase[a] + b, a < b
    std::vector<Sq>      pairA, pairB;     // decode, per pair id
    U64 npair = 0;

    U64 nkk    = 0;    // canonical king pairs
    U32 npc    = 0;    // configurations per king pair, = nsq * npair
    U64 nslots = 0;    // nkk * npc -- entries per side-to-move array

    explicit IndexKQKBB(const Geometry& geo) : g(geo) { build(); }

    inline U64 slot(int32_t kk, U32 pc) const { return (U64)kk * npc + pc; }
    inline int32_t pairIdSorted(Sq a, Sq b) const { return pairBase[a] + b; }  // a < b
    inline int32_t pairId(Sq a, Sq b) const {
        return a < b ? pairBase[a] + b : pairBase[b] + a;
    }
    inline U32 cfgId(Sq wq, Sq b1, Sq b2) const {
        return (U32)((U64)wq * npair + (U64)pairId(b1, b2));
    }
    inline void decode(U32 pc, Sq& wq, Sq& b1, Sq& b2) const {
        wq = (Sq)(pc / npair);
        U32 pid = (U32)(pc % npair);
        b1 = pairA[pid]; b2 = pairB[pid];
    }
    // Decoding one configuration at a time costs a division; the sweeps that
    // walk a whole block instead walk the two factors, which costs none.
    inline void decodePair(U32 pid, Sq& b1, Sq& b2) const {
        b1 = pairA[pid]; b2 = pairB[pid];
    }

    inline int32_t kkOfPair(Sq wkTri, Sq bk) const {
        return kkOf[(size_t)g.triId[wkTri] * g.nsq + bk];
    }

    // Is every man on a distinct square?  The codec keeps the two bishops
    // apart by construction, but the queen shares the square space with all
    // three of the others, so 3-in-n^2 of the slots denote nothing.  Leaving
    // them live would let the solver read a phantom position in which the
    // queen both gives check and stands on a king.
    inline bool cfgLive(Sq wk, Sq bk, Sq wq, Sq b1, Sq b2) const {
        return wq != wk && wq != bk && wq != b1 && wq != b2 &&
               b1 != wk && b1 != bk && b2 != wk && b2 != bk;
    }

    // ---- canonicalisation --------------------------------------------------
    // Slot of an arbitrary placement.  Returns the king-pair index, or -1 when
    // the pair is illegal; the squares need not be distinct, which is the
    // caller's business through cfgLive.
    //
    // One lexicographic pass over the elements of D4 that carry the white king
    // into the fundamental triangle, minimising (black king, queen, sorted
    // bishops) in that order.  Taking the black king first is what makes the
    // block key independent of where the other three men stand.
    inline int32_t slotOf(Sq wk, Sq bk, Sq wq, Sq b1, Sq b2, U64& out) const {
        const U8* gs  = &g.canonSym[(size_t)wk * NSYM];
        const int len = g.canonSymLen[wk];
        Sq bBk = g.image(gs[0], bk), bQ = g.image(gs[0], wq);
        Sq bA = g.image(gs[0], b1), bB = g.image(gs[0], b2);
        if (bA > bB) { Sq t = bA; bA = bB; bB = t; }
        for (int i = 1; i < len; ++i) {
            Sq k = g.image(gs[i], bk);
            if (k > bBk) continue;
            Sq q = g.image(gs[i], wq);
            Sq a = g.image(gs[i], b1), b = g.image(gs[i], b2);
            if (a > b) { Sq t = a; a = b; b = t; }
            if (k < bBk || q < bQ || (q == bQ && (a < bA || (a == bA && b < bB)))) {
                bBk = k; bQ = q; bA = a; bB = b;
            }
        }
        // Every element that carries the white king into the triangle carries
        // it to the same square, the triangle meeting each orbit once.
        int32_t kk = kkOf[(size_t)g.triId[g.image(gs[0], wk)] * g.nsq + bBk];
        if (kk < 0) return -1;
        out = slot(kk, (U32)((U64)bQ * npair + (U64)pairIdSorted(bA, bB)));
        return kk;
    }
    inline int32_t slotOf(const PosBB& p, U64& out) const {
        return slotOf(p.wk, p.bk, p.wq, p.b1, p.b2, out);
    }
    inline bool slotOfPos(const PosBB& p, U64& out) const { return slotOf(p, out) >= 0; }

    // Fast path for the retrograde inner loop: both kings are unchanged and
    // already canonical, so only the residual stabiliser of the pair has to be
    // tried -- and for all but O(n^2) of the pairs that is the identity, which
    // makes this one sort and one multiply.  Queen and bishop retractions both
    // land here, which is nearly all of them.
    inline U64 slotInBlock(int32_t kk, Sq wq, Sq b1, Sq b2) const {
        const int len = kkStabLen[kk];
        Sq bQ = wq, bA = b1, bB = b2;
        if (bA > bB) { Sq t = bA; bA = bB; bB = t; }
        if (len > 1) {
            const U8* stab = &kkStab[(size_t)kk * NSYM];
            for (int i = 1; i < len; ++i) {
                Sq q = g.image(stab[i], wq);
                if (q > bQ) continue;
                Sq a = g.image(stab[i], b1), b = g.image(stab[i], b2);
                if (a > b) { Sq t = a; a = b; b = t; }
                if (q < bQ || a < bA || (a == bA && b < bB)) { bQ = q; bA = a; bB = b; }
            }
        }
        return slot(kk, (U32)((U64)bQ * npair + (U64)pairIdSorted(bA, bB)));
    }

    // Is this the canonical configuration for its king pair?  Slots that fail
    // name the same position as another slot and are marked dead, so that the
    // solver never expands one position twice.
    inline bool cfgIsCanonical(int32_t kk, Sq wq, Sq b1, Sq b2) const {
        const int len = kkStabLen[kk];
        if (len == 1) return true;
        const U8* stab = &kkStab[(size_t)kk * NSYM];
        Sq a0 = b1, b0 = b2;
        if (a0 > b0) { Sq t = a0; a0 = b0; b0 = t; }
        for (int i = 1; i < len; ++i) {
            Sq q = g.image(stab[i], wq);
            if (q > wq) continue;
            Sq a = g.image(stab[i], b1), b = g.image(stab[i], b2);
            if (a > b) { Sq t = a; a = b; b = t; }
            if (q < wq || a < a0 || (a == a0 && b < b0)) return false;
        }
        return true;
    }

    // Number of board placements in this position's symmetry class.  The two
    // bishops being interchangeable, a symmetry that swaps them fixes the
    // position.
    int orbitSize(const PosBB& p) const {
        int fixed = 0;
        for (int s = 0; s < NSYM; ++s) {
            if (g.image(s, p.wk) != p.wk) continue;
            if (g.image(s, p.bk) != p.bk) continue;
            if (g.image(s, p.wq) != p.wq) continue;
            Sq a = g.image(s, p.b1), b = g.image(s, p.b2);
            if ((a == p.b1 && b == p.b2) || (a == p.b2 && b == p.b1)) ++fixed;
        }
        return fixed ? NSYM / fixed : NSYM;
    }

private:
    void build() {
        const int nsq = g.nsq;

        kkOf.assign(g.triSq.size() * nsq, -1);
        for (size_t t = 0; t < g.triSq.size(); ++t) {
            const Sq wk = g.triSq[t];
            const auto& st = g.triStab[t];
            for (Sq bk = 0; bk < nsq; ++bk) {
                if (g.kingsTouch(wk, bk)) continue;
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

        npair = (U64)nsq * (nsq - 1) / 2;
        pairBase.resize(nsq);
        for (Sq a = 0; a < nsq; ++a)
            pairBase[a] = (int32_t)((U64)a * nsq - (U64)a * (a + 1) / 2) - a - 1;
        pairA.resize(npair);
        pairB.resize(npair);
        for (Sq a = 0; a < nsq; ++a)
            for (Sq b = a + 1; b < nsq; ++b) {
                int32_t id = pairBase[a] + b;
                pairA[id] = a;
                pairB[id] = b;
            }

        npc    = (U32)((U64)nsq * npair);
        nslots = nkk * (U64)npc;

        kkStab.assign(nkk * NSYM, 0xFF);
        kkStabLen.assign(nkk, 1);
        for (U64 kk = 0; kk < nkk; ++kk) {
            const Sq wk = kkWk[kk], bk = kkBk[kk];
            int len = 0;
            for (int s = 0; s < NSYM; ++s)
                if (g.image(s, wk) == wk && g.image(s, bk) == bk)
                    kkStab[kk * NSYM + len++] = (U8)s;
            kkStabLen[kk] = (U8)len;   // element 0 is the identity
        }
    }
};

} // namespace kqk
