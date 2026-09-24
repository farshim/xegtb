// genindex.hpp -- the D4-reduced index for the general solver.
//
// The plain ordered product in general.hpp costs a factor of eight in memory
// and on disk against every other table in this program, all of which key a
// block on a canonical pair of squares and let the rest of the men run free
// inside it.  This does the same thing, with one difference: index.hpp keys on
// the KING pair, and half the materials here have no such pair -- a side may
// have no king, or three -- so the key is simply the first two men of the
// material, whatever they are.  Nothing about the reduction cares what they
// are; D4 acts on squares.
//
//   slot = pairId(sq0, sq1) * nsq^(k-2) + the rest, as a plain radix
//
// The saving is the orbit size: a pair off every axis of symmetry has eight
// images and only one of them is kept.
//
// WHAT THE REDUCTION COSTS, and it is not only memory.  A pair that lies ON a
// symmetry axis has a nontrivial residual stabiliser -- elements of D4 that
// fix both squares -- and those elements permute the remaining men among
// themselves.  Two different placements of the rest can then be the same
// position, so one of them has to be declared canonical and the other dead.
// `restCanonical` is the one predicate that decides it, and every caller must
// go through it: index.hpp records that a past bug came from two places
// disagreeing about exactly this.
#pragma once

#include "geometry.hpp"

#include <vector>

namespace kqk {

class GenIndexD4 {
public:
    const Geometry* g = nullptr;
    int nsq = 0, k = 0;
    U64 nrest = 0;          // nsq^(k-2): placements of the men after the first two
    U64 npair = 0;          // canonical pairs
    U64 nslots = 0;

    // pairOf[triId(a) * nsq + b] is the pair's index, or -1 when it is not
    // canonical (or the two squares coincide).
    std::vector<int32_t> pairOf;
    std::vector<Sq>      pairA, pairB;
    // Residual stabiliser per canonical pair: the elements of D4 fixing both
    // squares.  Element 0 (the identity) is always first, so a length of one
    // is the common case and the test below folds to nothing.
    std::vector<U8>      pStab;             // NSYM entries per pair
    std::vector<U8>      pStabLen;

    GenIndexD4() = default;
    GenIndexD4(const Geometry& geo, int nmen) : g(&geo), nsq(geo.nsq), k(nmen) {
        build();
    }

    // Is this placement of the men after the first two the canonical one for
    // its pair?  True always when the pair has no residual symmetry.
    inline bool restCanonical(int32_t pid, const Sq* rest) const {
        const int len = pStabLen[(size_t)pid];
        if (len <= 1) return true;
        for (int i = 1; i < len; ++i) {
            const int sym = pStab[(size_t)pid * NSYM + i];
            // Lexicographic comparison of the image against the original; the
            // first difference decides, and equality means this element fixes
            // the whole placement, which is not a reason to discard it.
            for (int j = 0; j < k - 2; ++j) {
                const Sq im = g->image(sym, rest[j]);
                if (im < rest[j]) return false;
                if (im > rest[j]) break;
            }
        }
        return true;
    }

    // The canonical image of a placement, and its slot.  Returns false when the
    // placement is not a position of this material (two men on one square).
    inline bool slotOf(const Sq* sq, U64& out) const {
        Sq best[8];
        bool have = false;
        const int len = g->canonSymLen[(size_t)sq[0]];
        for (int i = 0; i < len; ++i) {
            const int sym = g->canonSym[(size_t)sq[0] * NSYM + i];
            Sq im[8];
            for (int j = 0; j < k; ++j) im[j] = g->image(sym, sq[j]);
            if (!have) { for (int j = 0; j < k; ++j) best[j] = im[j]; have = true; continue; }
            // Compare from the second man on; the first is in the triangle for
            // every element considered here.
            for (int j = 1; j < k; ++j) {
                if (im[j] < best[j]) { for (int q = 0; q < k; ++q) best[q] = im[q]; break; }
                if (im[j] > best[j]) break;
            }
        }
        if (!have) return false;
        const int32_t pid = pairOf[(size_t)g->triId[best[0]] * nsq + best[1]];
        if (pid < 0) return false;
        U64 r = 0;
        for (int j = 2; j < k; ++j) r = r * (U64)nsq + (U64)best[j];
        out = (U64)pid * nrest + r;
        return true;
    }

    inline void decode(U64 slot, Sq* sq) const {
        const U64 pid = slot / nrest;
        U64 r = slot % nrest;
        sq[0] = pairA[(size_t)pid];
        sq[1] = pairB[(size_t)pid];
        for (int j = k - 1; j >= 2; --j) { sq[j] = (Sq)(r % (U64)nsq); r /= (U64)nsq; }
    }

    inline int32_t pairIdOf(U64 slot) const { return (int32_t)(slot / nrest); }

private:
    void build() {
        pairOf.assign(g->triSq.size() * (size_t)nsq, -1);
        for (size_t t = 0; t < g->triSq.size(); ++t) {
            const Sq a = g->triSq[t];
            const auto& st = g->triStab[t];
            for (Sq b = 0; b < nsq; ++b) {
                if (b == a) continue;
                // Keep only the smallest second square in its orbit under the
                // stabiliser of the first.
                bool canon = true;
                for (size_t i = 1; i < st.size(); ++i)
                    if (g->image(st[i], b) < b) { canon = false; break; }
                if (!canon) continue;
                pairOf[t * (size_t)nsq + b] = (int32_t)pairA.size();
                pairA.push_back(a);
                pairB.push_back(b);
                // What is left fixing both.
                U8 buf[NSYM];
                int len = 0;
                for (size_t i = 0; i < st.size(); ++i)
                    if (g->image(st[i], b) == b) buf[len++] = st[i];
                pStabLen.push_back((U8)len);
                const size_t base = pStab.size();
                pStab.resize(base + NSYM, 0);
                for (int i = 0; i < len; ++i) pStab[base + (size_t)i] = buf[i];
            }
        }
        npair = pairA.size();
        nrest = 1;
        for (int i = 2; i < k; ++i) nrest *= (U64)nsq;
        nslots = npair * nrest;
    }
};

} // namespace kqk
