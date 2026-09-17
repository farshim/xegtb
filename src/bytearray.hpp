// bytearray.hpp -- the storage under the two value arrays, in RAM or on disk.
//
// The solver's `w` and `b` are the only large allocations in the program, and
// past about 10 GiB they stop fitting: a 15 x 15 KNNNK table is 21.6 GiB
// against 16 GB of RAM.  Letting the OS page that through swap thrashes badly,
// because an anonymous dirty page must be written to swap and read back before
// it can be touched again, and the induction touches most of the table on
// every early ply.
//
// Backing the same bytes with a file turns that traffic into ordinary buffered
// I/O over a region the kernel may drop and re-read at will, and the access
// pattern is what makes it pay: phase A sweeps each block's configurations in
// index order and walks the blocks in order, so an early ply is essentially a
// sequential streaming pass.  Only the king retractions, whose count is
// proportional to the frontier rather than to the table, jump between blocks.
//
// The interface is the slice of std::vector the solver actually used, so that
// switching storage did not mean touching the induction.
#pragma once

#include <cstring>
#include <stdexcept>
#include <string>

#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

#include "geometry.hpp"

namespace kqk {

// Empty means anonymous memory.  A directory name means "put the value arrays
// in a file there instead", set by --scratch.
inline std::string gScratchDir;

class ByteArray {
public:
    ByteArray() = default;
    ~ByteArray() { release(); }
    ByteArray(const ByteArray&) = delete;
    ByteArray& operator=(const ByteArray&) = delete;

    void resize(U64 n) { alloc(n); }
    void assign(U64 n, U8 v) {
        alloc(n);
        if (n) std::memset(p_, v, (size_t)n);
    }

    U8*       data()       { return p_; }
    const U8* data() const { return p_; }
    U64       size() const { return n_; }
    U8&       operator[](U64 i)       { return p_[i]; }
    const U8& operator[](U64 i) const { return p_[i]; }
    bool      onDisk() const { return fd_ >= 0; }

private:
    void alloc(U64 n) {
        release();
        if (!n) return;
        n_ = n;
        if (gScratchDir.empty()) {
            p_ = (U8*)mmap(nullptr, (size_t)n, PROT_READ | PROT_WRITE,
                           MAP_PRIVATE | MAP_ANON, -1, 0);
            if (p_ == MAP_FAILED) { p_ = nullptr; n_ = 0; throw std::bad_alloc(); }
            return;
        }
        // A file, immediately unlinked: it is scratch, it must not survive a
        // crash, and the space comes back the moment the process exits even if
        // it exits badly.
        static int seq = 0;
        path_ = gScratchDir + "/kqk-scratch-" + std::to_string((long)getpid()) +
                "-" + std::to_string(seq++) + ".bin";
        fd_ = ::open(path_.c_str(), O_RDWR | O_CREAT | O_TRUNC, 0600);
        if (fd_ < 0) throw std::runtime_error("cannot create " + path_);
        ::unlink(path_.c_str());
        if (::ftruncate(fd_, (off_t)n) != 0) {
            ::close(fd_); fd_ = -1;
            throw std::runtime_error("cannot size the scratch file to " +
                                     std::to_string(n) + " bytes -- out of disk?");
        }
        p_ = (U8*)mmap(nullptr, (size_t)n, PROT_READ | PROT_WRITE, MAP_SHARED, fd_, 0);
        if (p_ == MAP_FAILED) {
            p_ = nullptr; ::close(fd_); fd_ = -1; n_ = 0;
            throw std::runtime_error("cannot map the scratch file");
        }
    }

    void release() {
        if (p_) ::munmap(p_, (size_t)n_);
        if (fd_ >= 0) ::close(fd_);
        p_ = nullptr; n_ = 0; fd_ = -1;
    }

    U8*         p_  = nullptr;
    U64         n_  = 0;
    int         fd_ = -1;
    std::string path_;
};

} // namespace kqk
