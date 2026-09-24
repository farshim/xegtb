# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A dependency-free C++20 endgame-tablebase generator for an *n* × *n* chess board, solved by
parallel retrograde analysis. One binary, `egtb`, holds every endgame. `README.md` (~2,600 lines)
is the primary design document and results paper; §2–§4 explain the invariants the solver rests
on, §6 the command line, §7 the file layout and what adding each endgame cost. Read the relevant
README section before changing a solver. `artifacts/MANIFEST.md` documents the checked-in
results, stats, lines and logs.

## Build, test, run

```sh
make -j8                 # -> ./egtb plus symlinks ./kqk ./krk ./kbbk ./kbnk (invoking under
                         #    a symlink name selects that --endgame)
make test                # ./egtb selftest --max 8  (exhaustive Bellman re-derivation, small boards)
./egtb selftest --max 5  # a fast smoke test (seconds)
./tests/run_tests.sh     # the full correctness gate: verification, thread-count determinism,
                         #   file round-trips, brute-force cross-checks, fixed "laws" per endgame,
                         #   and (§22) every configuration played out through `egtb serve`
./egtb serve             # the browser explorer on http://127.0.0.1:8080/
./egtb serve --tables DIR # ... backed by a store of solved tables, read then written
make clean
```

Compiler defaults: `clang++ -std=c++20 -O3 -march=native -DNDEBUG -pthread`. Every `.o` depends
on every header, so a header edit rebuilds everything (about 6 s on 8 cores). The `xcrun_db`
cache warning from clang inside the sandbox is harmless.

There is no unit-test framework. Tests are shell assertions on `egtb` output in
`tests/run_tests.sh`, grouped into numbered sections. To run one section, copy its loop out
of the script; the building blocks are:

```sh
./egtb gen -n 8 --endgame krk --verify --quiet      # look for "0 mismatches -- table is consistent"
./egtb bruteforce -n 6 --endgame kbnk               # look for "0 disagreements"
./egtb kqkk --capture --min 3 --max 6 --verify --brute
./egtb kings --white 3 --black 2 -n 6 --verify --brute
```

Standalone programs that compile on their own (build lines are in their headers):
`examples/probe_example.cpp` (library usage), `tests/rect_kk.cpp` (rectangular-board K+K vs K,
sharing no code with `src/`), `scratch/monotone.cpp` (an experiment).

The illustrated PDF in `doc/` needs **lualatex** and at least three passes; use `make -C doc`
(or `latexmk` from the root, which the `.latexmkrc` configures), never a fixed two runs of
lualatex. `doc/Makefile` explains why and deletes an unconverged PDF on purpose.

## Architecture

**Two solver families share the repo, split by one invariant: is Black bare?**

1. **Shared solver** (`Table` in `src/table.hpp`; `solver.cpp`, `verify.cpp`, `brute.cpp`,
   `stats.cpp`, `probe.cpp`, `io.cpp`): KQK, KRK, KBBK, KBNK, KNK, KNNK, KNNNK. Black has a
   lone king, so Black never checks, White never captures, and any Black capture is an
   immediate draw (or, for KNNNK, a conversion into the KNNK table). Those facts give a strict
   two-phase alternation, unsigned one-byte depth entries, and a counter-free phase B. The
   solver, index codec and move generator are all templated on `Endgame` (enum in
   `geometry.hpp`) so piece counts and ray sets fold to constants. `forEachMove` in
   `geometry.hpp` is the *single* definition of how a piece moves, used both forwards and for
   retraction.
2. **Endgames with their own solver, one file each**, because Black is armed or the rules
   differ: `kqkr.cpp` (KQKR/KQKB, signed entries, converts into KQK/KRK), `kqkbb.cpp`
   (KQKBB, five men, index in `indexbb.hpp`), `kqkk.cpp` (KQKK under mating rules, index in
   `indexkk.hpp`, block keyed on a king *triple*), `kqkkcap.cpp` (KQKK under capture rules),
   `kings.cpp` (W kings vs B kings, capture rules, six-table conversion lattice, `--tb DIR`
   on-disk store), `mixed.cpp` (two *unlike* white men vs one black man, capture rules,
   deliberately no symmetry reduction so it cross-checks `kings.cpp`). `policy.cpp` is a
   table-free KQK mating rule and its exhaustive scorer.

**A third layer reads all of them: the browser explorer.** `src/explore.cpp` holds one adapter
per table type behind the `Engine` interface in `explore.hpp` — turn a placement into a list of
men, value it, walk its legal moves — plus the catalogue of configurations. `src/serve.cpp` is
`egtb serve`, a dependency-free loopback HTTP server over those adapters, and `web/` is the two
pages it serves. Every adapter walks moves through the endgame's own exported generator
(`genWhite`/`genBlack`, `kqkrMoves`, `kqkbbMoves`, `kqkkMoves`, `kqkkCapMoves`,
`TableKings::moves`, `TableMixed::moves`), never its own; adding a configuration is one `Family`
row and, for a new table type, one `Engine`. No HTML or JavaScript changes. See README §6
"In a browser" and §7 "What putting it in a browser actually took".

**The store.** `serve --tables DIR` loads a solved table when the file is there and solves and
writes it when it is not; a file that will not load is a miss, never a wrong board. Adding it
gave `TableKQKR` and `TableKQKBB` an on-disk form for the first time (shared, in `io.cpp`, RLE
over *values* not bytes) and added `FLAG_CAPTURE` to `Table`'s header, which had not recorded
the rule set. `TableMixed` has no format and does not need one. A table is written only when
solving it took more than `--save-over` seconds. §23 of the gate checks a cold pass and a warm
pass agree exactly.

`main.cpp` dispatches subcommands; `gen/stats/probe/line/longest/verify/bruteforce/sizes/selftest`
belong to the shared solver, while `kqkr`, `kqkbb`, `kqkk`, `knnnk`, `kings`, `rooks`, `mixed`,
`policy`, `bishops` are the per-endgame commands, and `serve` is the web explorer. Table files are self-describing (endgame and
rule set in the header), so only `gen`, `sizes`, `bruteforce`, `selftest` take `--endgame`.

**Index and symmetry.** `index.hpp` keys a block on the canonical king pair under the dihedral
group D₄ (462 pairs on 8 × 8), and the *configuration* codec inside a block encodes the other
men: one man, ordered pair, unordered pair, unordered triple. Slots whose squares coincide are
"phantoms"; `Index::cfgLive` is the one predicate deciding whether a slot is real, and every
caller must use it (a past bug came from two places disagreeing). Values are depth-to-mate in
plies, relative to the side to move where signed.

**Three independent checks, all kept on purpose.** `verify.cpp` re-derives every entry from
successors with the forward generator; `brute.cpp` is a symmetry-free, single-threaded
reference solver compared position by position on small boards; `selftest` also checks
thread-count independence (output must be bit-identical for 1 vs N threads) and D₄ orbit
consistency. Past bugs produced plausible numbers rather than crashes and were caught only by
the verifier and brute force agreeing against the solver, so a change to any solver should run
both, and a new endgame needs its own conversion logic duplicated in the verifier and brute
force (see KNNNK in `run_tests.sh` §17).

**Memory.** The two value arrays are the only large allocations (`bytearray.hpp`). `--scratch DIR`
backs them with an unlinked file for tables past ~10 GiB; `kings --tb DIR` persists the lattice
as mmap'd raw tables.

## Conventions

- **Verification claims must be real.** Commit 8627c33 retracted nine commits' "identical on
  twelve families" claims because a zsh loop passed an unsplit string and every run fell back
  to the default board. When reporting a sweep, assert the expected count of boards/families
  actually ran so a silent no-op fails, and pass arguments separately rather than through a
  single unquoted variable.
- **Snapshot files are tracked history, not sources.** `*.bak`, `*.bak<N>`, `*.pre<stage>`
  (`kings.cpp.prerook`, `main.cpp.preq`, `README.md.bak`, `doc/*.bak*`) are pre-change copies
  kept in git. They are not in the Makefile and must not be edited, included, or "cleaned up"
  without being asked. `src/` files ending in `.cpp`/`.hpp` with no suffix are the live ones.
- **Commit messages** are `<file or area>: <what changed, as a sentence>` with a body that
  explains the reasoning and states measurements and what verification was run.
- Comments in this codebase argue *why* at length; match that style rather than adding
  what-comments. `README.md §7 "What adding each endgame actually took"` records the design
  lessons and should be extended when an endgame is added.
- Squares are algebraic (`d4`) for *n* ≤ 26 and 0-based `file,rank` beyond; both are accepted
  everywhere. `--btm` means Black to move. Moves in `line` output are written from-to
  (`Bd1-f3`) wherever a piece letter alone would be ambiguous.
- `artifacts/tables/` (1.3 GB) is gitignored and regenerable; everything else under
  `artifacts/` is checked in with `SHA256SUMS`.
