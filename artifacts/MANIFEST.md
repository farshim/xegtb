# kqk-egtb artifacts

Everything produced by the *n* × *n* KQK, KRK, KBBK, KBNK, KQKR, KQKB, KQKK,
KNK, KNNK, KNNNK and kings-only
tablebase generator in this repository, together with what is needed to check or
reproduce it.

Produced on an Apple M2, 8 cores, 16 GB, macOS 25.6, Apple clang 21,
`clang++ -std=c++20 -O3 -march=native`, `--threads 8`.

```
artifacts/
  tables/      93 ready-to-use tablebases
                 KQK, KRK  n = 3..24, 28, 32
                 KBBK      n = 3..14
                 KBNK      n = 3..12
                 KQKK      n = 3..10, mating rules, both readings
                 KQKK      n = 3..9,  capture rules (four tables per file)
  stats/       full census for every board computed, KQKK under both rules
  results/     the depth data, index sizes, benchmarks, the mating rule,
                 test-suite output
  lines/       optimal play, move by move, from the deepest win of an
                 endgame on a given board
  logs/        raw generator logs for the large runs
  SHA256SUMS   checksums for every file above
```

---

## tables/ — 93 files

`kqk<n>.kqk`, `krk<n>.krk`, `kbbk<n>.kbbk` and `kbnk<n>.kbnk`, run-length
encoded, loadable directly. A file records which endgame it holds, so no command below needs
`--endgame`:

```sh
../egtb stats  -f artifacts/tables/kqk16.kqk  --hist
../egtb probe  -f artifacts/tables/krk16.krk  --wk a1 --wr c3 --bk d4 --btm
../egtb line   -f artifacts/tables/krk16.krk  --wk a1 --wr b2 --bk j8 --board
../egtb probe  -f artifacts/tables/kbbk12.kbbk --wk a1 --wb1 b2 --wb2 d4 --bk f5
../egtb verify -f artifacts/tables/kbbk12.kbbk
../egtb longest -f artifacts/tables/kbnk12.kbnk --board
```

Every one was reloaded from disk and re-verified after being written: full
Bellman re-derivation for *n* ≤ 24 (KQK, KRK) and *n* ≤ 14 (KBBK, KBNK), a
1-in-37 sample for *n* = 28 and 32. All consistent.

`kqkk<n>.kqkk` and `kqkk<n>-loose.kqkk` hold KQKK, *n* = 3…10, under the two
readings of "a mate counts only when both kings are mated at once"; the rule
set is in the header, so a file cannot be read as the other one. They are
loaded by the `kqkk` command rather than by `stats`/`probe`, which belong to
the shared solver:

```sh
./egtb kqkk -f artifacts/tables/kqkk10.kqkk --line --mates 1
./egtb kqkk -f artifacts/tables/kqkk10-loose.kqkk
```

The loose tables run-length encode to about a fifth of their size, being almost
all draws; the strict ones do not compress at all and are stored raw (the
writer keeps whichever is smaller). KQKK boards above *n* = 10 are not stored
because they rebuild in seconds: *n* = 16 takes 26 s.

`kqkkcap<n>.cap` holds KQKK under the capture rules, *n* = 3…9 — all four of
its tables in one file, signed, two bytes an entry and no run-length encoding
(the values are too varied for it to pay). Read them with the same command:

```sh
./egtb kqkk --capture -f artifacts/tables/kqkkcap9.cap --stats
```

**Larger boards are deliberately not stored** — above *n* = 32 for the
one-piece endgames, above *n* = 14 for KBBK and above *n* = 12 for KBNK. They are cheaper to recompute
than to keep: *n* = 48 KRK is 3.05 GB on disk but rebuilds in under a minute,
and *n* = 20 KBBK is 3.14 GB but rebuilds in 76 s. Their complete statistics
*are* kept, in `stats/`. To rebuild one:

```sh
./egtb gen -n 48 --rook     -o krk48.krk    --rle --verify --stride 101
./egtb gen -n 20 --bishops  -o kbbk20.kbbk  --rle --verify --stride 101
./egtb gen -n 16 --kbnk     -o kbnk16.kbnk  --rle --verify --stride 101
```

## stats/ — the census for every board computed

`kqk<n>.txt` for *n* = 3…24, 28, 32, 40, 48, 56, 60; `krk<n>.txt` for
*n* = 3…24, 28, 32, 40, 48; `kbbk<n>.txt` for *n* = 3…18; `kbnk<n>.txt` for
*n* = 3…16; `kqkk<n>.txt` for *n* = 3…17, `kqkkcap<n>.txt` for *n* = 3…13 and
`kqkk<n>-loose.txt` for
*n* = 3…17. Each holds the legal,
won, drawn, mate, stalemate and piece-*en-prise* counts both over symmetry
classes and over the whole board, the deepest win with an example position, and
the full mate-in-*N* histogram.

The first line names the endgame. Files for *n* ≥ 40 were produced without
writing a table to disk.

**`kqk56.txt` and `kqk60.txt` are verbatim from the original KQK run** and are
the only two files here that predate the addition of KRK, so they lack the
`endgame` header line the others carry. Their numbers are unchanged; those two
boards need 7.2 GB and 10.8 GB and were not re-run. There is no KRK
counterpart for them: KRK at *n* = 56 would need 251 plies, one more than the
one-byte encoding holds (see the README, §5).

## results/

| file | contents |
|---|---|
| `max-dtm.csv` | KQK: deepest win for *n* = 3…36 plus 40, 48, 56, 60, against the closed form |
| `krk-max-dtm.csv` | KRK: deepest win for *n* = 3…50, against the period-6 law |
| `kbbk-max-dtm.csv` | KBBK: deepest win for *n* = 3…22, with first differences |
| `kbnk-max-dtm.csv` | KBNK: deepest win for *n* = 3…19, split by board parity |
| `index-sizes.csv` | canonical king pairs, entries per side and memory for *n* = 3…64 — identical for both endgames |
| `benchmarks.csv` | KQK build time, table size and peak memory |
| `krk-benchmarks.csv` | the same for KRK |
| `kbbk-benchmarks.csv` | the same for KBBK |
| `kbnk-benchmarks.csv` | the same for KBNK |
| `policy.csv` | the table-free KQK mating rule scored exhaustively for *n* = 4…14 |
| `kqkr-max-dtm.csv` | KQKR: wins, draws, losses and the deepest win for *n* = 3…17 |
| `kqkr-fortress.csv` | one KQKR placement tracked across board sizes, won up to 15 and drawn at 16 |
| `kqkb-max-dtm.csv` | KQKB: wins, draws, losses and the deepest win for *n* = 3…17, ordinary chess |
| `kqkb-capture.csv` | KQKB under capture rules: the same, plus the stalemates that become losses, *n* = 3…17 |
| `kqkk-max-dtm.csv` | KQKK, strict rules: the full census and the deepest win for *n* = 3…17 |
| `kqkk-loose.csv` | KQKK, loose rules: the same, for *n* = 3…17 |
| `kvkk-transition.csv` | K vs K + K under capture rules, *n* = 3…22: the win share, the deepest win and where the hunt stops working |
| `kqkk-capture.csv` | KQKK, capture rules: the signed census, both deepest wins and both halves of each sub-endgame, *n* = 3…13 |
| `knnk-max-dtm.csv` | KNNK: the census, the mate count and the deepest win for *n* = 3…16, with the two closed forms alongside |
| `knnnk-max-dtm.csv` | KNNNK: the full census and the deepest win for *n* = 3…13 |
| `knnk-capture.csv` | KNNK under both rule sets side by side, *n* = 3…16: ordinary chess and capture rules (stalemate scored as a loss) |
| `knk-capture.csv` | KNK under capture rules, *n* = 3…16: the transition at 6→7 and the 2900 wins that remain |
| `knnk-capture-track.csv` | one KNNK placement tracked across board sizes under capture rules, won to 14 and drawn at 15 |
| `knnnk-quiet15.csv` | quiet drawn KNNNK placements on 15 × 15, with the trapped-knight reason for each |
| `knnnk-draws.csv` | KNNNK: the white-to-move placements sorted into loose / guarded / quiet, wins and draws separately, *n* = 3…12 |
| `kings-capture.csv` | Kings only under capture rules: KKK vs KK for *n* = 3…11, KKK vs K to 17, KK vs KK to 17 and KK vs K to 20, one row per board per endgame |
| `test-suite-output.txt` | full output of `tests/run_tests.sh`, ending `ALL TESTS PASSED` |

`policy.csv` scores the table-free mating rule of `src/policy.cpp` — a pure
function of the position, with no lookup and no dependence on *n*. White's move
is fixed to the rule, Black is left free, and the worst case is backward-induced
over the whole induced graph; a position from which the rule never mates counts
as a failure. It mates from **every** legal position on every board from 4 × 4
to 14 × 14 — 13 559 524 in all — taking at worst 1.79 times as long as the
tablebase. `stuck` and `cyclic` are both zero throughout; the `rule_*` columns
say how often each of the six rules fired. Reproduce with

```sh
./egtb policy --min 4 --max 14 --rules
./egtb policy --min 6 --max 8 --oracle   # control: must give ratio 1.00
```

`kqkr-max-dtm.csv` is the odd one out. KQKR is the endgame here in which Black
has a piece *that can hold its own*, so the table is signed and converts, and it
is the only one whose depth does **not** simply grow: 35, 44, 54, 69, 85, 108, 132 moves for
*n* = 8…14 — the steepest growth in this repository, with a local exponent that
climbs through 2 and keeps climbing rather than settling at any power — then
**218** at *n* = 15, then *down* to 166 and 116 while the
drawn fraction jumps from 0.13% to 26.6% and stays there.
`kqkr-fortress.csv` follows one placement through it: wK a1, wQ g1, bK c1,
bR d1, with Black's rook interposed on the queen's rank, is mate in 26 at
*n* = 8, mate in 176 at *n* = 15 and drawn at *n* = 16. Reproduce with

```sh
./egtb kqkr --min 3 --max 14 --verify        # Bellman re-derivation of every entry
./egtb kqkr -n 5 --brute                     # unreduced, different algorithm
./egtb kqkr --min 4 --max 16 --selfcheck     # move generator and index vs naive ones
./egtb kqkr -n 12 --probe a1,g1,c1,d1        # the fortress placement
```

`kqkb-max-dtm.csv` and `kqkb-capture.csv` are the same material with Black's
rook exchanged for a bishop, and they are the opposite story in every respect.
The table is signed and converts exactly as KQKR does — into KQK when White
takes the bishop, into K+B vs K reversed when Black takes the queen — but a
bishop cannot hold the position the way a rook can:

* **White never loses, on any board from 3 to 17**, and the drawn share falls
  monotonically from 2.33% at *n* = 3 to 0.080% at *n* = 17 — 0.309% at 8 × 8.
  KQKR at *n* = 17 is 26.7% drawn, and loses 0.117% outright.
* The depth is **linear**: 5, 11, 17, 23, 27, 33, 37, 41, 47, 51, 55, 61, 65,
  69, 73 plies for *n* = 3…17, which is mate in 3 up to mate in 37. A least
  squares fit over *n* = 5…14 gives 4.76*n* − 6.05 with every residual under one
  ply. KQKR's depth over the same range climbs through a local exponent of 2
  and then collapses.

The capture rules cost this endgame almost nothing, and what they do cost is
countable. With one king a side the paper's theorem (§7) makes them ordinary
chess with one clause changed, and for this material the change is exactly
*stalemate loses*: the solver computes the other clause — no chess move and no
rule 2 move either, which would be a draw — and finds **zero** such positions on
every board, as a cornered king with one bishop must. The stalemates that flip
are **2(*n* − 2)** of Black, exactly, for every *n* from 3 to 17, and **none** of
White: a white queen always has a legal move, so White is never stalemated at
all.

What does change is the conversion. Under capture rules K+B vs K is no longer a
dead draw — a lone bishop and king can take a bare king's last square away — so
...BxQ becomes something Black can *win*, and White acquires losses he does not
have in chess: 1, 2, 11, 66 at *n* = 3…6, and then exactly ***n* − 2** from
*n* = 7 to 17. The 6 × 6 board is the outlier of the family in both directions,
holding 66 white losses and a black win 42 plies deep where every board from 7
up holds none deeper than 4.

`lines/kqkb-longest-n{6,8,11}-{chess,capture}.txt` follow optimal play from the
deepest win, move by move, to the mate. The three board sizes are not arbitrary:
under the ordinary rules the deepest win on 6 × 6, on 8 × 8 and on 11 × 11 is
the **same configuration** — all four men on the long diagonal, the white king
at a1, the black king ⌊(*n* − 1)/2⌋ steps along it, the bishop on the next square
and the queen beyond. It is mate in 12, 17 and 24 respectively. Each line
converts into KQK when White wins the bishop and is followed into that table to
the mate, so the ply numbering runs unbroken from the start to the mating move.
Reproduce with

```sh
./egtb kqkr --bishop --min 3 --max 17                    # the chess table
./egtb kqkr --bishop --capture --min 3 --max 17          # the capture table
./egtb kqkr --bishop --min 3 --max 5 --verify --brute    # both checkers
./egtb kqkr --bishop --capture --min 3 --max 5 --verify --brute
./egtb kqkr --bishop --min 4 --max 14 --selfcheck        # generator and index
./egtb kqkr --bishop -n 8 --line                         # the 8 x 8 line above
```

`knnk-max-dtm.csv` and `knnnk-max-dtm.csv` are the knight endgames, and the
first exists because of the second. Two knights cannot *force* mate, but they
can mate: K+N+N vs K holds **120 mate positions on 8 × 8**, exactly 16*n* − 8 on
every board from 4 × 4 up, and White's wins number exactly 104*n* − 216 for
*n* ≥ 5. What is absent is zugzwang — the deepest white win is **one ply on
every board size from 3 to 16**, so White wins only where he mates on the move,
and black-to-move losses equal mates exactly. The single exception is the
3 × 3 board, where 36 losses stand against 32 mates: one symmetry class in
which Black must step into mate.

That is why KNNNK converts. …K×N does not always leave a draw, so the value has
to be read out of the KNNK table rather than assumed; `--no-sub` suppresses the
attachment so the solver's refusal can be tested rather than trusted. Three
knights then win 98.7% of 8 × 8 white-to-move placements rather than all of
them, and `knnnk-draws.csv` says why: **94.9% of the draws have a knight loose**
— attacked by the black king and undefended — against 23.6% of the wins. The
*guarded* column is exactly 128 placements on every board from 7 × 7 to 12 × 12.

`knnk-capture.csv` is the same material under \S8's capture rules, which for one
king a side reduce to chess with stalemate scored as a loss --- the second
clause of the theorem, checkmate becoming a draw under total immobility, cannot
fire here, because a cornered king has three on-board neighbours and two knights
can block at most two. Two knights cannot force mate; they **can** force
stalemate. So White's wins go from 616 placements on 8 × 8 to **5 713 976**, and
up to 6 × 6 he wins *every* legal position. The mate count is identical under
both rules and the chess stalemate count equals the capture-rule loss count
exactly, which is the clause relabelling precisely that set and nothing else.

It then has a critical board size: the deepest win runs 51, 61, 75, 91, 111,
151, **219** plies for *n* = 8…14 and the win collapses to 0.45% at 15 × 15.
`knnk-capture-track.csv` follows one placement through it — wK a1, wN c2, wN c3,
bK e5 is mate in 20 at *n* = 8, mate in 103 at *n* = 14 and drawn at *n* = 15.
`knk-capture.csv` is the same story one piece down and three boards earlier: a
lone knight forces stalemate from 99.5% of 6 × 6 placements, then from exactly
2900 placements on every board from 10 × 10 up. That is why the KNNK capture
table converts rather than scoring …K×N as a draw. Reproduce with

```sh
./egtb gen -n 8  --endgame knnk --capture      # 5 713 976 wins against 616
./egtb gen -n 15 --endgame knnk --capture      # the collapse
./egtb gen -n 12 --endgame knk  --capture      # 2900, and 40 stalemate losses
./egtb bruteforce -n 9 --endgame knnk --capture
```

The 15 × 15 KNNNK table --- 11 591 361 600 entries per side, **21.6 GiB** --- is
the largest built here and had to be built against a mapped file rather than in
memory; it took four and a quarter hours, and `artifacts/stats/knnnk15.txt`
holds its output, including a sampled Bellman re-derivation (1 in 100 003) with
zero mismatches. Its deepest win is 99 plies and 0.142% of white-to-move
placements are drawn. `knnnk-quiet15.csv` lists *quiet* ones --- nothing
attacked at all --- and the reason is the same in every case: a knight is
trapped in a corner with both its flight squares attacked by the black king and
defended by nothing, so it is lost and what remains is drawn KNNK. The trap does
not depend on the board, and the same five squares are drawn at 12 × 12,
10 × 10 and 8 × 8.

No closed form is claimed for the KNNNK depth. It grows by about four moves per
unit of board size over 8 ≤ *n* ≤ 13, but its local exponent (0.95–1.45) does
not separate from that of KQK (0.82–1.27) whose law is exactly linear, so this
range cannot tell a linear law from the quadratic one a knight-only endgame
should eventually show. Reproduce with

```sh
./egtb gen -n 8 --endgame knk               # no mate exists, on any board
./egtb gen -n 8 --endgame knnk              # 120 mates, deepest win 1 ply
./egtb knnnk --min 3 --max 12 --draws       # the census and the draw breakdown
./egtb knnnk --min 5 --max 10 --verify --brute
./egtb bruteforce -n 7 --endgame knnnk      # 530 832 288 placements, unreduced
```

`kqkk-max-dtm.csv` and `kqkk-loose.csv` are the two readings of the KQKK rule
that a mate counts only when both black kings are mated at once. Under the
strict reading — Black may leave neither king attacked — **White wins every
legal white-to-move position at every board size from 3 to 17**, the
`wtm_draw` column being zero throughout, and the 8 × 8 mate is in 7 against
mate in 10 for the same queen against one king. Two identities hold in every
row and are worth checking against: `btm_legal = btm_loss + btm_draw`, and
`btm_draw = stalemate + en_prise`, the second saying there is no positional
draw anywhere in the table. `single_mate` counts the stalemates in which
exactly one king is in check — the mates this variant declines to count, and
so what the rule costs: 93 508 of the 94 624 stalemates at *n* = 8, and 99.96%
of them at *n* = 16. Under the loose reading — only both kings attacked at once
is forbidden — the endgame collapses to exactly **80 n − 96** won placements
for 5 ≤ *n* ≤ 14, none deeper than mate in 2. Reproduce with

```sh
./egtb kqkk --min 3 --max 17 --stats         # the census in the csv
./egtb kqkk --min 4 --max 6 --verify --brute # Bellman, and an unreduced solver
./egtb kqkk --min 4 --max 12 --selfcheck     # generator and symmetry class
./egtb kqkk -n 8 --mates 1 --single 1        # a double mate, and a single one
```

`kvkk-transition.csv` follows K vs K + K on its own, which is a three-man
endgame and so reaches boards the four-man table never could. It is where the
capture rules' one phase transition lives: two black kings run a lone white king
down from **every** placement up to 14 x 14, and at 15 x 15 they stop -- 7.0% of
placements still won, falling to 3.1% at n = 22, with the deepest win frozen at
exactly 73 plies for every board past the transition. Rebuild it with
`./egtb kqkk --capture --kvkk --min 3 --max 22`, seconds a board. The row was
computed twice, by the symmetry-reduced table and by an unreduced solver on an
ordered index, agreeing on the win count, the deepest win and the
white-to-move draw count at n = 8 and 12..20.

`kings-capture.csv` is that same rule set with the queen deleted, so that
nothing is left on the board but kings: three white against two black, and the
three smaller endgames the table converts into. White wins from **every**
white-to-move placement on every board computed, 3 x 3 to 11 x 11, and the whole
reason is the K + K + K vs K row: up to 14 x 14 that endgame is won with *either*
side to move, so any capture White can make in the five-man table wins on the
spot. At 15 x 15 that stops being true -- 8.9% of its black-to-move placements
turn drawn, every one of them because Black takes a white king and reaches the
K + K vs K that has just stopped being won. The other conversion goes at the
same board and in Black's favour: K + K vs K + K falls from 13.3% won at
14 x 14 to 0.03% at 15 x 15, so the capture that is Black's whole defence
almost always lands in a draw. The clause the five-man win rests on expires
four boards past where the five-man table can be built.

The K + K vs K rows are `kvkk-transition.csv` seen from the other colour, and
they reproduce it exactly -- win count, deepest win and the white-to-move draw
count -- at every board from 8 x 8 to 20 x 20, transition and frozen 73-ply
depth included. That is the strongest cross-check in this directory: two
solvers with no shared code, no shared index and no shared move generator,
agreeing on where a phase transition is. Rebuild the four rows with

```
./egtb kings --min 3 --max 11                       # KKK vs KK; n = 11 takes ~2 h
./egtb kings --white 3 --black 1 --min 8 --max 17   # KKK vs K
./egtb kings --white 2 --black 2 --min 3 --max 17   # KK vs KK, transition included
c++ -std=c++20 -O2 -o rect_kk tests/rect_kk.cpp && ./rect_kk -f 24 -r 14   # rectangles
./egtb kings --white 2 --black 1 --min 3 --max 20   # KK vs K, seconds a board
```

`kqkk-capture.csv` is the third reading of the KQKK rule, and the only one in
which the objective is to *capture* the kings rather than to mate them: every
king is an ordinary man that captures and can be captured, a player wins by
taking all of the opponent's, and there is no check, mate or stalemate
anywhere. It is the only KQKK table Black can win. The columns split
three ways per side to move, and again over *quiet* placements -- nothing
hanging, which is exactly the set the strict rules call legal -- because with
two kings free to walk up to anything, the unrestricted census says more about
the tempo than about the endgame. Over the 2 534 392 quiet placements at
*n* = 8 the strict rule gives White 100% and this one gives him 65.9%, with
Black holding 34.1% and winning 48. The three sub-endgames are in the same
row: `K vs K + K` is a **black win from every one** of its positions at every
board this file covers, which is what makes the queen unlosable, and
`K + Q vs K` is a white win from every one,
one move faster than ordinary KQK because there is no stalemate to avoid.
Reproduce with

```sh
./egtb kqkk --capture --min 3 --max 11 --stats
./egtb kqkk --capture --min 3 --max 6 --verify --brute
./egtb kqkk --capture -n 8 --single 1     # a zugzwang with a queen on the board
```

`max-dtm.csv` is the evidence for the KQK depth law: the deepest KQK win on an
*n* × *n* board is **mate in ⌈3(*n*−2)/2⌉**, with **zero** disagreements over
9 ≤ *n* ≤ 60 and the 8 × 8 board as the sole exception (10 rather than 9).

`krk-max-dtm.csv` is the evidence for the KRK law, which has period 6 rather
than 2 and no closed form of the KQK shape: **m(n) = 14⌊n/6⌋ + c(n mod 6)**
with **c = (−3, 0, 2, 5, 7, 10)**, equivalently *m*(*n*) = *m*(*n*−6) + 14.
It holds over 12 ≤ *n* ≤ 50 with **exactly one** disagreement, at *n* = 24
(54 rather than the predicted 53) — the same shape of anomaly KQK shows at
*n* = 8. The `agrees` column in each file flags this directly.

`kbbk-max-dtm.csv` asserts **no law**. The KBBK range reaches only *n* = 22,
which is far too short to tell a genuine formula from a local run; the file
records the measured depths and their first differences and leaves it there.

`kbnk-max-dtm.csv` carries a `parity` column because KBNK is really two
interleaved sequences: even boards are much deeper than the odd boards on
either side (93 at *n* = 16 against 63 at *n* = 15), since on an odd board
every corner is the same colour. KBNK is also the one endgame here whose depth
is **quadratic** rather than linear in *n* — over the odd boards
0.1411 *n*² + 2.095 *n* − 0.82 fits all ten computed points to within 0.64
moves, and a fit to *n* ≤ 19 predicted *n* = 21 to within one move. No exact
closed form is claimed. See the README, §5.

The even boards stop at *n* = 18 not for want of memory but because *n* = 20
needs more than the 250 plies a one-byte entry holds, and the generator refuses
rather than wrapping; *n* = 21 is odd, hence shallower, and fits.

## logs/

| file | contents |
|---|---|
| `gen-n40-n48-n56.log` | per-ply progress, statistics and `/usr/bin/time -l` for KQK *n* = 40, 48, 56 |
| `gen-n60.log` | the same for *n* = 60, the largest board run |
| `timings-raw.log` | the clean KQK timing sweep for *n* = 8, 16, 24, 32, 40 |

---

## Reproducing

```sh
make                       # build ./egtb and the ./krk symlink
./tests/run_tests.sh       # the full correctness gate
```

The generator is deterministic: output is bit-identical regardless of thread
count, which `run_tests.sh` checks for 1, 2, 3, 5 and 8 threads in both
endgames. Regenerating any table with the same command must reproduce the same
checksum in `SHA256SUMS`.

```sh
shasum -a 256 -c SHA256SUMS      # run from inside artifacts/
```

Note that these checksums are for **file format version 3**, which added an
explicit endgame field and a second longest-position square. Tables written by
an earlier build carry version 1 or 2 and will not match, though the current
binary still loads them.

## The 8 × 8 cross-checks

`./egtb selftest` reproduces the published KQK figures exactly and checks the
KRK figures against constants derived from the unreduced reference solver in
`src/brute.cpp`. For *n* = 3…8 that solver is also compared against the real
generator position by position, over every placement on the board.

| quantity | KQK computed | KQK published | KRK | KBBK | KBNK |
|---|---:|---:|---:|---:|---:|
| canonical king pairs | 462 | 462 (Syzygy `MapKK`) | 462 | 462 | 462 |
| checkmates | 364 | 364 | 216 | 1 552 | 464 |
| stalemates | 872 | 872 | 68 | 10 204 | 12 888 |
| piece *en prise* draws | 22 176 | 22 176 | 22 176 | 1 116 752 | 2 330 120 |
| black-to-move draws | 23 048 | 23 048 | 22 244 | 4 016 252 | 2 472 416 |
| white-to-move draws | 0 | — | 0 | 2 578 420 | 53 320 |
| deepest win | mate in 10 | mate in 10 | mate in 16 | mate in 19 | mate in 33 |

Mate in 33 is the textbook KBNK figure.

The *en prise* counts agree between KQK and KRK necessarily: Black may take the
piece exactly when it stands next to the black king undefended, which for a
single piece does not depend on what it is.

Every one of KBBK's 2 578 420 white-to-move draws has its two bishops on the
same colour, and every same-coloured position is drawn — checked for *n* = 3…18.
The opposite-coloured positions are won bar 520 placements on 8 × 8, in each of
which a bishop is trapped beside a cornered king. See the README, §5.
