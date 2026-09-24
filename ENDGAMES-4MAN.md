# Four-man endgames on n x n boards, n = 3..10

Every endgame with four men on the board, in both rule sets, with the ones
already generated and stored on the external HDD marked.

- Generated: 2026-09-19
- Store scanned: `/Volumes/1.75TB/xegtb`
- Regenerate this file: `python3 mk4man.py`

Legend: `x` generated and in the store | `.` not generated | `-` outside the
supported range, or no solver for it in this binary.

Only the `kings` command writes into a `--tb` store, so only section D can be
marked `x` by scanning it. Sections A and C are written as single files with
`-o FILE` and are tracked separately.

**Status: 8 of 484 generatable (endgame, n) pairs are stored.**

Section E is the king-less set: the same capture rules with no king on the
board at all, so the game is won purely by capturing every enemy man. It is
the `kings` solver with `--wp/--bp` set to a non-king piece; the solver does
not care which man is on the board. Each side's men must all be alike -- 4-man
material with two unlike men on one side has no solver here (`mixed` does that,
but only 2-vs-1, which is three men).

## A. Mating rules (normal chess) -- generatable here

| endgame | n=3 | n=4 | n=5 | n=6 | n=7 | n=8 | n=9 | n=10 | command |
|---|---|---|---|---|---|---|---|---|---|
| KBBK | . | . | . | . | . | . | . | . | `./egtb gen -n N --endgame kbbk -o FILE` |
| KBNK | . | . | . | . | . | . | . | . | `./egtb gen -n N --endgame kbnk -o FILE` |
| KNNK | . | . | . | . | . | . | . | . | `./egtb gen -n N --endgame knnk -o FILE` |
| KQKR | . | . | . | . | . | . | . | . | `./egtb kqkr -n N -o FILE` |
| KQKB | . | . | . | . | . | . | . | . | `./egtb kqkr --bishop -n N -o FILE` |
| KQKK (strict) | - | . | . | . | . | . | . | . | `./egtb kqkk -n N -o FILE` |
| KQKK (loose) | - | . | . | . | . | . | . | . | `./egtb kqkk --loose -n N -o FILE` |

## B. Mating rules -- 4-man material with no solver in this binary

| endgame | n=3 | n=4 | n=5 | n=6 | n=7 | n=8 | n=9 | n=10 | command |
|---|---|---|---|---|---|---|---|---|---|
| KQQK | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KQRK | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KQBK | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KQNK | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KRRK | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KRBK | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KRNK | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KQKQ | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KQKN | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KRKR | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KRKB | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KRKN | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KBKB | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KBKN | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |
| KNKN | - | - | - | - | - | - | - | - | `-- no solver in this binary --` |

## C. Capture rules -- shared solver and KQKK

| endgame | n=3 | n=4 | n=5 | n=6 | n=7 | n=8 | n=9 | n=10 | command |
|---|---|---|---|---|---|---|---|---|---|
| KBBK (capture) | . | . | . | . | . | . | . | . | `./egtb gen -n N --endgame kbbk --capture -o FILE` |
| KBNK (capture) | . | . | . | . | . | . | . | . | `./egtb gen -n N --endgame kbnk --capture -o FILE` |
| KNNK (capture) | . | . | . | . | . | . | . | . | `./egtb gen -n N --endgame knnk --capture -o FILE` |
| KQKK (capture) | - | . | . | . | . | . | . | - | `./egtb kqkk --capture -n N -o FILE` |

## D. Capture rules -- the lattice with kings on the board (W+B=4)

| endgame | n=3 | n=4 | n=5 | n=6 | n=7 | n=8 | n=9 | n=10 | command |
|---|---|---|---|---|---|---|---|---|---|
| KKK vs K | x | x | x | x | x | x | x | x | `./egtb kings --white 3 --black 1 --min 3 --max 10 --tb DIR` |
| KKK vs Q | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp king --bp queen --min 3 --max 10 --tb DIR` |
| KKK vs R | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp king --bp rook --min 3 --max 10 --tb DIR` |
| KKK vs B | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp king --bp bishop --min 3 --max 10 --tb DIR` |
| KKK vs N | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp king --bp knight --min 3 --max 10 --tb DIR` |
| QQQ vs K | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp queen --bp king --min 3 --max 10 --tb DIR` |
| RRR vs K | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp rook --bp king --min 3 --max 10 --tb DIR` |
| BBB vs K | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp bishop --bp king --min 3 --max 10 --tb DIR` |
| NNN vs K | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp knight --bp king --min 3 --max 10 --tb DIR` |
| KK vs KK | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --min 3 --max 10 --tb DIR` |
| KK vs QQ | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp king --bp queen --min 3 --max 10 --tb DIR` |
| KK vs RR | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp king --bp rook --min 3 --max 10 --tb DIR` |
| KK vs BB | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp king --bp bishop --min 3 --max 10 --tb DIR` |
| KK vs NN | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp king --bp knight --min 3 --max 10 --tb DIR` |
| QQ vs KK | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp queen --bp king --min 3 --max 10 --tb DIR` |
| RR vs KK | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp rook --bp king --min 3 --max 10 --tb DIR` |
| BB vs KK | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp bishop --bp king --min 3 --max 10 --tb DIR` |
| NN vs KK | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp knight --bp king --min 3 --max 10 --tb DIR` |

## E. Capture rules -- KING-LESS: no kings at all, win by capturing every enemy man

| endgame | n=3 | n=4 | n=5 | n=6 | n=7 | n=8 | n=9 | n=10 | command |
|---|---|---|---|---|---|---|---|---|---|
| QQQ vs Q | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp queen --bp queen --min 3 --max 10 --tb DIR` |
| QQQ vs R | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp queen --bp rook --min 3 --max 10 --tb DIR` |
| QQQ vs B | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp queen --bp bishop --min 3 --max 10 --tb DIR` |
| QQQ vs N | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp queen --bp knight --min 3 --max 10 --tb DIR` |
| RRR vs Q | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp rook --bp queen --min 3 --max 10 --tb DIR` |
| RRR vs R | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp rook --bp rook --min 3 --max 10 --tb DIR` |
| RRR vs B | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp rook --bp bishop --min 3 --max 10 --tb DIR` |
| RRR vs N | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp rook --bp knight --min 3 --max 10 --tb DIR` |
| BBB vs Q | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp bishop --bp queen --min 3 --max 10 --tb DIR` |
| BBB vs R | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp bishop --bp rook --min 3 --max 10 --tb DIR` |
| BBB vs B | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp bishop --bp bishop --min 3 --max 10 --tb DIR` |
| BBB vs N | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp bishop --bp knight --min 3 --max 10 --tb DIR` |
| NNN vs Q | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp knight --bp queen --min 3 --max 10 --tb DIR` |
| NNN vs R | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp knight --bp rook --min 3 --max 10 --tb DIR` |
| NNN vs B | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp knight --bp bishop --min 3 --max 10 --tb DIR` |
| NNN vs N | . | . | . | . | . | . | . | . | `./egtb kings --white 3 --black 1 --wp knight --bp knight --min 3 --max 10 --tb DIR` |
| QQ vs QQ | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp queen --bp queen --min 3 --max 10 --tb DIR` |
| QQ vs RR | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp queen --bp rook --min 3 --max 10 --tb DIR` |
| QQ vs BB | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp queen --bp bishop --min 3 --max 10 --tb DIR` |
| QQ vs NN | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp queen --bp knight --min 3 --max 10 --tb DIR` |
| RR vs QQ | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp rook --bp queen --min 3 --max 10 --tb DIR` |
| RR vs RR | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp rook --bp rook --min 3 --max 10 --tb DIR` |
| RR vs BB | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp rook --bp bishop --min 3 --max 10 --tb DIR` |
| RR vs NN | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp rook --bp knight --min 3 --max 10 --tb DIR` |
| BB vs QQ | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp bishop --bp queen --min 3 --max 10 --tb DIR` |
| BB vs RR | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp bishop --bp rook --min 3 --max 10 --tb DIR` |
| BB vs BB | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp bishop --bp bishop --min 3 --max 10 --tb DIR` |
| BB vs NN | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp bishop --bp knight --min 3 --max 10 --tb DIR` |
| NN vs QQ | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp knight --bp queen --min 3 --max 10 --tb DIR` |
| NN vs RR | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp knight --bp rook --min 3 --max 10 --tb DIR` |
| NN vs BB | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp knight --bp bishop --min 3 --max 10 --tb DIR` |
| NN vs NN | . | . | . | . | . | . | . | . | `./egtb kings --white 2 --black 2 --wp knight --bp knight --min 3 --max 10 --tb DIR` |

