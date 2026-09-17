#!/bin/sh
# tests/run_tests.sh -- correctness gate for the KQK, KRK, KBBK and KBNK
# tablebases.
set -e
cd "$(dirname "$0")/.."
EGTB=./egtb
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
fail=0
say() { printf '%s\n' "$*"; }

# KBBK is a four-man table: n^2 (n^2 - 1) / 2 piece placements per king pair
# rather than n^2, so the same memory reaches a much smaller board.  Each
# section picks its board sizes accordingly.
sizes_for() {
  case "$1" in
    kbbk|kbnk) echo "$2" ;;
    *)         echo "$3" ;;
  esac
}

say "== 1. exhaustive self-test, n = 3..10, the bare-king endgames =="
say "   (full Bellman re-derivation of every entry; also a position-by-position"
say "    comparison against the unreduced solver -- n <= 8 for the one-piece"
say "    endgames, n <= 6 for KBBK and KBNK, whose arrays grow as n^6.  For"
say "    KBBK it also checks that bishop colour decides the drawn positions.)"
$EGTB selftest --max 10 --brute 8 || fail=1

say ""
say "== 2. full verification of larger boards =="
for p in kqk krk kbbk kbnk; do
  for n in $(sizes_for $p "10 12 14" "12 16 20 24"); do
    out=$($EGTB gen -n $n --endgame $p --verify --quiet 2>&1)
    echo "$out" | grep -q "0 mismatches -- table is consistent" \
      && say "   $p  n=$n  full verify ok" \
      || { say "   $p  n=$n  FAILED"; echo "$out"; fail=1; }
  done
done

say ""
say "== 3. thread-count independence (bit-identical output) =="
for p in kqk krk kbbk kbnk; do
  for n in $(sizes_for $p "9 12" "14 18"); do
    $EGTB gen -n $n --endgame $p --threads 1 -o "$TMP/a.tb" --quiet >/dev/null
    ok=1
    for t in 2 3 5 8; do
      $EGTB gen -n $n --endgame $p --threads $t -o "$TMP/b.tb" --quiet >/dev/null
      cmp -s "$TMP/a.tb" "$TMP/b.tb" || ok=0
    done
    [ $ok = 1 ] && say "   $p  n=$n  identical for 1/2/3/5/8 threads" \
                || { say "   $p  n=$n  THREAD-DEPENDENT OUTPUT"; fail=1; }
  done
done

say ""
say "== 4. file round-trip, raw and run-length encoded =="
for p in kqk krk kbbk kbnk; do
  n=$(sizes_for $p 11 16)
  $EGTB gen -n $n --endgame $p -o "$TMP/raw.tb"       --quiet >/dev/null
  $EGTB gen -n $n --endgame $p -o "$TMP/rle.tb" --rle --quiet >/dev/null
  r=$(wc -c < "$TMP/raw.tb"); c=$(wc -c < "$TMP/rle.tb")
  say "   $p  n=$n  raw $r bytes, run-length $c bytes"
  a=$($EGTB stats -f "$TMP/raw.tb"); b=$($EGTB stats -f "$TMP/rle.tb")
  [ "$a" = "$b" ] && say "   $p  both files report identical statistics" \
                  || { say "   $p  ROUND-TRIP MISMATCH"; fail=1; }
  # The endgame itself must survive the round trip: a file knows what it holds.
  want=$(echo "$p" | tr 'a-z' 'A-Z')
  echo "$a" | grep -q "^endgame  *$want " \
    && say "   $p  reloaded file reports the right endgame" \
    || { say "   $p  ENDGAME LOST IN ROUND TRIP"; fail=1; }
  $EGTB verify -f "$TMP/rle.tb" | grep -q "table is consistent" \
    && say "   $p  decoded run-length table verifies" \
    || { say "   $p  RLE TABLE FAILED VERIFY"; fail=1; }
done

say ""
say "== 5. the known 8x8 facts =="
$EGTB gen -n 8 --queen   -o "$TMP/q8.tb" --quiet >/dev/null
$EGTB gen -n 8 --rook    -o "$TMP/r8.tb" --quiet >/dev/null
$EGTB gen -n 8 --bishops -o "$TMP/b8.tb" --quiet >/dev/null
check_max() {
  $EGTB longest -f "$1" | head -1
  $EGTB longest -f "$1" | grep -q "mate in $2" \
    && say "   deepest 8x8 $3 win is mate in $2  ok" \
    || { say "   WRONG 8x8 $3 MAXIMUM"; fail=1; }
}
check_max "$TMP/q8.tb" 10 KQK
check_max "$TMP/r8.tb" 16 KRK
check_max "$TMP/b8.tb" 19 KBBK
$EGTB gen -n 8 --kbnk -o "$TMP/bn8.tb" --quiet >/dev/null
check_max "$TMP/bn8.tb" 33 KBNK
$EGTB probe -f "$TMP/q8.tb" --wk a1 --wq c3 --bk d4 --btm | grep -q draw \
  && say "   loose queen with black to move is a draw  ok" \
  || { say "   EN PRISE CASE WRONG"; fail=1; }
$EGTB probe -f "$TMP/r8.tb" --wk a1 --wr c3 --bk d4 --btm | grep -q draw \
  && say "   loose rook with black to move is a draw   ok" \
  || { say "   EN PRISE CASE WRONG"; fail=1; }

say ""
say "== 6. one position, four endgames: what each piece actually covers =="
say "   (wK c3, white man(men) on b2, bK a1, Black to move.  A queen on b2"
say "    covers a1 down the diagonal and is defended, so it is mate; a rook"
say "    does not attack a1 at all, so it is stalemate.)"
$EGTB probe -f "$TMP/q8.tb" --wk c3 --wq b2 --bk a1 --btm | grep -q "mate in 0" \
  && say "   queen b2 mates the cornered king      ok" \
  || { say "   DIAGONAL MATE WRONG"; fail=1; }
$EGTB probe -f "$TMP/r8.tb" --wk c3 --wr b2 --bk a1 --btm | grep -q draw \
  && say "   rook b2 only stalemates it            ok" \
  || { say "   ROOK IS ATTACKING DIAGONALLY"; fail=1; }
# Two bishops need three men to seal a corner: Bb2 gives the check along the
# dark diagonal, Bc4 covers a2 along the light one, and the king covers b1 and
# defends b2.  A far-flung second bishop is not enough -- with Bb2 and Bh6 the
# king simply walks out to a2.
$EGTB probe -f "$TMP/b8.tb" --wk c2 --wb1 b2 --wb2 c4 --bk a1 --btm | grep -q "mate in 0" \
  && say "   bishops b2+c4 with Kc2 mate a1        ok" \
  || { say "   BISHOP MATE WRONG"; fail=1; }
$EGTB probe -f "$TMP/b8.tb" --wk c3 --wb1 b2 --wb2 h6 --bk a1 --btm | grep -q draw \
  && say "   bishops b2+h6 do not: Ka2 escapes     ok" \
  || { say "   DISTANT BISHOP UNEXPECTEDLY MATES"; fail=1; }

say ""
say "== 7. KBBK: bishop colour and the trapped-bishop draws =="
say "   (two same-coloured bishops can never mate; opposite-coloured ones win"
say "    except when one is trapped beside a cornered king)"
$EGTB probe -f "$TMP/b8.tb" --wk c3 --wb1 b2 --wb2 d2 --bk a1 --btm | grep -q draw \
  && say "   same-coloured bishops cannot mate     ok" \
  || { say "   SAME-COLOUR BISHOPS WON"; fail=1; }
# wK c1, bishops e1 and a2, bK a1, White to move.  Every rescue of the a2
# bishop stalemates Black, and every other move drops it.
$EGTB probe -f "$TMP/b8.tb" --wk c1 --wb1 e1 --wb2 a2 --bk a1 | grep -q draw \
  && say "   trapped bishop, White to move: draw   ok" \
  || { say "   TRAPPED-BISHOP CASE WRONG"; fail=1; }
for rescue in b1 c4; do
  $EGTB probe -f "$TMP/b8.tb" --wk c1 --wb1 e1 --wb2 $rescue --bk a1 --btm | grep -q draw \
    && say "   ... after B-$rescue Black is stalemated  ok" \
    || { say "   RESCUE $rescue NOT A DRAW"; fail=1; }
done

say ""
say "== 8. KQK maximum depth follows ceil(3(n-2)/2) for n >= 9 =="
for n in 9 10 11 13 17 22 27; do
  got=$($EGTB gen -n $n --queen --quiet 2>/dev/null | awk '/longest win/{print $8}')
  want=$(( (3*n - 6 + 1) / 2 ))
  [ "$got" = "$want" ] && say "   n=$n  mate in $got  ok" \
                       || { say "   n=$n  mate in $got, expected $want"; fail=1; }
done

say ""
say "== 9. KRK maximum depth follows m(n) = 14*floor(n/6) + c(n mod 6) =="
say "   (c = -3, 0, 2, 5, 7, 10; period 6, one exception at n = 24)"
for pair in "9 18" "10 21" "12 25" "16 35" "18 39" "20 44" "24 54"; do
  set -- $pair; n=$1; want=$2
  got=$($EGTB gen -n $n --rook --quiet 2>/dev/null | awk '/longest win/{print $8}')
  [ "$got" = "$want" ] && say "   n=$n  mate in $got  ok" \
                       || { say "   n=$n  mate in $got, expected $want"; fail=1; }
done

say ""
say "== 10. KBBK maximum depth: measured regression values =="
for pair in "8 19" "10 24" "12 29" "14 35" "16 40"; do
  set -- $pair; n=$1; want=$2
  got=$($EGTB gen -n $n --bishops --quiet 2>/dev/null | awk '/longest win/{print $8}')
  [ "$got" = "$want" ] && say "   n=$n  mate in $got  ok" \
                       || { say "   n=$n  mate in $got, expected $want"; fail=1; }
done

say ""
say "== 10b. KBNK: a defended piece cannot be captured =="
say "   (wK b1, wB e1, wN c2, bK d1, Black to move.  The knight defends the"
say "    bishop, so Kxe1 is not a move and Black is lost; a solver that treats"
say "    'the king steps onto a piece' as a capture calls this a draw.)"
$EGTB gen -n 5 --kbnk -o "$TMP/bn5.tb" --quiet >/dev/null
$EGTB probe -f "$TMP/bn5.tb" --wk b1 --wb e1 --wn c2 --bk d1 --btm \
  | grep -q "mate in 10" \
  && say "   defended bishop, Black to move: lost in 10  ok" \
  || { say "   DEFENDED-CAPTURE CASE WRONG"; fail=1; }
# The same shape with the piece genuinely loose really is a draw.
$EGTB probe -f "$TMP/bn5.tb" --wk a1 --wb e1 --wn e3 --bk d1 --btm \
  | grep -q draw \
  && say "   loose bishop, Black to move: draw       ok" \
  || { say "   LOOSE-PIECE CASE WRONG"; fail=1; }

say ""
say "== 11. cross-endgame invariant: en prise counts must agree for KQK/KRK =="
say "   (Black may take the piece iff it stands next to the black king"
say "    undefended, which for a single piece does not depend on which it is)"
for n in 6 8 11 14; do
  q=$($EGTB gen -n $n --queen --quiet 2>/dev/null | awk '/en prise/{print $NF}' | tail -1)
  r=$($EGTB gen -n $n --rook  --quiet 2>/dev/null | awk '/en prise/{print $NF}' | tail -1)
  [ "$q" = "$r" ] && say "   n=$n  both $q  ok" \
                  || { say "   n=$n  queen $q vs rook $r"; fail=1; }
done

say ""
say "== 12. the table-free mating rule mates from every position =="
say "   (White's move is fixed to the rule in src/policy.cpp, Black plays"
say "    anything, and the worst case is backward-induced over every legal"
say "    placement.  Cycles and dead ends both count as failures.)"
out=$($EGTB policy --min 4 --max 8 2>&1)
echo "$out" | grep -q 'FAILS' \
  && { say "   THE RULE FAILS SOMEWHERE"; echo "$out"; fail=1; } \
  || say "   n=4..8: mates from everywhere, no cycles, no dead ends  ok"
# and it stays near the bound
for n in 6 8; do
  r=$(echo "$out" | awk -v n=$n '$1==n {print $5}')
  awk -v r="$r" 'BEGIN{exit !(r+0 > 0 && r+0 <= 1.8)}' \
    && say "   n=$n  ratio $r  <= 1.8  ok" \
    || { say "   n=$n  ratio $r out of range"; fail=1; }
done
# The control: with the tablebase's own move substituted the same harness must
# reproduce the optimum exactly.  If it does not, the scorer is measuring
# itself rather than the rule.
ratios=$($EGTB policy --min 6 --max 8 --oracle 2>&1 | awk '$1+0>=6 {print $5}' | tr '\n' ' ')
[ "$ratios" = "1.00 1.00 1.00 " ] \
  && say "   oracle control: ratio 1.00 at n=6,7,8            ok" \
  || { say "   ORACLE CONTROL GAVE '$ratios', EXPECTED 1.00 1.00 1.00"; fail=1; }

say ""
say "== 13. KQKR: the one endgame here in which Black is armed =="
say "   (signed entries and conversion into KQK and KRK.  Black's ...RxQ leaves"
say "    a bare white king, which White loses, so this table has wins, draws"
say "    and losses -- none of the other four does.)"
out=$($EGTB kqkr -n 5 --verify --brute 2>&1)
echo "$out" | grep -q 'bellman ok, brute ok' \
  && say "   n=5: Bellman re-derivation and unreduced brute force both agree  ok" \
  || { say "   n=5 CROSS-CHECKS FAILED"; echo "$out"; fail=1; }
# The published 8x8 figure.  Nothing in this program was fitted to it.
$EGTB kqkr -n 8 2>&1 | grep -q 'mate in 35' \
  && say "   8x8 deepest win: mate in 35, the published value            ok" \
  || { say "   8x8 DEEPEST WIN IS NOT 35"; fail=1; }
# The move generator and the index, against independent implementations.  The
# brute force needs n^8 entries and stops at n=6, so on larger boards these two
# are the only things covering those components.
$EGTB kqkr --min 4 --max 16 --selfcheck 2>/dev/null | grep -q 'self-check passed' \
  && say "   move generator and index agree with naive versions, n=4..16   ok" \
  || { say "   KQKR SELF-CHECK FAILED"; fail=1; }
# The fortress: rook interposed on the queen's line, all four men in the corner.
# Its depth runs away with the board size -- 26, 30, 37 moves at n = 8, 9, 10 --
# and at n = 16 the position is drawn outright.
for nd in "8 26" "9 30" "10 37"; do
  n=${nd% *}; want=${nd#* }
  $EGTB kqkr -n $n --probe a1,g1,c1,d1 2>/dev/null \
    | grep -q "White mates in $want moves" \
    && say "   fortress wK a1 wQ g1 bK c1 bR d1 at n=$n: mate in $want        ok" \
    || { say "   FORTRESS AT n=$n IS NOT MATE IN $want"; fail=1; }
done

say ""
say "== 14. KQKK: king and queen against TWO black kings =="
say "   (the black kings may stand beside each other but not beside the white"
say "    king, and a mate counts only when both of them are mated at once.)"
out=$($EGTB kqkk --min 4 --max 6 --verify --brute 2>&1)
n_ok=$(echo "$out" | grep -c 'bellman ok, brute ok')
[ "$n_ok" = 3 ] \
  && say "   n=4,5,6: Bellman re-derivation and unreduced brute force agree  ok" \
  || { say "   KQKK CROSS-CHECKS FAILED"; echo "$out"; fail=1; }
$EGTB kqkk --min 4 --max 12 --selfcheck 2>/dev/null | grep -q 'self-check passed' \
  && say "   move generator, and the value as a class function, n=4..12       ok" \
  || { say "   KQKK SELF-CHECK FAILED"; fail=1; }
# A mate: the queen forks both kings from c2 and the white king defends her, so
# ...Kb1xc2 is not available and neither king has a square.
$EGTB kqkk -n 8 --probe c3,c2,a2,b1 2>/dev/null \
  | grep -q 'black is mated -- both kings at once' \
  && say "   wK c3 wQ c2, kings a2 and b1: a double mate                     ok" \
  || { say "   THE DOUBLE MATE IS NOT REPORTED AS ONE"; fail=1; }
# The rule itself: Black has no legal move and one king is in check.  That is
# mate by the ordinary rule and a draw by this one.
$EGTB kqkk -n 8 --probe a1,b1,c1,d1 2>/dev/null \
  | grep -q 'draw -- one king is mated, which does not count' \
  && say "   wK a1 wQ b1, kings c1 and d1: a single mate, so a draw          ok" \
  || { say "   THE SINGLE MATE IS NOT REPORTED AS A DRAW"; fail=1; }
# White wins every legal white-to-move position, at every board size computed.
# The second black king is a liability, not a defence: both kings must be kept
# out of check at once, so the queen always finds a fork.
for n in 8 10 12; do
  $EGTB kqkk -n $n --stats 2>/dev/null | grep -q 'white to move: 100.00% won, 0.00% drawn' \
    && say "   n=$n: every legal white-to-move position is won               ok" \
    || { say "   n=$n HAS WHITE-TO-MOVE DRAWS"; fail=1; }
done
$EGTB kqkk -n 8 2>/dev/null | grep -q 'mate in 7' \
  && say "   8x8 deepest win: mate in 7                                      ok" \
  || { say "   8x8 KQKK DEEPEST WIN IS NOT 7"; fail=1; }
# The other reading of the rule -- Black may stand in check, and only both at
# once is forbidden -- is a different game, and almost entirely drawn.
out=$($EGTB kqkk -n 5 --loose --verify --brute 2>&1)
echo "$out" | grep -q 'bellman ok, brute ok' \
  && say "   loose rules, n=5: both cross-checks agree                       ok" \
  || { say "   LOOSE-RULE CROSS-CHECKS FAILED"; echo "$out"; fail=1; }
$EGTB kqkk -n 8 --loose --stats 2>/dev/null | grep -q 'white to move: 0.01% won' \
  && say "   loose rules, 8x8: White wins 0.01% of positions                 ok" \
  || { say "   LOOSE-RULE 8x8 WIN FRACTION CHANGED"; fail=1; }
say ""
say "== 15. KQKK determinism and file round-trip =="
$EGTB kqkk -n 9 --threads 1 -o "$TMP/kk1.tb" >/dev/null 2>&1
ok=1
for t in 2 3 5 8; do
  $EGTB kqkk -n 9 --threads $t -o "$TMP/kkt.tb" >/dev/null 2>&1
  cmp -s "$TMP/kk1.tb" "$TMP/kkt.tb" || ok=0
done
[ $ok = 1 ] && say "   n=9 identical for 1/2/3/5/8 threads                             ok" \
            || { say "   KQKK OUTPUT IS THREAD-DEPENDENT"; fail=1; }
a=$($EGTB kqkk -f "$TMP/kk1.tb" 2>&1 | grep 'longest win')
b=$($EGTB kqkk -n 9 2>&1 | grep 'deepest white win')
[ -n "$a" ] && say "   a saved table reads back and re-censuses: $a" \
            || { say "   KQKK FILE DID NOT ROUND-TRIP"; fail=1; }
# A loose table must not be readable as a strict one: the rule set is in the
# header, and the census that comes back has to be the loose one.
$EGTB kqkk -n 7 --loose -o "$TMP/kkl.tb" >/dev/null 2>&1
$EGTB kqkk -f "$TMP/kkl.tb" 2>&1 | grep -q 'rules                 loose' \
  && say "   a loose table identifies itself as one when read back           ok" \
  || { say "   THE RULE SET DID NOT SURVIVE THE FILE"; fail=1; }

say ""
say "== 16. KQKK under CAPTURE rules =="
say "   (every king is an ordinary man that captures and can be captured, and a"
say "    player wins by taking all of the opponent's.  No check and no mate;"
say "    both sides can win, so the entries are signed, and the table converts"
say "    into three sub-endgames built under the same rules.)"
# The kings really are on equal ground: a king may stand beside a king, the
# placement is legal for either side to move, and whoever moves captures.
out=$($EGTB kqkk --capture -n 8 --probe a1,h8,b1,d5 2>/dev/null)
echo "$out" | grep -q 'white to move: White wins in 17 plies' \
  && echo "$out" | grep -q 'black to move: BLACK wins in 1 plies' \
  && say "   a black king beside the white king: whoever moves takes it        ok" \
  || { say "   KINGS BESIDE KINGS DO NOT BEHAVE AS EXPECTED"; echo "$out"; fail=1; }
# And a king may stand where the queen bears on it -- illegal under the mating
# rules, ordinary here.
$EGTB kqkk --capture -n 8 --probe a1,d3,d1,d5 2>/dev/null \
  | grep -q 'white to move: White wins in 15 plies' \
  && $EGTB kqkk -n 8 --probe a1,d3,d1,d5 2>/dev/null | grep -q 'white to move: illegal' \
  && say "   both black kings attacked at once: legal here, illegal there      ok" \
  || { say "   THE LEGALITY DIFFERENCE BETWEEN THE RULE SETS CHANGED"; fail=1; }
out=$($EGTB kqkk --capture --min 3 --max 6 --verify --brute 2>&1)
n_ok=$(echo "$out" | grep -c 'bellman ok, brute ok')
[ "$n_ok" = 4 ] \
  && say "   n=3..6: Bellman re-derivation and unreduced brute force agree     ok" \
  || { say "   CAPTURE-RULE CROSS-CHECKS FAILED"; echo "$out"; fail=1; }
# The three sub-endgames are results in their own right, and the whole shape of
# the endgame rests on them.
cap8=$($EGTB kqkk --capture -n 8 --stats 2>&1)
echo "$cap8" | grep -q 'K vs K + K   black to move: 124992 of 124992 are black wins' \
  && say "   K vs K+K: two kings hunt down a lone king, from every position   ok" \
  || { say "   K vs K+K IS NOT A BLACK WIN EVERYWHERE"; fail=1; }
echo "$cap8" | grep -q 'K + Q vs K   white to move: 249984 of 249984 are white wins' \
  && say "   K+Q vs K: with no stalemate, White wins from every position      ok" \
  || { say "   K+Q vs K IS NOT A WHITE WIN EVERYWHERE"; fail=1; }
echo "$cap8" | grep -q 'K vs K       3612 of 4032 placements drawn' \
  && say "   K vs K: drawn except where the kings already touch               ok" \
  || { say "   K vs K CENSUS CHANGED"; fail=1; }
# K vs K + K is a table in its own right, and three squares address it.  Under
# the mating rules this material needs no table -- with no white piece nothing
# can attack anything, so every legal position is drawn -- so this is the only
# rule set that has one.
$EGTB kqkk --capture -n 8 --probe c1,a1,e1 2>/dev/null \
  | grep -q 'black to move: BLACK wins in 33 plies' \
  && say "   K vs K+K probed directly: kings a1 and e1 win in 17 moves      ok" \
  || { say "   THE K vs K+K SUB-TABLE IS NOT PROBEABLE"; fail=1; }

# K vs K + K has a critical board size, and it is between 14 and 15: up to
# 14x14 two kings win from every placement, at 15x15 only 7% of them, and the
# deepest win drops from 62 moves to 37 and stays there.  Cheap to check --
# it is a three-man endgame, seconds a board.
kv=$($EGTB kqkk --capture --kvkk --min 14 --max 15 2>&1)
echo "$kv" | grep -q ' 14 .* 100.0% .* 123 ply .*black wins everywhere' \
  && say "   K vs K+K at n=14: black wins everywhere, deepest 123 plies      ok" \
  || { say "   n=14 IS NOT WON EVERYWHERE"; echo "$kv"; fail=1; }
echo "$kv" | grep -q ' 15 .* 7.0% .* 73 ply .*THE HUNT FAILS' \
  && say "   K vs K+K at n=15: the hunt fails, 7.0% left, deepest 73 plies   ok" \
  || { say "   THE n=15 TRANSITION IS GONE"; echo "$kv"; fail=1; }

# The one-king theorem: with one king a side these rules are chess with the
# stalemate clause replaced.  Checked against the ordinary KQK table, which this
# program builds with a different solver -- every chess win stays a win, every
# chess loss stays a loss, and every chess mate *and* every chess stalemate has
# capture value exactly -2, the king falling on the ply after next.
out=$($EGTB kqkk --capture --theorem --min 3 --max 8 2>&1)
echo "$out" | grep -q 'theorem check passed' \
  && say "   one-king theorem holds against the ordinary KQK table, n=3..8   ok" \
  || { say "   ONE-KING THEOREM VIOLATED"; echo "$out"; fail=1; }
# and its three counts at 8x8 must be the ordinary KQK census, man for man
echo "$out" | grep -q '364        872' \
  && say "   8x8: 364 mates and 872 stalemates, the KQK census exactly        ok" \
  || { say "   THE THEOREM CHECK'S COUNTS ARE NOT THE KQK CENSUS"; fail=1; }
echo "$out" | grep -q 'chess draws: 22176 still drawn, 0 now lost by the mover, 0 now won by it' \
  && say "   8x8: the 22176 queen-en-prise draws stay draws, none drifts      ok" \
  || { say "   THE CHESS DRAWS DRIFTED"; fail=1; }

# A fork now wins a king rather than the game: White must still convert.
$EGTB kqkk --capture -n 8 --probe a1,d4,d2,f2 2>/dev/null \
  | grep -q 'white to move: White wins in 13 plies' \
  && say "   the open-board fork wins a king, then needs 13 plies in all      ok" \
  || { say "   THE FORK VALUE CHANGED"; fail=1; }
# The queen is not expendable: whoever moves first here decides the game.
out=$($EGTB kqkk --capture -n 8 --probe a1,h1,g1,a8 2>/dev/null)
echo "$out" | grep -q 'white to move: White wins in 11 plies' \
  && echo "$out" | grep -q 'black to move: BLACK wins in 35 plies' \
  && say "   wQ h1 beside a king: White wins with the move, Black without     ok" \
  || { say "   THE TEMPO POSITION CHANGED"; echo "$out"; fail=1; }
# Zugzwang: nothing hanging, White to move, and already lost -- his king is
# sealed in the corner by two kings that defend each other.
$EGTB kqkk --capture -n 8 --probe a1,h3,c1,c2 2>/dev/null \
  | grep -q 'white to move: BLACK wins in 4 plies' \
  && say "   wK a1 wQ h3 against kings c1 and c2: White is in zugzwang        ok" \
  || { say "   THE ZUGZWANG POSITION CHANGED"; fail=1; }
$EGTB kqkk --capture -n 8 --single 0 2>/dev/null | grep -q '48 such placements in all' \
  && say "   48 quiet placements in all have White to move and lost           ok" \
  || { say "   THE COUNT OF QUIET LOST PLACEMENTS CHANGED"; fail=1; }
# File round-trip: the four tables come back and re-censusing gives the same.
$EGTB kqkk --capture -n 7 -o "$TMP/cap7.cap" >/dev/null 2>&1
a=$($EGTB kqkk --capture -f "$TMP/cap7.cap" 2>&1 | grep 'deepest white win [0-9]')
b=$($EGTB kqkk --capture -n 7 --stats 2>&1 | grep 'deepest white win [0-9]')
[ -n "$a" ] && [ "$a" = "$b" ] \
  && say "   a saved capture table reads back identically                     ok" \
  || { say "   CAPTURE FILE DID NOT ROUND-TRIP"; fail=1; }

say ""
say "== 17. KNNK and KNNNK: two knights, and three =="
say "   (two knights cannot FORCE mate but can mate, so KNNK is not uniformly"
say "    drawn -- which is why KNNNK cannot score a knight capture as a draw"
say "    and has to convert into the KNNK table instead.)"

# The fact the whole design turns on: KNK holds no mate at all, so KNNK really
# does satisfy the solver's capture invariant, while KNNK holds 120 of them on
# 8x8, so KNNNK does not.
out=$($EGTB gen -n 8 --endgame knnk 2>&1)
echo "$out" | grep -qE '^ *mate +120 ' \
  && say "   KNNK has 120 mates on 8x8: a knight capture is NOT a free draw   ok" \
  || { say "   KNNK MATE COUNT WRONG ON 8x8"; echo "$out" | grep mate; fail=1; }

# Two knights win only where they mate on the move: there is no zugzwang in
# KNNK, so the induction stops after one ply on every board size.
for n in 6 8 10; do
  out=$($EGTB gen -n $n --endgame knnk --quiet 2>&1)
  echo "$out" | grep -q "longest win  1 plies" \
    && say "   KNNK n=$n: White wins only by mating on the move             ok" \
    || { say "   KNNK n=$n DEEPER THAN MATE IN 1"; echo "$out" | grep longest; fail=1; }
done

for n in 6 8 10 12; do
  out=$($EGTB gen -n $n --endgame knnk --verify --quiet 2>&1)
  echo "$out" | grep -q "0 mismatches -- table is consistent" \
    && say "   KNNK  n=$n  full verify ok" \
    || { say "   KNNK n=$n FAILED"; echo "$out"; fail=1; }
done

for n in 5 6; do
  $EGTB bruteforce -n $n --endgame knnk 2>&1 | grep -q "0 disagreements" \
    && say "   KNNK  n=$n  agrees with the unreduced solver                  ok" \
    || { say "   KNNK n=$n BRUTE FORCE DISAGREES"; fail=1; }
done

# KNNNK: the conversion has to be exercised by both checkers, so the Bellman
# re-derivation and the unreduced solver each carry their own copy of it.
for n in 5 6 7 8 9 10; do
  out=$($EGTB gen -n $n --endgame knnnk --verify --quiet 2>&1)
  echo "$out" | grep -q "0 mismatches -- table is consistent" \
    && say "   KNNNK n=$n  full verify ok" \
    || { say "   KNNNK n=$n FAILED"; echo "$out"; fail=1; }
done

for n in 4 5 6; do
  $EGTB bruteforce -n $n --endgame knnnk 2>&1 | grep -q "0 disagreements" \
    && say "   KNNNK n=$n  agrees with the unreduced solver                  ok" \
    || { say "   KNNNK n=$n BRUTE FORCE DISAGREES"; fail=1; }
done

# Refusing to solve without the sub-table is the guard that stops a silently
# wrong table being produced if the two-stage build is ever bypassed, so it is
# exercised rather than assumed: --no-sub suppresses the attachment.
out=$($EGTB gen -n 5 --endgame knnnk --no-sub --quiet 2>&1 || true)
echo "$out" | grep -q "needs a 5x5 KNNK table attached" \
  && say "   KNNNK refuses to solve without its KNNK table                    ok" \
  || { say "   KNNNK DID NOT REFUSE TO SOLVE WITHOUT ITS SUB-TABLE"; echo "$out"; fail=1; }

# The quiet three-knight draw of section 9.6, at a size where it is cheap: a
# trapped knight in the corner, nothing attacked, and drawn on every board.
for n in 8 10; do
  out=$($EGTB gen -n $n --endgame knnnk --quiet --probe \
        --wk f5 --wp1 a1 --wp2 e5 --wp3 f6 --bk c3 2>/dev/null | tail -1)
  echo "$out" | grep -q "draw" \
    && say "   quiet wK f5 wN a1 wN e5 wN f6 bK c3 is drawn at n=$n         ok" \
    || { say "   QUIET THREE-KNIGHT DRAW CHANGED AT n=$n"; echo "$out"; fail=1; }
done

# Three knights do NOT win from everywhere, and the draws are overwhelmingly
# positions with a knight hanging -- 94.9% of them against 23.6% of the wins.
out=$($EGTB knnnk -n 8 --draws 2>&1)
echo "$out" | grep -q "1.273%" \
  && say "   KNNNK 8x8: 1.273% of white-to-move placements are drawn         ok" \
  || { say "   KNNNK 8x8 DRAW SHARE CHANGED"; echo "$out"; fail=1; }
echo "$out" | grep -q "draws  loose 1274044 (94.9%)" \
  && say "   KNNNK 8x8: 94.9% of the draws have a knight loose               ok" \
  || { say "   KNNNK 8x8 DRAW CENSUS CHANGED"; echo "$out"; fail=1; }
echo "$out" | grep -q "wins   loose 24589660 (23.6%)" \
  && say "   KNNNK 8x8: only 23.6% of the WINS do, so it is a real contrast  ok" \
  || { say "   KNNNK 8x8 WIN CENSUS CHANGED"; echo "$out"; fail=1; }

say ""
say "== 18. storage is transparent: mapped file vs anonymous memory =="
say "   (--scratch puts the two value arrays in a file so a table larger than"
say "    RAM pages against the disk rather than against swap.  It must not"
say "    change a single byte of the answer.)"
SCR="$TMP/scratch"; mkdir -p "$SCR"
for spec in "kqk 12" "kbnk 8" "knnk 10" "knnnk 8"; do
  set -- $spec; e=$1; n=$2
  $EGTB gen -n $n --endgame $e -o "$TMP/ram.tb"                 --quiet >/dev/null 2>&1
  $EGTB gen -n $n --endgame $e -o "$TMP/disk.tb" --scratch "$SCR" --quiet >/dev/null 2>&1
  cmp -s "$TMP/ram.tb" "$TMP/disk.tb" \
    && say "   $e n=$n: mapped-file table is byte-identical to the in-memory one  ok" \
    || { say "   $e n=$n SCRATCH TABLE DIFFERS"; fail=1; }
done

say ""
say "== 19. KNNK under CAPTURE rules: stalemate becomes a loss =="
say "   (with one king a side the capture rules of section 8 are chess with two"
say "    clauses changed, and the second -- checkmate becomes a draw under total"
say "    immobility -- cannot fire for this material.  So they reduce to exactly"
say "    stalemate-loses, and two knights that cannot force MATE can force it.)"

# The clause relabels exactly the stalemates and nothing else: the mate count
# has to be untouched and the loss count has to equal the chess stalemate count.
cm=$($EGTB gen -n 8 --endgame knnk --quiet 2>/dev/null | sed -n '/whole board/,$p')
cp=$($EGTB gen -n 8 --endgame knnk --capture --quiet 2>/dev/null | sed -n '/whole board/,$p')
m1=$(echo "$cm" | grep -E "^ +mate " | awk '{print $2}')
s1=$(echo "$cm" | grep -E "^ +mate " | awk '{print $4}')
m2=$(echo "$cp" | grep -E "^ +mate " | awk '{print $2}')
s2=$(echo "$cp" | grep -E "^ +mate " | awk '{print $4}')
sl=$(echo "$cp" | grep "stalemate losses" | awk '{print $3}')
[ "$m1" = "$m2" ] && [ "$m1" = "120" ] \
  && say "   8x8: 120 mates under both rules -- the clause creates none      ok" \
  || { say "   MATE COUNT CHANGED UNDER CAPTURE RULES ($m1 vs $m2)"; fail=1; }
[ "$s1" = "$sl" ] && [ "$s2" = "0" ] && [ "$s1" = "3864" ] \
  && say "   8x8: all 3864 chess stalemates become losses, none left over    ok" \
  || { say "   STALEMATE RELABELLING WRONG ($s1 -> $sl, $s2 left)"; fail=1; }

# White wins everything up to 6x6, and the endgame is a win at all -- which the
# ordinary rules make false: there he wins only by mating on the move.
for n in 4 5 6; do
  o=$($EGTB gen -n $n --endgame knnk --capture --quiet 2>/dev/null | sed -n '/whole board/,$p')
  L=$(echo "$o" | grep "^white to move" | awk '{print $5}')
  W=$(echo "$o" | grep "^white to move" | awk '{print $7}')
  [ "$L" = "$W" ] \
    && say "   n=$n: White wins EVERY legal placement under capture rules     ok" \
    || { say "   n=$n NOT WON EVERYWHERE ($W of $L)"; fail=1; }
done

# The transition, both sides of it.
o14=$($EGTB gen -n 14 --endgame knnk --capture --quiet 2>/dev/null)
o15=$($EGTB gen -n 15 --endgame knnk --capture --quiet 2>/dev/null)
echo "$o14" | grep -q "longest win  219 plies" \
  && say "   n=14: deepest capture-rule win is 219 plies                     ok" \
  || { say "   n=14 DEPTH CHANGED"; echo "$o14" | grep longest; fail=1; }
echo "$o15" | grep -q "longest win  97 plies" \
  && say "   n=15: the win collapses, deepest drops to 97 plies              ok" \
  || { say "   n=15 DEPTH CHANGED"; echo "$o15" | grep longest; fail=1; }

# A quiet position -- nothing attacked at all -- carrying the transition on its
# own: mate in 104 at 14x14 and drawn at 15x15, with the same four men.
$EGTB gen -n 14 --endgame knnk --capture -o "$TMP/q14.tb" --quiet >/dev/null 2>&1
$EGTB gen -n 15 --endgame knnk --capture -o "$TMP/q15.tb" --quiet >/dev/null 2>&1
q14=$($EGTB probe -f "$TMP/q14.tb" --wk a1 --wp1 e1 --wp2 c3 --bk c1 2>&1 | tail -1)
q15=$($EGTB probe -f "$TMP/q15.tb" --wk a1 --wp1 e1 --wp2 c3 --bk c1 2>&1 | tail -1)
echo "$q14" | grep -q "mate in 104" \
  && say "   quiet wK a1 wN e1 wN c3 bK c1: mate in 104 at n=14            ok" \
  || { say "   QUIET POSITION VALUE CHANGED AT n=14"; echo "$q14"; fail=1; }
echo "$q15" | grep -q "draw" \
  && say "   the same quiet placement is DRAWN at n=15                     ok" \
  || { say "   QUIET POSITION NOT DRAWN AT n=15"; echo "$q15"; fail=1; }

# KNK under the same rules is NOT uniformly drawn, which is why KNNK converts.
o=$($EGTB gen -n 12 --endgame knk --capture --quiet 2>/dev/null | sed -n '/whole board/,$p')
w=$(echo "$o" | grep "^white to move" | awk '{print $7}')
[ "$w" = "2900" ] \
  && say "   KNK under capture rules: 2900 wins at n=12, so it converts      ok" \
  || { say "   KNK CAPTURE WIN COUNT CHANGED ($w)"; fail=1; }
$EGTB gen -n 12 --endgame knnk --capture --no-sub --quiet >/dev/null 2>&1 \
  && { say "   KNNK CAPTURE SOLVED WITHOUT ITS SUB-TABLE"; fail=1; } \
  || say "   KNNK under capture rules refuses to solve without KNK          ok"

# Both checkers, on both sides of the transition and over the conversion.
for n in 5 6 7 8 9; do
  $EGTB bruteforce -n $n --endgame knnk --capture 2>&1 | grep -q "0 disagreements" \
    && say "   KNNK capture n=$n agrees with the unreduced solver             ok" \
    || { say "   KNNK CAPTURE n=$n BRUTE FORCE DISAGREES"; fail=1; }
done
for n in 12 14 15; do
  $EGTB gen -n $n --endgame knnk --capture --verify --quiet 2>&1 \
    | grep -q "0 mismatches -- table is consistent" \
    && say "   KNNK capture n=$n  full verify ok" \
    || { say "   KNNK CAPTURE n=$n VERIFY FAILED"; fail=1; }
done

say ""
say "== 20. KQKB: the same solver, Black's man a bishop =="
say "   (kqkr.cpp is parameterised by Black's piece.  KQKB is what KQKBB"
say "    converts into when White takes a bishop, so it has to be right"
say "    before the five-man table can be.)"
for n in 4 5; do
  out=$($EGTB kqkr --bishop -n $n --verify --brute 2>&1)
  echo "$out" | grep -q 'bellman ok, brute ok' \
    && say "   n=$n: Bellman re-derivation and unreduced brute force agree      ok" \
    || { say "   KQKB n=$n CROSS-CHECKS FAILED"; echo "$out"; fail=1; }
done
$EGTB kqkr --bishop --min 4 --max 14 --selfcheck 2>/dev/null | grep -q 'self-check passed' \
  && say "   move generator and index agree with naive versions, n=4..14   ok" \
  || { say "   KQKB SELF-CHECK FAILED"; fail=1; }
# Parameterising the solver must not have changed the endgame it was written
# for: these are the same figures section 13 pins down.
$EGTB kqkr -n 8 2>&1 | grep -q 'mate in 35' \
  && say "   KQKR still mates in 35 at 8x8 after the generalisation        ok" \
  || { say "   KQKR REGRESSED UNDER THE GENERALISATION"; fail=1; }
# Under capture rules the same solver runs with one clause changed.  Both
# checkers again, since the terminals are what changed.
for n in 4 5; do
  out=$($EGTB kqkr --bishop --capture -n $n --verify --brute 2>&1)
  echo "$out" | grep -q 'bellman ok, brute ok' \
    && say "   capture rules n=$n: Bellman and brute force agree             ok" \
    || { say "   KQKB CAPTURE n=$n CROSS-CHECKS FAILED"; echo "$out"; fail=1; }
done
# The theorem's other clause -- no chess move and no rule 2 move either, which
# draws -- cannot fire for this material.  The solver checks rather than
# assumes, and warns if it ever does.
$EGTB kqkr --bishop --capture --min 3 --max 10 2>&1 | grep -q 'WARNING' \
  && { say "   TOTALLY IMMOBILE TERMINAL FOUND -- THE THEOREM'S OTHER CLAUSE FIRED"; fail=1; } \
  || say "   no totally immobile terminals, n=3..10, as the theorem needs  ok"
# The stalemates that flip are 2(n-2) of Black and none of White, exactly.
bad=0
for n in 3 5 8 12; do
  want=$(( 2 * (n - 2) ))
  $EGTB kqkr --bishop --capture -n $n 2>/dev/null \
    | grep -q "stalemates scored as losses: $want of Black, 0 of White" || bad=1
done
[ $bad = 0 ] && say "   stalemate losses are 2(n-2) of Black and 0 of White            ok" \
             || { say "   STALEMATE-LOSS COUNT IS NOT 2(n-2)"; fail=1; }
# White acquires losses under capture rules only because ...BxQ leaves K+B vs K,
# which is not a draw there.  From n=7 up there are exactly n-2 of them.
bad=0
for n in 7 10 14; do
  want=$(( n - 2 ))
  got=$($EGTB kqkr --bishop --capture -n $n 2>/dev/null \
        | awk -v nn="$n" '$1 == nn { print $5 }')
  [ "$got" = "$want" ] || bad=1
done
[ $bad = 0 ] && say "   white losses under capture rules are exactly n-2, n>=7        ok" \
             || { say "   WHITE LOSS COUNT UNDER CAPTURE RULES IS NOT n-2"; fail=1; }
# A line must reach the mate, not stop at the conversion into KQK.
$EGTB kqkr --bishop -n 8 --line 2>/dev/null | grep -q 'mate, 16 plies after the capture' \
  && say "   the 8x8 deepest line runs through KQK to the mate             ok" \
  || { say "   8x8 LINE DOES NOT REACH THE MATE"; fail=1; }

say ""
say "== 21. KQKBB: king and queen against king and TWO bishops =="
say "   (five men, a signed table, and two conversions -- KQKB when White"
say "    takes a bishop, KBBK reversed when Black takes the queen.  Black can"
say "    mate here, so the table has losses as well as wins and draws.)"
for n in 3 4; do
  out=$($EGTB kqkbb -n $n --verify --brute 2>&1)
  echo "$out" | grep -q 'bellman ok, brute ok' \
    && say "   n=$n: Bellman re-derivation and unreduced brute force agree      ok" \
    || { say "   KQKBB n=$n CROSS-CHECKS FAILED"; echo "$out"; fail=1; }
done
# n = 5 is 9.8 million unreduced placements against 472 500 canonical slots:
# the strongest statement available that the bishop-pair index is right.
out=$($EGTB kqkbb -n 5 --verify --brute 2>&1)
echo "$out" | grep -q 'bellman ok, brute ok' \
  && say "   n=5: 9.8M placements reduce to 472500 slots with no disagreement ok" \
  || { say "   KQKBB n=5 CROSS-CHECKS FAILED"; echo "$out"; fail=1; }
# The brute force needs n^10 entries and stops at n = 5, so above that these
# two are the only things covering the generator and the index.
$EGTB kqkbb --min 4 --max 12 --selfcheck 2>/dev/null | grep -q 'self-check passed' \
  && say "   move generator and index agree with naive versions, n=4..12   ok" \
  || { say "   KQKBB SELF-CHECK FAILED"; fail=1; }
for n in 6 7; do
  $EGTB kqkbb -n $n --verify 2>&1 | grep -q 'bellman ok' \
    && say "   n=$n  full Bellman re-derivation ok" \
    || { say "   KQKBB n=$n VERIFY FAILED"; fail=1; }
done
# Both bishops on one colour can never mate, so every such position is a draw
# or a white win -- never a black one.  The table computes that rather than
# assuming it, which makes it a real check on the conversion into KBBK.
$EGTB kqkbb -n 6 --probe a1,c3,f6,e5,d6 2>/dev/null \
  | grep -q 'white to move: draw' \
  && say "   same-coloured bishops cannot win: a sample position is drawn  ok" \
  || { say "   SAME-COLOURED BISHOP POSITION IS NOT DRAWN"; fail=1; }
# Thread-count independence, as for every other table here.
a=$($EGTB kqkbb -n 6 --threads 1 2>&1 | grep 'deepest white win')
b=$($EGTB kqkbb -n 6 --threads 5 2>&1 | grep 'deepest white win')
[ "$a" = "$b" ] && say "   1 and 5 threads give the same deepest win                     ok" \
                || { say "   KQKBB OUTPUT IS THREAD-DEPENDENT"; fail=1; }

say ""
[ $fail = 0 ] && say "ALL TESTS PASSED" || say "FAILURES PRESENT"
exit $fail
