import os, re, datetime, sys

STORE = "/Volumes/1.75TB/xegtb"
NS = list(range(3, 11))
OUT = "/Users/farshim/xegtb/ENDGAMES-4MAN.md"

present = set()
for f in os.listdir(STORE):
    m = re.match(r'(.+)-n(\d+)\.tb$', f)
    if m:
        present.add((m.group(1), int(m.group(2))))

LET = {"king":"K","queen":"Q","rook":"R","bishop":"B","knight":"N"}
PIECES = ["king","queen","rook","bishop","knight"]

rows = []   # (group, label, cmd, minN, maxN, tbname_or_None)

# A: mating rules, supported
for lbl, cmd in [
    ("KBBK", "./egtb gen -n N --endgame kbbk -o FILE"),
    ("KBNK", "./egtb gen -n N --endgame kbnk -o FILE"),
    ("KNNK", "./egtb gen -n N --endgame knnk -o FILE"),
    ("KQKR", "./egtb kqkr -n N -o FILE"),
    ("KQKB", "./egtb kqkr --bishop -n N -o FILE"),
]:
    rows.append(("A", lbl, cmd, 3, 10, None))
rows.append(("A", "KQKK (strict)", "./egtb kqkk -n N -o FILE", 4, 10, None))
rows.append(("A", "KQKK (loose)",  "./egtb kqkk --loose -n N -o FILE", 4, 10, None))

# B: mating rules, no solver in this binary
for lbl in ["KQQK","KQRK","KQBK","KQNK","KRRK","KRBK","KRNK",
            "KQKQ","KQKN","KRKR","KRKB","KRKN","KBKB","KBKN","KNKN"]:
    rows.append(("B", lbl, "-- no solver in this binary --", None, None, None))

# C: capture rules, shared solver + kqkk
for lbl, cmd in [
    ("KBBK (capture)", "./egtb gen -n N --endgame kbbk --capture -o FILE"),
    ("KBNK (capture)", "./egtb gen -n N --endgame kbnk --capture -o FILE"),
    ("KNNK (capture)", "./egtb gen -n N --endgame knnk --capture -o FILE"),
]:
    rows.append(("C", lbl, cmd, 3, 10, None))
rows.append(("C", "KQKK (capture)", "./egtb kqkk --capture -n N -o FILE", 4, 9, None))

# D: the kings lattice, W+B=4
for (W, B) in [(3,1), (2,2)]:
    for wp in PIECES:
        for bp in PIECES:
            wl, bl = LET[wp], LET[bp]
            tb = wl*W + "v" + bl*B
            lbl = "%s vs %s" % (wl*W, bl*B)
            extra = "" if (wp=="king" and bp=="king") else " --wp %s --bp %s" % (wp, bp)
            cmd = "./egtb kings --white %d --black %d%s --min 3 --max 10 --tb DIR" % (W, B, extra)
            grp = "D" if (wp == "king" or bp == "king") else "E"
            rows.append((grp, lbl, cmd, 3, 10, tb))

def cell(r, n):
    grp, lbl, cmd, lo, hi, tb = r
    if lo is None: return "-"
    if n < lo or n > hi: return "-"
    if tb is None: return "."
    return "x" if (tb, n) in present else "."

GROUPS = {
 "A": ("Mating rules (normal chess) -- generatable here", None),
 "B": ("Mating rules -- 4-man material with no solver in this binary", None),
 "C": ("Capture rules -- shared solver and KQKK", None),
 "D": ("Capture rules -- the lattice with kings on the board (W+B=4)", None),
 "E": ("Capture rules -- KING-LESS: no kings at all, win by capturing every enemy man", None),
}

hdr = " | ".join("n=%d" % n for n in NS)
sep = " | ".join("---" for n in NS)
L = []
L.append("# Four-man endgames on n x n boards, n = 3..10")
L.append("")
L.append("Every endgame with four men on the board, in both rule sets, with the ones")
L.append("already generated and stored on the external HDD marked.")
L.append("")
L.append("- Generated: %s" % datetime.date.today().isoformat())
L.append("- Store scanned: `%s`" % STORE)
L.append("- Regenerate this file: `python3 mk4man.py`")
L.append("")
L.append("Legend: `x` generated and in the store | `.` not generated | `-` outside the")
L.append("supported range, or no solver for it in this binary.")
L.append("")
L.append("Only the `kings` command writes into a `--tb` store, so only section D can be")
L.append("marked `x` by scanning it. Sections A and C are written as single files with")
L.append("`-o FILE` and are tracked separately.")
L.append("")
tot = sum(1 for r in rows for n in NS if cell(r, n) == "x")
cap = sum(1 for r in rows for n in NS if cell(r, n) != "-")
L.append("**Status: %d of %d generatable (endgame, n) pairs are stored.**" % (tot, cap))
L.append("")
L.append("Section E is the king-less set: the same capture rules with no king on the")
L.append("board at all, so the game is won purely by capturing every enemy man. It is")
L.append("the `kings` solver with `--wp/--bp` set to a non-king piece; the solver does")
L.append("not care which man is on the board. Each side's men must all be alike -- 4-man")
L.append("material with two unlike men on one side has no solver here (`mixed` does that,")
L.append("but only 2-vs-1, which is three men).")
L.append("")
for g in ["A","B","C","D","E"]:
    L.append("## %s. %s" % (g, GROUPS[g][0]))
    L.append("")
    L.append("| endgame | %s | command |" % hdr)
    L.append("|" + "---|" * (len(NS) + 2))
    for r in rows:
        if r[0] != g: continue
        cells = " | ".join(cell(r, n) for n in NS)
        L.append("| %s | %s | `%s` |" % (r[1], cells, r[2]))
    L.append("")
open(OUT, "w").write("\n".join(L) + "\n")
print("wrote", OUT)
print("stored pairs:", tot, "of", cap)
