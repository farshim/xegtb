# Build the illustrated summary.  lualatex is required: the chess pieces are
# Unicode glyphs from a system font, which pdflatex cannot reach.
#
# Three passes are needed, not two, and the third is not optional.  Each ply of
# a stepped diagram is an optional-content layer, and ocgx2 records which page
# each layer landed on in the .aux so that the next run can attach it to that
# page's resources.  Stop at two and the record is still the one from the run
# before, so every layer is declared on the page before the one that uses it:
# a conforming viewer cannot resolve them, shows all of a diagram's plies at
# once, and the controls do nothing.  The loop runs until the log stops asking,
# which is what "Rerun to get OCG references right" and the usual cross-
# reference warning both say.
PDF := endgames.pdf
SRC := endgames.tex endgames-preamble.tex stepboard.sty stepboard.lua

all: $(PDF)

$(PDF): $(SRC)
	@set -e; \
	for i in 1 2 3 4 5 6; do \
	  lualatex -interaction=nonstopmode $< >/dev/null; \
	  grep -qE 'Rerun to get|Please rerun|Rerun LaTeX' endgames.log || exit 0; \
	done; \
	rm -f $(PDF); \
	echo "error: endgames.log still asks for a rerun after six passes." >&2; \
	echo "The PDF has been deleted rather than left behind: an unconverged" >&2; \
	echo "build looks complete and has every stepped diagram scrambled." >&2; \
	exit 1

clean:
	rm -f *.aux *.log *.out *.toc

distclean: clean
	rm -f $(PDF)

.PHONY: all clean distclean
