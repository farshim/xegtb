# latexmk defaults to pdflatex, which cannot build this document: the chess men
# are Unicode glyphs from a system font (fontspec) and the diagrams come from an
# embedded Lua module.  Select lualatex instead.
$pdf_mode = 4;          # 4 = lualatex
$postscript_mode = $dvi_mode = 0;
