# The document lives in doc/ and loads endgames-preamble.tex, stepboard.sty and
# stepboard.lua from beside itself.  Building from the repository root works
# only if that directory is on the search path, and only under lualatex.
$pdf_mode = 4;          # 4 = lualatex
$postscript_mode = $dvi_mode = 0;
ensure_path('TEXINPUTS', './doc//');
ensure_path('LUAINPUTS', './doc//');
