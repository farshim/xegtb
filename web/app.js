// app.js -- the explorer.
//
// All of the chess is on the server.  This draws what /api/position sends back
// and sends a position string back when something is clicked; it never works
// out a move or a value for itself, which is why it does not care which
// endgame is on the board or how many men it has.

const GLYPH = { K: "♚", Q: "♛", R: "♜", B: "♝", N: "♞" };

const el = id => document.getElementById(id);
const params = new URLSearchParams(location.search);

const state = {
  family: params.get("f") || "kqk",
  n: parseInt(params.get("n") || "8", 10),
  pos: params.get("pos") || "",
  stm: params.get("stm") || "w",
  data: null,        // the last /api/position payload
  history: [],       // { pos, stm, san, n } before each move played
  selected: null,    // a square the user has clicked a man on
  busy: false,
};

// ---------------------------------------------------------------------------
// Talking to the server.
// ---------------------------------------------------------------------------

function url(extra) {
  const q = new URLSearchParams({ family: state.family, n: String(state.n) });
  if (extra && extra.pos) { q.set("pos", extra.pos); q.set("stm", extra.stm); }
  return "api/position?" + q.toString();
}

async function load(opts) {
  opts = opts || {};
  state.busy = true;
  state.selected = null;
  // "looking up", not "solving".  With a store behind the server almost every
  // board is read off the drive -- NNN vs BB on 12 x 12 answers in half a
  // second from six mapped tables -- and a page that says it is solving while
  // it reads is telling the reader the opposite of what happened.  What it
  // actually did is not knowable until the answer comes back, so the wait is
  // described neutrally and the truth is reported afterwards, from the
  // server's own account of where the tables came from.
  setStatus(opts.building || "looking up the position", true);
  try {
    const r = await fetch(url(opts.fresh ? null : { pos: state.pos, stm: state.stm }));
    const d = await r.json();
    if (d.error) { setStatus(d.error, false, true); state.busy = false; return; }
    state.data = d;
    state.n = d.n;
    state.pos = d.pos;
    state.stm = d.stm;
    render();
    setStatus([d.source, d.note].filter(x => x).join(" -- "));
    pushUrl();
  } catch (e) {
    setStatus("the server did not answer: " + e, false, true);
  }
  state.busy = false;
}

function pushUrl() {
  const q = new URLSearchParams({ f: state.family, n: String(state.n),
                                  pos: state.pos, stm: state.stm });
  history.replaceState(null, "", "?" + q.toString());
}

function setStatus(text, busy, bad) {
  const s = el("status");
  s.textContent = text;
  s.className = "sub" + (busy ? " busy" : "") + (bad ? " err" : "");
}

// ---------------------------------------------------------------------------
// Drawing.
// ---------------------------------------------------------------------------

function render() {
  const d = state.data;

  el("label").textContent = d.label;
  el("title").textContent = d.title + " — " +
      (d.rules === "capture"
        ? "capture rules: every man can be taken, and the game is won by taking the last of them"
        : "mating rules");
  document.title = "xegtb — " + d.label;

  const slider = el("n");
  slider.min = d.minN;
  slider.max = d.maxN;
  slider.value = d.n;
  el("nval").textContent = d.n + " × " + d.n;

  // Which sizes are files and which will be solved on the spot.  The slider
  // spans everything the configuration is defined for, and on a big board the
  // difference between the two is a page that opens and a page that thinks for
  // a minute, so it is worth saying which is which before the click.
  const disk = el("ndisk");
  if (disk) {
    const on = d.onDisk || [];
    if (!on.length) disk.textContent = "";
    else if (on.includes(d.n))
      disk.textContent = "on disk (" + on.join(", ") + ") — opened from the store";
    else
      disk.textContent = "solved here; on disk: " + on.join(", ");
  }

  drawBoard();
  drawVerdict();
  drawMoves();
  drawHistory();

  el("undo").disabled = state.history.length === 0;
  const playable = d.moves.filter(m => m.playable);
  el("best").disabled = d.moves.length === 0;
  el("run").disabled = playable.length === 0;
}

function drawBoard() {
  const d = state.data, n = d.n;
  const board = el("board");
  // 620px of board at most, and never a square so small the glyph vanishes.
  const px = Math.max(20, Math.min(58, Math.floor(620 / n)));
  document.documentElement.style.setProperty("--sq", px + "px");
  board.style.gridTemplateColumns = `repeat(${n}, var(--sq))`;

  const men = new Map();
  for (const m of d.men) men.set(m.f + "," + m.r, m);

  // What clicking would do: the destinations of the man currently selected.
  const targets = new Map();
  if (state.selected !== null)
    for (const mv of d.moves)
      if (mv.playable && mv.ff + "," + mv.fr === state.selected)
        targets.set(mv.tf + "," + mv.tr, mv);

  // Which squares can be picked up at all.
  const pickable = new Set(d.moves.filter(m => m.playable).map(m => m.ff + "," + m.fr));

  const hl = state.lastMove;
  let html = "";
  for (let r = n - 1; r >= 0; --r)
    for (let f = 0; f < n; ++f) {
      const key = f + "," + r;
      const man = men.get(key);
      const cls = ["sq", (f + r) % 2 ? "l" : "d"];
      if (hl && hl.ff === f && hl.fr === r) cls.push("from");
      if (hl && hl.tf === f && hl.tr === r) cls.push("to");
      if (state.selected === key) cls.push("sel");
      if (targets.has(key)) cls.push("pick", man ? "cap" : "");
      else if (pickable.has(key)) cls.push("pick");
      html += `<div class="${cls.join(" ")}" data-sq="${key}">` +
              (targets.has(key) ? '<span class="dot"></span>' : "") +
              (man ? `<span class="man ${man.c}">${GLYPH[man.p] || man.p}</span>` : "") +
              "</div>";
    }
  board.innerHTML = html;

  let ranks = "", files = "";
  for (let r = n - 1; r >= 0; --r) ranks += `<div>${n <= 26 ? r + 1 : r}</div>`;
  for (let f = 0; f < n; ++f) files += `<div>${n <= 26 ? String.fromCharCode(97 + f) : f}</div>`;
  el("ranks").innerHTML = ranks;
  el("ranks").style.gridTemplateRows = `repeat(${n}, var(--sq))`;
  el("files").innerHTML = files;
  el("files").style.gridTemplateColumns = `repeat(${n}, var(--sq))`;
  el("files").style.marginLeft = "22px";
}

function drawVerdict() {
  const d = state.data;
  const v = el("verdict");
  v.className = "verdict " + d.value.kind;
  v.textContent = d.value.text;

  const bits = [];
  bits.push((d.stm === "w" ? "White" : "Black") + " to move");
  bits.push(d.quiet ? "a quiet position: nothing can be taken"
                    : "not quiet: something can be taken");
  if (d.value.terminal) bits.push(d.value.terminal);
  el("detail").textContent = bits.join(" · ");
  el("posline").textContent = d.pos;
}

// How a move's value reads in the list.  A win in no plies at all is the game
// ending on this move, not a mate in zero.
function dtmLabel(v, rules) {
  if (v.mover === "draw") return "draw";
  if (v.plies === 0)
    return v.mover === "win" ? (rules === "capture" ? "wins here" : "mate")
                             : (rules === "capture" ? "loses here" : "mated");
  const sign = v.mover === "win" ? "+" : "−";
  return rules === "capture" ? sign + v.plies + " ply"
                             : sign + "M" + v.moves + " (" + v.plies + " ply)";
}

function drawMoves() {
  const d = state.data;
  const box = el("moves");
  el("moveshead").textContent =
      d.moves.length + (d.moves.length === 1 ? " legal move" : " legal moves")
      + " for " + (d.stm === "w" ? "White" : "Black");

  if (!d.moves.length) {
    box.innerHTML = '<div class="sub" style="padding:4px 10px">' +
        (d.value.terminal || "no legal move from here") + "</div>";
    return;
  }

  const bestPlies = d.moves[0].value.plies;
  const bestKind = d.moves[0].value.mover;
  box.innerHTML = d.moves.map((m, i) => {
    const v = m.value;
    const best = v.mover === bestKind && v.plies === bestPlies;
    const dtm = dtmLabel(v, d.rules);
    const why = m.note ? m.note : "";
    return `<div class="move ${v.mover} ${best ? "best" : ""} ${m.playable ? "" : "dead"}"
                 data-i="${i}">
              <span class="san">${m.san}</span>
              <span class="dtm">${dtm}</span>
              <span class="why">${why}</span>
            </div>`;
  }).join("");
}

function drawHistory() {
  const p = el("histpanel");
  if (!state.history.length) { p.hidden = true; return; }
  p.hidden = false;
  let out = "", no = 1, first = state.history[0];
  // Number the moves as they would be over the board; a line opening with
  // Black still gets its number, as the play-out in the solvers does.
  if (first.stm === "b") out += "1... ";
  for (const h of state.history) {
    if (h.stm === "w") out += `${no}. `;
    out += `<b>${h.san}</b> `;
    if (h.stm === "b") ++no;
  }
  el("hist").innerHTML = out;
}

// ---------------------------------------------------------------------------
// Playing.
// ---------------------------------------------------------------------------

function play(m) {
  if (state.busy || !m.playable) return;
  state.history.push({ pos: state.pos, stm: state.stm, san: m.san });
  state.lastMove = { ff: m.ff, fr: m.fr, tf: m.tf, tr: m.tr };
  state.pos = m.pos;
  state.stm = m.stm;
  load();
}

el("moves").addEventListener("click", ev => {
  const row = ev.target.closest(".move");
  if (!row) return;
  play(state.data.moves[parseInt(row.dataset.i, 10)]);
});

el("moves").addEventListener("mouseover", ev => {
  const row = ev.target.closest(".move");
  if (!row || !state.data) return;
  const m = state.data.moves[parseInt(row.dataset.i, 10)];
  hover(m);
});
el("moves").addEventListener("mouseout", () => hover(null));

function hover(m) {
  const board = el("board");
  board.querySelectorAll(".sq").forEach(sq => { sq.style.outline = ""; });
  if (!m) return;
  const f = board.querySelector(`[data-sq="${m.ff},${m.fr}"]`);
  const t = board.querySelector(`[data-sq="${m.tf},${m.tr}"]`);
  if (f) f.style.outline = "2px solid var(--accent)";
  if (t) t.style.outline = "2px solid var(--accent)";
}

el("board").addEventListener("click", ev => {
  const cell = ev.target.closest(".sq");
  if (!cell || state.busy) return;
  const key = cell.dataset.sq;
  if (state.selected) {
    const m = state.data.moves.find(mv => mv.playable &&
        mv.ff + "," + mv.fr === state.selected && mv.tf + "," + mv.tr === key);
    if (m) { play(m); return; }
  }
  state.selected = (state.selected === key) ? null : key;
  drawBoard();
});

el("undo").addEventListener("click", () => {
  const h = state.history.pop();
  if (!h) return;
  state.pos = h.pos;
  state.stm = h.stm;
  state.lastMove = null;
  load();
});

el("best").addEventListener("click", () => {
  const m = state.data && state.data.moves[0];
  if (!m) return;
  if (!m.playable) { setStatus(m.note || "that move ends the game", false); return; }
  play(m);
});

el("run").addEventListener("click", async () => {
  // Best play by both sides, one request a ply, until the line ends.
  for (let i = 0; i < 400 && !state.busy; ++i) {
    const m = state.data && state.data.moves[0];
    if (!m || !m.playable) break;
    state.history.push({ pos: state.pos, stm: state.stm, san: m.san });
    state.lastMove = { ff: m.ff, fr: m.fr, tf: m.tf, tr: m.tr };
    state.pos = m.pos;
    state.stm = m.stm;
    await load();
    if (!state.data || !state.data.moves.length) break;
    await new Promise(r => setTimeout(r, 90));
  }
});

el("reset").addEventListener("click", () => {
  state.history = [];
  state.lastMove = null;
  state.pos = "";
  load({ fresh: true });
});

el("swap").addEventListener("click", () => {
  state.stm = state.stm === "w" ? "b" : "w";
  state.history = [];
  state.lastMove = null;
  load();
});

el("n").addEventListener("input", ev => {
  el("nval").textContent = ev.target.value + " × " + ev.target.value;
});
el("n").addEventListener("change", ev => {
  // A position means nothing on a board of another size, so this goes back to
  // the opening position of the new board.
  state.n = parseInt(ev.target.value, 10);
  state.pos = "";
  state.history = [];
  state.lastMove = null;
  load({ fresh: true, building: "looking up " + state.n + " × " + state.n });
});

load({ building: "looking up " + state.n + " × " + state.n });
