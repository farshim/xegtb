// site.js -- what the three pages share.
//
// index.html is a doorway; chess.html and capture.html are the two rule sets.
// Splitting them was the point: the same men are a different game under each,
// and a single list that interleaved them invited reading a depth from one as
// though it belonged to the other.  Everything below is drawn from the server
// -- /api/coverage enumerates the whole space of materials, /api/families the
// curated ones -- so nothing here needs editing when a configuration is added.

const GLYPH = { K: "♚", Q: "♛", R: "♜", B: "♝", N: "♞" };

function el(id) { return document.getElementById(id); }

function fmtBytes(b) {
  if (b >= 1e12) return (b / 1e12).toFixed(1) + " TB";
  if (b >= 1e9) return (b / 1e9).toFixed(1) + " GB";
  if (b >= 1e6) return (b / 1e6).toFixed(0) + " MB";
  if (b >= 1e3) return (b / 1e3).toFixed(0) + " kB";
  return b + " B";
}

// White's men then Black's, each as glyphs.  Both sides come in as plain
// letters from /api/coverage, so there is nothing to parse.
function glyphs(white, black) {
  const draw = (t, cls) =>
    [...(t || "")].filter(c => GLYPH[c])
      .map(c => `<span class="man ${cls}">${GLYPH[c]}</span>`).join("");
  return draw(white, "w") + ' <span style="opacity:.45">vs</span> ' + draw(black, "b");
}

// One material that has been solved: a row with a link per board size.  A
// mirror says so and says of what: the board it opens is the same endgame
// with the colours the other way round, which is the honest thing to show --
// there is no separate table and pretending otherwise would be inventing one.
// The key the filter matches against.  A material has more written forms than
// the one the label happens to use: "KKK vs N" is also KKKvN, KKKvsN and KKKN
// to anyone typing it, and the label's spaces are the least memorable part of
// it.  So the key carries every spelling with the punctuation squeezed out,
// and the query is squeezed the same way before being compared.
function matchKey(m) {
  const flat = s => (s || "").toLowerCase().replace(/[^a-z0-9]/g, "");
  const w = m.white || "", b = m.black || "";
  return [flat(m.label), flat(w + b), flat(w + "v" + b), flat(w + "vs" + b),
          flat(m.id), flat(m.mirrorOf)].join(" ");
}

function solvedRow(m) {
  return `
    <div class="drow" data-k="${matchKey(m)}">
      <div class="dmat">
        <span class="dglyph">${glyphs(m.white, m.black)}</span>
        <span class="dlabel">${m.label}</span>
        ${m.mirror ? `<span class="tag">${m.mirrorOf} reversed</span>` : ""}
      </div>
      <div class="dsizes">${m.boards.map(n =>
        `<a class="chip" href="board.html?f=${encodeURIComponent(m.id)}&n=${n}">${n}</a>`
      ).join("")}</div>
      <div class="dbytes">${m.men} men</div>
    </div>`;
}

// Render one rule set's page from its coverage, by piece count first.
//
// How many men are on the board is the first thing anyone wants to know: it
// says how big the table is, how hard it was, and where the frontier of what
// has been solved actually lies.  The shape of the endgame -- a bare black
// king, both sides armed, how many kings each side has -- is the second thing,
// and sits as a heading inside each count.
const MEN_NAME = { 2: "Two men", 3: "Three men", 4: "Four men", 5: "Five men",
                   6: "Six men" };

// A material with no table of its own still has a name worth finding.
function labelChip(m) {
  return `<span class="lbl" data-k="${matchKey(m)}">${m.label}</span>`;
}

function renderCoverage(box, d, groupOrder) {
  const counts = [];
  for (const m of d.rows) {
    let c = counts.find(x => x.men === m.men);
    if (!c) counts.push(c = { men: m.men, groups: [] });
    let g = c.groups.find(x => x.name === m.group);
    if (!g) c.groups.push(g = { name: m.group, solved: [], pending: [], none: [], mirrors: 0 });
    if (m.boards.length) g.solved.push(m);
    else if (m.supported) g.pending.push(m);
    else g.none.push(m);
    if (m.mirror) ++g.mirrors;
  }
  counts.sort((a, b) => a.men - b.men);
  for (const c of counts) {
    if (groupOrder)
      c.groups.sort((a, b) => groupOrder.indexOf(a.name) - groupOrder.indexOf(b.name));
    c.solved = c.groups.reduce((a, g) => a + g.solved.length, 0);
    c.total = c.groups.reduce((a, g) => a + g.solved.length + g.pending.length + g.none.length, 0);
    c.boards = c.groups.reduce((a, g) =>
      a + g.solved.reduce((b, m) => b + m.boards.length, 0), 0);
  }

  box.className = "";
  box.innerHTML = counts.map(c => `
    <section class="cov" data-men="${c.men}">
      <h2 class="menhead">${MEN_NAME[c.men] || (c.men + " men")}
        <span class="count">${c.solved.toLocaleString()} of ${c.total.toLocaleString()}
          materials answered &middot; ${c.boards.toLocaleString()} tables</span></h2>
      ${c.groups.map(g => `
        <div class="covgroup">
          <h3>${g.name}</h3>
          <p class="sub">
            ${g.solved.length.toLocaleString()} answered from the drive${
              g.mirrors ? ` (${g.mirrors} a table read with the colours swapped)` : ""} &middot;
            ${g.pending.length.toLocaleString()} solvable but not generated &middot;
            ${g.none.length.toLocaleString()} with no solver here
          </p>
          ${g.solved.length ? `<div class="drows">${g.solved.map(solvedRow).join("")}</div>` : ""}
          ${g.pending.length ? `
            <details class="dgroup">
              <summary>solvable, not yet generated <span class="count">${g.pending.length}</span></summary>
              <p class="labels">${g.pending.map(labelChip).join("")}</p>
            </details>` : ""}
          ${g.none.length ? `
            <details class="dgroup">
              <summary>no solver in this repository <span class="count">${g.none.length}</span></summary>
              <p class="labels">${g.none.map(labelChip).join("")}</p>
            </details>` : ""}
        </div>`).join("")}
    </section>`).join("");
}

// The filter box, shared by both rule-set pages.  It opens every collapsed
// section while it has text in it, so a match cannot hide inside one.
function wireFilter(input, box) {
  input.addEventListener("input", () => {
    // Squeezed the same way the keys are, so that "KKKvN", "KKK v N" and
    // "kkk vs n" are one query.
    const q = input.value.trim().toLowerCase().replace(/[^a-z0-9]/g, "");
    for (const sec of box.querySelectorAll(".cov")) {
      let total = 0;
      for (const grp of sec.querySelectorAll(".covgroup")) {
        let shown = 0;
        // The generated tables and the bare names sitting in the collapsed
        // lists are searched alike: a material with no solver is still an
        // answer to "where is it?", and hiding it behind a fold that the
        // filter cannot open is what made it look absent altogether.
        for (const r of grp.querySelectorAll(".drow, .lbl")) {
          const hit = !q || r.dataset.k.includes(q);
          r.hidden = !hit;
          if (hit) ++shown;
        }
        for (const det of grp.querySelectorAll("details.dgroup")) {
          const inner = det.querySelectorAll(".lbl:not([hidden])").length;
          det.hidden = q !== "" && inner === 0;
          if (q !== "" && inner) det.open = true;
        }
        grp.hidden = q !== "" && shown === 0;
        total += shown;
      }
      sec.hidden = q !== "" && total === 0;
    }
  });
}
