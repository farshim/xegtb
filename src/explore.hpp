// explore.hpp -- one material-agnostic view of a position, and the per-endgame
// adapters that produce it.
//
// The browser explorer (serve.cpp) knows nothing about any endgame.  It asks a
// configuration for a position, gets back a list of men and a list of moves
// each carrying a value, and draws that.  Everything a family knows about
// itself -- how many men it has, which of them Black owns, what a capture
// converts into, how its entries are encoded -- stops here.
//
// That is deliberate and it is the extension point: adding an endgame to the
// web front end is adding one `Family` row to the catalogue in explore.cpp and
// one `Engine` that fills a `View` and a `std::vector<MoveOut>`.  No HTML, no
// JavaScript and no route changes.  `/api/families` is generated from the
// catalogue, so a new row appears in the browser by itself.
//
// Two conventions hold across every family here, because the front end relies
// on them:
//
//   * A `Val` is always stated from WHITE's point of view, whatever the table's
//     own encoding is -- several of them are relative to the side to move.  The
//     sorting of a move list is the one place the mover's point of view is
//     recovered, and serve.cpp does that itself.
//   * White's men are written with an upper-case letter and Black's with a
//     lower-case one, as the multi-royal endgames already print them: with two
//     black kings on the board `Kd7` would not say whose king moved.
#pragma once

#include <memory>
#include <string>
#include <vector>

#include "geometry.hpp"

namespace kqk {

// A man on the board, in the only terms the front end understands.
struct Man {
    char color = 'w';    // 'w' or 'b'
    char piece = 'K';    // K Q R B N
    Sq   sq    = -1;
};

// A placement and whose turn it is.  The men are in a family-canonical order:
// White's king, White's other men, Black's king, Black's other men.
struct View {
    std::vector<Man> men;
    bool wtm = true;
};

// What the table says, always from White's point of view.
struct Val {
    enum Kind { Illegal, Draw, WhiteWins, BlackWins };
    Kind kind  = Illegal;
    int  plies = 0;          // distance to the end for the winner; 0 for a draw
    std::string text;        // "White wins -- mate in 10 (19 plies)"
    // Set when the position is over, or as good as: "mate", "stalemate",
    // "white wins -- black has no men left", "draw -- insufficient material".
    std::string terminal;
};

struct MoveOut {
    Sq   from = -1, to = -1;
    bool capture = false;
    std::string san;         // "Qd1-d5", "kf7xg6"
    View after;
    Val  val;                // of the position after the move, White-relative
    // False when the move leaves this configuration's lattice altogether --
    // the value is known and shown, but there is nowhere to click through to.
    bool playable = true;
    std::string note;        // "takes the queen: KQK is left, and it is a draw"
};

class Engine {
public:
    virtual ~Engine() = default;

    // Set by the server when the statistics already say there is no White
    // win on this board and the table is too big to be worth scanning for
    // one.  An engine that sees it opens on an arbitrary placement instead of
    // walking the whole mapped table to confirm what the file already said.
    // Without it, BBB vs QQ on 12 x 12 -- a configuration White never wins --
    // spent over twenty minutes proving that before answering.
    mutable bool skipScan = false;

    // How this engine's tables came to exist: "mapped 6 of 6 tables from the
    // store", "solved". Filled in by buildEngine from what the loaders
    // reported, and passed on by /api/position, so that "the website plays
    // this one off the drive" can be checked per configuration instead of
    // being taken on trust.
    std::string source;

    virtual const Geometry& geo() const = 0;
    // "KQK", "KKK vs K", as the catalogue names it.
    virtual std::string material() const = 0;

    // Validate a placement the browser sent back and put its men into this
    // family's canonical order.  False with `err` set when it is not a
    // position of this configuration at all.
    virtual bool accept(View& v, std::string& err) const = 0;

    virtual Val value(const View& v) const = 0;
    virtual std::vector<MoveOut> moves(const View& v) const = 0;
    // Quiet: no capture available to either side, whoever is to move, and
    // nobody in check.  The same predicate the censuses use.
    virtual bool quiet(const View& v) const = 0;

    // The position the explorer opens on.  In order of preference: the deepest
    // win White has from a quiet placement with White to move; failing that
    // the deepest win from any placement; failing that any quiet placement.
    // `note` comes back saying which of the three it is.
    virtual View start(std::string& note) const = 0;
};

// One configuration, as the catalogue lists it and as an id names it.
//
// The id is structured, so that configurations nobody thought to list can
// still be addressed: `kings-3-1-king-king`, `mixed-king-queen-knight`.  The
// catalogue is then a curated set of ids rather than the set of legal ones.
struct Family {
    std::string id;         // "kqk", "kings-3-1-king-king"
    std::string label;      // "KQK", "KKK vs K"
    std::string title;      // "King and queen against king"
    std::string group;      // the heading it sits under in the catalogue
    std::string rules;      // "mate", "capture"
    std::string blurb;      // a sentence for the card
    int minN = 3, maxN = 12, defN = 8;

    // What kind of engine to build, and the parameters it takes.  `arg` is
    // read by the builder alone: the endgame for the shared solver, the man
    // counts and piece kinds for kings and mixed.
    enum Kind { Shared, Kqkr, Kqkbb, Kqkk, KqkkCap, Kings, Mixed, General };
    Kind kind = Shared;
    int  arg[4] = { 0, 0, 0, 0 };
};

// The curated list, in catalogue order.
const std::vector<Family>& familyCatalogue();

// A family by id: the catalogue first, then the structured forms.  Null when
// the id names nothing buildable.  The returned Family is owned by the caller.
bool familyById(const std::string& id, Family& out);

// Where the explorer keeps solved tables between runs.  Empty means it keeps
// none and solves everything in memory, which is what it did before this
// existed and is still the right thing for a directory nobody wants filled.
//
// A store is read first and written second: the file for (family, board) is
// loaded if it is there and can be read, and otherwise the table is solved and
// then written for next time.  A file that fails to load for any reason -- a
// truncated write, a format from another version, a header that disagrees with
// the index this build computes -- is a miss and nothing more; the table is
// solved as if it had not been there.  That is the only safe reading, because
// the alternative is showing a board from a file nobody can vouch for.
struct Store {
    std::string dir;
    // Solving a table that takes no time is not worth a file, and some of
    // these are enormous: KQKBB on 8 x 8 is 238 MB before encoding.  So a
    // table is written only when solving it cost more than this.
    double minSeconds = 2.0;
    bool   rle = true;
};

// The name a configuration's table takes in a store, without a directory:
// "kqk8", "kqkbb7", "kqkkloose12".  Exposed because the catalogue marks which
// boards are already on disk, and the mark has to agree with what the loader
// will actually look for.  Empty when this configuration has no on-disk form.
std::string storeStem(const Family& f, int n);
std::string storeExt(const Family& f);

// What a store actually HOLDS, read from the directory rather than inferred
// from the catalogue.  The two are different things and the difference is the
// point: the catalogue is a curated list of configurations the explorer knows
// how to open, while a store that a sweep has been writing into for days holds
// hundreds of configurations nobody listed, under three different naming
// schemes.  A page that shows only the catalogue is not showing the collection.
//
// The scan is a directory read and one stat per file, and nothing else -- no
// table is opened, no header is parsed, no board is solved.  A name is taken
// at face value: `KKKvNN-n9.tb` is the 3-kings-against-2-knights table on a
// 9 x 9 because that is what kings.cpp calls it.  If the file behind the name
// is corrupt the loader will find that out and treat it as a miss, exactly as
// it does for every other file; listing it here is a claim about the directory,
// not about the bytes.
struct StoreEntry {
    std::string id;         // the family id that opens it, or empty when none does
    std::string label;      // "KKK vs KK"
    std::string title;
    std::string group;      // the heading it sits under
    std::string rules;      // "mate" | "capture"
    std::vector<int> boards;        // board sizes held, ascending
    unsigned long long bytes = 0;   // of this configuration's own files
    int files = 0;
    bool listed = false;    // also in the curated catalogue
};

struct StoreScan {
    std::string dir;
    std::vector<StoreEntry> entries;   // catalogue order first, then discovered
    int filesTotal = 0;                 // every regular file in the directory
    unsigned long long bytesTotal = 0;
};

// Read `dir` and work out what is in it.  An empty directory name, or one that
// cannot be opened, gives an empty scan rather than an error: a store is
// optional everywhere else and it stays optional here.
StoreScan scanStore(const std::string& dir);

// One material of the whole space, listed whether or not anything here can
// solve it.
//
// The catalogue says what the explorer offers and the store says what has been
// computed; neither says what EXISTS.  A reader looking for KRKBB -- king and
// rook against king and two bishops, an ordinary five-man chess endgame --
// found nothing on the page and no way to tell whether it had been overlooked,
// was still being generated, or cannot be solved here at all.  The answer is
// the third, and a page that enumerates the space can say so.
struct MaterialRow {
    std::string white, black;   // piece letters, White's men then Black's
    std::string label;          // "KRKBB", "KKK vs NN"
    std::string id;             // the family that opens it; empty when none can
    std::string group;          // the heading it belongs under
    int  men = 0;
    bool supported = false;     // a solver exists for it
    // Set when the material is this collection's own table read from the
    // other side: KKB -- a bare white king against king and bishop -- is KBK
    // with the colours swapped, and there are no pawns here, so the position
    // is the same position and the table already holds its answer.  Nothing
    // needs solving; only the reading of it is reversed.
    bool mirror = false;
    std::string mirrorOf;       // "KBK", the table it is the reflection of
    std::vector<int> boards;    // the boards on disk, ascending
};

// Every material of at most `maxMen` men under one rule set, in a sensible
// order, each marked with what is known about it.  `scan` fills in the boards.
std::vector<MaterialRow> coverage(bool capture, int maxMen, const StoreScan& scan);

// The boards of one configuration that `dir` holds, which is the same question
// the scan answers for all of them at once.  Separate because a single page
// asking about a single family should not read the whole directory.
std::vector<int> storeBoards(const Family& f, const std::string& dir);

// Builds the tables for one configuration on one board, loading whatever the
// store already holds.  Throws nothing; returns null with `err` set.
std::unique_ptr<Engine> buildEngine(const Family& f, int n, int threads, std::string& err,
                                    const Store& store = Store{});

// `egtb serve`, in serve.cpp: the local web server that puts the above in a
// browser.  Never returns until it is interrupted.
int runServe(int argc, char** argv, int threads);

} // namespace kqk
