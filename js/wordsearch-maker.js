/* Gridleaf Word Search Maker 1.0 (c) 2026 Gridleaf Studio, gridleafstudio.com/word-search-maker/
 * Everything runs in this browser tab: the words, the puzzle and the PDF never leave the visitor's device.
 * The generator is a port of products/puzzles/wordsearch.py: words placed longest first with a preference for
 * overlaps, random filler letters, then a full check of the finished grid in all 8 directions:
 *   - every word appears exactly once (a palindrome read both ways counts as one place);
 *   - no blocked word appears where it uses a random filler letter.
 * PDFs are drawn with pdf-lib (MIT, self-hosted at /js/pdf-lib.min.js, loaded only on the first download).
 * Plain classic script, no build step. Page settings come from window.WSM_CONFIG (written by site/wsmaker.py). */
(function () {
  "use strict";

  var DIRS = [[0, 1], [1, 0], [1, 1], [-1, 1], [0, -1], [-1, 0], [-1, -1], [1, -1]];
  var LEVEL_DIRS = { easy: DIRS.slice(0, 2), medium: DIRS.slice(0, 4), hard: DIRS };
  var LEVEL_TEXT = {
    easy: "Words go across and down.",
    medium: "Words go across, down and diagonally.",
    hard: "Words go across, down and diagonally, forwards and backwards."
  };
  var LETTERS = "AABCDEEEFGHIIJKLMNOOPQRSTTUUVWXYZ";   // a little vowel-heavy so the grid looks natural
  // The same list as products/puzzles/wordsearch.py BLOCK (site/wsmaker.py checks it covers that list). Only checked
  // where a blocked word uses at least one random filler letter, so the visitor's own words never trigger it.
  var BLOCK = [
    "FUCK", "SHIT", "CUNT", "DICK", "COCK", "PISS", "TWAT", "SLUT", "WHORE", "NIGGER", "NIGGA", "BITCH", "PORN",
    "RAPE", "PUSSY", "JIZZ", "WANK", "SPIC", "KIKE", "CHINK", "GOOK", "DYKE", "FAG", "SEX", "CUM", "ASS", "KKK",
    "NAZI", "BOOB", "ANAL", "TITS", "HOMO", "DAMN", "CRAP", "PEE", "POO", "POOP", "TURD", "FART", "BUTT", "PUKE",
    "BARF", "WEE", "JAP", "WOP", "COON", "PAKI", "NIG", "NEGRO", "NIGRA", "JIGABOO", "SAMBO", "DARKIE", "DARKY",
    "PICKANINNY", "WIGGER", "HONKY", "HONKIE", "SPICK", "SPIK", "BEANER", "WETBACK", "DAGO", "WOG", "KRAUT",
    "POLACK", "PIKEY", "GYPO", "GYP", "KYKE", "HEEB", "HYMIE", "YID", "RAGHEAD", "TOWELHEAD", "MUZZIE", "KAFIR",
    "KAFFIR", "COOLIE", "ZIPPERHEAD", "INJUN", "REDSKIN", "SQUAW", "ABBO", "BOONG", "HITLER", "HEIL", "FAGGOT",
    "LESBO", "LEZZIE", "TRANNY", "SHEMALE", "POOFTER", "RETARD", "TARD", "SPAZ", "SPASTIC", "MONG", "TIT", "FUK",
    "FUC", "FCK", "FCUK", "PHUK", "PHUCK", "KUNT", "SHAT", "ARSE", "BASTARD", "BOLLOCKS", "BOLLOX", "BUGGER",
    "TOSSER", "PRICK", "DOUCHE", "DAMMIT", "HELL", "FECK", "MOFO", "WTF", "STFU", "KYS", "PENIS", "SEXY", "NUDE",
    "XXX", "ORGY", "ORGASM", "HORNY", "EROTIC", "MILF", "DILDO", "CLIT", "VAGINA", "VULVA", "SCROTUM", "TESTICLE",
    "SEMEN", "SPERM", "SPUNK", "BONER", "ERECTION", "PUBE", "PUBIC", "NIPPLE", "ANUS", "RECTUM", "HOOKER", "PIMP",
    "SKANK", "THOT", "SLAG", "SHAG", "MINGE", "PECKER", "BLOWJOB", "HANDJOB", "RIMJOB", "JERKOFF", "QUEEF", "SODOMY",
    "PEDO", "PAEDO", "INCEST", "RAPIST", "MOLEST"];
  var SIZES = [10, 12, 15, 18, 20];
  var LP_SIZES = [10, 12, 15];
  var MAX_WORDS = { 10: 10, 12: 15, 15: 22, 18: 30, 20: 36 };
  var MAX_WORDS_LP = { 10: 10, 12: 14, 15: 18 };
  var MIN_LEN = 3;
  var ATTEMPTS = 60;

  // ------------------------------------------------------------------------------------------ helpers
  function rng(seed) {                       // mulberry32: small, fast, seeded
    var a = seed >>> 0;
    return function () {
      a = (a + 0x6D2B79F5) >>> 0;
      var t = a;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  function stripMarks(s) {
    return String(s).normalize("NFD").replace(/[̀-ͯ]/g, "")
      .replace(/ß/g, "SS").replace(/ẞ/g, "SS").replace(/[Ææ]/g, "AE").replace(/[Œœ]/g, "OE")
      .replace(/[Øø]/g, "O").replace(/[Łł]/g, "L").replace(/[Đđ]/g, "D").replace(/[Þþ]/g, "TH");
  }
  function maxWords(size, lp) { return (lp ? MAX_WORDS_LP : MAX_WORDS)[size] || MAX_WORDS[size]; }
  function reverse(s) { return s.split("").reverse().join(""); }
  function dirSet(level) {
    var set = {};
    (LEVEL_DIRS[level] || LEVEL_DIRS.medium).forEach(function (d) { set[d.join(",")] = 1; });
    return set;
  }

  // ------------------------------------------------------------------------------------------ words
  /* Split the visitor's text into words. Returns {words: [{display, key}], issues: [{word, why, dup}]}.
     display = what the word list shows (capitals A-Z, spaces, hyphens, apostrophes); key = the letters hidden in the grid.
     level matters for reversals: Easy and Medium never run backwards, so SAW and WAS (or RAT and STAR) can both stay;
     on Hard one would read as the other backwards, so the later one is left out. */
  function parseWords(text, size, lp, level) {
    var hard = level === "hard";
    var entries = String(text || "").split(/[\n\r,;]+/);
    var words = [], issues = [], seen = {};
    entries.forEach(function (entry) {
      var orig = entry.trim();
      if (!orig) return;
      if (/[0-9]/.test(orig)) {
        issues.push({ word: orig, why: "has numbers, which can't go in the grid: spell them out (Fourth of July, Route Sixty-Six)" });
        return;
      }
      var t = stripMarks(orig).toUpperCase().replace(/[‘’ʼ`]/g, "'").replace(/[‐-―]/g, "-").replace(/&/g, " AND ");
      var display = t.replace(/[^A-Z' -]+/g, "").replace(/\s+/g, " ").replace(/^[ '-]+|[ '-]+$/g, "");
      var key = display.replace(/[^A-Z]/g, "");
      if (!key) { issues.push({ word: orig, why: "has no letters A–Z" }); return; }
      if (key.length < MIN_LEN) { issues.push({ word: orig, why: "is too short (words need 3 letters or more)" }); return; }
      if (key.length > size) { issues.push({ word: orig, why: "is too long for a " + size + " × " + size + " grid (" + key.length + " letters, " + size + " at most)" }); return; }
      if (seen[key]) { issues.push({ word: orig, why: "is already on the list", dup: true }); return; }
      seen[key] = 1;
      words.push({ display: display, key: key, orig: orig });
    });
    // A word inside a longer word would appear twice, so the shorter one is left out. On Hard the same goes for a
    // word inside another one read backwards, and for a word that is another word backwards (the later one goes).
    var byLen = words.slice().sort(function (a, b) { return b.key.length - a.key.length; });   // stable: list order kept
    var drop = {};
    var backNote = ". On Hard, where words also run backwards, it would appear twice: choose Easy or Medium to keep both";
    byLen.forEach(function (w, i) {
      for (var j = 0; j < i; j++) {
        var o = byLen[j];
        if (drop[o.key]) continue;
        var why = "";
        if (o.key.length > w.key.length && o.key.indexOf(w.key) >= 0) why = "is part of " + o.display + ", so it would appear twice";
        else if (hard && o.key.length > w.key.length && reverse(o.key).indexOf(w.key) >= 0) why = "is part of " + o.display + " backwards" + backNote;
        else if (hard && o.key.length === w.key.length && reverse(o.key) === w.key && w.key !== o.key) why = "is " + o.display + " backwards" + backNote;
        if (why) {
          drop[w.key] = 1;
          issues.push({ word: w.orig, why: why });
          break;
        }
      }
    });
    words = words.filter(function (w) { return !drop[w.key]; });
    var cap = maxWords(size, lp);
    if (words.length > cap) {
      words.slice(cap).forEach(function (w) {
        issues.push({ word: w.orig, why: "didn't fit: a " + size + " × " + size + (lp ? " large-print" : "") + " puzzle holds up to " + cap + " words" });
      });
      words = words.slice(0, cap);
    }
    return { words: words, issues: issues };
  }

  // ------------------------------------------------------------------------------------------ grid
  var lineCache = {};
  /* All straight lines through an n × n grid in the 8 directions: {cells: [r * n + c, ...], d: "dr,dc"}. */
  function gridLines(n) {
    if (lineCache[n]) return lineCache[n];
    var out = [];
    for (var r = 0; r < n; r++) for (var c = 0; c < n; c++) DIRS.forEach(function (d) {
      var pr = r - d[0], pc = c - d[1];
      if (pr >= 0 && pr < n && pc >= 0 && pc < n) return;      // not the start of a line in this direction
      var cells = [], rr = r, cc = c;
      while (rr >= 0 && rr < n && cc >= 0 && cc < n) { cells.push(rr * n + cc); rr += d[0]; cc += d[1]; }
      out.push({ cells: cells, d: d.join(",") });
    });
    return (lineCache[n] = out);
  }
  function cellKey(cells) { return cells.slice().sort(function (a, b) { return a - b; }).join(","); }

  /* Every distinct place (set of cells) where `word` can be read, with the directions it reads in there
     (a palindrome reads both ways in one place). [{cells, key, dirs: {"dr,dc": 1}}] */
  function occurrences(grid, n, word, strs) {
    var LN = gridLines(n), found = {}, out = [];
    for (var li = 0; li < LN.length; li++) {
      var s = strs[li], i = s.indexOf(word);
      while (i >= 0) {
        var cells = LN[li].cells.slice(i, i + word.length), k = cellKey(cells);
        if (!found[k]) { found[k] = { cells: cells, key: k, dirs: {} }; out.push(found[k]); }
        found[k].dirs[LN[li].d] = 1;
        i = s.indexOf(word, i + 1);
      }
    }
    return out;
  }
  function inLevel(o, allowed) { return Object.keys(o.dirs).some(function (d) { return allowed[d]; }); }
  function lineStrings(grid, n) {
    return gridLines(n).map(function (ln) { return ln.cells.map(function (i) { return grid[i]; }).join(""); });
  }

  /* Problems in a filled grid: null if clean, false if a second copy of a word can't be repaired, otherwise a list of
     filler-cell groups to re-roll.
     - A copy that uses a random filler letter, in any of the 8 directions, is always re-rolled.
     - A copy made only of puzzle words is fatal if it reads in a direction this level uses. If it reads only in a
       direction the level never uses (SAW backwards inside WAS on Easy or Medium), the solver can't meet it: fine. */
  function problems(grid, n, placed, keys, wordCell, allowed) {
    var strs = lineStrings(grid, n), fixes = [], fatal = false;
    keys.forEach(function (w) {
      var want = cellKey(placed[w]);
      occurrences(grid, n, w, strs).forEach(function (o) {
        if (o.key === want) return;
        var filler = o.cells.filter(function (i) { return !wordCell[i]; });
        if (filler.length) fixes.push(filler);
        else if (inLevel(o, allowed)) fatal = true;
      });
    });
    BLOCK.forEach(function (bad) {
      occurrences(grid, n, bad, strs).forEach(function (o) {
        var filler = o.cells.filter(function (i) { return !wordCell[i]; });
        if (filler.length) fixes.push(filler);
      });
    });
    if (fatal) return false;
    return fixes.length ? fixes : null;
  }

  function tryPlace(keys, n, dirs, R) {
    var grid = new Array(n * n).fill(""), placed = {}, missed = [];
    var order = keys.slice().sort(function (a, b) { return b.length - a.length; });
    order.forEach(function (w) {
      var L = w.length, spots = [];
      for (var r = 0; r < n; r++) for (var c = 0; c < n; c++) for (var di = 0; di < dirs.length; di++) {
        var dr = dirs[di][0], dc = dirs[di][1], er = r + dr * (L - 1), ec = c + dc * (L - 1);
        if (er < 0 || er >= n || ec < 0 || ec >= n) continue;
        var ok = true, ov = 0;
        for (var k = 0; k < L; k++) {
          var ch = grid[(r + dr * k) * n + c + dc * k];
          if (ch === "") continue;
          if (ch !== w[k]) { ok = false; break; }
          ov++;
        }
        if (ok && ov < L) spots.push([ov, R(), r, c, dr, dc]);
      }
      if (!spots.length) { missed.push(w); return; }
      spots.sort(function (a, b) { return (b[0] - a[0]) || (b[1] - a[1]); });
      // prefer some overlap (looks professional) but keep it random
      var top = R() < 0.5 ? spots.slice(0, Math.max(1, Math.floor(spots.length / 6))) : spots;
      var s = top[Math.floor(R() * top.length)], cells = [];
      for (var q = 0; q < L; q++) {
        var idx = (s[2] + s[4] * q) * n + s[3] + s[5] * q;
        grid[idx] = w[q];
        cells.push(idx);
      }
      placed[w] = cells;
    });
    return { grid: grid, placed: placed, missed: missed };
  }

  function fillAndRepair(grid, n, placed, keys, R, allowed) {
    var wordCell = new Uint8Array(n * n);
    keys.forEach(function (w) { placed[w].forEach(function (i) { wordCell[i] = 1; }); });
    var letter = function () { return LETTERS[Math.floor(R() * LETTERS.length)]; };
    for (var i = 0; i < grid.length; i++) if (!grid[i]) grid[i] = letter();
    for (var it = 0; it < 300; it++) {
      var p = problems(grid, n, placed, keys, wordCell, allowed);
      if (p === null) return true;
      if (p === false) return false;
      p.forEach(function (cells) { grid[cells[Math.floor(R() * cells.length)]] = letter(); });
    }
    return false;
  }

  /* Build a puzzle. words: [{display, key}] from parseWords. Same inputs + seed = same puzzle. */
  function generate(words, n, level, seed, attempts) {
    level = LEVEL_DIRS[level] ? level : "medium";
    var R = rng(seed), dirs = LEVEL_DIRS[level], allowed = dirSet(level), keys = words.map(function (w) { return w.key; });
    var best = null;
    for (var a = 0; a < (attempts || ATTEMPTS); a++) {
      var res = tryPlace(keys, n, dirs, R);
      if (best && res.missed.length >= best.missed.length) continue;
      var placedKeys = keys.filter(function (k) { return res.placed[k]; });
      if (!fillAndRepair(res.grid, n, res.placed, placedKeys, R, allowed)) continue;
      res.keys = placedKeys;
      best = res;
      if (!res.missed.length) break;
    }
    if (!best) return null;
    var byKey = {};
    words.forEach(function (w) { byKey[w.key] = w; });
    var list = best.keys.map(function (k) { return byKey[k]; })
      .sort(function (x, y) { return x.display < y.display ? -1 : x.display > y.display ? 1 : 0; });
    var puzzle = {
      n: n, level: level, seed: seed, grid: best.grid, placed: best.placed, words: list,
      missed: best.missed.map(function (k) { return byKey[k]; })
    };
    var errs = verify(puzzle);
    if (errs.length) throw new Error("word search failed verification: " + errs.join("; "));
    return puzzle;
  }

  /* Independent check of a finished puzzle. Returns a list of problems (empty = valid):
     each word reads exactly once in the directions its level uses, at the place it was put; any other reading of it
     (only possible in a direction the level never uses) is made of puzzle words alone, never of filler letters;
     no blocked word uses a filler letter. On Hard every direction is used, so each word reads exactly once, full stop. */
  function verify(p) {
    var n = p.n, errs = [], strs = lineStrings(p.grid, n), wordCell = {};
    var allowed = dirSet(p.level);
    if (p.grid.length !== n * n) errs.push("grid size");
    p.grid.forEach(function (ch, i) { if (!/^[A-Z]$/.test(ch)) errs.push("cell " + i + " is not a letter"); });
    p.words.forEach(function (w) { (p.placed[w.key] || []).forEach(function (i) { wordCell[i] = 1; }); });
    p.words.forEach(function (w) {
      var cells = p.placed[w.key];
      if (!cells) { errs.push(w.key + " not placed"); return; }
      var occ = occurrences(p.grid, n, w.key, strs);
      var seen = occ.filter(function (o) { return inLevel(o, allowed); });
      if (seen.length !== 1) errs.push(w.key + " appears " + seen.length + " times");
      else if (seen[0].key !== cellKey(cells)) errs.push(w.key + " is not where it was placed");
      occ.forEach(function (o) {
        if (!inLevel(o, allowed) && o.cells.some(function (i) { return !wordCell[i]; })) errs.push(w.key + " has a stray copy in the filler letters");
      });
      if (cells.map(function (i) { return p.grid[i]; }).join("") !== w.key) errs.push(w.key + " letters differ");
      var d = [Math.floor(cells[1] / n) - Math.floor(cells[0] / n), cells[1] % n - cells[0] % n].join(",");
      if (!allowed[d]) errs.push(w.key + " runs in a direction this level doesn't use");
    });
    BLOCK.forEach(function (bad) {
      occurrences(p.grid, n, bad, strs).forEach(function (o) {
        if (o.cells.some(function (i) { return !wordCell[i]; })) errs.push("blocked word in the filler letters");
      });
    });
    return errs;
  }

  // ------------------------------------------------------------------------------------------ PDF
  var PAPER = { letter: [612, 792], a4: [595.28, 841.89] };
  var libPromise = null;
  function loadPdfLib() {
    if (window.PDFLib) return Promise.resolve(window.PDFLib);
    if (!libPromise) {
      libPromise = new Promise(function (resolve, reject) {
        var s = document.createElement("script");
        s.src = (window.WSM_CONFIG && window.WSM_CONFIG.pdfLib) || "/js/pdf-lib.min.js";
        s.onload = function () { window.PDFLib ? resolve(window.PDFLib) : reject(new Error("pdf-lib missing")); };
        s.onerror = function () { libPromise = null; reject(new Error("pdf-lib failed to load")); };
        document.head.appendChild(s);
      });
    }
    return libPromise;
  }

  /* Keep only characters the standard Helvetica font can print (accents are dropped if needed). */
  function pdfSafe(text, font) {
    var set = {};
    try { font.getCharacterSet().forEach(function (cp) { set[cp] = 1; }); } catch (e) { set = null; }
    var ok = function (ch) { return set ? set[ch.codePointAt(0)] : /[\x20-\x7E\xA0-\xFF]/.test(ch); };
    var out = "";
    Array.from(String(text).normalize("NFC")).forEach(function (ch) {
      if (ok(ch)) { out += ch; return; }
      var plain = stripMarks(ch);
      if (Array.from(plain).every(ok)) out += plain;
    });
    return out.replace(/\s+/g, " ").trim();
  }

  function drawPage(doc, L, p, o, answer) {
    var size = PAPER[o.paper] || PAPER.letter, W = size[0], H = size[1], M = 40, UW = W - 2 * M;
    var page = doc.addPage([W, H]);
    var ink = L.rgb(47 / 255, 58 / 255, 51 / 255), muted = L.rgb(110 / 255, 120 / 255, 111 / 255), sage = L.rgb(111 / 255, 143 / 255, 122 / 255);
    var reg = o.fonts.reg, bold = o.fonts.bold, lp = o.lp, n = p.n;
    var centered = function (txt, y, font, sz, color) {
      page.drawText(txt, { x: (W - font.widthOfTextAtSize(txt, sz)) / 2, y: y, size: sz, font: font, color: color });
    };
    var y = H - M;
    // title (shrinks to fit the width)
    var title = pdfSafe(o.title, bold) || "Word Search", ts = lp ? 30 : 26;
    while (ts > 12 && bold.widthOfTextAtSize(title, ts) > UW) ts -= 1;
    y -= ts * 0.78;
    centered(title, y, bold, ts, ink);
    y -= ts * 0.62;
    var ss = lp ? 15 : 11.5;
    y -= ss * 1.25;
    var sub = answer ? "Answer key" : "Find all " + p.words.length + " words. " + LEVEL_TEXT[p.level], subF = answer ? bold : reg, ss2 = ss;
    while (ss2 > 8 && subF.widthOfTextAtSize(sub, ss2) > UW) ss2 -= 0.5;
    centered(sub, y, subF, ss2, answer ? ink : muted);
    y -= ss * 1.1;
    if (o.nameLines && !answer) {
      y -= ss * 1.9;
      var nameW = reg.widthOfTextAtSize("Name ", ss), dateW = reg.widthOfTextAtSize("Date ", ss);
      var dateX = M + UW * 0.66;
      page.drawText("Name", { x: M, y: y, size: ss, font: reg, color: muted });
      page.drawLine({ start: { x: M + nameW + 4, y: y - 2 }, end: { x: dateX - 16, y: y - 2 }, thickness: 0.8, color: muted });
      page.drawText("Date", { x: dateX, y: y, size: ss, font: reg, color: muted });
      page.drawLine({ start: { x: dateX + dateW + 4, y: y - 2 }, end: { x: W - M, y: y - 2 }, thickness: 0.8, color: muted });
      y -= ss * 0.6;
    }
    y -= lp ? 14 : 12;
    // word list size: preferred columns, fewer if the longest word doesn't fit, then a smaller font
    var fs = lp ? 16 : 12, cols = lp ? 3 : 4, words = p.words.map(function (w) { return w.display; });
    var font = lp ? bold : reg, box = !answer;
    var itemW = function (sz) {
      return Math.max.apply(null, words.map(function (w) { return font.widthOfTextAtSize(w, sz); })) + (sz * 1.15) + 10;
    };
    while (cols > 2 && itemW(fs) > UW / cols) cols--;
    while (fs > 8 && itemW(fs) > UW / cols) fs -= 0.5;
    var rows = Math.ceil(words.length / cols), step = fs * (lp ? 1.8 : 1.75);
    // grid: as big as the space allows. Below it: frame padding, a gap, the list rows and the last row's descenders.
    var gap = fs * 2.0, below = 8 + gap + (rows - 1) * step + fs * 0.3;
    var gs = Math.min(UW, y - M - below), cell = gs / n;
    var gx = (W - gs) / 2, gTop = y;
    var pad = Math.min(8, cell * 0.3);
    var bx = gx - pad, bw = gs + 2 * pad, rr = 10, k = 0.5523 * rr;
    page.drawSvgPath(
      "M " + rr + " 0 H " + (bw - rr) + " C " + (bw - rr + k) + " 0 " + bw + " " + (rr - k) + " " + bw + " " + rr +
      " V " + (bw - rr) + " C " + bw + " " + (bw - rr + k) + " " + (bw - rr + k) + " " + bw + " " + (bw - rr) + " " + bw +
      " H " + rr + " C " + (rr - k) + " " + bw + " 0 " + (bw - rr + k) + " 0 " + (bw - rr) +
      " V " + rr + " C 0 " + (rr - k) + " " + (rr - k) + " 0 " + rr + " 0 Z",
      { x: bx, y: gTop + pad, borderColor: sage, borderWidth: lp ? 1.6 : 1.2 });
    var cx = function (i) { return gx + (i % n + 0.5) * cell; }, cy = function (i) { return gTop - (Math.floor(i / n) + 0.5) * cell; };
    if (answer) {
      p.words.forEach(function (w) {
        var cells = p.placed[w.key], a = cells[0], b = cells[cells.length - 1];
        page.drawLine({ start: { x: cx(a), y: cy(a) }, end: { x: cx(b), y: cy(b) }, thickness: cell * 0.74,
          color: sage, opacity: 0.38, lineCap: L.LineCapStyle.Round });
      });
    }
    var lf = lp ? bold : reg, lsz = cell * (lp ? 0.6 : 0.56), capH = lsz * 0.718;
    p.grid.forEach(function (ch, i) {
      page.drawText(ch, { x: cx(i) - lf.widthOfTextAtSize(ch, lsz) / 2, y: cy(i) - capH / 2, size: lsz, font: lf, color: ink });
    });
    // word list, column by column, under the grid
    var colW = UW / cols, used = Math.min(UW, cols * Math.min(colW, itemW(fs) + 18)), lx = (W - used) / 2, lw = used / cols;
    var ly = gTop - gs - pad - gap;
    words.forEach(function (w, i) {
      var col = Math.floor(i / rows), row = i % rows, x = lx + col * lw, yy = ly - row * step;
      if (box) {
        var bsz = fs * 0.72;
        page.drawRectangle({ x: x, y: yy - 1, width: bsz, height: bsz, borderColor: muted, borderWidth: 0.8 });
        x += fs * 1.15;
      }
      page.drawText(w, { x: x, y: yy, size: fs, font: font, color: ink });
    });
    return page;
  }

  /* PDF bytes: page 1 the puzzle, page 2 the answer key. o: {title, paper, lp, nameLines} */
  function makePdf(p, o) {
    return loadPdfLib().then(function (L) {
      return L.PDFDocument.create().then(function (doc) {
        return Promise.all([doc.embedFont(L.StandardFonts.Helvetica), doc.embedFont(L.StandardFonts.HelveticaBold)]).then(function (f) {
          var opts = { title: o.title, paper: o.paper, lp: o.lp, nameLines: o.nameLines, fonts: { reg: f[0], bold: f[1] } };
          var t = pdfSafe(o.title, f[1]) || "Word Search";
          doc.setTitle(t + " (word search)");
          doc.setSubject("Word search puzzle and answer key");
          doc.setCreator("Gridleaf Word Search Maker (gridleafstudio.com)");
          doc.setProducer("pdf-lib");
          drawPage(doc, L, p, opts, false);
          drawPage(doc, L, p, opts, true);
          return doc.save();
        });
      });
    });
  }

  function fileName(title, paper) {
    var slug = stripMarks(title || "").toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-+|-+$/g, "").slice(0, 40).replace(/-+$/, "");
    return (slug || "word-search") + (/word-search/.test(slug) ? "" : "-word-search") + "-" + (paper === "a4" ? "a4" : "letter") + ".pdf";
  }

  // ------------------------------------------------------------------------------------------ page UI
  var CFG = window.WSM_CONFIG || {};
  var $ = function (id) { return document.getElementById(id); };
  var el = {};
  var state = { seed: 0, puzzle: null, parsed: null, timer: 0, busy: false };

  function newSeed() {
    try { return crypto.getRandomValues(new Uint32Array(1))[0]; } catch (e) { return Math.floor(Math.random() * 4294967296); }
  }
  function defaultPaper() {
    var lang = (navigator.languages && navigator.languages[0]) || navigator.language || "en-US";
    return /^en$|-(US|CA|MX|PH|CL|CO|VE|GT|CR|PA|DO|PR|SV|NI|HN|BO)$/i.test(lang) ? "letter" : "a4";
  }
  function options() {
    return {
      title: el.title.value.trim() || "Word Search", size: +el.size.value, level: el.level.value,
      lp: el.lp.checked, nameLines: el.name.checked, paper: el.paper.value
    };
  }
  function syncSizes() {
    var lp = el.lp.checked;
    Array.prototype.forEach.call(el.size.options, function (opt) { opt.disabled = lp && LP_SIZES.indexOf(+opt.value) < 0; });
    if (lp && LP_SIZES.indexOf(+el.size.value) < 0) el.size.value = "15";
  }
  function li(text, cls) {
    var x = document.createElement("li");
    x.textContent = text;
    if (cls) x.className = cls;
    return x;
  }

  function renderPreview(p, o) {
    var n = p.n, svgNS = "http://www.w3.org/2000/svg", S = 10 * n + 8;
    var svg = el.svg;
    while (svg.firstChild) svg.removeChild(svg.firstChild);
    svg.setAttribute("viewBox", "-4 -4 " + S + " " + S);
    svg.setAttribute("aria-label", "Preview of the word search: " + n + " by " + n + " letters, " + p.words.length + " words");
    var frame = document.createElementNS(svgNS, "rect");
    [["x", -3], ["y", -3], ["width", 10 * n + 6], ["height", 10 * n + 6], ["rx", 3], ["fill", "#fff"], ["stroke", "#6F8F7A"], ["stroke-width", 0.6]]
      .forEach(function (a) { frame.setAttribute(a[0], a[1]); });
    svg.appendChild(frame);
    var hl = document.createElementNS(svgNS, "g");
    hl.setAttribute("id", "wsm-answers");
    hl.setAttribute("stroke", "#6F8F7A");
    hl.setAttribute("stroke-opacity", "0.38");
    hl.setAttribute("stroke-linecap", "round");
    hl.setAttribute("stroke-width", "7.4");
    if (!el.show.checked) hl.setAttribute("display", "none");
    p.words.forEach(function (w) {
      var c = p.placed[w.key], a = c[0], b = c[c.length - 1], line = document.createElementNS(svgNS, "line");
      line.setAttribute("x1", (a % n) * 10 + 5); line.setAttribute("y1", Math.floor(a / n) * 10 + 5);
      line.setAttribute("x2", (b % n) * 10 + 5); line.setAttribute("y2", Math.floor(b / n) * 10 + 5);
      hl.appendChild(line);
    });
    svg.appendChild(hl);
    var g = document.createElementNS(svgNS, "g");
    g.setAttribute("font-family", "Helvetica, Arial, sans-serif");
    g.setAttribute("font-size", o.lp ? "6.1" : "5.6");
    g.setAttribute("font-weight", o.lp ? "700" : "400");
    g.setAttribute("text-anchor", "middle");
    g.setAttribute("fill", "#2F3A33");
    p.grid.forEach(function (ch, i) {
      var t = document.createElementNS(svgNS, "text");
      t.setAttribute("x", (i % n) * 10 + 5);
      t.setAttribute("y", Math.floor(i / n) * 10 + 5 + (o.lp ? 2.2 : 2.0));
      t.textContent = ch;
      g.appendChild(t);
    });
    svg.appendChild(g);
    el.ptitle.textContent = o.title;
    el.list.innerHTML = "";
    p.words.forEach(function (w) { el.list.appendChild(li(w.display)); });
  }

  function renderStatus(parsed, p) {
    el.status.innerHTML = "";
    var issues = parsed.issues.slice();
    if (p) p.missed.forEach(function (w) {
      issues.push({ word: w.orig, why: "didn't fit in the grid this time: try a bigger grid, fewer words, a harder level (more directions) or New layout" });
    });
    if (p && p.collided) issues.push({ word: p.collided.orig, why: "couldn't be placed without a second copy of a word showing up where the other words cross: try New layout, another size or another level" });
    var head = document.createElement("p");
    if (parsed.words.length && !p) {
      head.textContent = "These words couldn't be made into a puzzle without some of them appearing twice. Try New layout, another size or another level.";
    } else if (!p || !p.words.length) {
      head.textContent = "Add at least one word (3 letters or more) to make a puzzle.";
    } else {
      var total = p.words.length + issues.filter(function (x) { return !x.dup; }).length;   // a repeat isn't a separate word
      head.textContent = total > p.words.length
        ? p.words.length + " of " + total + " words are in the puzzle, each exactly once."
        : "All " + p.words.length + " words are in the puzzle, each exactly once.";
    }
    el.status.appendChild(head);
    if (issues.length) {
      var ul = document.createElement("ul");
      issues.forEach(function (x) { ul.appendChild(li("Left out: " + x.word + " " + x.why + ".")); });
      el.status.appendChild(ul);
    }
  }

  /* A puzzle for these words; if no layout works (some words can only collide), leave out one word at a time,
     last first, and report it. */
  function build(words, o) {
    var p = null;
    try { p = generate(words, o.size, o.level, state.seed); } catch (e) { p = null; }
    for (var i = words.length - 1; !p && i >= 0 && words.length > 1; i--) {
      var rest = words.slice(0, i).concat(words.slice(i + 1));
      try { p = generate(rest, o.size, o.level, state.seed, 12); } catch (e) { p = null; }
      if (p) p.collided = words[i];
    }
    return p;
  }

  function regenerate() {
    clearTimeout(state.timer);
    state.pending = false;
    var o = options();
    syncSizes();
    o.size = +el.size.value;
    var parsed = parseWords(el.words.value, o.size, o.lp, o.level);
    state.parsed = parsed;
    var p = parsed.words.length ? build(parsed.words, o) : null;
    state.puzzle = p;
    el.count.textContent = parsed.words.length + " word" + (parsed.words.length === 1 ? "" : "s") + " · up to " +
      maxWords(o.size, o.lp) + " fit a " + o.size + " × " + o.size + (o.lp ? " large-print" : "") + " puzzle";
    if (p && p.words.length) {
      renderPreview(p, o);
      el.preview.hidden = false;
      el.pdf.disabled = false;
    } else {
      el.preview.hidden = true;
      el.pdf.disabled = true;
    }
    renderStatus(parsed, p);
  }
  function soon() { clearTimeout(state.timer); state.pending = true; state.timer = setTimeout(regenerate, 350); }

  /* Replace the words with a ready-made list (only ever from a button the visitor clicks), with an Undo. */
  function loadList(list) {
    var before = { words: el.words.value, title: el.title.value }, text = list.words.join("\n");
    el.words.value = text;
    if (list.title) el.title.value = list.title;
    state.seed = newSeed();
    regenerate();
    if (before.words.trim() && before.words.trim() !== text) {
      state.undo = before;
      el.undomsg.textContent = "Loaded the " + list.name + " list. ";
      el.undo.hidden = false;
    } else {
      state.undo = null;
      el.undo.hidden = true;
    }
  }
  function undoLoad() {
    if (!state.undo) return;
    el.words.value = state.undo.words;
    el.title.value = state.undo.title;
    state.undo = null;
    el.undo.hidden = true;
    regenerate();
    el.words.focus();
  }

  function download() {
    if (state.pending) regenerate();          // typed just now: use the words on screen, not the last preview
    if (!state.puzzle || state.busy) return;
    var o = options(), label = el.pdf.textContent;
    state.busy = true;
    el.pdf.disabled = true;
    el.pdf.textContent = "Making your PDF…";
    makePdf(state.puzzle, o).then(function (bytes) {
      var blob = new Blob([bytes], { type: "application/pdf" }), a = document.createElement("a");
      a.href = URL.createObjectURL(blob);
      a.download = fileName(o.title, o.paper);
      document.body.appendChild(a);
      a.click();
      setTimeout(function () { URL.revokeObjectURL(a.href); a.remove(); }, 10000);
      el.pdfnote.textContent = "Downloaded " + a.download + ": page 1 is the puzzle, page 2 the answer key. Print at 100% (Actual size).";
    }).catch(function () {
      el.pdfnote.textContent = "Sorry, the PDF couldn't be made. Please reload the page and try again.";
    }).then(function () {
      state.busy = false;
      el.pdf.disabled = !state.puzzle;
      el.pdf.textContent = label;
    });
  }

  function init() {
    if (!$("wsm")) return;
    ["title", "words", "theme", "use", "undo", "undomsg", "undobtn", "size", "level", "lp", "name", "paper", "svg", "show",
      "status", "list", "pdf", "new", "count", "preview", "ptitle", "pdfnote"].forEach(function (k) { el[k] = $("wsm-" + k); });
    var pre = CFG.preset || {};
    el.paper.value = defaultPaper();
    if (pre.size) el.size.value = String(pre.size);
    if (pre.level) el.level.value = pre.level;
    el.lp.checked = !!pre.lp;
    el.name.checked = !!pre.nameLines;
    var lists = CFG.lists || [];
    if (lists.length) { el.words.value = lists[0].words.join("\n"); el.title.value = lists[0].title; }
    // theme menu: this page's lists first, then all themes
    var themes = CFG.themes || [];
    var addGroup = function (label, items, prefix) {
      if (!items.length) return;
      var og = document.createElement("optgroup");
      og.label = label;
      items.forEach(function (t, i) {
        var opt = document.createElement("option");
        opt.value = prefix + i;
        opt.textContent = t.name;
        og.appendChild(opt);
      });
      el.theme.appendChild(og);
    };
    addGroup(CFG.listsLabel || "On this page", lists, "l");
    addGroup("More themes", themes, "t");
    // Choosing in the menu changes nothing by itself (arrow keys fire "change"); the button loads the list.
    var chosen = function () {
      var v = el.theme.value;
      return v ? (v[0] === "l" ? lists : themes)[+v.slice(1)] : null;
    };
    el.theme.addEventListener("change", function () { el.use.disabled = !chosen(); });
    el.use.disabled = true;
    el.use.addEventListener("click", function () { var t = chosen(); if (t) loadList(t); });
    el.undobtn.addEventListener("click", undoLoad);
    Array.prototype.forEach.call(document.querySelectorAll("[data-wsm-list]"), function (b) {
      b.addEventListener("click", function () {
        var t = lists[+b.getAttribute("data-wsm-list")];
        if (t) { loadList(t); el.theme.value = ""; el.use.disabled = true; $("wsm").scrollIntoView({ behavior: "smooth", block: "start" }); }
      });
    });
    el.words.addEventListener("input", function () { state.undo = null; el.undo.hidden = true; soon(); });
    el.title.addEventListener("input", function () { el.ptitle.textContent = el.title.value.trim() || "Word Search"; });
    [el.size, el.level, el.lp].forEach(function (x) { x.addEventListener("change", regenerate); });
    el.show.addEventListener("change", function () {
      var g = $("wsm-answers");
      if (g) { if (el.show.checked) g.removeAttribute("display"); else g.setAttribute("display", "none"); }
    });
    el["new"].addEventListener("click", function () { state.seed = newSeed(); regenerate(); });
    el.pdf.addEventListener("click", download);
    var warm = function () { loadPdfLib().catch(function () {}); };
    el.pdf.addEventListener("pointerenter", warm);
    el.pdf.addEventListener("focus", warm);
    state.seed = CFG.seed || newSeed();
    regenerate();
  }

  window.GLWS = {
    parseWords: parseWords, generate: generate, verify: verify, makePdf: makePdf, fileName: fileName,
    state: state, regenerate: regenerate, SIZES: SIZES, MAX_WORDS: MAX_WORDS, MAX_WORDS_LP: MAX_WORDS_LP, BLOCK: BLOCK
  };
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", init); else init();
})();
