// main.ts is mend, the CLI SPEC.md specifies (MIT). It does all of SPEC.md: the command line, the output and exit
// codes, safe paths, format detection, line matching at three tiers (section 5), unified diffs (section 6),
// SEARCH/REPLACE blocks (section 7), V4A patches (section 8), JSON edits (section 9) and the all-or-nothing
// write (section 10). Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file's lines under section 3: its line break, its lines, whether it ends with a line break. */
interface FileState {
  br: string;
  lines: string[];
  final: boolean;
}

function splitFile(text: string): FileState {
  if (text === '') return { br: '\n', lines: [], final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const final = text.endsWith(br);
  const parts = text.split(br);
  if (final) parts.pop();
  return { br, lines: parts, final };
}

function joinFile(s: FileState): string {
  if (s.lines.length === 0) return '';
  return s.lines.join(s.br) + (s.final ? s.br : '');
}

/** Section 5: line equality at one tier (0 exact, 1 trailing spaces/tabs off, 2 both sides off). */
const trail = (s: string): string => s.replace(/[ \t]+$/, '');
const both = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const lead = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
};

function eqTier(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return trail(a) === trail(b);
  return both(a) === both(b);
}

/** Every 0-based position at or after `from` where O occurs in `lines` at `tier`. */
function occurrences(lines: string[], o: string[], from: number, tier: number): number[] {
  const out: number[] = [];
  const start = Math.max(0, from);
  for (let i = start; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!eqTier(lines[i + j]!, o[j]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier (0, 1, 2; only 0 when strict) at which O occurs at or after `from`, with its positions. */
function findOcc(lines: string[], o: string[], from: number, strict: boolean): { tier: number; pos: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const pos = occurrences(lines, o, from, t);
    if (pos.length > 0) return { tier: t, pos };
  }
  return null;
}

/** One line of an edit's old (O) or new (N) side; ctx lines are also in the other side. */
interface PLine {
  text: string;
  ctx: boolean;
}

/**
 * Build the lines that replace a matched occurrence: context lines are written as the file's own matched lines;
 * at tier 2 every other line of N is re-indented (the leading spaces/tabs P of O's first line replaced by F,
 * the file's first matched line's, where the line starts with P).
 */
function buildReplacement(n: PLine[], o: PLine[], fileLines: string[], pos: number, tier: number): string[] {
  const oCtx: number[] = [];
  o.forEach((l, i) => {
    if (l.ctx) oCtx.push(i);
  });
  const f = tier === 2 && o.length > 0 ? lead(fileLines[pos]!) : '';
  const p = tier === 2 && o.length > 0 ? lead(o[0]!.text) : '';
  let k = 0;
  return n.map((l) => {
    if (l.ctx) {
      const oi = oCtx[k++]!;
      return fileLines[pos + oi]!;
    }
    if (tier === 2 && l.text !== '' && l.text.trim() !== '' && l.text.startsWith(p)) {
      return f + l.text.slice(p.length);
    }
    return l.text;
  });
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  /** Successful moves, as [old, new] pairs, for the `R` lines of the exit-0 report. */
  readonly moves: Array<[string, string]> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/** Section 6: unified diffs. */

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;
const DIFFGIT_RE = /^diff --git a\/(\S+) b\/(\S+)$/;

interface Hunk {
  /** Old-file start line (1-based) from the hunk header. */
  a: number;
  o: PLine[];
  n: PLine[];
  /** A `\` line follows the hunk's last context or `+` line. */
  noeol: boolean;
  /** A `\` line follows the hunk's last `+` line (for creations). */
  noeolPlus: boolean;
}

interface UniSection {
  hasPair: boolean;
  pairOld: string | null;
  pairNew: string | null;
  renOld: string | null;
  renNew: string | null;
  diffOld: string | null;
  diffNew: string | null;
  create: boolean;
  del: boolean;
  hunks: Hunk[];
}

/** The path of a `--- ` / `+++ ` header line: text after four characters, up to the first tab, trimmed. */
function headerPath(line: string): string | null {
  let t = line.slice(4);
  const tab = t.indexOf('\t');
  if (tab >= 0) t = t.slice(0, tab);
  t = t.trim();
  if (t === '/dev/null') return null;
  if (t.startsWith('a/') || t.startsWith('b/')) t = t.slice(2);
  return t;
}

/** Collect one hunk's body starting at `start`; returns the hunk and the index after the body. */
function collectBody(lines: string[], start: number, a: number): { hunk: Hunk; next: number } {
  const body: string[] = [];
  let j = start;
  while (j < lines.length) {
    const l = lines[j]!;
    if (l.startsWith('diff --git ')) break;
    if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
    if (l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l.startsWith('\\') || l === '') {
      body.push(l);
      j++;
    } else break;
  }
  while (body.length > 0 && body[body.length - 1] === '') body.pop();
  const o: PLine[] = [];
  const n: PLine[] = [];
  let lastCtxOrPlus = -1;
  let lastPlus = -1;
  for (let k = 0; k < body.length; k++) {
    const l = body[k]!;
    if (l.startsWith(' ')) {
      o.push({ text: l.slice(1), ctx: true });
      n.push({ text: l.slice(1), ctx: true });
      lastCtxOrPlus = k;
    } else if (l.startsWith('-')) {
      o.push({ text: l.slice(1), ctx: false });
    } else if (l.startsWith('+')) {
      n.push({ text: l.slice(1), ctx: false });
      lastCtxOrPlus = k;
      lastPlus = k;
    } else if (l === '') {
      o.push({ text: '', ctx: true });
      n.push({ text: '', ctx: true });
      lastCtxOrPlus = k;
    }
  }
  const after = (k: number): boolean => k >= 0 && body[k + 1] !== undefined && body[k + 1]!.startsWith('\\');
  return { hunk: { a, o, n, noeol: after(lastCtxOrPlus), noeolPlus: after(lastPlus) }, next: j };
}

/** Apply one hunk to a file's state; `d` is the section's line offset so far. */
function applyHunk(st: FileState, h: Hunk, d: number, strict: boolean, path: string): void {
  if (h.o.length === 0) {
    const at = Math.min(Math.max(h.a + d, 0), st.lines.length);
    const atEnd = at === st.lines.length;
    st.lines.splice(at, 0, ...h.n.map((l) => l.text));
    if (atEnd) st.final = !h.noeol;
    return;
  }
  const found = findOcc(st.lines, h.o.map((l) => l.text), 0, strict);
  if (found === null) throw new Fail('no-match', path);
  const target = h.a - 1 + d;
  let best = found.pos[0]!;
  let bestDist = Math.abs(best - target);
  for (const p of found.pos) {
    const dist = Math.abs(p - target);
    if (dist < bestDist) {
      best = p;
      bestDist = dist;
    }
  }
  const touchesEof = best + h.o.length === st.lines.length;
  const rep = buildReplacement(h.n, h.o, st.lines, best, found.tier);
  st.lines.splice(best, h.o.length, ...rep);
  if (touchesEof) st.final = !h.noeol;
}

function parseUnified(lines: string[], strict: boolean): Edit[] {
  const sections: UniSection[] = [];
  const fresh = (): UniSection => ({
    hasPair: false,
    pairOld: null,
    pairNew: null,
    renOld: null,
    renNew: null,
    diffOld: null,
    diffNew: null,
    create: false,
    del: false,
    hunks: [],
  });
  let cur: UniSection | null = null;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = DIFFGIT_RE.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      cur = fresh();
      cur.diffOld = m[1]!;
      cur.diffNew = m[2]!;
      sections.push(cur);
      i++;
      continue;
    }
    if (cur === null) {
      if (line.startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
      if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
        cur = fresh();
        cur.hasPair = true;
        cur.pairOld = headerPath(line);
        cur.pairNew = headerPath(lines[i + 1]!);
        sections.push(cur);
        i += 2;
        continue;
      }
      i++;
      continue;
    }
    if (cur.hunks.length === 0) {
      if (line.startsWith('@@')) {
        const m = HUNK_RE.exec(line);
        if (!m) throw new Exit2(`error: parse ${i + 1}`);
        const r = collectBody(lines, i + 1, parseInt(m[1]!, 10));
        cur.hunks.push(r.hunk);
        i = r.next;
        continue;
      }
      if (line.startsWith('--- ')) {
        if (!(lines[i + 1] ?? '').startsWith('+++ ')) throw new Exit2(`error: parse ${i + 2}`);
        if (!cur.hasPair) {
          cur.hasPair = true;
          cur.pairOld = headerPath(line);
          cur.pairNew = headerPath(lines[i + 1]!);
        }
        i += 2;
        continue;
      }
      if (line.startsWith('rename from ')) {
        if (cur.renOld === null) cur.renOld = line.slice(12).trim();
        i++;
        continue;
      }
      if (line.startsWith('rename to ')) {
        if (cur.renNew === null) cur.renNew = line.slice(10).trim();
        i++;
        continue;
      }
      if (line.startsWith('new file mode')) {
        cur.create = true;
        i++;
        continue;
      }
      if (line.startsWith('deleted file mode')) {
        cur.del = true;
        i++;
        continue;
      }
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      const m = HUNK_RE.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const r = collectBody(lines, i + 1, parseInt(m[1]!, 10));
      cur.hunks.push(r.hunk);
      i = r.next;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      cur = fresh();
      cur.hasPair = true;
      cur.pairOld = headerPath(line);
      cur.pairNew = headerPath(lines[i + 1]!);
      sections.push(cur);
      i += 2;
      continue;
    }
    i++;
  }
  return sections.map((sec) => {
    const oldP = sec.hasPair ? sec.pairOld : (sec.renOld ?? sec.diffOld);
    const newP = sec.hasPair ? sec.pairNew : (sec.renNew ?? sec.diffNew);
    const isCreate = sec.create || oldP === null;
    const isDelete = !isCreate && (sec.del || newP === null);
    const isMove = !isCreate && !isDelete && oldP !== null && newP !== null && oldP !== newP;
    if (isCreate) {
      const p = newP ?? '';
      return (tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        const made: string[] = [];
        for (const h of sec.hunks) for (const l of h.n) if (!l.ctx) made.push(l.text);
        let final = true;
        for (let k = sec.hunks.length - 1; k >= 0; k--) {
          if (sec.hunks[k]!.n.some((l) => !l.ctx)) {
            final = !sec.hunks[k]!.noeolPlus;
            break;
          }
        }
        tree.now.set(p, made.length === 0 ? '' : made.join('\n') + (final ? '\n' : ''));
      };
    }
    if (isDelete) {
      const p = oldP ?? '';
      return (tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      };
    }
    if (isMove) {
      const op = oldP!;
      const np = newP!;
      return (tree: Tree) => {
        if (!safe(op)) throw new Fail('unsafe', op);
        if (!safe(np)) throw new Fail('unsafe', np);
        const before = tree.get(op);
        if (before === null) throw new Fail('missing', op);
        if (tree.get(np) !== null) throw new Fail('exists', np);
        const st = splitFile(before);
        let d = 0;
        for (const h of sec.hunks) {
          applyHunk(st, h, d, strict, op);
          d += h.n.length - h.o.length;
        }
        tree.now.set(np, joinFile(st));
        tree.now.set(op, null);
        tree.moves.push([op, np]);
      };
    }
    const p = oldP ?? '';
    return (tree: Tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const st = splitFile(before);
      let d = 0;
      for (const h of sec.hunks) {
        applyHunk(st, h, d, strict, p);
        d += h.n.length - h.o.length;
      }
      tree.now.set(p, joinFile(st));
    };
  });
}

/** Section 7: SEARCH/REPLACE blocks. */

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevReplace = -1;
  let prevPath: string | null = null;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchLine = i;
    let path: string | null = null;
    for (let j = searchLine - 1; j > prevReplace; j--) {
      const l = lines[j]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchLine + 1}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = searchLine + 1; j < n; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    if (eq < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < n; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    const oldLines = lines.slice(searchLine + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    const p = path;
    edits.push((tree: Tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (oldLines.length === 0) {
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
        return;
      }
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const st = splitFile(before);
      const found = findOcc(st.lines, oldLines, 0, strict);
      if (found === null) throw new Fail('no-match', p);
      if (found.pos.length > 1) throw new Fail('ambiguous', p);
      const o: PLine[] = oldLines.map((t) => ({ text: t, ctx: false }));
      const nn: PLine[] = newLines.map((t) => ({ text: t, ctx: false }));
      const repLines = buildReplacement(nn, o, st.lines, found.pos[0]!, found.tier);
      st.lines.splice(found.pos[0]!, oldLines.length, ...repLines);
      tree.now.set(p, joinFile(st));
    });
    prevPath = path;
    prevReplace = rep;
    i = rep + 1;
  }
  return edits;
}

/** Section 8: V4A patches. */

interface VChunk {
  anchor: string | null;
  eof: boolean;
  o: PLine[];
  n: PLine[];
}

function parseV4a(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last >= 0 && blank(lines[last]!)) last--;
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  const isSectionStart = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
  let i = first + 1;
  while (i < last) {
    if (blank(lines[i]!)) {
      i++;
      continue;
    }
    const line = lines[i]!;
    if (!isSectionStart(line)) throw new Exit2(`error: parse ${i + 1}`);
    let j = i + 1;
    while (j < last && !isSectionStart(lines[j]!)) j++;
    let end = j;
    while (end > i + 1 && blank(lines[end - 1]!)) end--;
    const body = lines.slice(i + 1, end);
    if (line.startsWith('*** Add File: ')) {
      const p = line.slice('*** Add File: '.length).trim();
      for (let k = 0; k < body.length; k++) {
        const bl = body[k]!;
        if (!(bl.startsWith('+') || bl === '')) throw new Exit2(`error: parse ${i + 2 + k}`);
      }
      const made = body.map((bl) => (bl.startsWith('+') ? bl.slice(1) : ''));
      edits.push((tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, made.length === 0 ? '' : made.join('\n') + '\n');
      });
    } else if (line.startsWith('*** Delete File: ')) {
      const p = line.slice('*** Delete File: '.length).trim();
      for (let k = 0; k < body.length; k++) {
        if (!blank(body[k]!)) throw new Exit2(`error: parse ${i + 2 + k}`);
      }
      edits.push((tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
    } else {
      const p = line.slice('*** Update File: '.length).trim();
      const updateLineNo = i + 1;
      const baseIdx = i + 1;
      let moveTo: string | null = null;
      let k = 0;
      if (body.length > 0 && body[0]!.startsWith('*** Move to: ')) {
        moveTo = body[0]!.slice('*** Move to: '.length).trim();
        k = 1;
      }
      const chunks: VChunk[] = [];
      let cur: VChunk | null = null;
      while (k < body.length) {
        const l = body[k]!;
        if (l === '*** End of File') {
          if (cur === null) throw new Exit2(`error: parse ${baseIdx + k + 1}`);
          cur.eof = true;
          cur = null;
          k++;
          continue;
        }
        if (l.startsWith('@@')) {
          const anchor = l.slice(2).trim();
          cur = { anchor: anchor === '' ? null : anchor, eof: false, o: [], n: [] };
          chunks.push(cur);
          k++;
          continue;
        }
        if (l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l === '') {
          if (cur === null) {
            if (chunks.length > 0) throw new Exit2(`error: parse ${baseIdx + k + 1}`);
            cur = { anchor: null, eof: false, o: [], n: [] };
            chunks.push(cur);
          }
          if (l.startsWith(' ')) {
            cur.o.push({ text: l.slice(1), ctx: true });
            cur.n.push({ text: l.slice(1), ctx: true });
          } else if (l.startsWith('-')) {
            cur.o.push({ text: l.slice(1), ctx: false });
          } else if (l.startsWith('+')) {
            cur.n.push({ text: l.slice(1), ctx: false });
          } else {
            cur.o.push({ text: '', ctx: true });
            cur.n.push({ text: '', ctx: true });
          }
          k++;
          continue;
        }
        throw new Exit2(`error: parse ${baseIdx + k + 1}`);
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateLineNo}`);
      const mv = moveTo;
      const chs = chunks;
      edits.push((tree: Tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        const before = tree.get(p);
        if (before === null) throw new Fail('missing', p);
        if (mv !== null) {
          if (!safe(mv)) throw new Fail('unsafe', mv);
          if (tree.get(mv) !== null) throw new Fail('exists', mv);
        }
        const st = splitFile(before);
        let cursor = 0;
        for (const ch of chs) {
          if (ch.anchor !== null) {
            let found: number | null = null;
            const tiers = strict ? [0] : [0, 1, 2];
            for (const t of tiers) {
              for (let q = Math.max(0, cursor); q < st.lines.length; q++) {
                if (eqTier(st.lines[q]!, ch.anchor, t)) {
                  found = q;
                  break;
                }
              }
              if (found !== null) break;
            }
            if (found === null) throw new Fail('no-match', p);
            cursor = found + 1;
          }
          if (ch.o.length === 0) {
            const at = ch.eof ? st.lines.length : cursor;
            const rep = ch.n.map((l) => l.text);
            st.lines.splice(at, 0, ...rep);
            cursor = at + rep.length;
          } else {
            const oText = ch.o.map((l) => l.text);
            const tiers = strict ? [0] : [0, 1, 2];
            let hit: { tier: number; pos: number } | null = null;
            for (const t of tiers) {
              const pos = occurrences(st.lines, oText, cursor, t).filter((pp) => !ch.eof || pp + oText.length === st.lines.length);
              if (pos.length > 0) {
                hit = { tier: t, pos: pos[0]! };
                break;
              }
            }
            if (hit === null) throw new Fail('no-match', p);
            const rep = buildReplacement(ch.n, ch.o, st.lines, hit.pos, hit.tier);
            st.lines.splice(hit.pos, ch.o.length, ...rep);
            cursor = hit.pos + rep.length;
          }
        }
        const out = joinFile(st);
        if (mv !== null) {
          tree.now.set(mv, out);
          tree.now.set(p, null);
          tree.moves.push([p, mv]);
        } else {
          tree.now.set(p, out);
        }
      });
    }
    i = j;
  }
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else edits = parseV4a(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  interface Row {
    key: string;
    text: string;
  }
  const rows: Row[] = [];
  const movedNew = new Set<string>();
  const movedOld = new Set<string>();
  for (const [oldP, newP] of tree.moves) {
    if (tree.original(oldP) !== null && tree.now.get(oldP) === null && tree.original(newP) === null && tree.now.get(newP) !== null) {
      rows.push({ key: newP, text: `R ${oldP} -> ${newP}` });
      movedNew.add(newP);
      movedOld.add(oldP);
    }
  }
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    if (movedNew.has(p) || movedOld.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const outRows = rows.map((r) => r.text);
  if (!check) {
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      if (tree.now.get(p) === null) rmSync(p, { force: true });
    }
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const now = tree.now.get(p)!;
      if (now === null) continue;
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  return { code: 0, out: [...outRows, `ok: ${outRows.length} ${outRows.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
