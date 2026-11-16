// parse.js — a dependency-free Markdown parser that mirrors marked 18.1.3
// (default options: GFM on, breaks off) byte for byte.
//
// Structure:
//   parse() splits the source into lines and runs a recursive block parser
//   (parseBlocks) that produces a small node tree while collecting link
//   reference definitions into a shared map. Rendering (renderNodes) then
//   walks the tree and runs the inline parser (parseInlineTokens) over
//   paragraph / heading / table-cell text. Because rendering happens after
//   the whole document has been block-parsed, forward references resolve.
//   The inline parser is a single scanner that produces tokens, forms
//   links/images with a bracket stack, and then runs the CommonMark
//   delimiter-stack algorithm for emphasis plus a pairing pass for
//   GFM strikethrough.

// ---------------------------------------------------------------- utilities

const ASCII_PUNCT = new Set('!"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~'.split(''));

function isAsciiPunct(ch) {
  return ch !== undefined && ch.length === 1 && ASCII_PUNCT.has(ch);
}

function isPunctCh(ch) {
  if (ch === undefined) return false;
  if (ch.length === 1 && ch.charCodeAt(0) < 128) return ASCII_PUNCT.has(ch);
  return /[\p{P}\p{S}]/u.test(ch);
}

function isWsCh(ch) {
  if (ch === undefined) return true;
  if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === '\f' || ch === '\v') return true;
  return /\s/.test(ch);
}

// Escape for element content / code: every special char is escaped.
function escapeHtml(s) {
  return s
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

// Escape for double-quoted attribute values (href/title/alt). Like marked,
// an '&' that already introduces an entity-looking sequence is left alone.
const ENTITY_AHEAD = /^(?:#\d{1,7}|#[xX][0-9a-fA-F]{1,6}|[A-Za-z][A-Za-z0-9]*);/;
function escapeAttr(s) {
  let out = '';
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (c === '&') {
      out += ENTITY_AHEAD.test(s.slice(i + 1)) ? '&' : '&amp;';
    } else if (c === '"') out += '&quot;';
    else if (c === "'") out += '&#39;';
    else if (c === '<') out += '&lt;';
    else if (c === '>') out += '&gt;';
    else out += c;
  }
  return out;
}

// marked's cleanUrl: percent-encode like encodeURI, undoing %25 doubling.
function cleanUrl(href) {
  try {
    return encodeURI(href).replace(/%25/g, '%');
  } catch {
    return href;
  }
}

// Remove backslash escapes of ASCII punctuation.
function unescapeStr(s) {
  return s.replace(/\\([!"#$%&'()*+,\-./:;<=>?@\[\\\]^_`{|}~])/g, '$1');
}

function isBlankLine(line) {
  return /^[ \t]*$/.test(line);
}

// Column width of the leading whitespace of a line (tab = to next mult of 4).
function leadCols(line) {
  let col = 0;
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (c === ' ') col += 1;
    else if (c === '\t') col += 4 - (col % 4);
    else break;
  }
  return col;
}

// Remove up to n columns of leading whitespace. A tab straddling the cut is
// replaced by the spaces that remain of it. Assumes the line's leading
// whitespace is at least n columns wide (or the line is blank).
function stripCols(line, n) {
  let col = 0;
  let i = 0;
  while (i < line.length && col < n) {
    const c = line[i];
    if (c === ' ') { col += 1; i += 1; }
    else if (c === '\t') {
      const w = 4 - (col % 4);
      if (col + w <= n) { col += w; i += 1; }
      else return ' '.repeat(col + w - n) + line.slice(i + 1);
    } else break;
  }
  return line.slice(i);
}

// Remove up to n leading whitespace characters (spaces and tabs each
// count as one character, regardless of column width). marked dedents
// backtick-fence content this way: a tab anywhere within the first n
// whitespace characters is dropped whole, with no column remainder.
function stripWsChars(line, n) {
  let i = 0;
  while (i < line.length && i < n && (line[i] === ' ' || line[i] === '\t')) i += 1;
  return line.slice(i);
}

// ------------------------------------------------------- reference handling

function normalizeLabel(s) {
  return s
    .replace(/[ \t\n\r]+/g, ' ')
    .trim()
    .toLowerCase()
    .replace(/ß/g, 'ss')
    .replace(/ς/g, 'σ')
    .replace(/ﬀ/g, 'ff')
    .replace(/ﬁ/g, 'fi')
    .replace(/ﬂ/g, 'fl')
    .replace(/ﬃ/g, 'ffi')
    .replace(/ﬄ/g, 'ffl')
    .replace(/ﬅ/g, 'st')
    .replace(/ﬆ/g, 'st');
}

// Try to parse a link reference definition starting at lines[i].
// Returns { label, href, title, lines } or null.
function tryParseDef(lines, i) {
  if (!/^[ \t]{0,3}\[/.test(lines[i])) return null;
  // Join a few lines: a definition may span several lines (label line,
  // destination on the next line, a title spanning further lines).
  const text = lines.slice(i, i + 10).join('\n');
  let p = 0;
  // Up to 3 columns of indentation.
  let col = 0;
  while (p < text.length && col < 3 && (text[p] === ' ' || text[p] === '\t')) {
    if (text[p] === ' ') col += 1; else col += 4 - (col % 4);
    p += 1;
  }
  if (col > 3) return null;
  if (text[p] !== '[') return null;
  // Label: up to an unescaped ']'; no unescaped '[' inside.
  let j = p + 1;
  let label = '';
  let closed = false;
  while (j < text.length) {
    const c = text[j];
    if (c === '\\' && j + 1 < text.length) { label += c + text[j + 1]; j += 2; continue; }
    if (c === '[') return null;
    if (c === ']') { closed = true; break; }
    label += c; j += 1;
  }
  if (!closed || label.length === 0) return null;
  j += 1; // past ']'
  if (text[j] !== ':') return null;
  j += 1;
  // Whitespace (may include one newline, never a blank line).
  const skipWs = (pos) => {
    let sawNl = false;
    while (pos < text.length) {
      const c = text[pos];
      if (c === ' ' || c === '\t') { pos += 1; continue; }
      if (c === '\n') {
        if (sawNl) {
          // A second newline means a blank line: only allowed if nothing
          // but whitespace sits between the two newlines -> that IS a blank
          // line, so stop and report failure via marker.
          return -1;
        }
        sawNl = true; pos += 1; continue;
      }
      break;
    }
    return pos;
  };
  j = skipWs(j);
  if (j < 0 || j >= text.length) return null;
  // Destination.
  let href;
  if (text[j] === '<') {
    let k = j + 1;
    let dest = '';
    let ok = false;
    while (k < text.length) {
      const c = text[k];
      if (c === '\\' && k + 1 < text.length) { dest += c + text[k + 1]; k += 2; continue; }
      if (c === '>') { ok = true; break; }
      if (c === '<' || c === '\n') return null;
      dest += c; k += 1;
    }
    if (!ok) return null;
    href = unescapeStr(dest);
    j = k + 1;
  } else {
    let k = j;
    let depth = 0;
    let dest = '';
    while (k < text.length) {
      const c = text[k];
      if (c === '\\' && k + 1 < text.length && isAsciiPunct(text[k + 1])) {
        dest += c + text[k + 1]; k += 2; continue;
      }
      if (c === ' ' || c === '\t' || c === '\n' || c === '\r') break;
      if (c < ' ') return null;
      if (c === '(') depth += 1;
      if (c === ')') { if (depth === 0) break; depth -= 1; }
      dest += c; k += 1;
    }
    if (depth !== 0 || dest.length === 0) return null;
    href = unescapeStr(dest);
    j = k;
  }
  const afterDest = j;
  // Optional title: it must be separated from the destination by
  // whitespace, and may sit on a following line.
  const j2 = skipWs(j);
  let title = null;
  let titleEnd = -1;
  let titleBad = false;
  if (j2 > afterDest && j2 < text.length && (text[j2] === '"' || text[j2] === "'" || text[j2] === '(')) {
    const open = text[j2];
    const close = open === '(' ? ')' : open;
    let k = j2 + 1;
    let t = '';
    let ok = false;
    while (k < text.length) {
      const c = text[k];
      if (c === '\\' && k + 1 < text.length) { t += c + text[k + 1]; k += 2; continue; }
      if (c === close) { ok = true; break; }
      if (open === '(' && c === '(') { ok = false; break; }
      if (c === '\n') {
        // A title may span lines but may not cross a blank line.
        let q = k + 1;
        while (q < text.length && (text[q] === ' ' || text[q] === '\t')) q += 1;
        if (q >= text.length || text[q] === '\n') { ok = false; break; }
      }
      t += c; k += 1;
    }
    if (ok) { title = unescapeStr(t); titleEnd = k + 1; }
    else titleBad = true;
  }
  // Was the title attempted on a later line than the destination?
  const titleOnLaterLine = j2 > afterDest && text.slice(afterDest, j2).includes('\n');
  if (titleEnd >= 0) {
    j = titleEnd;
    // After a title only spaces/tabs may follow on the line.
    while (j < text.length && (text[j] === ' ' || text[j] === '\t')) j += 1;
    if (j < text.length && text[j] !== '\n') {
      // Junk after the title: if the title sat on its own line, that line
      // simply is not part of the definition; on the destination's own
      // line the whole definition is malformed.
      if (!titleOnLaterLine) return null;
      title = null;
      titleEnd = -1;
    }
  } else if (titleBad && !titleOnLaterLine) {
    return null;
  }
  if (titleEnd < 0) {
    // No title: after the destination only spaces/tabs may follow.
    j = afterDest;
    while (j < text.length && (text[j] === ' ' || text[j] === '\t')) j += 1;
    if (j < text.length && text[j] !== '\n') return null;
  }
  const consumed = text.slice(0, j);
  const lineCount = consumed.split('\n').length;
  const normLabel = normalizeLabel(label);
  if (normLabel === '') return null;
  return { label: normLabel, href, title, lines: lineCount };
}

// ------------------------------------------------------------ block matchers

const FENCE_RE = /^(`{3,}|~{3,})(.*)$/;
const ATX_RE = /^(#{1,6})(?:[ \t]+(.*)|[ \t]*)$/;
const HR_RE = /^([-*_])(?:[ \t]*\1){2,}[ \t]*$/;
const SETEXT_RE = /^(=+|-+)[ \t]*$/;
const BQ_RE = /^>[ \t]?/;

function matchFence(line) {
  if (leadCols(line) > 3) return null;
  const s = stripCols(line, leadCols(line));
  const m = FENCE_RE.exec(s);
  if (!m) return null;
  const ch = m[1][0];
  const info = m[2];
  if (ch === '`' && info.includes('`')) return null;
  return { ch, len: m[1].length, info: unescapeStr(info.trim()), indent: leadCols(line) };
}

function matchFenceClose(line, ch, len) {
  if (leadCols(line) > 3) return false;
  const s = stripCols(line, leadCols(line));
  const re = ch === '`' ? /^`+[ \t]*$/ : /^~+[ \t]*$/;
  if (!re.test(s)) return false;
  return s.trim().length >= len;
}

function matchATX(line) {
  if (leadCols(line) > 3) return null;
  const s = stripCols(line, leadCols(line));
  const m = ATX_RE.exec(s);
  if (!m) return null;
  let content = m[2] ?? '';
  content = content.replace(/[ \t]+$/, '');
  if (/^#+$/.test(content)) content = '';
  else content = content.replace(/[ \t]+#+$/, '');
  content = content.replace(/[ \t]+$/, '');
  return { level: m[1].length, text: content };
}

function isThematicBreak(line) {
  if (leadCols(line) > 3) return false;
  const s = stripCols(line, leadCols(line));
  return HR_RE.test(s);
}

function isSetextUnderline(line) {
  if (leadCols(line) > 3) return 0;
  const s = stripCols(line, leadCols(line));
  const m = SETEXT_RE.exec(s);
  if (!m) return 0;
  return m[1][0] === '=' ? 1 : 2;
}

const HTML_BLOCK_TAGS = new Set(('address article aside base basefont blockquote body caption center col ' +
  'colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset ' +
  'h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu menuitem nav noframes ol ' +
  'optgroup option p param search section summary table tbody td tfoot th thead title tr track ul').split(' '));

const TAG_NAME_RE = /^[A-Za-z][A-Za-z0-9-]*/;
const ATTR_RE = /^\s+[A-Za-z_:][A-Za-z0-9_.:-]*(?:\s*=\s*(?:[^<>"'=\s]+|'[^']*'|"[^"]*"))?/;

// Match a complete open/close tag starting at s[pos] === '<'.
// Returns the matched string or null. Closing tags may not carry
// attributes (per the CommonMark tag grammar).
function matchTag(s, pos) {
  let p = pos + 1;
  let closing = false;
  if (s[p] === '/') { closing = true; p += 1; }
  const nm = TAG_NAME_RE.exec(s.slice(p));
  if (!nm) return null;
  p += nm[0].length;
  if (closing) {
    p += /^[ \t\n]*/.exec(s.slice(p))[0].length;
    if (s[p] !== '>') return null;
    return s.slice(pos, p + 1);
  }
  let m;
  while ((m = ATTR_RE.exec(s.slice(p))) !== null) p += m[0].length;
  p += /^\s*/.exec(s.slice(p))[0].length;
  if (s[p] === '/') p += 1;
  if (s[p] !== '>') return null;
  return s.slice(pos, p + 1);
}

// Determine the HTML block type starting on this line (indent <= 3).
// Returns { type, tag } or null. Types follow CommonMark 1..7.
function matchHtmlBlock(line) {
  const ind = leadCols(line);
  if (ind > 3) return null;
  const s = stripCols(line, ind);
  if (!s.startsWith('<')) return null;
  let m = /^<(script|pre|style|textarea)(?=[\s>]|$)/i.exec(s);
  if (m) return { type: 1, tag: m[1].toLowerCase() };
  if (s.startsWith('<!--')) return { type: 2 };
  if (s.startsWith('<?')) return { type: 3 };
  if (/^<![A-Za-z]/.test(s)) return { type: 4 };
  if (s.startsWith('<![CDATA[')) return { type: 5 };
  m = /^<\/?([A-Za-z][A-Za-z0-9-]*)(?=[\s/>]|$)/.exec(s);
  if (m && HTML_BLOCK_TAGS.has(m[1].toLowerCase())) return { type: 6 };
  // Type 7: a complete tag alone on the line (plus whitespace).
  const tag = matchTag(s, 0);
  if (tag !== null && /^[ \t]*$/.test(s.slice(tag.length))) {
    const nm = /^<\/?([A-Za-z][A-Za-z0-9-]*)/.exec(tag)[1].toLowerCase();
    if (nm !== 'script' && nm !== 'pre' && nm !== 'style' && nm !== 'textarea') {
      return { type: 7 };
    }
  }
  return null;
}

function htmlBlockEnded(lines, start, type, tag) {
  // Returns index one past the last line of the block.
  let i = start + 1;
  if (type === 6 || type === 7) {
    while (i < lines.length && !isBlankLine(lines[i])) i += 1;
    return i;
  }
  const hasEnd = (txt) => {
    if (type === 1) return new RegExp('</' + tag, 'i').test(txt);
    if (type === 2) return txt.includes('-->');
    if (type === 3) return txt.includes('?>');
    if (type === 4) return txt.includes('>');
    return txt.includes(']]>');
  };
  // Check the first line, ignoring the opening construct itself.
  let first = lines[start];
  if (type === 1) {
    const idx = first.toLowerCase().indexOf('<' + tag);
    first = first.slice(idx + tag.length + 1);
  } else if (type === 2) {
    const s = stripCols(first, leadCols(first));
    if (s.startsWith('<!-->') || s.startsWith('<!--->')) return start + 1;
    first = first.slice(first.indexOf('<!--') + 4);
  }
  if (hasEnd(first)) return start + 1;
  while (i < lines.length) {
    if (hasEnd(lines[i])) return i + 1;
    i += 1;
  }
  return i;
}

// List marker matching with column arithmetic.
// Returns { ordered, bullet, delim, num, contentCol, empty } or null.
function matchListMarker(line) {
  let p = 0;
  let col = 0;
  while (p < line.length && col <= 3 && (line[p] === ' ' || line[p] === '\t')) {
    if (line[p] === ' ') col += 1; else col += 4 - (col % 4);
    p += 1;
  }
  if (col > 3) return null;
  const c = line[p];
  let ordered = false;
  let bullet = null;
  let delim = null;
  let num = null;
  let mlen = 0;
  if (c === '-' || c === '+' || c === '*') {
    bullet = c; mlen = 1;
  } else if (c >= '0' && c <= '9') {
    let q = p;
    let digits = '';
    while (q < line.length && line[q] >= '0' && line[q] <= '9' && digits.length < 10) {
      digits += line[q]; q += 1;
    }
    if (digits.length > 9) return null;
    if (line[q] !== '.' && line[q] !== ')') return null;
    ordered = true; delim = line[q]; num = parseInt(digits, 10);
    mlen = digits.length + 1;
  } else return null;
  const markerEndCol = col + mlen;
  // Following whitespace / end of line.
  let q = p + mlen;
  let wcol = markerEndCol;
  while (q < line.length && (line[q] === ' ' || line[q] === '\t')) {
    if (line[q] === ' ') wcol += 1; else wcol += 4 - (wcol % 4);
    q += 1;
  }
  const w = wcol - markerEndCol;
  if (q >= line.length) {
    // Empty item.
    return { ordered, bullet, delim, num, contentCol: markerEndCol + 1, empty: true };
  }
  if (w === 0) return null;
  const contentCol = w >= 5 ? markerEndCol + 1 : wcol;
  return { ordered, bullet, delim, num, contentCol, empty: false };
}

// Extract a list item's first-line content given its content column.
function contentFromCol(line, contentCol) {
  let p = 0;
  let col = 0;
  while (p < line.length) {
    const c = line[p];
    if (c === ' ') { if (col + 1 > contentCol) break; col += 1; p += 1; continue; }
    if (c === '\t') {
      const w = 4 - (col % 4);
      if (col + w > contentCol) {
        return ' '.repeat(col + w - contentCol) + line.slice(p + 1);
      }
      col += w; p += 1; continue;
    }
    // Non-whitespace: consume it if it ends at or before contentCol.
    if (col >= contentCol) break;
    col += 1; p += 1;
  }
  return line.slice(p);
}

// Container-aware column strip, used for list items and (via bqStrip)
// blockquotes. Like marked, leading whitespace is processed by columns
// with tabs expanded to tab stops: whitespace at or beyond the cut is
// emitted as spaces, while the rest of the line stays byte-identical.
// The caller guarantees the line's leading whitespace reaches contentCol
// (or the line is a list item's first line, whose marker is consumed too).
function contentFromCol2(line, contentCol) {
  let i = 0;
  let col = 0;
  let out = '';
  while (i < line.length && col < contentCol) {
    const c = line[i];
    if (c === ' ') { col += 1; i += 1; continue; }
    if (c === '\t') {
      const w = 4 - (col % 4);
      if (col + w <= contentCol) { col += w; i += 1; continue; }
      out += ' '.repeat(col + w - contentCol);
      col += w; i += 1;
      break;
    }
    col += 1; i += 1;
  }
  // Expand any remaining leading whitespace into the output.
  while (i < line.length && (line[i] === ' ' || line[i] === '\t')) {
    if (line[i] === ' ') { out += ' '; col += 1; i += 1; continue; }
    const w = 4 - (col % 4);
    out += ' '.repeat(w);
    col += w; i += 1;
  }
  return out + line.slice(i);
}

// Strip a blockquote marker: up to 3 columns of indent, '>', and up to one
// column of following whitespace (column-aware, tabs become spaces).
function bqStrip(line) {
  let i = 0;
  let col = 0;
  while (i < line.length && (line[i] === ' ' || line[i] === '\t')) {
    if (line[i] === ' ') col += 1; else col += 4 - (col % 4);
    i += 1;
  }
  i += 1; col += 1; // the '>'
  let out = '';
  if (line[i] === ' ') { i += 1; col += 1; }
  else if (line[i] === '\t') {
    const w = 4 - (col % 4);
    out += ' '.repeat(w - 1);
    col += w; i += 1;
  }
  while (i < line.length && (line[i] === ' ' || line[i] === '\t')) {
    if (line[i] === ' ') { out += ' '; col += 1; i += 1; continue; }
    const w = 4 - (col % 4);
    out += ' '.repeat(w);
    col += w; i += 1;
  }
  return out + line.slice(i);
}

// ------------------------------------------------------------- table support

// Split a table row into raw cell strings on unescaped pipes.
function splitRow(line) {
  const s = line.trim();
  const cells = [];
  let cur = '';
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (c === '\\' && i + 1 < s.length) { cur += c + s[i + 1]; i += 1; continue; }
    if (c === '|') { cells.push(cur); cur = ''; continue; }
    cur += c;
  }
  cells.push(cur);
  if (cells.length > 1 && cells[0].trim() === '') cells.shift();
  if (cells.length > 1 && cells[cells.length - 1].trim() === '') cells.pop();
  return cells;
}

// In table cells, an escaped pipe is unescaped before inline parsing
// (GFM: this applies even inside code spans).
function unescapePipes(s) {
  let out = '';
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '\\' && i + 1 < s.length && s[i + 1] === '|') { out += '|'; i += 1; continue; }
    if (s[i] === '\\' && i + 1 < s.length && s[i + 1] === '\\') { out += '\\\\'; i += 1; continue; }
    out += s[i];
  }
  return out;
}

// If lines[i] + lines[i+1] form a table header + delimiter, describe it.
function matchTable(lines, i) {
  if (i + 1 >= lines.length) return null;
  const headerLine = lines[i];
  const delimLine = lines[i + 1];
  if (isBlankLine(headerLine) || isBlankLine(delimLine)) return null;
  if (leadCols(headerLine) > 3 || leadCols(delimLine) > 3) return null;
  if (!headerLine.includes('|') && !delimLine.includes('|')) return null;
  const header = splitRow(headerLine).map(c => unescapePipes(c.trim()));
  const delims = splitRow(delimLine).map(c => c.trim());
  if (header.length === 0 || header.length !== delims.length) return null;
  const aligns = [];
  for (const d of delims) {
    if (!/^:?-+:?$/.test(d)) return null;
    if (d.startsWith(':') && d.endsWith(':')) aligns.push('center');
    else if (d.endsWith(':')) aligns.push('right');
    else if (d.startsWith(':')) aligns.push('left');
    else aligns.push(null);
  }
  return { header, aligns };
}

function isTableRowBreak(line) {
  // A line of only spaces (or empty) ends the table; a line containing
  // a tab — even only a tab — is consumed as a row by marked.
  if (/^ *$/.test(line)) return true;
  if (matchFence(line)) return true;
  if (matchATX(line)) return true;
  if (isThematicBreak(line)) return true;
  if (leadCols(line) <= 3 && stripCols(line, leadCols(line)).startsWith('>')) return true;
  if (matchListMarker(line)) return true;
  if (matchHtmlBlock(line)) return true;
  return false;
}

// -------------------------------------------------------------- block parser
// ctx: { refs: Map, endsAtDocEnd: boolean, srcEndsNl: boolean }

function parseBlocks(lines, ctx) {
  const nodes = [];
  let pendingSep = false;
  let sawContent = false;
  // ctx.blankSep records whether any two blocks at this level were
  // separated by a blank line (drives list looseness). Link reference
  // definitions count as content for this purpose.
  const push = (nd) => {
    if (pendingSep) { ctx.blankSep = true; pendingSep = false; }
    sawContent = true;
    nodes.push(nd);
  };
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i];
    if (isBlankLine(line)) {
      if (sawContent) pendingSep = true;
      i += 1; continue;
    }

    // Link reference definitions at the start of a block.
    let consumedDef = false;
    while (i < n && !isBlankLine(lines[i])) {
      const d = tryParseDef(lines, i);
      if (!d) break;
      if (!ctx.refs.has(d.label)) ctx.refs.set(d.label, { href: d.href, title: d.title });
      i += d.lines;
      consumedDef = true;
    }
    if (consumedDef) {
      if (pendingSep) { ctx.blankSep = true; pendingSep = false; }
      sawContent = true;
      if (i >= n || isBlankLine(lines[i])) continue;
    }
    if (i >= n) break;
    const cur = lines[i];

    // Fenced code.
    const fence = matchFence(cur);
    if (fence) {
      const content = [];
      let j = i + 1;
      while (j < n && !matchFenceClose(lines[j], fence.ch, fence.len)) {
        content.push(fence.ch === '`' ? stripWsChars(lines[j], fence.indent) : lines[j]);
        j += 1;
      }
      const closedFence = j < n;
      if (closedFence) j += 1; // closing fence
      // marked drops one trailing empty content line before a closing fence.
      if (closedFence && content.length && content[content.length - 1] === '') content.pop();
      const info = fence.info;
      const lang = info ? info.split(/[ \t]+/)[0] : '';
      push({ t: 'code', lang, text: content.length ? content.join('\n') + '\n' : '' });
      i = j;
      continue;
    }

    // ATX heading.
    const atx = matchATX(cur);
    if (atx) {
      push({ t: 'heading', level: atx.level, text: atx.text });
      i += 1;
      continue;
    }

    // HTML block.
    const hb = matchHtmlBlock(cur);
    if (hb) {
      const end = htmlBlockEnded(lines, i, hb.type, hb.tag);
      let text = lines.slice(i, end).join('\n');
      // marked keeps the line-ending newline when another block follows
      // immediately (or at EOF when the source ends with one), but not
      // when the block is terminated by a blank line. For the
      // terminator-ended types (1-5) a tab-only line does not count as
      // blank here; for types 6/7 it does.
      if (end < n) {
        const terminated = hb.type >= 6 ? isBlankLine(lines[end]) : lines[end] === '';
        if (!terminated) text += '\n';
      } else if (ctx.endsAtDocEnd && ctx.srcEndsNl) {
        text += '\n';
      }
      push({ t: 'html', text });
      i = end;
      continue;
    }

    // Thematic break.
    if (isThematicBreak(cur)) {
      push({ t: 'hr' });
      i += 1;
      continue;
    }

    // Blockquote.
    if (leadCols(cur) <= 3 && stripCols(cur, leadCols(cur)).startsWith('>')) {
      const inner = [];
      const lazyIdx = new Set();
      let j = i;
      let inFence = null;
      while (j < n) {
        const l = lines[j];
        const ind = leadCols(l);
        if (ind <= 3 && stripCols(l, ind).startsWith('>')) {
          const rest = bqStrip(l);
          inner.push(rest);
          const f = matchFence(rest);
          if (inFence) {
            if (f && matchFenceClose(rest, inFence.ch, inFence.len)) inFence = null;
          } else if (f) inFence = f;
          j += 1;
          continue;
        }
        // Lazy continuation: a paragraph line without the marker.
        if (!inFence && !isBlankLine(l) && inner.length > 0 &&
            !isBlankLine(inner[inner.length - 1]) && isLazyLine(l, inner)) {
          // marked keeps a lazy line's leading whitespace when it is
          // under 4 columns, and drops it entirely at 4+; a lazy '='
          // setext underline absorbed into a paragraph of 2+ lines is
          // additionally indented by four spaces.
          let lazyLine = leadCols(l) >= 4 ? l.replace(/^[ \t]+/, '') : l;
          if (isSetextUnderline(l) === 1) {
            let run = 0;
            for (let q = inner.length - 1; q >= 0 && !isBlankLine(inner[q]); q--) run += 1;
            if (run >= 2) lazyLine = '    ' + lazyLine;
          }
          lazyIdx.add(inner.length);
          inner.push(lazyLine);
          j += 1;
          continue;
        }
        break;
      }
      const childCtx = { refs: ctx.refs, endsAtDocEnd: ctx.endsAtDocEnd && j >= n, srcEndsNl: ctx.srcEndsNl, lazy: lazyIdx, inList: ctx.inList };
      push({ t: 'bq', children: parseBlocks(inner, childCtx) });
      i = j;
      continue;
    }

    // List.
    const marker = matchListMarker(cur);
    if (marker) {
      const res = parseList(lines, i, ctx);
      push(res.node);
      i = res.next;
      continue;
    }

    // Table.
    const table = matchTable(lines, i);
    if (table) {
      const rows = [];
      let j = i + 2;
      while (j < n && !isTableRowBreak(lines[j])) {
        const rawCells = splitRow(lines[j]).map(c => unescapePipes(c.trim()));
        rows.push(table.header.map((_, idx) => rawCells[idx] ?? ''));
        j += 1;
      }
      push({ t: 'table', header: table.header, aligns: table.aligns, rows });
      i = j;
      continue;
    }

    // Indented code block.
    if (leadCols(cur) >= 4) {
      const content = [];
      let j = i;
      while (j < n) {
        const l = lines[j];
        if (isBlankLine(l)) { content.push(stripCols(l, 4)); j += 1; continue; }
        if (leadCols(l) >= 4) { content.push(stripCols(l, 4)); j += 1; continue; }
        break;
      }
      while (content.length && /^[ \t]*$/.test(content[content.length - 1])) content.pop();
      push({ t: 'code', lang: '', text: content.length ? content.join('\n') + '\n' : '' });
      i = j;
      continue;
    }

    // Paragraph (possibly a setext heading, possibly interrupted).
    const paraLines = [cur];
    let j = i + 1;
    let setext = 0;
    while (j < n) {
      const l = lines[j];
      if (isBlankLine(l)) {
        // marked quirk: a whitespace-only line at the very end of the
        // block still belongs to the paragraph (its string-based lexer
        // sees no blank line after it).
        if (l.length > 0 && j === n - 1) { paraLines.push(l); j += 1; }
        break;
      }
      const sx = ctx.lazy && ctx.lazy.has(j) ? 0 : isSetextUnderline(l);
      if (sx) { setext = sx; j += 1; break; }
      if (ctx.lazy && ctx.lazy.has(j)) { paraLines.push(l); j += 1; continue; }
      if (matchTable(lines, j)) break;
      if (interruptsParagraph(l, ctx.inList)) break;
      paraLines.push(l);
      j += 1;
    }
    if (setext) push({ t: 'heading', level: setext, text: paraLines.join('\n').trim() });
    else push({ t: 'p', text: paraLines.join('\n') });
    i = j;
  }
  return nodes;
}

// A lazy blockquote continuation line must be paragraph continuation text:
// it may not itself start a new block, and the quote's current last block
// must look like an open paragraph. A '=' setext underline still counts
// as paragraph text here (marked absorbs it lazily), while a '-'
// underline is a thematic break and does not.
function isLazyLine(line, inner) {
  if (isThematicBreak(line)) return false;
  if (isSetextUnderline(line) === 2) return false;
  if (isSetextUnderline(line) !== 1 && isLazyBlockStart(line, undefined)) return false;
  // The last inner line must be paragraph-ish text.
  const last = inner[inner.length - 1];
  if (matchFence(last) || matchATX(last) || isThematicBreak(last)) return false;
  if (leadCols(last) >= 4) return false;
  return true;
}

// Does this line start any block? Used for lazy-continuation checks,
// where even a block that could not interrupt a paragraph (such as an
// ordered list item not starting at 1) still ends the lazy run.
function isLazyBlockStart(line, nextLine) {
  if (matchFence(line)) return true;
  if (matchATX(line)) return true;
  if (isThematicBreak(line)) return true;
  if (matchHtmlBlock(line)) return true;
  const ind = leadCols(line);
  if (ind <= 3 && stripCols(line, ind).startsWith('>')) return true;
  if (matchListMarker(line)) return true;
  if (isSetextUnderline(line)) return true;
  if (nextLine !== undefined && matchTable([line, nextLine], 0)) return true;
  return false;
}

// Does this line start a block that interrupts a paragraph?
// Inside list items, marked lets any list marker interrupt the item's
// paragraph (the nested list becomes a sibling block in the item).
function interruptsParagraph(line, inList) {
  if (matchFence(line)) return true;
  if (matchATX(line)) return true;
  if (isThematicBreak(line)) return true;
  const ind = leadCols(line);
  if (ind <= 3 && stripCols(line, ind).startsWith('>')) return true;
  const hb = matchHtmlBlock(line);
  if (hb && hb.type !== 7) return true;
  const mk = matchListMarker(line);
  if (mk && !mk.empty) {
    if (inList) return true;
    if (!mk.ordered) return true;
    if (mk.num === 1) return true;
  }
  return false;
}

// Parse a whole list starting at lines[start]. Returns { node, next }.
function parseList(lines, start, ctx) {
  const first = matchListMarker(lines[start]);
  const ordered = first.ordered;
  const bullet = first.bullet;
  const delim = first.delim;
  const startNum = first.num;
  const items = [];
  let loose = false;
  let i = start;
  const n = lines.length;

  const sameList = (mk) => mk && mk.ordered === ordered &&
    (ordered ? mk.delim === delim : mk.bullet === bullet);

  while (i < n) {
    const mk = matchListMarker(lines[i]);
    if (!sameList(mk)) break;
    const contentCol = mk.contentCol;

    // An item whose first line is empty, followed by a blank line, holds
    // nothing at all: later lines belong outside the item.
    if (mk.empty && (i + 1 >= n || isBlankLine(lines[i + 1]))) {
      items.push([]);
      let k = i + 1;
      while (k < n && isBlankLine(lines[k])) k += 1;
      if (k < n && sameList(matchListMarker(lines[k])) && leadCols(lines[k]) <= 3) {
        loose = true;
        i = k;
        continue;
      }
      i = i + 1;
      break;
    }

    const itemLines = [contentFromCol2(lines[i], contentCol)];
    const itemLazy = new Set();
    let j = i + 1;
    let pendingBlanks = 0;
    let endedByNextItem = false;
    while (j < n) {
      const l = lines[j];
      if (isBlankLine(l)) { pendingBlanks += 1; j += 1; continue; }
      const nmk = matchListMarker(l);
      if (pendingBlanks > 0) {
        if (leadCols(l) >= contentCol) {
          // Blank line(s) inside the item, with more content following.
          for (let b = 0; b < pendingBlanks; b++) itemLines.push('');
          pendingBlanks = 0;
          itemLines.push(contentFromCol2(l, contentCol));
          j += 1;
          continue;
        }
        if (isThematicBreak(l)) break;
        if (sameList(nmk) && leadCols(l) <= 3) {
          // Blank line(s) between items -> loose list.
          loose = true;
          endedByNextItem = true;
          break;
        }
        // Blank(s) then an outdented non-item line: the list is over.
        break;
      }
      if (leadCols(l) < contentCol && isThematicBreak(l)) break;
      if (sameList(nmk) && leadCols(l) < contentCol && leadCols(l) <= 3) {
        endedByNextItem = true; break;
      }
      if (leadCols(l) >= contentCol) {
        itemLines.push(contentFromCol2(l, contentCol));
        j += 1;
        continue;
      }
      // Possible lazy continuation of the item's paragraph. Marked
      // keeps lazy lines verbatim when indented under 4 columns, and
      // drops their leading whitespace entirely at 4+ (cm-291/312).
      if (!isLazyBlockStart(l, lines[j + 1]) &&
          itemLines.length > 0 && !isBlankLine(itemLines[itemLines.length - 1]) &&
          !matchFence(itemLines[itemLines.length - 1])) {
        itemLazy.add(itemLines.length);
        itemLines.push(leadCols(l) >= 4 ? l.replace(/^[ \t]+/, '') : l);
        j += 1;
        continue;
      }
      break;
    }
    const childCtx = { refs: ctx.refs, endsAtDocEnd: ctx.endsAtDocEnd && j >= n, srcEndsNl: ctx.srcEndsNl, blankSep: false, inList: true, lazy: itemLazy };
    items.push(parseBlocks(itemLines, childCtx));
    if (childCtx.blankSep) loose = true;
    if (endedByNextItem) { i = j; continue; }
    // The list is over. Point i at the first line not consumed by the item
    // (the blank lines we only peeked at are skipped by the caller anyway).
    i = j - pendingBlanks;
    break;
  }

  return {
    node: { t: 'list', ordered, start: startNum, loose, items },
    next: i,
  };
}

// ------------------------------------------------------------- inline parser

const ENTITY_RE = /^&(?:#(\d{1,7})|#[xX]([0-9a-fA-F]{1,6})|([A-Za-z][A-Za-z0-9]*));/;
const SCHEME_AUTOLINK_RE = /^<([A-Za-z][A-Za-z0-9+.\-]{1,31}:[^<>\s]*)>/;
const EMAIL_AUTOLINK_RE = /^<([A-Za-z0-9.!#$%&'*+\/=?^_`{|}~-]+@[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?(?:\.[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?)+)>/;
const COMMENT_RE = /^<!--(?:>|->|[\s\S]*?-->)/;
const CDATA_RE = /^<!\[CDATA\[[\s\S]*?\]\]>/;
const PI_RE = /^<\?[\s\S]*?\?>/;
const DECL_RE = /^<![A-Za-z][^>]*>/;

// Parse an inline link destination/title starting at text[pos] === '('.
// Returns { href, title, end } or null.
function parseInlineDest(text, pos) {
  const len = text.length;
  let p = pos + 1;
  const skipWs = () => {
    const from = p;
    while (p < len && (text[p] === ' ' || text[p] === '\t' || text[p] === '\n' || text[p] === '\r')) p += 1;
    return p > from;
  };
  const parseTitleAt = (q) => {
    const open = text[q];
    if (open === '"' || open === "'") {
      let k = q + 1;
      let t = '';
      while (k < len) {
        const ch = text[k];
        if (ch === '\\' && k + 1 < len && isAsciiPunct(text[k + 1])) { t += ch + text[k + 1]; k += 2; continue; }
        if (ch === open) return { title: unescapeStr(t), end: k + 1 };
        t += ch; k += 1;
      }
      return null;
    }
    if (open === '(') {
      let k = q + 1;
      let t = '';
      while (k < len) {
        const ch = text[k];
        if (ch === '\\' && k + 1 < len && isAsciiPunct(text[k + 1])) { t += ch + text[k + 1]; k += 2; continue; }
        if (ch === ')') return { title: unescapeStr(t), end: k + 1 };
        if (ch === '(') return null;
        t += ch; k += 1;
      }
      return null;
    }
    return null;
  };

  const hadWs = skipWs();
  // Title with an empty destination: "(  \"title\"  )".
  if (hadWs && (text[p] === '"' || text[p] === "'" || text[p] === '(')) {
    const t = parseTitleAt(p);
    if (t) {
      let q = t.end;
      while (q < len && (text[q] === ' ' || text[q] === '\t' || text[q] === '\n')) q += 1;
      if (text[q] === ')') return { href: '', title: t.title, end: q + 1 };
    }
  }
  let href;
  if (text[p] === '<') {
    let k = p + 1;
    let dest = '';
    let ok = false;
    while (k < len) {
      const ch = text[k];
      if (ch === '\\' && k + 1 < len && isAsciiPunct(text[k + 1])) { dest += ch + text[k + 1]; k += 2; continue; }
      if (ch === '>') { ok = true; break; }
      if (ch === '<' || ch === '\n') return null;
      dest += ch; k += 1;
    }
    if (!ok) return null;
    href = unescapeStr(dest);
    p = k + 1;
  } else if (text[p] === ')') {
    href = '';
  } else {
    let k = p;
    let depth = 0;
    let dest = '';
    while (k < len) {
      const ch = text[k];
      if (ch === '\\' && k + 1 < len && isAsciiPunct(text[k + 1])) { dest += ch + text[k + 1]; k += 2; continue; }
      if (ch === '(') { depth += 1; dest += ch; k += 1; continue; }
      if (ch === ')') {
        if (depth === 0) break;
        depth -= 1; dest += ch; k += 1; continue;
      }
      if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch < ' ') break;
      dest += ch; k += 1;
    }
    if (depth !== 0) return null;
    href = unescapeStr(dest);
    p = k;
  }
  const hadWs2 = skipWs();
  let title = null;
  if (hadWs2 && (text[p] === '"' || text[p] === "'" || text[p] === '(')) {
    const t = parseTitleAt(p);
    if (!t) return null;
    title = t.title;
    p = t.end;
    skipWs();
  }
  if (text[p] === ')') return { href, title, end: p + 1 };
  return null;
}

// Match a GFM email autolink at the start of s. Domain segments must
// start and end with an alphanumeric; if the character right after the
// match would continue the domain with '-' or '_', the address is
// invalid as a whole and nothing is linked.
const EMAIL_RE = /^[A-Za-z0-9._%+-]+@(?:[A-Za-z0-9](?:[A-Za-z0-9_-]*[A-Za-z0-9])?\.)+[A-Za-z0-9](?:[A-Za-z0-9_-]*[A-Za-z0-9])?/;
function matchEmail(s, underscoreOpener) {
  const m = EMAIL_RE.exec(s);
  if (!m) return null;
  const after = s[m[0].length];
  if (after !== undefined && /[A-Za-z0-9-]/.test(after)) return null;
  // A trailing '_' poisons the address, unless it is the closing
  // delimiter of an underscore emphasis that is currently open.
  if (after === '_' && !underscoreOpener) return null;
  return m[0];
}

// Cheap candidate test for an extended autolink at text[i]: a real
// 'www.' / scheme:// / mailto: / xmpp: prefix, or an email local part
// immediately followed by '@'. Keeps the full matcher (and its slice)
// off the hot path for ordinary words.
function autolinkCandidate(text, i) {
  const c = text[i];
  if (c === 'w' && text.startsWith('www.', i)) return true;
  if (c === 'h' || c === 'H' || c === 'f' || c === 'F') {
    const head = text.slice(i, i + 8).toLowerCase();
    if (head.startsWith('http://') || head.startsWith('https://') || head.startsWith('ftp://')) return true;
  }
  if ((c === 'm' && text.startsWith('mailto:', i)) || (c === 'x' && text.startsWith('xmpp:', i))) return true;
  let j = i;
  while (j < text.length) {
    const cc = text.charCodeAt(j);
    const ok = (cc >= 48 && cc <= 57) || (cc >= 65 && cc <= 90) || (cc >= 97 && cc <= 122) ||
      cc === 46 || cc === 95 || cc === 37 || cc === 43 || cc === 45;
    if (!ok) break;
    j += 1;
  }
  return j > i && text[j] === '@';
}

// GFM extended autolink at the start of s (a whitespace-bounded slice
// beginning at the candidate position); returns { text, href } or null.
function matchExtendedAutolink(rest, underscoreOpener) {
  // mailto: / xmpp: prefixed email autolinks.
  const schemeM = /^(mailto|xmpp):/.exec(rest);
  if (schemeM) {
    const em = matchEmail(rest.slice(schemeM[0].length), false);
    if (em) {
      let link = schemeM[0] + em;
      if (schemeM[1] === 'xmpp') {
        // An xmpp autolink may carry one resource segment: /foo.
        const res = /^\/[^\s/]+/.exec(rest.slice(link.length));
        if (res) link += res[0];
      }
      return { text: link, href: link };
    }
    return null;
  }
  let m = /^www\.[^\s<]+/.exec(rest) || /^(?:https?|ftp):\/\/[^\s<]+/i.exec(rest);
  if (m) {
    let link = m[0];
    if (link.startsWith('www.')) {
      if (!/^www\.[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)+/.test(link)) return null;
    }
    // Trim trailing punctuation / unbalanced parens / trailing entity.
    for (;;) {
      if (link.length === 0) return null;
      const last = link[link.length - 1];
      if ('?!.,:*_~\'"'.includes(last)) { link = link.slice(0, -1); continue; }
      if (last === ')') {
        // Strip a trailing ')' only when it is stray — i.e. a depth
        // scan of the current link reaches it with no open '('.
        let depth = 0;
        let stray = false;
        for (let k = 0; k < link.length; k++) {
          const c = link[k];
          if (c === '(') depth += 1;
          else if (c === ')') {
            if (k === link.length - 1) stray = depth === 0;
            else if (depth > 0) depth -= 1;
          }
        }
        if (stray) { link = link.slice(0, -1); continue; }
      }
      if (last === ';') {
        const em = /&[A-Za-z][A-Za-z0-9]*;$/.exec(link);
        if (em) { link = link.slice(0, link.length - em[0].length); continue; }
        link = link.slice(0, -1); continue;
      }
      // Cut at the first '(' that has no matching ')' later.
      let cut = -1;
      for (let p = 0; p < link.length; p++) {
        if (link[p] !== '(') continue;
        let depth = 0;
        let matched = false;
        for (let q = p; q < link.length; q++) {
          if (link[q] === '(') depth += 1;
          else if (link[q] === ')') { depth -= 1; if (depth === 0) { matched = true; break; } }
        }
        if (!matched) { cut = p; break; }
      }
      if (cut >= 0) { link = link.slice(0, cut); continue; }
      break;
    }
    if (link.startsWith('www.') && !/^www\.[A-Za-z0-9-]+(?:\.[A-Za-z0-9-]+)/.test(link)) return null;
    return { text: link, href: link.startsWith('www.') ? 'http://' + link : link };
  }
  const em = matchEmail(rest, underscoreOpener);
  if (em) {
    return { text: em, href: 'mailto:' + em };
  }
  return null;
}

// marked pre-masks an inline text by pairing backtick runs: scanning
// left to right, each run is paired with the next run of the same
// length (runs in between are consumed), and emphasis/strikethrough
// delimiters between a paired opener and closer are inert — even when
// the pair crosses link boundaries, e.g. a label holding an unmatched
// `` / ` run pair and a code span later in the paragraph. Returns
// [start, end) ranges.
function backtickMaskRanges(text) {
  if (!text.includes('`')) return [];
  const runs = [];
  let i = 0;
  const n = text.length;
  while (i < n) {
    if (text[i] === '`') {
      let run = 0;
      while (text[i + run] === '`') run += 1;
      let bs = 0;
      for (let k = i - 1; k >= 0 && text[k] === '\\'; k--) bs += 1;
      runs.push({ start: i, end: i + run, len: run, escaped: bs % 2 === 1 });
      i += run;
    } else i += 1;
  }
  const ranges = [];
  let idx = 0;
  while (idx < runs.length) {
    const r = runs[idx];
    // An escaped run cannot open a mask span (it is literal text),
    // but it can close one (a code span's closing run may follow a
    // backslash inside the span).
    if (r.escaped) { idx += 1; continue; }
    let j = idx + 1;
    while (j < runs.length && runs[j].len !== r.len) j += 1;
    if (j < runs.length) { ranges.push([r.start, runs[j].end]); idx = j + 1; }
    else idx += 1;
  }
  return ranges;
}

// Turn delimiter tokens whose source position lies inside a mask
// range into literal text. `base` is the source offset of the text
// the ranges were computed on (0 for a whole inline text, the label
// start for link children).
function applyBacktickMask(tokens, ranges, base) {
  if (!ranges.length) return;
  for (let q = 0; q < tokens.length; q++) {
    const t = tokens[q];
    if (t.k !== 'delim' || t.pos === undefined) continue;
    const p = t.pos - base;
    for (const [s, e] of ranges) {
      if (p >= s && p < e) { tokens[q] = { k: 't', s: t.ch.repeat(t.n) }; break; }
      if (s > p) break;
    }
  }
}

function tokenizeInline(text, refs, gs) {
  const tokens = [];
  const brackets = [];
  const len = text.length;
  let buf = '';
  let i = 0;
  const flush = () => {
    if (buf.length) { tokens.push({ k: 't', s: buf }); buf = ''; }
  };
  const linkEndCached = (br) => {
    if (br._linkEnd === undefined) br._linkEnd = linkEndAt(text, br, refs);
    return br._linkEnd;
  };
  let underscoreOpeners = 0;

  while (i < len) {
    const c = text[i];

    if (c === '\\') {
      const nx = text[i + 1];
      if (nx === '\n') {
        flush();
        tokens.push({ k: 'br' });
        i += 2;
        // Leading spaces of the line after a hard break are dropped.
        while (text[i] === ' ' || text[i] === '\t') i += 1;
        continue;
      }
      if (nx !== undefined && isAsciiPunct(nx)) { buf += nx; i += 2; continue; }
      buf += '\\'; i += 1; continue;
    }

    if (c === '`') {
      let run = 0;
      while (text[i + run] === '`') run += 1;
      let j = i + run;
      let found = -1;
      // Inside a bracket that will actually form a link, marked has
      // already consumed the whole '[...](...)' construct, so a code
      // span cannot reach past the label's end. If the bracket will
      // not form a link, the span may cross ']' freely.
      let limit = len;
      if (brackets.length > 0 && brackets[brackets.length - 1].active) {
        const e = linkEndCached(brackets[brackets.length - 1]);
        if (e >= 0) limit = e;
      }
      while (j < limit) {
        if (text[j] === '`') {
          let r = 0;
          while (text[j + r] === '`') r += 1;
          if (r === run) { found = j; break; }
          j += r;
        } else j += 1;
      }
      if (found >= 0) {
        let content = text.slice(i + run, found).replace(/\n/g, ' ');
        if (content.length >= 2 && content.startsWith(' ') && content.endsWith(' ') && /[^ ]/.test(content)) {
          content = content.slice(1, -1);
        }
        flush();
        tokens.push({ k: 'code', s: content });
        i = found + run;
      } else {
        buf += '`'.repeat(run);
        i += run;
      }
      continue;
    }

    if (c === '&') {
      const m = ENTITY_RE.exec(text.slice(i, i + 34));
      if (m) {
        if (m[3] !== undefined) {
          flush();
          tokens.push({ k: 'entity', s: m[0] });
        } else {
          let cp = m[1] !== undefined ? parseInt(m[1], 10) : parseInt(m[2], 16);
          if (cp === 0 || cp > 0x10ffff || (cp >= 0xd800 && cp <= 0xdfff)) cp = 0xfffd;
          buf += String.fromCodePoint(cp);
        }
        i += m[0].length;
      } else {
        buf += '&'; i += 1;
      }
      continue;
    }

    if (c === '<') {
      const rest = text.slice(i);
      let m = COMMENT_RE.exec(rest) || CDATA_RE.exec(rest) || PI_RE.exec(rest) || DECL_RE.exec(rest);
      if (m) { flush(); tokens.push({ k: 'raw', s: m[0] }); i += m[0].length; continue; }
      m = SCHEME_AUTOLINK_RE.exec(rest);
      if (m) {
        flush();
        tokens.push({ k: 'link', href: m[1], title: null, children: [{ k: 't', s: m[1] }] });
        i += m[0].length; continue;
      }
      m = EMAIL_AUTOLINK_RE.exec(rest);
      if (m) {
        flush();
        tokens.push({ k: 'link', href: 'mailto:' + m[1], title: null, children: [{ k: 't', s: m[1] }] });
        i += m[0].length; continue;
      }
      const tag = matchTag(rest, 0);
      if (tag !== null) {
        flush(); tokens.push({ k: 'raw', s: tag });
        // marked keeps a lexer-wide inLink flag: an inline <a> start
        // tag disables GFM extended autolinks until a </a> appears
        // (document-wide, across blocks). Tags inside a link's text
        // do not leak (marked saves/restores around link text).
        if (gs && !brackets.some(b => b.active)) {
          if (/^<\/a\s*>/i.test(tag)) gs.inLink = false;
          else if (/^<a\s/.test(tag)) gs.inLink = true;
        }
        i += tag.length; continue;
      }
      buf += '<'; i += 1; continue;
    }

    if (c === '!' && text[i + 1] === '[') {
      flush();
      tokens.push({ k: 'open', image: true });
      brackets.push({ tokIdx: tokens.length - 1, srcIdx: i + 2, image: true, active: true });
      i += 2; continue;
    }

    if (c === '[') {
      flush();
      tokens.push({ k: 'open', image: false });
      brackets.push({ tokIdx: tokens.length - 1, srcIdx: i + 1, image: false, active: true });
      i += 1; continue;
    }

    if (c === ']') {
      const formed = tryFormLink(text, i, tokens, brackets, refs, () => flush());
      if (formed !== null) { i = formed; continue; }
      buf += ']'; i += 1; continue;
    }

    if (c === '*' || c === '_' || c === '~') {
      let run = 0;
      while (text[i + run] === c) run += 1;
      // Runs of 3+ tildes are never strikethrough delimiters.
      if (c === '~' && run > 2) { buf += '~'.repeat(run); i += run; continue; }
      const prevCh = i > 0 ? text[i - 1] : undefined;
      const nextCh = i + run < len ? text[i + run] : undefined;
      flush();
      if (c === '~') {
        tokens.push({ k: 'delim', ch: '~', n: run, canOpen: !isWsCh(nextCh), canClose: !isWsCh(prevCh), pos: i });
      } else {
        const prevWs = isWsCh(prevCh);
        const nextWs = isWsCh(nextCh);
        const prevP = isPunctCh(prevCh);
        const nextP = isPunctCh(nextCh);
        const leftFl = !nextWs && (!nextP || prevWs || prevP);
        const rightFl = !prevWs && (!prevP || nextWs || nextP);
        let canOpen;
        let canClose;
        if (c === '*') { canOpen = leftFl; canClose = rightFl; }
        else {
          canOpen = leftFl && (!rightFl || prevP);
          canClose = rightFl && (!leftFl || nextP);
        }
        tokens.push({ k: 'delim', ch: c, n: run, canOpen, canClose, pos: i });
        if (c === '_' && canOpen) underscoreOpeners += 1;
      }
      i += run; continue;
    }

    if (c === '\n') {
      if (/[ ]{2,}$/.test(buf)) {
        buf = buf.replace(/[ ]+$/, '');
        flush();
        tokens.push({ k: 'br' });
        i += 1;
        // Leading spaces of the line after a hard break are dropped.
        while (text[i] === ' ' || text[i] === '\t') i += 1;
      } else {
        buf += '\n';
        i += 1;
      }
      continue;
    }

    // Plain text: GFM extended autolinks may start here. They are
    // suppressed inside an open link/image bracket: marked matches
    // links at the '[', so link text is never scanned for bare URLs.
    const prevCh = i > 0 ? text[i - 1] : undefined;
    const boundary = prevCh === undefined || isWsCh(prevCh) ||
      (isPunctCh(prevCh) && prevCh !== '.' && prevCh !== '/' && prevCh !== '@');
    const inBracket = (gs && gs.inLink) || brackets.some(br => br.active && linkEndCached(br) >= 0);
    if (!inBracket && boundary && (c === 'w' || c === 'h' || c === 'f' || (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'))) {
      let auto = null;
      if (autolinkCandidate(text, i)) {
        let endB = i;
        while (endB < len && !isWsCh(text[endB]) && text[endB] !== '<') endB += 1;
        auto = matchExtendedAutolink(text.slice(i, endB), underscoreOpeners > 0);
      }
      if (auto) {
        flush();
        tokens.push({ k: 'link', href: auto.href, title: null, children: [{ k: 't', s: auto.text }] });
        i += auto.text.length;
        continue;
      }
    }
    buf += c; i += 1;
  }
  flush();
  return tokens;
}

// If the bracket `br` will form a link, return the index of the ']'
// that ends its label; otherwise return -1. The label scan mirrors
// marked's label pattern: escapes, nested brackets, and code-span
// units (a backtick run, non-backticks, a backtick run) are consumed
// atomically; an unmatched backtick run invalidates the label.
function linkEndAt(text, br, refs) {
  if (!br || !br.active) return -1;
  const len = text.length;
  let depth = 0;
  let k = br.srcIdx;
  let end = -1;
  // Marked's label scan pairs backtick runs sequentially at each
  // bracket level (any lengths pair). A leftover run is tolerated
  // only when it is 2+ long and ends exactly at the level's ']'.
  const pend = [null];
  while (k < len) {
    const ch = text[k];
    if (ch === '\\') { k += 2; continue; }
    if (ch === '`') {
      let r = 0;
      while (text[k + r] === '`') r += 1;
      pend[depth] = pend[depth] === null ? { len: r, end: k + r } : null;
      k += r;
      continue;
    }
    if (ch === '[') { depth += 1; pend[depth] = null; k += 1; continue; }
    if (ch === ']') {
      const p = pend[depth];
      if (p !== null && !(p.len >= 2 && p.end === k)) return -1;
      if (depth === 0) { end = k; break; }
      depth -= 1; k += 1; continue;
    }
    k += 1;
  }
  if (end === -1) return -1;
  const after = end + 1;
  if (text[after] === '(') return parseInlineDest(text, after) !== null ? end : -1;
  let labelRaw = null;
  if (text[after] === '[') {
    let q = after + 1;
    let lab = '';
    let ok = false;
    while (q < len) {
      const ch = text[q];
      if (ch === '\\' && q + 1 < len) { lab += ch + text[q + 1]; q += 2; continue; }
      if (ch === '[') break;
      if (ch === ']') { ok = true; break; }
      lab += ch; q += 1;
    }
    if (ok) labelRaw = lab;
  }
  const lookup = (labelRaw !== null && labelRaw.length > 0)
    ? normalizeLabel(labelRaw)
    : normalizeLabel(text.slice(br.srcIdx, end));
  return lookup !== null && lookup !== '' && refs.has(lookup) ? end : -1;
}

// Is this link label well-formed by marked's label rules? Backtick
// runs pair sequentially at each bracket level (any lengths pair);
// a leftover run must be 2+ long and end exactly at the level's
// closing ']' (or at the end of the label for the outermost level).
function labelTextValid(s) {
  let depth = 0;
  let k = 0;
  const pend = [null];
  while (k < s.length) {
    const ch = s[k];
    if (ch === '\\') { k += 2; continue; }
    if (ch === '`') {
      let r = 0;
      while (s[k + r] === '`') r += 1;
      pend[depth] = pend[depth] === null ? { len: r, end: k + r } : null;
      k += r;
      continue;
    }
    if (ch === '[') { depth += 1; pend[depth] = null; k += 1; continue; }
    if (ch === ']') {
      const p = pend[depth];
      if (p !== null && !(p.len >= 2 && p.end === k)) return false;
      depth -= 1;
      if (depth < 0) return false;
      k += 1;
      continue;
    }
    k += 1;
  }
  if (depth !== 0) return false;
  const p = pend[0];
  return p === null || (p.len >= 2 && p.end === s.length);
}

// Attempt to form a link/image at a ']' (position closeIdx in text).
// Returns the new scan position, or null if no link was formed.
// Only the nearest bracket opener can pair with this ']': if it was
// deactivated (a link formed inside it), the ']' is literal text.
let suppSeq = 0;
function tryFormLink(text, closeIdx, tokens, brackets, refs, flush) {
  if (brackets.length === 0) return null;
  const bi = brackets.length - 1;
  const br = brackets[bi];
  if (!br.active) {
    brackets.pop();
    return null;
  }
  // Marked quirk: when an inline link attempt '[...](...)' fails,
  // emphasis/strikethrough pairs wholly inside the label do not form
  // (code spans, nested links and autolinks in the label still work).
  const markSuppressed = () => {
    suppSeq += 1;
    for (let q = br.tokIdx + 1; q < tokens.length; q++) {
      if (tokens[q].k === 'delim') tokens[q].supp = suppSeq;
    }
  };
  if (!labelTextValid(text.slice(br.srcIdx, closeIdx))) {
    if (text[closeIdx + 1] === '(') markSuppressed();
    brackets.length = bi;
    return null;
  }
  const len = text.length;
  const after = closeIdx + 1;
  let href;
  let title = null;
  let endPos = null;

  if (text[after] === '(') {
    const d = parseInlineDest(text, after);
    if (d) { href = d.href; title = d.title; endPos = d.end; }
  }
  if (endPos === null) {
    // Reference forms.
    let labelRaw = null;
    let refEnd = after;
    if (text[after] === '[') {
      let k = after + 1;
      let lab = '';
      let ok = false;
      while (k < len) {
        const ch = text[k];
        if (ch === '\\' && k + 1 < len) { lab += ch + text[k + 1]; k += 2; continue; }
        if (ch === '[') break;
        if (ch === ']') { ok = true; break; }
        lab += ch; k += 1;
      }
      if (ok) { labelRaw = lab; refEnd = k + 1; }
    }
    let lookup = null;
    if (labelRaw !== null && labelRaw.length > 0) lookup = normalizeLabel(labelRaw);
    else lookup = normalizeLabel(text.slice(br.srcIdx, closeIdx));
    const def = lookup !== null && lookup !== '' ? refs.get(lookup) : undefined;
    if (def) {
      href = def.href; title = def.title;
      endPos = labelRaw !== null ? refEnd : after;
    }
  }
  if (endPos === null) {
    // No link: this bracket opener can never match; drop it.
    if (text[after] === '(') markSuppressed();
    brackets.length = bi;
    return null;
  }
  flush();
  const children = tokens.splice(br.tokIdx + 1);
  // Delimiters inside the label are masked by the label's own backtick
  // pairing, not by the enclosing text's mask.
  applyBacktickMask(children, backtickMaskRanges(text.slice(br.srcIdx, closeIdx)), br.srcIdx);
  processEmphasisAll(children);
  if (br.image) {
    tokens[br.tokIdx] = {
      k: 'img', href, title,
      altText: plainTextOf(children),
    };
  } else {
    tokens[br.tokIdx] = { k: 'link', href, title, children };
    // Links cannot contain links: deactivate earlier link openers.
    for (let q = 0; q < bi; q++) {
      if (!brackets[q].image) brackets[q].active = false;
    }
  }
  brackets.length = bi;
  return endPos;
}

// The CommonMark delimiter-stack algorithm for '*' and '_'.
function processEmphasis(tokens) {
  let ci = 0;
  while (ci < tokens.length) {
    const closer = tokens[ci];
    if (!closer || closer.k !== 'delim' || closer.ch === '~' || !closer.canClose || closer.n === 0) {
      ci += 1; continue;
    }
    let oi = ci - 1;
    let found = -1;
    while (oi >= 0) {
      const o = tokens[oi];
      if (o && o.k === 'delim' && o.ch === closer.ch && o.canOpen && o.n > 0) {
        if (o.supp !== undefined && o.supp === closer.supp) { oi -= 1; continue; }
        if ((o.canClose || closer.canOpen) &&
            ((o.n + closer.n) % 3 === 0) &&
            !(o.n % 3 === 0 && closer.n % 3 === 0)) {
          oi -= 1; continue;
        }
        // marked quirk: a '*'/'_' match is blocked when its content
        // holds a same-character emphasis node that follows whitespace
        // and the content ends in a word character — where the inner
        // node is of the other length, or the opener's run has 2+ to
        // give (e.g. '*a **b**c*' and '**a *b*c* d**' stay literal,
        // but '*a *b*c*' and '*foo**bar**baz*' do not). The block
        // applies only when nothing but text sits between the inner
        // node and the closer, and (for strong matches) only when
        // the closer's run is exactly 2.
        const useLen = o.n >= 2 && closer.n >= 2 ? 2 : 1;
        const lastIn = tokens[ci - 1];
        if (lastIn && lastIn.k === 't' && lastIn.s.length > 0 &&
            !isWsCh(lastIn.s[0]) && !isPunctCh(lastIn.s[0]) &&
            !(useLen === 2 && closer.n !== 2)) {
          const otherK = useLen === 2 ? 'em' : 'strong';
          let blocked = false;
          for (let q = oi + 1; q < ci; q++) {
            const tk = tokens[q];
            if ((tk.k === 'em' || tk.k === 'strong') && tk.ch === closer.ch &&
                (tk.k === otherK || (useLen === 1 && o.n >= 2))) {
              let p = q - 1;
              while (p > oi && tokens[p].k === 'delim' && tokens[p].n === 0) p -= 1;
              const prev = tokens[p];
              let textOnly = true;
              for (let r = q + 1; r < ci; r++) {
                if (tokens[r].k !== 't' && !(tokens[r].k === 'delim' && tokens[r].n === 0)) { textOnly = false; break; }
              }
              if (prev && prev.k === 't' && /\s$/.test(prev.s) && textOnly) blocked = true;
              break;
            }
          }
          // When the block rule fires, marked's scan leaves this
          // closer unmatched altogether: it does not fall back to an
          // earlier opener (e.g. '**c *d **e**f* g**' keeps the inner
          // '*' pair literal and lets the outer '**' pair as strong).
          // An opener the blocked match would have used up entirely
          // is likewise dead as an opener for later closers; a longer
          // opener run survives (its strong match is still live, as
          // in '**a *b*c* d**').
          if (blocked) {
            if (o.n === useLen) o.canOpen = false;
            found = -2; break;
          }
        }
        found = oi; break;
      }
      oi -= 1;
    }
    if (found < 0) { ci += 1; continue; }
    const opener = tokens[found];
    const use = opener.n >= 2 && closer.n >= 2 ? 2 : 1;
    opener.n -= use;
    closer.n -= use;
    const inner = tokens.splice(found + 1, ci - found - 1);
    const node = { k: use === 2 ? 'strong' : 'em', ch: closer.ch, children: inner };
    tokens.splice(found + 1, 0, node);
    ci = found + 2;
    if (closer.n === 0) ci += 1;
    else if (use === 2) {
      // Marked quirk, mirroring the block rule: when a strong match
      // leaves delimiters on a 3+ closer run and the new content has
      // the block-rule shape (an other-length same-char emphasis node
      // after whitespace, then only text ending in a word char), the
      // leftover delimiters render INSIDE the strong element.
      const ch2 = node.children;
      const lastC = ch2[ch2.length - 1];
      if (lastC && lastC.k === 't' && lastC.s.length > 0 &&
          !isWsCh(lastC.s[0]) && !isPunctCh(lastC.s[0])) {
        for (let q = 0; q < ch2.length; q++) {
          const tk = ch2[q];
          if (tk.k === 'em' && tk.ch === closer.ch) {
            let p = q - 1;
            while (p >= 0 && ch2[p].k === 'delim' && ch2[p].n === 0) p -= 1;
            const prev = ch2[p];
            let textOnly = true;
            for (let r = q + 1; r < ch2.length; r++) {
              if (ch2[r].k !== 't' && !(ch2[r].k === 'delim' && ch2[r].n === 0)) { textOnly = false; break; }
            }
            if (prev && prev.k === 't' && /\s$/.test(prev.s) && textOnly) {
              const leftover = tokens.splice(ci, 1)[0];
              node.children.push(leftover);
            }
            break;
          }
        }
      }
    }
  }
}

// Pairing pass for GFM strikethrough ('~' / '~~').
function processDel(tokens) {
  let ci = 0;
  while (ci < tokens.length) {
    const closer = tokens[ci];
    if (!closer || closer.k !== 'delim' || closer.ch !== '~' || !closer.canClose || closer.n === 0) {
      ci += 1; continue;
    }
    let oi = ci - 1;
    let found = -1;
    while (oi >= 0) {
      const o = tokens[oi];
      if (o && o.k === 'delim' && o.ch === '~' && o.canOpen && o.n > 0) {
        if (o.supp !== undefined && o.supp === closer.supp) { oi -= 1; continue; }
        found = oi; break;
      }
      oi -= 1;
    }
    if (found === -1) { ci += 1; continue; }
    const opener = tokens[found];
    const use = Math.min(2, opener.n, closer.n);
    opener.n -= use;
    closer.n -= use;
    const inner = tokens.splice(found + 1, ci - found - 1);
    tokens.splice(found + 1, 0, { k: 'del', children: inner });
    ci = found + 2;
    if (closer.n === 0) ci += 1;
  }
}

function processEmphasisAll(tokens) {
  processEmphasis(tokens);
  processDel(tokens);
  // Emphasis formed at this level can wrap still-unprocessed delimiters
  // of the other kind (e.g. **a ~~b~~ c**); process the wrapped children.
  for (const t of tokens) {
    if ((t.k === 'em' || t.k === 'strong' || t.k === 'del') && t.children) {
      processEmphasisAll(t.children);
    }
  }
}

function plainTextOf(tokens) {
  let out = '';
  for (const t of tokens) {
    switch (t.k) {
      case 't': out += t.s; break;
      case 'entity': out += t.s; break;
      case 'raw': break;
      case 'code': out += t.s; break;
      case 'br': out += ' '; break;
      case 'open': out += t.image ? '![' : '['; break;
      case 'delim': out += t.ch.repeat(t.n); break;
      case 'em': case 'strong': case 'del': out += plainTextOf(t.children); break;
      case 'link': out += plainTextOf(t.children); break;
      case 'img': out += t.altText; break;
      default: break;
    }
  }
  return out;
}

function renderTokens(tokens) {
  let out = '';
  for (const t of tokens) {
    switch (t.k) {
      case 't': out += escapeHtml(t.s); break;
      case 'entity': out += t.s; break;
      case 'raw': out += t.s; break;
      case 'code': out += '<code>' + escapeHtml(t.s) + '</code>'; break;
      case 'br': out += '<br>'; break;
      case 'open': out += t.image ? '![' : '['; break;
      case 'delim': out += t.ch.repeat(t.n); break;
      case 'em': out += '<em>' + renderTokens(t.children) + '</em>'; break;
      case 'strong': out += '<strong>' + renderTokens(t.children) + '</strong>'; break;
      case 'del': out += '<del>' + renderTokens(t.children) + '</del>'; break;
      case 'link':
        out += '<a href="' + escapeAttr(cleanUrl(t.href)) + '"' +
          (t.title !== null && t.title !== undefined ? ' title="' + escapeAttr(t.title) + '"' : '') +
          '>' + renderTokens(t.children) + '</a>';
        break;
      case 'img':
        out += '<img src="' + escapeAttr(cleanUrl(t.href)) + '" alt="' + escapeAttr(t.altText) + '"' +
          (t.title !== null && t.title !== undefined ? ' title="' + escapeAttr(t.title) + '"' : '') + '>';
        break;
      default: break;
    }
  }
  return out;
}

function parseInlineHtml(text, ctx) {
  const tokens = tokenizeInline(text, ctx.refs, ctx.gs);
  applyBacktickMask(tokens, backtickMaskRanges(text), 0);
  processEmphasisAll(tokens);
  return renderTokens(tokens);
}

// ------------------------------------------------------------ node rendering

function renderListItem(itemNodes, listNode, ctx) {
  if (itemNodes.length === 0) return '';
  let nodes = itemNodes;
  let checkbox = null;
  const first = itemNodes[0];
  if (first.t === 'p') {
    const m = /^\[( |x|X)\] /.exec(first.text);
    if (m) {
      checkbox = m[1] === ' '
        ? '<input disabled="" type="checkbox">'
        : '<input checked="" disabled="" type="checkbox">';
      nodes = itemNodes.slice();
      nodes[0] = { t: 'p', text: first.text.slice(3), checkbox };
    }
  }
  return renderNodes(nodes, ctx, !listNode.loose);
}

function renderNodes(nodes, ctx, tight) {
  let out = '';
  for (const nd of nodes) {
    switch (nd.t) {
      case 'p': {
        const inner = (nd.checkbox ?? '') + parseInlineHtml(nd.text, ctx);
        out += tight ? inner : '<p>' + inner + '</p>\n';
        break;
      }
      case 'heading':
        out += '<h' + nd.level + '>' + parseInlineHtml(nd.text, ctx) + '</h' + nd.level + '>\n';
        break;
      case 'code':
        out += '<pre><code' +
          (nd.lang ? ' class="language-' + escapeAttr(nd.lang) + '"' : '') +
          '>' + escapeHtml(nd.text) + '</code></pre>\n';
        break;
      case 'hr':
        out += '<hr>\n';
        break;
      case 'html':
        out += nd.text;
        break;
      case 'bq':
        out += '<blockquote>\n' + renderNodes(nd.children, ctx, false) + '</blockquote>\n';
        break;
      case 'list': {
        const tag = nd.ordered ? 'ol' : 'ul';
        const startAttr = nd.ordered && nd.start !== 1 ? ' start="' + nd.start + '"' : '';
        out += '<' + tag + startAttr + '>\n';
        for (const item of nd.items) {
          out += '<li>' + renderListItem(item, nd, ctx) + '</li>\n';
        }
        out += '</' + tag + '>\n';
        break;
      }
      case 'table': {
        out += '<table>\n<thead>\n<tr>\n';
        nd.header.forEach((cell, idx) => {
          const a = nd.aligns[idx];
          out += '<th' + (a ? ' align="' + a + '"' : '') + '>' +
            parseInlineHtml(cell, ctx) + '</th>\n';
        });
        out += '</tr>\n</thead>\n';
        if (nd.rows.length > 0) {
          out += '<tbody>';
          for (const row of nd.rows) {
            out += '<tr>\n';
            row.forEach((cell, idx) => {
              const a = nd.aligns[idx];
              out += '<td' + (a ? ' align="' + a + '"' : '') + '>' +
                parseInlineHtml(cell, ctx) + '</td>\n';
            });
            out += '</tr>\n';
          }
          out += '</tbody>';
        }
        out += '</table>\n';
        break;
      }
      default:
        break;
    }
  }
  return out;
}

// ------------------------------------------------------------------- entry

export function parse(markdown) {
  const src = String(markdown)
    .replace(/\0/g, '�')
    .replace(/\r\n/g, '\n')
    .replace(/\r/g, '\n');
  const endsNl = src.endsWith('\n');
  const lines = src.split('\n');
  if (endsNl) lines.pop();
  const ctx = { refs: new Map(), endsAtDocEnd: true, srcEndsNl: endsNl, gs: { inLink: false } };
  const nodes = parseBlocks(lines, ctx);
  return renderNodes(nodes, ctx, false);
}
