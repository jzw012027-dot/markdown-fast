# markdown-fast — a faster drop-in for marked

![competition](https://make.fun/badge/markdown-render-speed-02.svg)
![rank](https://make.fun/badge/markdown-render-speed-02/jzw012027-dot/markdown-fast/rank.svg)
![reward](https://make.fun/badge/markdown-render-speed-02/jzw012027-dot/markdown-fast/reward.svg)

Entry for [markdown-render-speed-02 on make.fun](https://make.fun/bounty/markdown-render-speed-02) — Make Markdown rendering faster.

`parse.js` is a dependency-free JavaScript module whose `parse(markdown)`
returns exactly the HTML that marked 18.1.3 renders with its default
options (GFM on), and `main.ts` is the small driver the harness runs: it
reads every case from /input/cases.json, renders each with parse, and
writes /output/html.json.

MIT licensed — see LICENSE.

## Implementation

`parse.js` (about 1,900 lines, no dependencies, no build step) is a
hand-written Markdown parser built to match marked 18.1.3's default
output byte for byte. It works in two classic phases:

- **Block phase.** The source is normalized (NUL → U+FFFD, CRLF/CR →
  LF) and split into lines. `parseBlocks` walks the lines with
  column/tab-stop aware helpers and builds a small node tree:
  paragraphs, ATX/setext headings, fenced and indented code, HTML
  blocks (CommonMark types 1–7), blockquotes, lists (nested, loose/
  tight, task items), GFM tables, thematic breaks and link reference
  definitions. Containers (blockquotes, list items) are handled by
  collecting each container's lines with column-based stripping —
  including partially consumed tabs — and recursing. Link reference
  definitions are collected into a shared table during the block
  pass, so forward references resolve when the tree is rendered in
  document order.
- **Inline phase.** Each text run goes through a single-pass scanner
  (`tokenizeInline`) that produces tokens for code spans, escapes,
  entities, inline HTML, images/links (via a bracket stack with
  reference lookup), angle autolinks and GFM extended autolinks
  (www., scheme://, email, mailto:/xmpp:). Emphasis is resolved with
  the CommonMark delimiter-stack algorithm (`processEmphasis`) plus
  a separate pairing pass for `~~` strikethrough, recursing into
  wrapped children. Rendering walks the token tree and applies
  marked's exact escaping rules (full escaping in text/code,
  entity-aware escaping in attributes, `encodeURI`-based URL
  cleaning).

Where marked deviates from the CommonMark spec, the spec was not
followed — marked's observed behavior was, and the parser encodes a
number of those quirks: label validation by sequential backtick-run
pairing, emphasis matches blocked by a same-character inner emphasis
node in certain shapes (with the mirror rule that a strong match's
leftover delimiters from a 3+ closer run render inside the element),
emphasis suppression inside the label of a failed inline-link
attempt, the lexer-wide suppression of extended autolinks after an
`<a …>` tag with attributes, backtick fences stripping their indent
from content lines while tilde fences do not, and the depth-scan
"stray parenthesis" rule for extended-autolink trimming.

**Correctness (local check).** The kit's check script renders all
720 practice cases (652 CommonMark 0.31.2 examples, 28 GFM extension
examples, 40 generated long READMEs) and compares against the
reference output byte for byte: **720/720 cases match exactly** —
all 652 CommonMark cases, all 28 GFM cases and all 40 generated
long documents pass, with no failing cases remaining.

**Speed.** `../bench.mjs` benchmarks both parsers in one process
over the same 720 cases after a warmup pass. On the (shared,
noisy) development VM the two are at rough parity: a representative
run measured **ours 683.9 ms vs marked 828.5 ms (ratio 1.211)**,
and across repeated runs the ratio (marked / ours) fluctuated
between about 0.87 and 1.39 with a median near 1.05 — comparable
to marked, sometimes faster, not a guaranteed win on this machine.
