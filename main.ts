// markdown-render-speed-02 driver (hand-written for this entry).
// Reads every case from (MAKEFUN_INPUT_DIR ?? "/input")/cases.json,
// renders each one with our own parse(), and writes a JSON array of
// { id, html } to (MAKEFUN_OUTPUT_DIR ?? "/output")/html.json.
import { parse } from "./parse.js";
import { readFileSync, writeFileSync, mkdirSync } from "node:fs";
import { join } from "node:path";

interface Case {
  id: string;
  markdown: string;
}

const inputDir: string = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const outputDir: string = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";

const raw: string = readFileSync(join(inputDir, "cases.json"), "utf-8");
const cases = JSON.parse(raw) as Case[];

const results = cases.map((c) => ({ id: c.id, html: parse(c.markdown) }));

mkdirSync(outputDir, { recursive: true });
writeFileSync(join(outputDir, "html.json"), JSON.stringify(results));
