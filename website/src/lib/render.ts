import katex from "katex";
import type { HypothesisLink } from "./types";

/**
 * Render an informal statement HTML string: keep its markup (including
 * <span data-link="..."> hover anchors) and replace $...$ / $$...$$ with KaTeX.
 */
export function renderInformal(html: string): string {
  // display math first so the inline pass doesn't eat the delimiters
  const display = html.replace(/\$\$([\s\S]+?)\$\$/g, (_m, tex) =>
    safeKatex(tex, true),
  );
  return display.replace(/\$([^$\n]+?)\$/g, (_m, tex) => safeKatex(tex, false));
}

function safeKatex(tex: string, displayMode: boolean): string {
  try {
    return katex.renderToString(tex.trim(), {
      displayMode,
      throwOnError: false,
      strict: false,
    });
  } catch {
    return `<code>${escapeHtml(tex)}</code>`;
  }
}

export function escapeHtml(s: string): string {
  return s
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;");
}

const LEAN_KEYWORDS = new Set([
  "theorem", "lemma", "def", "structure", "class", "instance", "where",
  "variable", "variables", "open", "namespace", "end", "import", "by",
  "fun", "let", "in", "if", "then", "else", "match", "with", "do", "have",
  "show", "from", "calc", "intro", "exact", "refine", "apply", "rw", "simp",
  "abbrev", "noncomputable", "protected", "private", "section", "deriving",
  "extends", "Prop", "Type", "Sort", "forall", "exists",
]);

/** very light tokenizer for a single segment of Lean text (already trusted as raw). */
function highlightSegment(seg: string): string {
  let out = "";
  // process line-comments and block comments / docstrings first by splitting
  // on comment boundaries; keep it simple and regex-based.
  const tokenRe = /(--[^\n]*|\/-[\s\S]*?-\/|[A-Za-z_][A-Za-z0-9_'.]*|\d+(?:\.\d+)?|[^\sA-Za-z0-9_]+|\s+)/g;
  let m: RegExpExecArray | null;
  while ((m = tokenRe.exec(seg)) !== null) {
    const t = m[0];
    if (t.startsWith("--") || t.startsWith("/-")) {
      out += `<span class="lean-comment">${escapeHtml(t)}</span>`;
    } else if (/^\d/.test(t)) {
      out += `<span class="lean-lit">${escapeHtml(t)}</span>`;
    } else if (/^[A-Za-z_]/.test(t)) {
      const bare = t.split(".")[0];
      if (LEAN_KEYWORDS.has(t) || LEAN_KEYWORDS.has(bare)) {
        out += `<span class="lean-kw">${escapeHtml(t)}</span>`;
      } else if (/^[A-Z]/.test(t)) {
        out += `<span class="lean-type">${escapeHtml(t)}</span>`;
      } else {
        out += escapeHtml(t);
      }
    } else {
      out += escapeHtml(t);
    }
  }
  return out;
}

interface Range {
  start: number;
  end: number;
  id: string;
}

/**
 * Render Lean code to HTML with light syntax highlighting and hypothesis tokens
 * wrapped in hoverable spans (data-link="<id>").
 */
export function renderLean(code: string, hypotheses: HypothesisLink[]): string {
  const ranges: Range[] = [];
  const used: [number, number][] = [];
  for (const h of hypotheses) {
    if (!h.leanToken) continue;
    let from = 0;
    let idx = -1;
    // find first non-overlapping occurrence
    while ((idx = code.indexOf(h.leanToken, from)) !== -1) {
      const end = idx + h.leanToken.length;
      const overlaps = used.some(([s, e]) => idx < e && end > s);
      if (!overlaps) {
        ranges.push({ start: idx, end, id: h.id });
        used.push([idx, end]);
        break;
      }
      from = idx + 1;
    }
  }
  ranges.sort((a, b) => a.start - b.start);

  let out = "";
  let cursor = 0;
  for (const r of ranges) {
    if (r.start > cursor) out += highlightSegment(code.slice(cursor, r.start));
    out += `<span class="hl-token" data-link="${r.id}">${highlightSegment(
      code.slice(r.start, r.end),
    )}</span>`;
    cursor = r.end;
  }
  if (cursor < code.length) out += highlightSegment(code.slice(cursor));
  return out;
}
