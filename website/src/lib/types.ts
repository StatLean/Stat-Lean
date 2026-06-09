export type CategoryId =
  | "parametric"
  | "semiparametric"
  | "empirical"
  | "probability";

export type ResultKind = "definition" | "theorem" | "lemma" | "proposition" | "corollary" | "equation";

/** A link between a Lean hypothesis token and a span in the informal statement. */
export interface HypothesisLink {
  /** stable id, e.g. "h1" */
  id: string;
  /** the exact Lean substring to make hoverable in the code pane (first match) */
  leanToken: string;
  /** short human label shown in the legend / tooltip */
  label: string;
  /** plain-language note explaining the correspondence (optional) */
  note?: string;
}

export interface DepNode {
  id: string;
  /** display label (last name component) */
  label: string;
  /** fully qualified Lean name */
  full: string;
  kind: "root" | "repo" | "mathlib";
  /** declaration role: theorem/lemma vs definition/structure */
  decl: "thm" | "def";
  /** defining module, e.g. "Mathlib.Analysis.InnerProductSpace.Projection.Basic" */
  module: string;
}

export interface DepGraph {
  root: string;
  nodes: DepNode[];
  edges: { source: string; target: string }[];
}

export interface ResultEntry {
  /** url-safe id, e.g. "eif_eq_orthogonalProjection" */
  id: string;
  category: CategoryId;
  kind: ResultKind;
  /** short Lean declaration name */
  leanName: string;
  /** fully-qualified Lean name (for doc-gen anchor) */
  fullName: string;
  /** human title shown in lists */
  title: string;
  /** citation, e.g. "van der Vaart (1998), Thm 25.18" */
  citation: string;
  /** source module path, e.g. "AsymptoticStatistics/Core/EIF.lean" */
  file: string;
  /** relative doc-gen4 URL */
  docGenUrl: string;
  /**
   * Informal statement as an HTML string. Math is written with $...$ / $$...$$
   * and rendered with KaTeX at display time. Hypothesis spans are wrapped as
   * <span data-link="h1">...</span> to drive hover highlighting.
   */
  informal: string;
  /** one-line plain summary for cards & search */
  summary: string;
  /** the Lean statement signature (code) */
  leanSignature: string;
  /** notes on hypotheses the Lean formalization adds vs. the textbook (optional) */
  formalizationNotes?: string;
  hypotheses: HypothesisLink[];
  /** whether a generated dependency graph exists under data/graphs/<id>.json */
  hasGraph: boolean;
}
