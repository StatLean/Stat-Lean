export type CategoryId =
  | "parametric"
  | "hypothesistesting"
  | "pointestimation"
  | "semiparametric"
  | "concentration"
  | "highdim"
  | "multipletesting"
  | "minimaxity"
  | "optimization"
  | "bayesian"
  | "nonparametric"
  | "probability";

export type ResultKind = "definition" | "theorem" | "lemma" | "proposition" | "corollary" | "equation";

/** The REFERENCE block on a result page (formal citation + bibliographic notes). */
export interface ReferenceBlock {
  /** Full formal citation, e.g. "A. W. van der Vaart, *Asymptotic Statistics*, …, 1998." May carry $…$ math. */
  formal: string;
  /** Concise pointer into the source, e.g. "Theorem 7.2" or "Eq. (15.13)". */
  pointer: string;
  /** Bibliographic-comments paragraph (may carry $…$ math); rendered after the citation. */
  biblio?: string;
  /** Anchor ids on the references page this block links to (e.g. ["vdv1998", "lecam1960"]). */
  keys: string[];
}

/** One book / paper on the global references page. */
export interface Reference {
  /** stable anchor id, e.g. "vdv1998", "lu2026", "wainwright2019". */
  key: string;
  /** first author's surname, used for alphabetical ordering. */
  sortKey: string;
  /** full bibliographic entry as HTML (may carry $…$ math and *italics* via markdown-ish render). */
  html: string;
}

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
  /** 1-3 index terms for the Index page (standard textbook terminology). */
  keywords?: string[];
  /** short Lean declaration name */
  leanName: string;
  /** fully-qualified Lean name (for doc-gen anchor) */
  fullName: string;
  /** human title shown in lists */
  title: string;
  /** citation, e.g. "van der Vaart (1998), Thm 25.18" */
  citation: string;
  /**
   * Short pointer shown to the right of the informal statement, e.g.
   * "van der Vaart (1998), §19.2; Thm 18.14" or "Lu (2026), Thm 4.7".
   * The author–year prefix links to the references page (see `reference.keys`).
   * Falls back to `citation` when absent.
   */
  shortRef?: string;
  /** Full reference block shown above the formalization notes. */
  reference?: ReferenceBlock;
  /** source module path, e.g. "StatLean/AsymptoticStatistics/Core/EIF.lean" */
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
