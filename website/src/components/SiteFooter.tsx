import { Link } from "react-router-dom";
import { REPO_URL, DOCS_BASE } from "../lib/site";
import { Logo } from "./Logo";

export function SiteFooter() {
  return (
    <footer className="border-t hairline mt-24">
      <div className="max-w-page mx-auto px-5 sm:px-8 py-12 grid gap-8 sm:grid-cols-3 text-sm">
        <div>
          <div className="flex items-center gap-2.5 mb-1">
            <Logo className="w-8 h-8 text-ink shrink-0" />
            <span className="font-display text-lg font-semibold">Stat-Lean</span>
          </div>
          <p className="text-ink-soft mt-2 leading-relaxed font-serif">
            Formalized results from asymptotic statistical theory, each
            informal statement aligned with its machine-checked Lean&nbsp;4 /
            Mathlib formalization.
          </p>
        </div>
        <div className="font-sans">
          <div className="text-ink-faint uppercase tracking-widest text-xs mb-3">
            Browse
          </div>
          <ul className="space-y-1.5 text-ink-soft">
            <li><Link className="ulink" to="/search">Search results</Link></li>
            <li><Link className="ulink" to="/dependencies">Dependency graph</Link></li>
            <li><Link className="ulink" to="/category/parametric">Parametric Statistics</Link></li>
            <li><Link className="ulink" to="/category/semiparametric">Semiparametric Statistics</Link></li>
            <li><Link className="ulink" to="/category/empirical">Empirical Processes</Link></li>
            <li><Link className="ulink" to="/category/probability">Miscellaneous Results</Link></li>
          </ul>
        </div>
        <div className="font-sans">
          <div className="text-ink-faint uppercase tracking-widest text-xs mb-3">
            Project
          </div>
          <ul className="space-y-1.5 text-ink-soft">
            <li><a className="ulink" href={REPO_URL}>Source repository</a></li>
            <li><a className="ulink" href={DOCS_BASE}>doc-gen4 API reference</a></li>
          </ul>
        </div>
      </div>
      <div className="border-t hairline">
        <div className="max-w-page mx-auto px-5 sm:px-8 py-5 text-xs text-ink-faint font-sans flex flex-wrap gap-x-4 gap-y-1 justify-between">
          <span>Formalized in Lean 4 · Mathlib v4.29.1</span>
          <span>Built with a hypothesis-disciplined multi-agent workflow.</span>
        </div>
      </div>
    </footer>
  );
}
