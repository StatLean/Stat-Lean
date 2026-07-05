import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Supremum over ℝ equals supremum over ℚ for right-approximable functions

For a bounded function $h : \mathbb{R} \to \mathbb{R}$ that is *right
approximable along the rationals* — for every $x$ and $\delta > 0$ there is a
rational $q \ge x$ with $h(x) \le h(q) + \delta$ — the (conditionally
complete) suprema agree:
$$ \sup_{x \in \mathbb{R}} h(x) \;=\; \sup_{q \in \mathbb{Q}} h(q). $$
In particular this holds when `h` is right-continuous at every point
(density of ℚ). This is the deterministic device of the project's fixed sup
policy: it recovers an *uncountable* supremum from a countable one with no
measure theory involved, and is consumed by the Glivenko–Cantelli theorem
(`VC/GlivenkoCantelli.lean`).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press — no numbered statement; this is the unspoken
"reduce to a countable dense set" step in the proof of Theorem 8.3.17
(Glivenko–Cantelli).

**Proof formalization notes.** Stated over the conditionally complete lattice
ℝ, so `BddAbove` is a genuine hypothesis (`ciSup` junk behavior otherwise).
`≥` is the nontrivial direction: `le_ciSup` on the ℚ side after extracting a
rational δ-approximant; `≤` of the ℚ-sup by the ℝ-sup is monotone
restriction. `right_approx_of_rightContinuous` derives the approximability
hypothesis from right-continuity (`ContinuousWithinAt h (Set.Ici x) x`) via
`exists_rat_btwn`. Edge behavior: ℝ and ℚ are both nonempty, so the `ciSup`s
are honest suprema under `hbd`. Pure order/topology; candidate upstream.
Named-sorry fallback of this work item: `iSup_eq_iSup_rat_of_right_approx`.

**Bibliographic comments.** The reduction of the Kolmogorov–Smirnov /
Glivenko–Cantelli supremum to a countable dense set is classical (V. Glivenko
and F. Cantelli, *Giorn. Ist. Ital. Attuari* 4 (1933)); the right-continuity
route used here follows the standard CDF treatment, cf. HDP §8.3 Notes.
-/

open Set

namespace StatLean.ConcentrationInequalities

/-- Sup over ℝ equals sup over ℚ for a bounded, right-ℚ-approximable
function (LEAN-ONLY sup-policy device; no book content). -/
theorem iSup_eq_iSup_rat_of_right_approx {h : ℝ → ℝ}
    -- LEAN-ONLY: boundedness so the conditionally complete `ciSup` is an
    -- honest supremum (junk otherwise); automatic for the |empFrac − μ| ≤ 1
    -- consumers.
    (hbd : BddAbove (Set.range h))
    -- LEAN-ONLY: right approximability along ℚ; derived from
    -- right-continuity by `right_approx_of_rightContinuous`.
    (happ : ∀ x : ℝ, ∀ δ > 0, ∃ q : ℚ, x ≤ (q : ℝ) ∧ h x ≤ h (q : ℝ) + δ) :
    (⨆ x : ℝ, h x) = ⨆ q : ℚ, h (q : ℝ) := by
  sorry

/-- Right-continuity gives right approximability along ℚ (LEAN-ONLY: density
of ℚ via `exists_rat_btwn`; no book content). -/
lemma right_approx_of_rightContinuous {h : ℝ → ℝ}
    -- LEAN-ONLY: right-continuity at every point; supplied by the CDF
    -- `StieltjesFunction` API and by the finite-sample empirical CDF.
    (hc : ∀ x : ℝ, ContinuousWithinAt h (Set.Ici x) x) :
    ∀ x : ℝ, ∀ δ > 0, ∃ q : ℚ, x ≤ (q : ℝ) ∧ h x ≤ h (q : ℝ) + δ := by
  sorry

end StatLean.ConcentrationInequalities
