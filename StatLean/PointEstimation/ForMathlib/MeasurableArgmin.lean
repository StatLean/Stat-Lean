import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# A measurable selection of minimizers of a parametrized convex scan

Given a family `f : Ω → ℝ → ℝ≥0∞` of convex, continuous, coercive functions of a real scan
variable, depending measurably on a parameter `ω`, there is a **measurable** map
`u : Ω → ℝ` picking a minimizer of `f ω` for every `ω`.

* `iInf_eq_iInf_rat_of_continuous` — a continuous `ℝ≥0∞`-valued function has the same
  infimum over `ℝ` as over `ℚ`;
* `exists_forall_le_of_continuous_of_coercive` — a continuous coercive function attains its
  infimum;
* `exists_measurable_argmin` — the measurable selection.

This is the brick that makes "minimize the conditional risk pointwise, then read the answer
off as an estimator" legitimate: the pointwise minimizer must be a *measurable* function of
the conditioning variable before it can be called an estimator at all.

**Reference.** Classical measurable-selection theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* **Continuity, not lower semicontinuity — deliberate.** The natural hypothesis for a
  measurable-argmin theorem is lower semicontinuity in the scan variable, and the statement
  below does hold in that generality. Continuity is assumed instead because it keeps the
  selection *elementarily* provable: the relaxed sublevel sets can be tested on rationals
  (see the next item), whereas the lower semicontinuous version routes through a genuine
  selection theorem. Weakening `hcont` to `LowerSemicontinuous (f ω)` is a strengthening that
  can be made later without touching any call site.
* **Rational-relaxed-sublevel selection.** Take `u ω` to be the *leftmost* minimizer,
  `u ω = sInf {v | f ω v = ⨅ w, f ω w}` (nonempty by
  `exists_forall_le_of_continuous_of_coercive`, closed by continuity, bounded below by
  coercivity, and an interval by convexity). Measurability follows from
  `u ω < r ↔ ∃ q : ℚ, (q : ℝ) < r ∧ ⨅ v ∈ Set.Iic (q : ℝ), f ω v = ⨅ v, f ω v`, where each
  relativized infimum is again a countable infimum over rationals by the density argument of
  `iInf_eq_iInf_rat_of_continuous`. Every set on the right is measurable because `f` is
  jointly measurable, and the union is countable.
* `iInf_eq_iInf_rat_of_continuous` is stated globally over `ℝ`; the selection proof uses the
  same density argument relativized to `Set.Iic q`, which is the special case of
  `⨅ x ∈ closure s, g x = ⨅ x ∈ s, g x` for continuous `g`.
* **Convexity is `ConvexOn ℝ≥0 Set.univ`.** For an `ℝ≥0∞`-valued function this is the only
  convexity predicate that typechecks at this pin: `ConvexOn 𝕜` needs `SMul 𝕜 ℝ≥0∞`, and
  `ℝ≥0∞` is a module over `ℝ≥0` but not over `ℝ`. On `[0, ∞]`-valued functions of a real
  variable the `ℝ≥0`-coefficient definition is the usual midpoint-convexity condition, so
  nothing is lost.
* **Coercivity is `Tendsto (f ω) (cocompact ℝ) (𝓝 ⊤)`, not `… atTop`.** In `ℝ≥0∞`,
  `Filter.atTop = pure ⊤` (`OrderTop.atTop_eq`), so the `atTop` phrasing would read "`f ω`
  equals `⊤` off a compact set" — true but useless. The `𝓝 ⊤` form is the intended "`f ω`
  blows up at infinity"; for `ℝ`-valued scans (see `ForMathlib/ConvexMinimizers.lean`) the
  two coincide and `atTop` is used there.
* **Attainment is derived, never hypothesized.** The conclusion asserts
  `f ω (u ω) = ⨅ v, f ω v`, i.e. that the infimum *is attained at the selected point*; it is
  forced by continuity plus coercivity and so must not appear as a hypothesis.

**Bibliographic comments.** Measurable selections of set-valued maps are due to
K. Kuratowski and C. Ryll-Nardzewski ("A general theorem on selectors," *Bull. Acad. Polon.
Sci. Sér. Sci. Math. Astronom. Phys.* **13** (1965), 397–403); the special case of an
argmin selection for a Carathéodory integrand is the standard application of that theorem,
here replaced by the elementary leftmost-minimizer construction.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.PointEstimation

/-- The infimum of a continuous `ℝ≥0∞`-valued function over `ℝ` is already attained as an
infimum over the rationals. -/
theorem iInf_eq_iInf_rat_of_continuous
    -- USER-INPUT: the function to be minimized; free choice
    {g : ℝ → ℝ≥0∞}
    -- USER-INPUT: continuity; the density argument fails for a merely measurable `g`
    (hg : Continuous g) :
    (⨅ x : ℝ, g x) = ⨅ q : ℚ, g (q : ℝ) := by
  sorry

/-- A continuous coercive `ℝ≥0∞`-valued function on `ℝ` attains its infimum. -/
theorem exists_forall_le_of_continuous_of_coercive
    -- USER-INPUT: the function to be minimized; free choice
    {g : ℝ → ℝ≥0∞}
    -- USER-INPUT: continuity; closedness of sublevel sets
    (hg : Continuous g)
    -- USER-INPUT: coercivity; compactness of a nontrivial sublevel set. See the header for
    -- why the target filter is `𝓝 ⊤` rather than `atTop`.
    (hcoer : Tendsto g (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞))) :
    ∃ x : ℝ, ∀ y : ℝ, g x ≤ g y := by
  sorry

/-- **Measurable argmin.** A jointly measurable family of convex, continuous, coercive
functions of a real scan variable admits a measurable minimizer selection. -/
theorem exists_measurable_argmin {Ω : Type*} [MeasurableSpace Ω]
    -- USER-INPUT: the parametrized objective (a conditional risk in applications)
    {f : Ω → ℝ → ℝ≥0∞}
    -- USER-INPUT: joint measurability; without it no selection can be measurable
    (hf : Measurable (Function.uncurry f))
    -- USER-INPUT: continuity in the scan variable; see the header on the LSC strengthening
    (hcont : ∀ ω, Continuous (f ω))
    -- USER-INPUT: convexity in the scan variable; makes the minimizer set an interval
    (hconv : ∀ ω, ConvexOn ℝ≥0 Set.univ (f ω))
    -- USER-INPUT: coercivity in the scan variable; forces attainment
    (hcoer : ∀ ω, Tendsto (f ω) (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞))) :
    ∃ u : Ω → ℝ, Measurable u ∧ ∀ ω, f ω (u ω) = ⨅ v : ℝ, f ω v := by
  sorry

end StatLean.PointEstimation
