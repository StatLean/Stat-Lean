import Mathlib.InformationTheory.Hamming
import StatLean.PointEstimation.Equivariance.Defs

/-!
# Finite-sample replacement breakdown point

The replacement finite-sample breakdown point of an estimator at a data set `x` is the
largest fraction `m*/n` of observations that can be replaced by arbitrary values while the
estimate stays bounded (`MMY §3.2.5`, eq. (3.24)–(3.25); Donoho–Huber 1983). Replacement
contamination is measured by the Hamming distance `hammingDist x y = #{i : xᵢ ≠ yᵢ}`
(Mathlib's `hammingDist`), which must not be conflated with the population ε-mixture of
`Core/Contamination.lean` — the two contamination models get separate primitives.

* `Resists T x m` — the estimate stays uniformly bounded over all `m`-replacements of `x`.
* `BreaksUnder T x m` — some `m`-replacement drives `|T|` beyond any bound.
* `breakdownCount T x` — `m* = max {m ≤ n : Resists T x m}` (`MMY` eq. (3.25)).
* `breakdownPoint T x` — `ε*_n = m*/n` (`MMY` eq. (3.24)).
* `locEquivariant_not_resists`, `locEquivariant_breakdownCount_le` — no location-equivariant
  estimator resists `⌈n/2⌉` replacements: `m* ≤ ⌊(n-1)/2⌋` (`MMY` eq. (3.26), §3.8.2).

**Scope (location parameters).** The parameter space is `ℝ`, so "breakdown" means
`|T y| → ∞`; the boundary-of-`Θ` refinement needed for scale parameters (implosion to `0`)
is deferred to the scale round.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §3.2.5 (eq.
(3.24)–(3.26)), §3.8.2.

**Bibliographic comments.** D. L. Donoho and P. J. Huber, "The notion of breakdown point,"
in *A Festschrift for Erich L. Lehmann*, Wadsworth, 1983, pp. 157–184.
-/

namespace StatLean.RobustStatistics

variable {n : ℕ} (T : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)

/-- **Resistance to `m` replacements** (`MMY §3.2.5`): the estimate stays uniformly
bounded when at most `m` observations of `x` are replaced by arbitrary values. -/
def Resists (m : ℕ) : Prop :=
  ∃ M : ℝ, ∀ y : Fin n → ℝ, hammingDist x y ≤ m → |T y| ≤ M

/-- **Breakdown under `m` replacements** (`MMY §3.2.5`): replacing at most `m`
observations can drive the estimate beyond any bound. -/
def BreaksUnder (m : ℕ) : Prop :=
  ∀ M : ℝ, ∃ y : Fin n → ℝ, hammingDist x y ≤ m ∧ M < |T y|

variable {T x}

/-- Breakdown is the negation of resistance. -/
theorem breaksUnder_iff_not_resists {m : ℕ} : BreaksUnder T x m ↔ ¬Resists T x m := by
  sorry

/-- Resistance is antitone in the number of allowed replacements. -/
theorem Resists.anti {m m' : ℕ} (hmm' : m ≤ m') (h : Resists T x m') : Resists T x m := by
  sorry

/-- Every estimator resists `0` replacements. -/
theorem resists_zero : Resists T x 0 := by
  sorry

variable (T x)

/-- The **breakdown count** `m*` (`MMY §3.2.5`, eq. (3.25)): the largest number `m ≤ n`
of replacements the estimator resists at `x`. -/
noncomputable def breakdownCount : ℕ :=
  sSup {m | m ≤ n ∧ Resists T x m}

/-- The **finite-sample replacement breakdown point** `ε*_n = m*/n`
(`MMY §3.2.5`, eq. (3.24)). Junk value `0` when `n = 0`. -/
noncomputable def breakdownPoint : ℝ :=
  breakdownCount T x / n

variable {T x}

/-- The estimator resists its breakdown count. -/
theorem resists_breakdownCount : Resists T x (breakdownCount T x) := by
  sorry

/-- Any resisted replacement number (at most `n`) is below the breakdown count. -/
theorem le_breakdownCount {m : ℕ} (hm : m ≤ n) (h : Resists T x m) :
    m ≤ breakdownCount T x := by
  sorry

/-- The breakdown count is at most the sample size. -/
theorem breakdownCount_le_card : breakdownCount T x ≤ n := by
  sorry

/-- Characterization by a witness pair: resists `m`, breaks under `m + 1`. -/
theorem breakdownCount_eq_of_resists_of_breaksUnder {m : ℕ} (hm : m ≤ n)
    (hres : Resists T x m) (hbreak : BreaksUnder T x (m + 1)) :
    breakdownCount T x = m := by
  sorry

/-- Breaking under one replacement forces breakdown count `0`. -/
theorem breakdownCount_eq_zero_of_breaksUnder_one (h : BreaksUnder T x 1) :
    breakdownCount T x = 0 := by
  sorry

/-! ### The maximal breakdown of location-equivariant estimators (`MMY` eq. (3.26)) -/

/-- **No location-equivariant estimator resists `⌈n/2⌉` replacements** (`MMY §3.8.2`,
finite-sample form): if `n ≤ 2m`, a resisted `m`-replacement bound would contradict shift
equivariance, since a data set can be driven toward both `x` and an arbitrarily large
shift of `x` simultaneously. -/
theorem locEquivariant_not_resists (hT : PointEstimation.IsLocEquivariant T)
    (hn : 0 < n) {m : ℕ} (hm : n ≤ 2 * m) : ¬Resists T x m := by
  sorry

/-- **The maximal finite-sample breakdown bound** (`MMY §3.2.5`, eq. (3.26)): every
location-equivariant estimator has `m* ≤ ⌊(n-1)/2⌋`. The sample median attains this bound
(`LocationScale/MedianBreakdown.lean`). -/
theorem locEquivariant_breakdownCount_le (hT : PointEstimation.IsLocEquivariant T)
    (hn : 0 < n) : breakdownCount T x ≤ (n - 1) / 2 := by
  sorry

end StatLean.RobustStatistics
