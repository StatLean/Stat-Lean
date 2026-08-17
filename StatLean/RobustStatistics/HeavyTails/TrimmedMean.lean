import StatLean.RobustStatistics.ForMathlib.OrderStatPerturb
import StatLean.RobustStatistics.LocationScale.Mean
import StatLean.ConcentrationInequalities.Bernstein.Bernstein
import Mathlib.Probability.Moments.Variance

/-!
# The trimmed mean is sub-Gaussian — truncation at data-driven quantiles

Truncating at fixed levels cannot be sub-Gaussian (the levels must scale with the
confidence); the modern result — Oliveira–Orenstein (2019), presented as `LM §2.3` — is
that trimming a `log(1/δ)/n`-fraction *chosen from the data* is. This file formalizes
the sample-split variant analyzed in `LM Theorem 6`: one half of the data picks the
truncation levels as order statistics, the other half is averaged after truncation:

  `μ̂₂ₙ = (1/n) ∑ᵢ φ_{α,β}(Xᵢ)`,  `α = Y*₍εn₎`, `β = Y*₍₍₁₋ε₎n₎`, `ε = 16 log(8/δ)/(3n)`,

and `|μ̂₂ₙ − μ| ≤ 9σ√(log(8/δ)/n)` with probability `≥ 1 − δ`. Unlike median-of-means,
the trimmed mean is also robust to adversarial contamination (Lugosi–Mendelson (2021),
Ann. Statist. — bib note only; not formalized this round).

* `truncate` — the truncation function `φ_{a,b}` (`LM §2.3`); Huber's score is the
  symmetric special case `truncate (−c) c = huberPsi c`.
* `trimmedMeanAt` — the two-sample estimator with `Fin`-indexed truncation levels.
* `quantile` — `Q_p = sup{M : P(X ≥ M) ≥ 1 − p}` (`LM §2.3` proof).
* `orderStat_quantile_brackets` — the Bernstein bracketing `LM (2.6)`–`(2.7)`.
* `truncated_bias_le` / `truncated_concentration` — the two proof halves.
* `trimmedMean_deviation` — `LM Theorem 6`.

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §2.3, displays (2.6)–(2.7), Theorem 6; after R. I. Oliveira and P. Orenstein,
*The sub-Gaussian property of trimmed means* (2019). Truncation levels are Round-1
`orderStat`s; the count concentration is `ConcentrationInequalities.bernstein_inequality`.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

open StatLean.MultipleTesting in
/-- **The truncation function** `φ_{a,b}(x) = max a (min b x)` (`LM §2.3`): the identity
on `[a, b]`, clipped to the nearer endpoint outside. For `a ≤ b` this is the projection
onto `[a, b]`; Huber's score is the symmetric case `truncate (−c) c = huberPsi c`. -/
noncomputable def truncate (a b x : ℝ) : ℝ := max a (min b x)

/-- Truncation projects into the interval: `a ≤ b → truncate a b x ∈ [a, b]`. -/
theorem truncate_mem_Icc {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    truncate a b x ∈ Set.Icc a b := by
  sorry

/-- Truncation fixes interval points: `x ∈ [a, b] → truncate a b x = x`. -/
theorem truncate_eq_self {a b x : ℝ} (hx : x ∈ Set.Icc a b) : truncate a b x = x := by
  sorry

open StatLean.MultipleTesting in
/-- **The two-sample trimmed mean** (`LM §2.3`, the estimator of Theorem 6): truncate
the `x`-sample at the `a`-th and `b`-th order statistics of the independent `y`-sample
and average. The intended indices are `a = εn − 1` and `b = (1−ε)n − 1` (0-indexed) for
the trimming fraction `ε`; they are parameters here, fixed by the theorem. -/
noncomputable def trimmedMeanAt {n : ℕ} (a b : Fin n) (x y : Fin n → ℝ) : ℝ :=
  sampleMean (fun i => truncate (orderStat y a) (orderStat y b) (x i))

/-- **The upper quantile function** `Q_p = sup{M : P(X ≥ M) ≥ 1 − p}` (`LM §2.3`
proof). For a probability measure and `p ∈ (0, 1)` the defining set is nonempty and
bounded above, so the supremum is honest. -/
noncomputable def quantile (P : Measure ℝ) (p : ℝ) : ℝ :=
  sSup {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}}

/-- The quantile's defining set is nonempty and bounded above when `0 < p < 1`
(`LM §2.3` proof, implicit): mass to the right tends to `1` at `−∞` and to `0` at
`+∞`. -/
theorem quantile_set_nonempty_bddAbove (P : Measure ℝ) [IsProbabilityMeasure P]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}}.Nonempty ∧
      BddAbove {M : ℝ | 1 - p ≤ P.real {x | M ≤ x}} := by
  sorry

/-- **Right-tail mass at the quantile** (`LM §2.3` proof, "in that case
`P(X ≥ Q_p) = 1 − p`"): for a nonatomic distribution the quantile achieves its level
exactly. The no-atoms hypothesis is LM's "assume `X` has a nonatomic distribution"
simplification, carried explicitly. -/
theorem measure_ge_quantile (P : Measure ℝ) [IsProbabilityMeasure P]
    -- USER-INPUT: nonatomic distribution; LM §2.3 proof ("for ease of exposition")
    (hatom : ∀ t : ℝ, P {t} = 0)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    P.real {x | quantile P p ≤ x} = 1 - p := by
  sorry

variable {Ξ : Type*} [MeasurableSpace Ξ] {μprob : Measure Ξ} [IsProbabilityMeasure μprob]
  {P : Measure ℝ} [IsProbabilityMeasure P]

open StatLean.MultipleTesting in
/-- **The Bernstein order-statistic brackets** (`LM (2.6)`–`(2.7)`): with probability at
least `1 − 4 exp(−(3/16) r)`, the trimming order statistics of an i.i.d. sample `Y` are
bracketed by population quantiles — writing `ε = r/n`,

  `Q_{ε/2} ≤ Y*₍εn₎ ≤ Q_{2ε}`  and  `Q_{1−2ε} ≤ Y*₍₍₁₋ε₎n₎ ≤ Q_{1−ε/2}`.

Each one-sided count deviation is a Bernstein event for indicator sums at rate
`exp(−(3/16)εn) = exp(−(3/16)r)`. -/
theorem orderStat_quantile_brackets {n r : ℕ} {Y : Fin n → Ξ → ℝ}
    {a b : Fin n}
    -- LEAN-ONLY: coordinate measurability; LM §2.3 regularity
    (hY_meas : ∀ i, Measurable (Y i))
    -- USER-INPUT: jointly independent sample; LM Theorem 6
    (hY_indep : iIndepFun Y μprob)
    -- USER-INPUT: common law P; LM Theorem 6
    (hY_law : ∀ i, μprob.map (Y i) = P)
    -- USER-INPUT: nonatomic P; LM §2.3 proof simplification
    (hatom : ∀ t : ℝ, P {t} = 0)
    -- USER-INPUT: the trim count is in the working range 1 ≤ r, 4r < n
    -- (so that ε = r/n has 2ε < 1/2); LM Theorem 6 sample-size condition
    (hr1 : 1 ≤ r) (hrn : 4 * r < n)
    -- USER-INPUT: the trimming indices, 0-indexed: a = εn − 1, b = (1−ε)n − 1;
    -- LM §2.3 step (2)
    (ha : (a : ℕ) + 1 = r) (hb : (b : ℕ) + r + 1 = n) :
    1 - 4 * Real.exp (-(3 / 16) * r)
      ≤ μprob.real {ξ |
          quantile P (r / (2 * n)) ≤ orderStat (fun i => Y i ξ) a ∧
          orderStat (fun i => Y i ξ) a ≤ quantile P (2 * r / n) ∧
          quantile P (1 - 2 * r / n) ≤ orderStat (fun i => Y i ξ) b ∧
          orderStat (fun i => Y i ξ) b ≤ quantile P (1 - r / (2 * n))} := by
  sorry

/-- **The truncation-bias bound** (`LM Theorem 6` proof, the display
`|E[φ_{α,β}(X)|Y] − μ| ≤ σ√(32ε)`): whenever the truncation levels are quantile-
bracketed as in `orderStat_quantile_brackets`, the conditional bias of the truncated
variable is at most `σ√(32ε)` with `ε = r/n` — via Chebyshev on the tail location
(`Q_{1−2ε} ≤ μ + σ/√(2ε)`) and Cauchy–Schwarz on the truncated tails. Stated at the
population level: for any deterministic levels `α β` inside the brackets. -/
theorem truncated_bias_le {μ₀ σ2 : ℝ} {r n : ℕ} {α β : ℝ}
    -- USER-INPUT: P is square-integrable with mean μ₀ and variance σ²; LM Theorem 6
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    -- USER-INPUT: nonatomic P; LM §2.3 proof simplification
    (hatom : ∀ t : ℝ, P {t} = 0)
    (hr1 : 1 ≤ r) (hrn : 4 * r < n)
    -- USER-INPUT: the levels sit inside the LM (2.6)–(2.7) brackets
    (hα₁ : quantile P (r / (2 * n)) ≤ α) (hα₂ : α ≤ quantile P (2 * r / n))
    (hβ₁ : quantile P (1 - 2 * r / n) ≤ β) (hβ₂ : β ≤ quantile P (1 - r / (2 * n))) :
    |(∫ x, truncate α β x ∂P) - μ₀| ≤ Real.sqrt σ2 * Real.sqrt (32 * r / n) := by
  sorry

open StatLean.MultipleTesting in
/-- **The trimmed mean is sub-Gaussian** (`LM Theorem 6`): two independent i.i.d.
samples of size `n` (presented as one jointly independent family on `Fin n ⊕ Fin n`;
`.inl` = averaged sample, `.inr` = truncation-calibration sample), variance `σ² > 0`,
`δ ∈ (0,1)` with `n > (16/3) log(8/δ)`, trim count `r = εn` for
`ε = 16 log(8/δ)/(3n)` (LM's "εn is an integer" simplification, carried as the
integrality hypothesis `hr`). Then with probability at least `1 − δ`,

  `|μ̂₂ₙ − μ₀| ≤ 9 σ √(log(8/δ)/n)`.

**Constant note.** LM's `9` combines a bias term they bound by `6σ√(log(8/δ)/n)` and a
Bernstein term bounded by `3σ√(log(8/δ)/n)`; the closure lane must verify the composite
constant and, per the project constants policy, repair to the provable value (keeping
the `σ√(log(8/δ)/n)` shape) with a documented deviation if `9` does not survive
formalization. -/
theorem trimmedMean_deviation {n r : ℕ} {Z : Fin n ⊕ Fin n → Ξ → ℝ}
    {a b : Fin n} {μ₀ σ2 δ : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §2.3 regularity
    (hZ_meas : ∀ i, Measurable (Z i))
    -- USER-INPUT: the 2n observations are jointly independent; LM Theorem 6
    (hZ_indep : iIndepFun Z μprob)
    -- USER-INPUT: common law P; LM Theorem 6
    (hZ_law : ∀ i, μprob.map (Z i) = P)
    -- USER-INPUT: P is square-integrable with mean μ₀ and variance σ² > 0; LM Thm 6
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2) (hσ : 0 < σ2)
    -- USER-INPUT: nonatomic P; LM §2.3 proof simplification
    (hatom : ∀ t : ℝ, P {t} = 0)
    -- USER-INPUT: confidence level and sample-size condition; LM Theorem 6
    (hδ : 0 < δ) (hδ1 : δ < 1) (hn : 16 / 3 * Real.log (8 / δ) < n)
    -- USER-INPUT: trim count integrality ε·n = r; LM §2.3 step (1) simplification
    (hr : (r : ℝ) = 16 * Real.log (8 / δ) / 3) (hr1 : 1 ≤ r) (hrn : 4 * r < n)
    -- USER-INPUT: trimming indices (0-indexed); LM §2.3 step (2)
    (ha : (a : ℕ) + 1 = r) (hb : (b : ℕ) + r + 1 = n) :
    μprob.real {ξ | 9 * Real.sqrt σ2 * Real.sqrt (Real.log (8 / δ) / n)
        < |trimmedMeanAt a b (fun i => Z (.inl i) ξ) (fun i => Z (.inr i) ξ) - μ₀|}
      ≤ δ := by
  sorry

end StatLean.RobustStatistics
