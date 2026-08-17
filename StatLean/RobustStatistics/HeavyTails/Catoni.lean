import StatLean.RobustStatistics.MEstimation.MLocationFunctional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Moments.Variance

/-!
# Catoni's mean estimator — a soft-truncation M-estimator with sub-Gaussian deviation

Catoni (2012, Ann. IHP) replaces the empirical-mean estimating equation
`∑ (Xᵢ − y) = 0` by `∑ ψ(α(Xᵢ − y)) = 0` for a "soft truncation" influence function `ψ`
that grows only logarithmically (`LM §2.2`). The log-companion bounds
`−log(1 − x + x²/2) ≤ ψ(x) ≤ log(1 + x + x²/2)` turn the exponential moment of the
estimating function into an explicit quadratic in `y`, and Markov's inequality localizes
the root: with the right `α`, `|μ̂ − μ| < √(2σ²log(1/δ)/(n − 2 log(1/δ)))` with
probability `≥ 1 − 2δ` (`LM Theorem 5`) — sub-Gaussian with the *optimal* constant `√2`.

* `catoniPsi`, log-companion bounds, antisymmetry, strict monotonicity, continuity,
  limits at `±∞`.
* `catoniR` — the estimating function `R_{n,α}(y) = ∑ ψ(α(xᵢ − y))`; strict
  antitonicity in `y`, continuity, and the unique root (`existsUnique_isCatoniEstimate`).
* `integral_exp_catoniR_le` — the exponential-moment bound (`LM §2.2`, first display
  chain), the analytic heart.
* `catoni_deviation` — `LM Theorem 5`.

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §2.2, Theorem 5; the estimator and the wider family of admissible `ψ` are from
O. Catoni, *Challenging the empirical mean and empirical variance: a deviation study*,
Ann. Inst. H. Poincaré Probab. Stat. 48 (2012). Root existence/uniqueness reuses the
IVT/monotone route of `MEstimation/MLocationFunctional`.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

/-- **Catoni's soft-truncation influence function** (`LM §2.2`, the "one specific
choice"): `ψ(x) = log(1 + x + x²/2)` for `x ≥ 0` and `−log(1 − x + x²/2)` for `x < 0`.
Both companion polynomials are positive everywhere (discriminant `< 0`), so `ψ` is
well-defined and real-analytic on each branch. -/
noncomputable def catoniPsi (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.log (1 + x + x ^ 2 / 2) else -Real.log (1 - x + x ^ 2 / 2)

/-- The companion polynomials are positive: `0 < 1 + x + x²/2` for every `x` (and by
symmetry `0 < 1 − x + x²/2`). -/
theorem catoni_companion_pos (x : ℝ) : 0 < 1 + x + x ^ 2 / 2 := by
  nlinarith [sq_nonneg (x + 1)]

/-- The mirrored companion polynomial `1 − x + x²/2` is positive too (`catoni_companion_pos`
at `−x`); the negative branch of `ψ` is therefore well defined. -/
private theorem catoni_companion_pos' (x : ℝ) : 0 < 1 - x + x ^ 2 / 2 := by
  nlinarith [sq_nonneg (x - 1)]

/-- Both branches vanish at `0`, so `ψ(0) = 0`. -/
@[simp] private theorem catoniPsi_zero : catoniPsi 0 = 0 := by
  simp [catoniPsi]

/-- Catoni's `ψ` is antisymmetric: `ψ(−x) = −ψ(x)` (`LM §2.2`, "an antisymmetric
increasing function"). -/
theorem catoniPsi_neg (x : ℝ) : catoniPsi (-x) = -catoniPsi x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h1 : ¬ (0 ≤ x) := not_le.2 hx
    have h2 : (0:ℝ) ≤ -x := by linarith
    simp only [catoniPsi, if_pos h2, if_neg h1, neg_neg]
    ring_nf
  · simp [hx]
  · have h1 : (0:ℝ) ≤ x := hx.le
    have h2 : ¬ ((0:ℝ) ≤ -x) := by simpa using hx
    simp only [catoniPsi, if_pos h1, if_neg h2]
    ring_nf

/-- **The upper log-companion bound** (`LM §2.2`): `ψ(x) ≤ log(1 + x + x²/2)` for all
`x`. On the negative branch this is `1 ≤ (1 + x + x²/2)(1 − x + x²/2) = 1 + x⁴/4`. -/
theorem catoniPsi_le (x : ℝ) : catoniPsi x ≤ Real.log (1 + x + x ^ 2 / 2) := by
  rcases le_or_gt 0 x with hx | hx
  · simp [catoniPsi, hx]
  · have hA := catoni_companion_pos x
    have hB := catoni_companion_pos' x
    have hmul : Real.log ((1 + x + x ^ 2 / 2) * (1 - x + x ^ 2 / 2))
        = Real.log (1 + x + x ^ 2 / 2) + Real.log (1 - x + x ^ 2 / 2) :=
      Real.log_mul hA.ne' hB.ne'
    have hprod : (1 + x + x ^ 2 / 2) * (1 - x + x ^ 2 / 2) = 1 + x ^ 4 / 4 := by ring
    have hnn : 0 ≤ Real.log (1 + x ^ 4 / 4) :=
      Real.log_nonneg (by nlinarith [sq_nonneg (x ^ 2)])
    rw [hprod] at hmul
    simp only [catoniPsi, if_neg (not_le.2 hx)]
    linarith

/-- **The lower log-companion bound** (`LM §2.2`, by antisymmetry):
`−log(1 − x + x²/2) ≤ ψ(x)`. -/
theorem le_catoniPsi (x : ℝ) : -Real.log (1 - x + x ^ 2 / 2) ≤ catoniPsi x := by
  have h := catoniPsi_le (-x)
  rw [catoniPsi_neg] at h
  have e : 1 + -x + (-x) ^ 2 / 2 = 1 - x + x ^ 2 / 2 := by ring
  rw [e] at h
  linarith

/-- `ψ ≥ 0` on the nonnegative branch (`ψ(0) = 0` and `log` is nonnegative there). -/
private theorem catoniPsi_nonneg_of_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ catoniPsi y := by
  simp only [catoniPsi, if_pos hy]
  exact Real.log_nonneg (by nlinarith [sq_nonneg y])

/-- `ψ < 0` strictly on the negative branch. -/
private theorem catoniPsi_neg_of_neg {y : ℝ} (hy : y < 0) : catoniPsi y < 0 := by
  simp only [catoniPsi, if_neg (not_le.2 hy)]
  have : 0 < Real.log (1 - y + y ^ 2 / 2) :=
    Real.log_pos (by nlinarith [sq_nonneg y])
  linarith

/-- Catoni's `ψ` is strictly increasing (`LM §2.2`, "increasing"). -/
theorem catoniPsi_strictMono : StrictMono catoniPsi := by
  intro a b hab
  rcases le_or_gt 0 a with ha | ha
  · have hb : (0:ℝ) ≤ b := ha.trans hab.le
    simp only [catoniPsi, if_pos ha, if_pos hb]
    exact Real.log_lt_log (catoni_companion_pos a) (by nlinarith)
  · rcases le_or_gt 0 b with hb | hb
    · exact lt_of_lt_of_le (catoniPsi_neg_of_neg ha) (catoniPsi_nonneg_of_nonneg hb)
    · -- both on the negative branch: `1 − y + y²/2` is strictly decreasing there
      simp only [catoniPsi, if_neg (not_le.2 ha), if_neg (not_le.2 hb)]
      have h := Real.log_lt_log (catoni_companion_pos' b)
        (show 1 - b + b ^ 2 / 2 < 1 - a + a ^ 2 / 2 by
          nlinarith [mul_pos (sub_pos.2 hab) (show (0:ℝ) < 2 - a - b by linarith)])
      linarith

/-- Catoni's `ψ` is continuous (the two branches agree at `0` with value `0`). -/
theorem catoniPsi_continuous : Continuous catoniPsi := by
  have h1 : Continuous fun x : ℝ => Real.log (1 + x + x ^ 2 / 2) :=
    Continuous.log (by fun_prop) fun x => (catoni_companion_pos x).ne'
  have h2 : Continuous fun x : ℝ => -Real.log (1 - x + x ^ 2 / 2) :=
    (Continuous.log (by fun_prop) fun x => (catoni_companion_pos' x).ne').neg
  exact Continuous.if_le h1 h2 continuous_const continuous_id
    (fun x hx => by simp [← hx])

/-- Catoni's `ψ` tends to `+∞` at `+∞` (logarithmically — unbounded, unlike Huber's
score, but slowly enough for the exponential-moment device). -/
theorem catoniPsi_tendsto_atTop : Tendsto catoniPsi atTop atTop := by
  have hp : Tendsto (fun x : ℝ => 1 + x + x ^ 2 / 2) atTop atTop :=
    tendsto_atTop_mono (fun x => by nlinarith [sq_nonneg x] : ∀ x : ℝ, x ≤ 1 + x + x ^ 2 / 2)
      tendsto_id
  refine (Real.tendsto_log_atTop.comp hp).congr' ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  simp [catoniPsi, hx, Function.comp]

/-- Catoni's `ψ` tends to `−∞` at `−∞`. -/
theorem catoniPsi_tendsto_atBot : Tendsto catoniPsi atBot atBot := by
  have h1 : Tendsto (fun x : ℝ => catoniPsi (-x)) atBot atTop :=
    catoniPsi_tendsto_atTop.comp tendsto_neg_atBot_atTop
  have h2 : Tendsto (fun x : ℝ => -catoniPsi (-x)) atBot atBot :=
    tendsto_neg_atTop_atBot.comp h1
  refine h2.congr fun x => ?_
  rw [catoniPsi_neg, neg_neg]

/-- **Catoni's estimating function** `R_{n,α}(y) = ∑ᵢ ψ(α(xᵢ − y))` (`LM §2.2`). -/
noncomputable def catoniR {n : ℕ} (α : ℝ) (x : Fin n → ℝ) (y : ℝ) : ℝ :=
  ∑ i, catoniPsi (α * (x i - y))

/-- **Catoni's mean estimate** (`LM §2.2`): a root of the estimating function.
Uniqueness (for `α > 0`, `n ≠ 0`) is `existsUnique_isCatoniEstimate` below. -/
def IsCatoniEstimate {n : ℕ} (α : ℝ) (x : Fin n → ℝ) (yhat : ℝ) : Prop :=
  catoniR α x yhat = 0

/-- The estimating function is strictly decreasing in `y` (for `α > 0` and at least one
observation), being a sum of strictly decreasing terms. -/
theorem catoniR_strictAnti {n : ℕ} (hn : n ≠ 0) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) : StrictAnti (catoniR α x) := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  intro a b hab
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
  exact catoniPsi_strictMono (mul_lt_mul_of_pos_left (by linarith) hα)

/-- The estimating function is continuous in `y`. -/
theorem catoniR_continuous {n : ℕ} (α : ℝ) (x : Fin n → ℝ) :
    Continuous (catoniR α x) :=
  continuous_finset_sum _ fun i _ => catoniPsi_continuous.comp (by fun_prop)

/-- **Existence and uniqueness of Catoni's estimate** (`LM §2.2`, "the unique value `y`
such that `R_{n,α}(y) = 0`"): for `α > 0` and a nonempty sample, the estimating function
is a continuous strictly decreasing bijection-onto-a-neighborhood-of-0 (it inherits the
`±∞` limits of `ψ`), so it has exactly one root. -/
theorem existsUnique_isCatoniEstimate {n : ℕ} (hn : n ≠ 0) {α : ℝ} (hα : 0 < α)
    (x : Fin n → ℝ) : ∃! yhat, IsCatoniEstimate α x yhat := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  -- A bracket built from the extreme observations: below `min xᵢ` every score is `> 0`,
  -- above `max xᵢ` every score is `< 0`. (Cheaper than transporting the `±∞` limits.)
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min x
  obtain ⟨i₁, hi₁⟩ := Finite.exists_max x
  have hab : x i₀ - 1 ≤ x i₁ + 1 := by have := hi₀ i₁; linarith
  have hpa : 0 < catoniR α x (x i₀ - 1) := by
    refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    have h := catoniPsi_strictMono (mul_pos hα (by have := hi₀ i; linarith) :
      (0:ℝ) < α * (x i - (x i₀ - 1)))
    simpa using h
  have hnb : catoniR α x (x i₁ + 1) < 0 := by
    refine Finset.sum_neg (fun i _ => ?_) Finset.univ_nonempty
    have h := catoniPsi_strictMono (show α * (x i - (x i₁ + 1)) < 0 by
      have := hi₁ i
      nlinarith)
    simpa using h
  obtain ⟨y, -, hy⟩ := intermediate_value_Icc' hab (catoniR_continuous α x).continuousOn
    ⟨hnb.le, hpa.le⟩
  exact ⟨y, hy, fun z hz => (catoniR_strictAnti hn hα x).injective (hz.trans hy.symm)⟩

variable {Ξ : Type*} [MeasurableSpace Ξ] {μprob : Measure Ξ} [IsProbabilityMeasure μprob]
  {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **The exponential-moment bound** (`LM §2.2`, first display chain): for i.i.d. data
with mean `μ₀` and variance `σ²`, for every fixed `y`,

  `E exp(R_{n,α}(y)) ≤ exp( nα(μ₀ − y) + nα²(σ² + (μ₀ − y)²)/2 )`.

Pointwise `exp ψ(α(X−y)) ≤ 1 + α(X−y) + α²(X−y)²/2` (upper companion), expectations
multiply across independent coordinates, and `1 + u ≤ eᵘ` closes. -/
theorem integral_exp_catoniR_le {n : ℕ} {X : Fin n → Ξ → ℝ} {μ₀ σ2 α y : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §2.2 regularity
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: jointly independent observations; LM Theorem 5
    (hX_indep : iIndepFun X μprob)
    -- USER-INPUT: common law P; LM Theorem 5
    (hX_law : ∀ i, μprob.map (X i) = P)
    -- USER-INPUT: P is square-integrable; LM Theorem 5 ("with variance σ²")
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: mean and variance of P; LM Theorem 5
    (hmean : ∫ x, x ∂P = μ₀) (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    (hα : 0 < α) :
    ∫ ξ, Real.exp (catoniR α (fun i => X i ξ) y) ∂μprob
      ≤ Real.exp ((n : ℝ) * α * (μ₀ - y)
          + (n : ℝ) * α ^ 2 * (σ2 + (μ₀ - y) ^ 2) / 2) := by
  sorry

/-- **Catoni's estimator is sub-Gaussian with the optimal constant** (`LM Theorem 5`):
for i.i.d. data with mean `μ₀` and variance `σ² > 0`, `δ ∈ (0,1)` with
`n > 2 log(1/δ)`, and the tuned parameter

  `α = √( 2 log(1/δ) / (n σ² (1 + 2log(1/δ)/(n − 2log(1/δ)))) )`,

every root `Ŷ(ξ)` of the estimating equation satisfies, with probability at least
`1 − 2δ`,

  `|Ŷ − μ₀| < √( 2σ² log(1/δ) / (n − 2 log(1/δ)) )`.

The estimator is presented as a given measurable selection of roots, as with the Round-1
M-estimator theorems (existence and uniqueness are `existsUnique_isCatoniEstimate`). -/
theorem catoni_deviation {n : ℕ} (hn : n ≠ 0) {X : Fin n → Ξ → ℝ}
    {Yhat : Ξ → ℝ} {μ₀ σ2 α δ : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §2.2 regularity
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: jointly independent observations; LM Theorem 5
    (hX_indep : iIndepFun X μprob)
    -- USER-INPUT: common law P; LM Theorem 5
    (hX_law : ∀ i, μprob.map (X i) = P)
    -- USER-INPUT: P is square-integrable; LM Theorem 5
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: mean and variance of P; LM Theorem 5
    (hmean : ∫ x, x ∂P = μ₀) (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    (hσ : 0 < σ2)
    -- USER-INPUT: confidence level and sample-size condition; LM Theorem 5
    (hδ : 0 < δ) (hδ1 : δ < 1) (hnδ : 2 * Real.log (1 / δ) < n)
    -- USER-INPUT: Catoni's tuned parameter; LM Theorem 5
    (hαdef : α = Real.sqrt (2 * Real.log (1 / δ)
      / (n * σ2 * (1 + 2 * Real.log (1 / δ) / (n - 2 * Real.log (1 / δ))))))
    -- USER-INPUT: Ŷ solves the estimating equation sample-wise; LM §2.2
    (hroot : ∀ ξ, IsCatoniEstimate α (fun i => X i ξ) (Yhat ξ))
    -- LEAN-ONLY: measurability of the root selection, for the deviation event
    (hYmeas : Measurable Yhat) :
    μprob.real {ξ | Real.sqrt (2 * σ2 * Real.log (1 / δ) / (n - 2 * Real.log (1 / δ)))
        ≤ |Yhat ξ - μ₀|}
      ≤ 2 * δ := by
  sorry

end StatLean.RobustStatistics
