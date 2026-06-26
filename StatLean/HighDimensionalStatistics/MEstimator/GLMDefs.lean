import StatLean.HighDimensionalStatistics.ForMathlib.VecNorms
import StatLean.HighDimensionalStatistics.LinearModel.Defs
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Fixed-design generalized linear model (Wainwright §9.1, eq 9.5; §9.5 conditions G1/G2)

Data model for the GLM corollaries (Cor 9.26 / 9.27): a fixed design `X ∈ ℝ^{n×d}`, target `θ*`, and
independent responses `yᵢ` drawn from the exponential family (9.5) with partition function `ψ` of
bounded second derivative (`0 ≤ ψ'' ≤ B²`, condition G2). The exponential-family structure is captured
by its **constitutive moment-generating-function identity** `𝔼[e^{s·yᵢ}] = exp(ψ(ηᵢ + s) − ψ(ηᵢ))`
with `ηᵢ = ⟨xᵢ, θ*⟩`, which is exactly what the proof of Corollary 9.26 (p. 288) uses to center and
bound the score. Fixed design ⇒ the score `Vᵢⱼ = (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` is a function of `yᵢ` only — no
conditional-expectation machinery.

Laptop-only shared data model; consumed by `ScoreSubGaussian`, `GoodEvent`, `GLMCorollaries`.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

variable {n d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The linear predictor `ηᵢ(θ) = ⟨xᵢ, θ⟩ = ∑ⱼ Xᵢⱼ·θⱼ` (the `i`-th coordinate of `Xθ`). -/
def linPred (X : Matrix (Fin n) (Fin d) ℝ) (θ : EuclideanSpace ℝ (Fin d)) (i : Fin n) : ℝ :=
  ∑ j, X i j * θ.ofLp j

/-- A **fixed-design generalized linear model** (Wainwright §9.1, eq 9.5; G2). Each response `yᵢ` is an
exponential-family variate with natural parameter `ηᵢ = ⟨xᵢ, θ*⟩` and partition function `ψ`. -/
structure GLMExpFamily (n d : ℕ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) where
  /-- Constitutive: the fixed design matrix `X ∈ ℝ^{n×d}`. -/
  X : Matrix (Fin n) (Fin d) ℝ
  /-- Constitutive: the target regression vector `θ*`. -/
  θstar : EuclideanSpace ℝ (Fin d)
  /-- Constitutive (eq 9.5): the partition / cumulant function `ψ`. -/
  ψ : ℝ → ℝ
  /-- Constitutive: its first derivative `ψ'` (the mean function). -/
  ψ' : ℝ → ℝ
  /-- Constitutive: its second derivative `ψ''` (the variance function). -/
  ψ'' : ℝ → ℝ
  /-- The cumulant bound parameter `B` (condition G2). -/
  B : ℝ
  /-- Constitutive: the responses `yᵢ : Ω → ℝ`. -/
  y : Fin n → Ω → ℝ
  /-- Constitutive: `ψ'` is the derivative of `ψ`. -/
  hψ' : ∀ a, HasDerivAt ψ (ψ' a) a
  /-- Constitutive: `ψ''` is the derivative of `ψ'`. -/
  hψ'' : ∀ a, HasDerivAt ψ' (ψ'' a) a
  /-- Constitutive (exponential family: `ψ''` = conditional variance ≥ 0, so `ψ` is convex). -/
  hψ''_nonneg : ∀ a, 0 ≤ ψ'' a
  /-- Constitutive (G2): bounded second derivative `‖ψ''‖∞ ≤ B²`. -/
  hψ''_le : ∀ a, ψ'' a ≤ B ^ 2
  /-- Constitutive: each response is measurable. -/
  hy_meas : ∀ i, Measurable (y i)
  /-- Constitutive: the responses are jointly independent (fixed design). -/
  hindep : iIndepFun y μ
  /-- Constitutive (eq 9.5): the exponential-family MGF identity
  `𝔼[e^{s·yᵢ}] = exp(ψ(ηᵢ + s) − ψ(ηᵢ))` (with the dispersion `c(σ) = 1`, as in the Cor 9.26 proof). -/
  hmgf : ∀ (i : Fin n) (s : ℝ),
    mgf (y i) μ s = Real.exp (ψ (linPred X θstar i + s) - ψ (linPred X θstar i))

variable {μ : Measure Ω}

/-- The `j`-th coordinate of the score `∇Lₙ(θ*) = (1/n)∑ᵢ Vᵢ`, namely
`(1/n)∑ᵢ (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` (Wainwright Cor 9.26 proof, the random vector `Vᵢⱼ`). -/
noncomputable def scoreCoord (M : GLMExpFamily n d μ) (j : Fin d) (ω : Ω) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (M.ψ' (linPred M.X M.θstar i) - M.y i ω) * M.X i j

/-- The score vector `∇Lₙ(θ*) ∈ ℝ^d`, with coordinates `scoreCoord`. -/
noncomputable def scoreVec (M : GLMExpFamily n d μ) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp (p := 2) (fun j => scoreCoord M j ω)

/-- The GLM negative-log-likelihood cost `Lₙ(θ) = (1/n)∑ᵢ[ψ(⟨xᵢ,θ⟩) − yᵢ⟨xᵢ,θ⟩]` (eq 9.7/9.61). -/
noncomputable def glmCost (M : GLMExpFamily n d μ) (ω : Ω) (θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (M.ψ (linPred M.X θ i) - M.y i ω * linPred M.X θ i)

/-- **Column-normalization condition (G1)**: `∑ᵢ Xᵢⱼ² ≤ n·C²` for every `j`
(i.e. `maxⱼ √(∑ᵢ Xᵢⱼ²/n) ≤ C`). -/
def IsColumnNormalized (X : Matrix (Fin n) (Fin d) ℝ) (C : ℝ) : Prop :=
  ∀ j, ∑ i, X i j ^ 2 ≤ (n : ℝ) * C ^ 2

end StatLean.HighDimensionalStatistics.MEstimator
