import StatLean.PointEstimation.InformationInequality.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Additivity of the Fisher information over independent observations

The information carried by two independent observations is the sum of the informations
they carry separately: for `X ~ p_θ` on `𝓧` and `Y ~ q_θ` on `𝓨`, independent, the joint
density is `p_θ(x) q_θ(y)` and
$$ I_{(X,Y)}(\theta) \;=\; I_X(\theta) + I_Y(\theta), \qquad\text{hence}\qquad
   I_{X_1,\dots,X_n}(\theta) \;=\; n\,I(\theta) $$
for an independent identically distributed sample. The joint score is the sum of the two
scores and the cross term vanishes because each score has mean zero.

Contents:
* `prodFamily` — the product family `θ ↦ p_θ ⊗ q_θ` on `𝓧 × 𝓨`;
* `fisherInfo_prod` — additivity of the information over an independent pair;
* `piFamily` — the `n`-fold product family on `Fin n → 𝓧`;
* `fisherInfo_pi` — the information in an independent identically distributed sample of
  size `n` is `n` times the information in one observation.

**Reference.** Classical additivity of the Fisher information under independence, together
with its identically-distributed specialization. Original sources in the bibliographic
comments below.

**Proof formalization notes.**
* The product family is built at the level of *densities*, `p_θ(x) q_θ(y)`, so that the
  dominating measure of the pair is the product `μ ⊗ ν` and the score of the pair is
  literally the sum `ℓ̇_θ(x) + ℓ̇_θ(y)` on the common support (product rule for the
  parameter derivative, then division by the product density).
* The cross term `2 ∫∫ ℓ̇_θ(x) ℓ̇_θ(y) p_θ(x) q_θ(y)` factorizes by Fubini into a product of
  two mean-zero integrals; this is the only place the mean-zero hypotheses are used, and it
  is why they appear as hypotheses rather than being absorbed into the definitions.
* The `n`-fold statement is not obtained by iterating the pair statement (the carrier
  `Fin n → 𝓧` is not a nested binary product); it is proved directly, the score of the
  product density being the sum of the coordinate scores and the cross terms vanishing
  pairwise.
* The σ-finiteness instances are Lean-side requirements of the product-measure theory
  (Fubini), not conditions of the classical statement.

**Bibliographic comments.** Additivity of the information over independent observations
is due to R. A. Fisher ("Theory of statistical estimation," *Proc. Camb. Phil. Soc.* **22**
(1925), 700–725, where the information in a sample is computed as `n` times the information
in a single observation); it underlies the `1/n` scale of the information bound in
C. R. Rao ("Information and the accuracy attainable in the estimation of statistical
parameters," *Bull. Calcutta Math. Soc.* **37** (1945), 81–91) and H. Cramér
(*Mathematical Methods of Statistics*, Princeton University Press, 1946, §32.3).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/-! ## Two independent observations -/

/-- The **product family** of two dominated families: the density of the pair is the
product of the densities, `(θ, (x, y)) ↦ p_θ(x) q_θ(y)`, relative to the product of the
dominating measures. Measurability and non-negativity are inherited coordinatewise. -/
noncomputable def prodFamily (M : ParametricFamily 𝓧 ℝ) (N : ParametricFamily 𝓨 ℝ) :
    ParametricFamily (𝓧 × 𝓨) ℝ where
  density θ z := M.density θ z.1 * N.density θ z.2
  density_meas θ :=
    ((M.density_meas θ).comp measurable_fst).mul ((N.density_meas θ).comp measurable_snd)
  density_nonneg θ z := mul_nonneg (M.density_nonneg θ z.1) (N.density_nonneg θ z.2)

/-- **Additivity of the information over an independent pair**: the information carried by
`(X, Y)` with independent components is `I_X(θ) + I_Y(θ)`.

The joint score splits as `ℓ̇_θ(x) + ℓ̇_θ(y)`; squaring and integrating, the cross term is
the product of the two (vanishing) mean scores. -/
theorem fisherInfo_prod (M : ParametricFamily 𝓧 ℝ) (N : ParametricFamily 𝓨 ℝ)
    (μ : Measure 𝓧) (ν : Measure 𝓨)
    -- LEAN-ONLY: σ-finiteness of the dominating measures, required by Fubini for the
    -- product measure; no restriction of the classical statement
    [SigmaFinite μ] [SigmaFinite ν]
    -- USER-INPUT: both families are probability-density families
    (hM : IsPDFOf M μ) (hN : IsPDFOf N ν)
    -- USER-INPUT: both families have a common support; classical regularity condition
    (hMsupp : HasCommonSupport M) (hNsupp : HasCommonSupport N)
    (θ : ℝ)
    -- USER-INPUT: on their supports, both densities are differentiable in the parameter;
    -- classical smoothness condition, needed for the product rule (off the support the
    -- parameter map is constant `0` by the common-support condition)
    (hMdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    (hNdiff : ∀ y, 0 < N.density θ y → DifferentiableAt ℝ (fun t => N.density t y) θ)
    -- USER-INPUT: both scores have mean zero; classical regularity condition, and exactly
    -- what kills the cross term
    (hM0 : ∫ x, score M θ x * M.density θ x ∂μ = 0)
    (hN0 : ∫ y, score N θ y * N.density θ y ∂ν = 0)
    -- LEAN-ONLY: finiteness of both informations as Bochner integrals
    (hMint : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ)
    (hNint : Integrable (fun y => score N θ y ^ 2 * N.density θ y) ν)
    -- LEAN-ONLY: integrability of the two mean scores, needed to factorize the cross term
    (hMint1 : Integrable (fun x => score M θ x * M.density θ x) μ)
    (hNint1 : Integrable (fun y => score N θ y * N.density θ y) ν) :
    fisherInfo (prodFamily M N) (μ.prod ν) θ = fisherInfo M μ θ + fisherInfo N ν θ := by
  sorry

/-! ## An independent identically distributed sample -/

/-- The **`n`-fold product family**: the density of an independent identically distributed
sample of size `n` is the product `∏ i, p_θ(x i)`, relative to the `n`-fold product of the
dominating measure. For `n = 0` the density is the empty product `1`, which is the correct
degenerate value (the model on the one-point sample space carries no information). -/
noncomputable def piFamily (M : ParametricFamily 𝓧 ℝ) (n : ℕ) :
    ParametricFamily (Fin n → 𝓧) ℝ where
  density θ x := ∏ i, M.density θ (x i)
  density_meas θ :=
    Finset.measurable_prod _ fun i _ => (M.density_meas θ).comp (measurable_pi_apply i)
  density_nonneg θ x := Finset.prod_nonneg fun i _ => M.density_nonneg θ (x i)

/-- **The information in an independent identically distributed sample**: a sample of size
`n` carries `n` times the information carried by one observation. -/
theorem fisherInfo_pi (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- LEAN-ONLY: σ-finiteness of the dominating measure, required by the product-measure
    -- theory
    [SigmaFinite μ]
    (n : ℕ) (θ : ℝ)
    -- USER-INPUT: the family is a probability-density family
    (hM : IsPDFOf M μ)
    -- USER-INPUT: the family has a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    -- USER-INPUT: on the support, the density is differentiable in the parameter
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    -- USER-INPUT: the score has mean zero; classical regularity condition
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0)
    -- LEAN-ONLY: finiteness of the information as a Bochner integral
    (hint : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ)
    -- LEAN-ONLY: integrability of the mean score, needed to factorize the cross terms
    (hint1 : Integrable (fun x => score M θ x * M.density θ x) μ) :
    fisherInfo (piFamily M n) (Measure.pi fun _ : Fin n => μ) θ = (n : ℝ) * fisherInfo M μ θ := by
  sorry

end StatLean.PointEstimation
