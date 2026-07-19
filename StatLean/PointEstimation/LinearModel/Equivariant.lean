import StatLean.PointEstimation.LinearModel.Canonical
import StatLean.MultipleTesting.ForMathlib.ChiSquared
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Equivariant optimality in the normal linear model

The estimators that are optimal among unbiased estimators are also optimal among
equivariant ones, for the natural groups acting on the normal linear model:

* translations of the signal block, `Y ↦ Y + (a, 0)`, under which `η ↦ η + a` and a linear
  functional `∑ λᵢ ηᵢ` of the mean shifts by `∑ λᵢ aᵢ` — the group for which `∑ λᵢ Yᵢ` is
  minimum risk equivariant under any convex even loss `ρ(d − ∑ λᵢ ηᵢ)`;
* the same translations together with the scale changes `Y ↦ cY`, under which
  `σ² ↦ c²σ²` — the group for which a fixed multiple of the residual sum of squares is
  minimum risk equivariant for `σ²` under the loss `(d − σ²)²/σ⁴`; the multiplier is a
  ratio of chi-square moments, and equals `1/(n − s + 2)`;
* translations by the mean subspace in the original coordinates, `X ↦ X + b` with `b ∈ W`,
  for which the least-squares functional is minimum risk equivariant.

Contents: `IsCanonicalEquivariant`, `canonicalRisk`, `IsCanonicalMRE`;
`IsCanonicalScaleEquivariant`, `canonicalScaleRisk`, `IsCanonicalScaleMRE`,
`residualScaleConst`; `IsSubspaceEquivariant`, `linearBaseRisk`, `IsSubspaceMRE`.

**Reference.** Classical equivariant estimation in normal linear models; original sources
in the bibliographic comments below.

**Proof formalization notes.**
* *Lightweight group formalization.* Equivariance is expressed by explicit functional
  equations on the competing estimators (`IsCanonicalEquivariant`,
  `IsCanonicalScaleEquivariant`, `IsSubspaceEquivariant`) rather than through the general
  `[Group G] [MulAction G _]` framework. The acting groups here are concrete (`ℝˢ` acting
  by translation of a coordinate block, and its semidirect product with the positive
  reals), the induced action on the decision space is a shift or a power, and routing
  through the general framework would force an instance-heavy encoding for no gain. The
  general-framework bridge lemmas can be added later without changing these statements.
* *Constant risk.* Under each group the risk of an equivariant estimator is constant in the
  parameter, so minimum risk equivariance is stated as minimality of the risk at a single
  base parameter — `(η, σ²) = (0, σ²)` for the translation group and `(0, 1)` for the
  location-scale group. Losses enter `∫⁻` through `ENNReal.ofReal` (junk-value discipline).
* *The scale clause.* The optimal multiplier of the residual sum of squares is only pinned
  down once the acting group contains the scale changes: under translations alone the risk
  still depends on `σ²`. The statement below therefore uses the location-scale group, which
  is also the route by which the classical proof obtains the constant.
* *The constant.* `residualScaleConst m r` is the ratio of chi-square moments
  `E[V^r]/E[V^{2r}]`, `V ∼ χ²_m`; for `r = 1` the moments `E[V] = m` and
  `E[V²] = m(m + 2)` (`StatLean.MultipleTesting.integral_id_chiSquared` and
  `StatLean.MultipleTesting.variance_chiSquared`) give the classical
  `1/(m + 2) = 1/(n − s + 2)` — a larger denominator than the unbiased `1/(n − s)`.

**Bibliographic comments.** Equivariant estimation of location and scale parameters is due
to E. J. G. Pitman ("The estimation of the location and scale parameters of a continuous
population of any given form," *Biometrika* **30** (1939), 391–421); its use in the linear
model follows H. Scheffé (*The Analysis of Variance*, Wiley, 1959) and C. R. Rao (*Linear
Statistical Inference and Its Applications*, 2nd ed., Wiley, 1973), with the
coordinate-free viewpoint of W. Kruskal ("When are Gauss–Markov and least squares
estimators identical?" in *Essays in Probability and Statistics*, 1965). The underlying
least-squares theory is that of C. F. Gauss (*Theoria combinationis observationum
erroribus minimis obnoxiae*, 1821/1823) and A. A. Markov (*Wahrscheinlichkeitsrechnung*,
Teubner, 1912). The distribution of the residual sum of squares goes back to F. R. Helmert
(*Z. Math. Phys.* **21** (1876), 192–218).
-/

open MeasureTheory ProbabilityTheory
open StatLean.MultipleTesting (chiSquared)
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {s m n : ℕ}

/-! ## Translations of the signal block -/

/-- **Equivariance under translations of the signal block**: shifting the first `s`
coordinates by `a` shifts the estimator of `∑ λᵢ ηᵢ` by `∑ λᵢ aᵢ`. -/
def IsCanonicalEquivariant (lam : Fin s → ℝ)
    (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  ∀ (a : Fin s → ℝ) (y : EuclideanSpace ℝ (Fin (s + m))),
    δ (y + canonicalMean a) = δ y + ∑ i, lam i * a i

/-- Risk of `δ` at the base parameter `(η, σ²) = (0, σ²)` for a loss
`ρ(d − ∑ λᵢ ηᵢ)`; for equivariant estimators the risk equals this constant. -/
noncomputable def canonicalRisk (σ2 : PosVar) (ρ : ℝ → ℝ)
    (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (ρ (δ y))
    ∂(canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), σ2))

/-- **Minimum risk equivariant** estimator of `∑ λᵢ ηᵢ` under translations of the signal
block: measurable, equivariant, and of minimal (constant) risk among all such. -/
def IsCanonicalMRE (σ2 : PosVar) (lam : Fin s → ℝ) (ρ : ℝ → ℝ)
    (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  Measurable δ ∧ IsCanonicalEquivariant lam δ ∧
    ∀ δ' : EuclideanSpace ℝ (Fin (s + m)) → ℝ,
      Measurable δ' → IsCanonicalEquivariant lam δ' →
        canonicalRisk σ2 ρ δ ≤ canonicalRisk σ2 ρ δ'

/-- The unbiased optimal estimator `∑ λᵢ Yᵢ` of `∑ λᵢ ηᵢ` is also minimum risk equivariant
under translations of the signal block, for every convex even loss. -/
theorem isCanonicalMRE_linear_combination
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional
    (lam : Fin s → ℝ) (σ2 : PosVar) {ρ : ℝ → ℝ}
    -- USER-INPUT: convex loss in the estimation error
    (hconv : ConvexOn ℝ Set.univ ρ)
    -- USER-INPUT: even loss in the estimation error
    (heven : ∀ t : ℝ, ρ (-t) = ρ t) :
    IsCanonicalMRE (m := m) σ2 lam ρ (fun y => ∑ i, lam i * canonicalHead y i) := by
  sorry

/-! ## Translations of the signal block together with scale changes -/

/-- **Equivariance of degree `2r` under the location-scale group**: the transformation
`y ↦ c(y + (a, 0))` multiplies an estimator of `σ^{2r} = (σ²)^r` by `c^{2r}`. -/
def IsCanonicalScaleEquivariant (r : ℕ) (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → ∀ (a : Fin s → ℝ) (y : EuclideanSpace ℝ (Fin (s + m))),
    δ (c • (y + canonicalMean a)) = c ^ (2 * r) * δ y

/-- Risk of `δ` at the base parameter `(η, σ²) = (0, 1)` for the loss
`(d − (σ²)^r)²/(σ²)^{2r}`; for equivariant estimators the risk equals this constant. -/
noncomputable def canonicalScaleRisk (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal ((δ y - 1) ^ 2)
    ∂(canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), ⟨1, zero_lt_one⟩))

/-- **Minimum risk equivariant** estimator of `(σ²)^r` under the location-scale group. -/
def IsCanonicalScaleMRE (r : ℕ) (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  Measurable δ ∧ IsCanonicalScaleEquivariant r δ ∧
    ∀ δ' : EuclideanSpace ℝ (Fin (s + m)) → ℝ,
      Measurable δ' → IsCanonicalScaleEquivariant r δ' →
        canonicalScaleRisk δ ≤ canonicalScaleRisk δ'

/-- The optimal multiplier of `(S²)^r`: the ratio `E[V^r]/E[V^{2r}]` of chi-square moments
with `k` degrees of freedom — the constant minimizing `E(c·V^r − 1)²`. -/
noncomputable def residualScaleConst (k r : ℕ) : ℝ :=
  (∫ v, v ^ r ∂(chiSquared k)) / (∫ v, v ^ (2 * r) ∂(chiSquared k))

/-- The multiplier at `r = 1`: `E[V] = m` and `E[V²] = m(m + 2)` give
`residualScaleConst m 1 = 1/(m + 2)`, the classical `1/(n − s + 2)`. -/
theorem residualScaleConst_one
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    residualScaleConst m 1 = 1 / ((m : ℝ) + 2) := by
  sorry

/-- A fixed multiple of `(S²)^r` is minimum risk equivariant for `(σ²)^r` under the
location-scale group, the multiplier being the chi-square moment ratio. -/
theorem isCanonicalScaleMRE_residual_pow
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m)
    -- USER-INPUT: the degree of the estimated power of the variance
    {r : ℕ} (hr : 0 < r) :
    IsCanonicalScaleMRE (s := s) (m := m) r
      (fun y => residualScaleConst m r * canonicalRSS y ^ r) := by
  sorry

/-- The classical variance clause: under the loss `(d − σ²)²/σ⁴`, the minimum risk
equivariant estimator of `σ²` is `S²/(m + 2)`, that is `S²/(n − s + 2)`. -/
theorem isCanonicalScaleMRE_residual_variance
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    IsCanonicalScaleMRE (s := s) (m := m) 1 (fun y => canonicalRSS y / ((m : ℝ) + 2)) := by
  sorry

/-! ## Translations by the mean subspace, in the original coordinates -/

/-- **Equivariance under translations by the mean subspace**: shifting the observation by
`b ∈ W` shifts an estimator of `⟪γ, ξ⟫` by `⟪γ, b⟫`. -/
def IsSubspaceEquivariant (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (γ : EuclideanSpace ℝ (Fin n)) (δ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ b ∈ W, ∀ y : EuclideanSpace ℝ (Fin n), δ (y + b) = δ y + ⟪γ, b⟫_ℝ

/-- Risk of `δ` at the base parameter `ξ = 0` for a loss `ρ(d − ⟪γ, ξ⟫)`; for equivariant
estimators the risk equals this constant. -/
noncomputable def linearBaseRisk (σ2 : PosVar) (ρ : ℝ → ℝ)
    (δ : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (ρ (δ y)) ∂(gaussianVector (0 : EuclideanSpace ℝ (Fin n)) σ2.1)

/-- **Minimum risk equivariant** estimator of `⟪γ, ξ⟫` under translations by the mean
subspace. -/
def IsSubspaceMRE (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (σ2 : PosVar)
    (γ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ → ℝ) (δ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Measurable δ ∧ IsSubspaceEquivariant W γ δ ∧
    ∀ δ', Measurable δ' → IsSubspaceEquivariant W γ δ' →
      linearBaseRisk σ2 ρ δ ≤ linearBaseRisk σ2 ρ δ'

/-- The least-squares functional is minimum risk equivariant for `⟪γ, ξ⟫` under
translations by the mean subspace, for every convex even loss. -/
theorem isSubspaceMRE_lse_functional (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection]
    -- USER-INPUT: the mean subspace is a proper subspace (`s < n`); standing dimension
    -- condition of the model
    (hW : Module.finrank ℝ W < n) (σ2 : PosVar)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional, taken
    -- inside the mean subspace (a general one is replaced by its projection)
    {γ : EuclideanSpace ℝ (Fin n)} (hγ : γ ∈ W) {ρ : ℝ → ℝ}
    -- USER-INPUT: convex loss in the estimation error
    (hconv : ConvexOn ℝ Set.univ ρ)
    -- USER-INPUT: even loss in the estimation error
    (heven : ∀ t : ℝ, ρ (-t) = ρ t) :
    IsSubspaceMRE W σ2 γ ρ (fun y => ⟪γ, lse W y⟫_ℝ) := by
  sorry

end StatLean.PointEstimation
