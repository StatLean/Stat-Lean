import StatLean.HighDimensionalStatistics.MEstimator.GLMDefs
import StatLean.HighDimensionalStatistics.ForMathlib.PsiTaylor
import StatLean.ConcentrationInequalities.SubGaussian.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Sub-Gaussianity of the GLM score (Wainwright Cor 9.26 proof, p. 288)

The probabilistic core of the GLM corollaries: each coordinate of the score
`∇Lₙ(θ*) = (1/n)∑ᵢ Vᵢ`, namely `scoreCoord M j = (1/n)∑ᵢ (ψ'(ηᵢ) − yᵢ)·xᵢⱼ`, is sub-Gaussian with
variance proxy `≤ B²C²/n` under conditions (G1) (column normalization) and (G2) (the GLM exp-family
with `ψ'' ≤ B²`).

The per-term variable `Vᵢⱼ = (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` has MGF `exp(ψ(ηᵢ+s) − ψ(ηᵢ) − s·ψ'(ηᵢ))`
(`s = −t·xᵢⱼ`) by the constitutive `hmgf` identity, which `psi_taylor_upper` bounds by `exp(B²xᵢⱼ²t²/2)` —
so `Vᵢⱼ` is centered sub-Gaussian with proxy `B²xᵢⱼ²`. Summing over the independent `i` and rescaling
by `1/n` (the `Lasso/RandomNoise.lean` `colInner_isSubGaussian` pattern) + (G1) gives proxy `B²C²/n`.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatLean.ConcentrationInequalities

variable {n d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Integrability of `exp(s·yᵢ)` for every `s`, derived from the constitutive MGF identity:
if `exp(s·yᵢ)` were not integrable, the MGF would be the junk value `0` (`mgf_undef`), contradicting
`M.hmgf i s = exp(…) > 0`. -/
private lemma y_exp_integrable (M : GLMExpFamily n d μ) (i : Fin n) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * M.y i ω)) μ := by
  by_contra hni
  have h0 := mgf_undef hni
  rw [M.hmgf i s] at h0
  exact (Real.exp_pos _).ne' h0

/-- The set of exponents at which `exp(t·yᵢ)` is integrable is all of `ℝ` (from `y_exp_integrable`),
so `0` lies in its interior — the hypothesis needed for `deriv_mgf_zero` / integrability of `yᵢ`. -/
private lemma y_integrableExpSet_univ (M : GLMExpFamily n d μ) (i : Fin n) :
    integrableExpSet (M.y i) μ = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact y_exp_integrable M i t

/-- The mean function identity `E[yᵢ] = ψ'(ηᵢ)`. The mean is the derivative of the MGF at `0`
(`deriv_mgf_zero`); the constitutive `hmgf` gives `mgf yᵢ = exp(ψ(ηᵢ+·) − ψ(ηᵢ))`, whose derivative
at `0` is `ψ'(ηᵢ)`. -/
private lemma y_mean (M : GLMExpFamily n d μ) (i : Fin n) :
    ∫ ω, M.y i ω ∂μ = M.ψ' (linPred M.X M.θstar i) := by
  set η := linPred M.X M.θstar i with hη
  have hmem : (0 : ℝ) ∈ interior (integrableExpSet (M.y i) μ) := by
    rw [y_integrableExpSet_univ M i, interior_univ]; exact Set.mem_univ 0
  rw [← deriv_mgf_zero hmem]
  have hmgf_eq : mgf (M.y i) μ = fun s => Real.exp (M.ψ (η + s) - M.ψ η) := by
    funext s; rw [M.hmgf i s, hη]
  rw [hmgf_eq]
  have hinner : HasDerivAt (fun s => M.ψ (η + s) - M.ψ η) (M.ψ' η) 0 := by
    have h1 : HasDerivAt (fun s => M.ψ (η + s)) (M.ψ' η) 0 := by
      have := (M.hψ' (η + 0)).comp 0 ((hasDerivAt_id 0).const_add η)
      simpa using this
    simpa using h1.sub_const (M.ψ η)
  have hderiv : HasDerivAt (fun s => Real.exp (M.ψ (η + s) - M.ψ η)) (M.ψ' η) 0 := by
    simpa using hinner.exp
  exact hderiv.deriv

/-- The per-term score variable `Vᵢⱼ = (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` is centered sub-Gaussian with proxy
`B²·xᵢⱼ²`. Derived from the constitutive MGF identity (`M.hmgf`) and `psi_taylor_upper`:
`mgf Vᵢⱼ μ t = exp(ψ(ηᵢ + (−t·xᵢⱼ)) − ψ(ηᵢ) − (−t·xᵢⱼ)·ψ'(ηᵢ)) ≤ exp(B²·xᵢⱼ²·t²/2)`. -/
theorem score_term_hasSubgaussianMGF (M : GLMExpFamily n d μ) (i : Fin n) (j : Fin d) :
    HasSubgaussianMGF (fun ω => (M.ψ' (linPred M.X M.θstar i) - M.y i ω) * M.X i j)
      ⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ μ := by
  set η := linPred M.X M.θstar i with hη
  set a := M.X i j with ha
  refine ⟨?_, ?_⟩
  · -- integrable_exp_mul
    intro t
    have heq : (fun ω => Real.exp (t * ((M.ψ' η - M.y i ω) * a)))
        = (fun ω => Real.exp (t * (a * M.ψ' η)) * Real.exp ((-a * t) * M.y i ω)) := by
      funext ω; rw [← Real.exp_add]; congr 1; ring
    rw [heq]
    exact (y_exp_integrable M i (-a * t)).const_mul _
  · -- mgf_le
    intro t
    have hmgfeq : mgf (fun ω => (M.ψ' η - M.y i ω) * a) μ t
        = Real.exp (M.ψ (η + (-a * t)) - M.ψ η - (-a * t) * M.ψ' η) := by
      have hfun : (fun ω => (M.ψ' η - M.y i ω) * a)
          = (fun ω => a * M.ψ' η + (-a) * M.y i ω) := by
        funext ω; ring
      rw [hfun, mgf_const_add, mgf_const_mul, M.hmgf i, ← hη, ← Real.exp_add]
      congr 1; ring
    rw [hmgfeq, NNReal.coe_mk]
    apply Real.exp_le_exp.mpr
    calc M.ψ (η + (-a * t)) - M.ψ η - (-a * t) * M.ψ' η
        ≤ M.B ^ 2 / 2 * (-a * t) ^ 2 :=
          psi_taylor_upper M.ψ M.ψ' M.ψ'' M.B M.hψ' M.hψ'' M.hψ''_le η (-a * t)
      _ = M.B ^ 2 * a ^ 2 * t ^ 2 / 2 := by ring

/-- **GLM score coordinate sub-Gaussianity.** Under column normalization (G1, `IsColumnNormalized X C`)
and the GLM exp-family with `0 ≤ ψ'' ≤ B²` (G2, in `M`), the score coordinate
`scoreCoord M j = (1/n)∑ᵢ (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` is sub-Gaussian with variance proxy `B²C²/n`. -/
theorem score_coord_isSubGaussian (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : IsColumnNormalized M.X C) (hn : 0 < n) (j : Fin d) :
    IsSubGaussian (scoreCoord M j) ⟨M.B ^ 2 * C ^ 2 / n, by positivity⟩ μ := by
  set V : Fin n → Ω → ℝ :=
    fun i ω => (M.ψ' (linPred M.X M.θstar i) - M.y i ω) * M.X i j with hV
  -- Independence of the per-term family from `M.hindep`.
  have hV_indep : iIndepFun V μ :=
    M.hindep.comp (fun i x => (M.ψ' (linPred M.X M.θstar i) - x) * M.X i j)
      (fun i => (measurable_const.sub measurable_id).mul measurable_const)
  -- Each per-term variable is sub-Gaussian with proxy `B²xᵢⱼ²`.
  have hV_sg : ∀ i, HasSubgaussianMGF (V i) ⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ μ :=
    fun i => score_term_hasSubgaussianMGF M i j
  -- Sum over the independent terms.
  have hsum : HasSubgaussianMGF (fun ω => ∑ i, V i ω)
      (∑ i, (⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ : ℝ≥0)) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hV_indep (fun i _ => hV_sg i)
  -- Rescale by `1/n`.
  have hscaled := hsum.const_mul (1 / (n : ℝ))
  -- Mean-zero of each term (`E[yᵢ] = ψ'(ηᵢ)`) hence of the coordinate.
  have hVi : ∀ i, ∫ ω, V i ω ∂μ = 0 := by
    intro i
    have hyi : Integrable (M.y i) μ :=
      integrable_of_mem_interior_integrableExpSet (by
        rw [y_integrableExpSet_univ M i, interior_univ]; exact Set.mem_univ 0)
    have hrw : (fun ω => V i ω)
        = fun ω => M.ψ' (linPred M.X M.θstar i) * M.X i j - M.X i j * M.y i ω := by
      funext ω; simp only [hV]; ring
    rw [show (∫ ω, V i ω ∂μ)
          = ∫ ω, (M.ψ' (linPred M.X M.θstar i) * M.X i j - M.X i j * M.y i ω) ∂μ from by
        rw [hrw]]
    rw [integral_sub (integrable_const _) (hyi.const_mul _), integral_const,
        integral_const_mul, y_mean M i, probReal_univ, one_smul]
    ring
  have hmean : ∫ ω, scoreCoord M j ω ∂μ = 0 := by
    have hsc_eq : scoreCoord M j = fun ω => (1 / (n : ℝ)) * ∑ i, V i ω := by
      funext ω; simp only [scoreCoord, hV]
    simp only [hsc_eq]
    rw [integral_const_mul,
        integral_finset_sum Finset.univ (fun i _ => (hV_sg i).integrable),
        Finset.sum_congr rfl (fun i _ => hVi i), Finset.sum_const_zero, mul_zero]
  -- Proxy monotonicity: the rescaled proxy `(1/n²)∑ᵢ B²xᵢⱼ²` is `≤ B²C²/n` by (G1).
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hB2 : (0 : ℝ) ≤ M.B ^ 2 := sq_nonneg _
  -- Proxy bound in `ℝ≥0` (cast to `ℝ` and clear denominators).
  have hproxy : (⟨(1 / (n : ℝ)) ^ 2, by positivity⟩
        * ∑ i, (⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ : ℝ≥0))
      ≤ (⟨M.B ^ 2 * C ^ 2 / n, by positivity⟩ : ℝ≥0) := by
    -- Bound the sum by `B²·(n·C²)` entirely within `ℝ≥0` (cast termwise via the sum coercion).
    have hreal : ∑ i, M.B ^ 2 * M.X i j ^ 2 ≤ M.B ^ 2 * ((n : ℝ) * C ^ 2) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hC j) hB2
    have hsum_le : (∑ i, (⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ : ℝ≥0))
        ≤ (⟨M.B ^ 2 * ((n : ℝ) * C ^ 2), by positivity⟩ : ℝ≥0) := by
      apply NNReal.coe_le_coe.mp
      rw [NNReal.coe_mk]
      refine le_trans (le_of_eq ?_) hreal
      refine (NNReal.coe_sum _ _).trans ?_
      simp only [NNReal.coe_mk]
    calc (⟨(1 / (n : ℝ)) ^ 2, by positivity⟩ : ℝ≥0)
            * ∑ i, (⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ : ℝ≥0)
          ≤ (⟨(1 / (n : ℝ)) ^ 2, by positivity⟩ : ℝ≥0)
            * ⟨M.B ^ 2 * ((n : ℝ) * C ^ 2), by positivity⟩ :=
            mul_le_mul_of_nonneg_left hsum_le (zero_le _)
      _ = ⟨M.B ^ 2 * C ^ 2 / n, by positivity⟩ := by
            rw [show (⟨(1 / (n : ℝ)) ^ 2, by positivity⟩ : ℝ≥0)
                  * ⟨M.B ^ 2 * ((n : ℝ) * C ^ 2), by positivity⟩
                = ⟨(1 / (n : ℝ)) ^ 2 * (M.B ^ 2 * ((n : ℝ) * C ^ 2)), by positivity⟩ from rfl]
            apply NNReal.coe_injective
            simp only [NNReal.coe_mk]
            field_simp
  have hup : HasSubgaussianMGF (fun ω => (1 / (n : ℝ)) * ∑ i, V i ω)
      (⟨M.B ^ 2 * C ^ 2 / n, by positivity⟩ : ℝ≥0) μ :=
    ⟨hscaled.integrable_exp_mul, fun t => (hscaled.mgf_le t).trans
      (Real.exp_le_exp.mpr (by gcongr; exact_mod_cast hproxy))⟩
  -- Assemble: centered (mean zero) sub-Gaussian.
  rw [isSubGaussian_iff, hmean]
  simp only [sub_zero]
  exact hup

end StatLean.HighDimensionalStatistics.MEstimator
