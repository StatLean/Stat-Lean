import StatLean.Bayesian.Conjugacy.NormalNormal

/-!
# Linear-shrinkage and James–Stein risk

The optimality side of the normal hierarchy. The linear-shrinkage estimator `c·X` has frequentist
risk `∑ᵢ((1−c)²θᵢ² + c²σ²)` and Bayes risk (under `θ ∼ N(0, τ²)`) `p·((1−c)²τ² + c²σ²)`, minimized
at the oracle weight `c* = τ²/(σ²+τ²)` — the empirical-Bayes shrinkage factor whose Bayes risk
`p·σ²τ²/(σ²+τ²)` is proved in `StatLean.MultipleTesting.empiricalBayes_risk` (Candès, STAT 300C;
cited, not imported — the DAG forbids importing that area's concept files). The James–Stein
estimator `(1 − (p−2)σ²/‖X‖²)·X` strictly dominates the MLE `X` in dimension `p ≥ 3` (the Stein
effect).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). Note 2.8.2 (the Stein effect), p. 96; Example 4.2.3 (truncated
James–Stein); §10.5 (empirical-Bayes justifications of the Stein effect), p. 484.

**Proof formalization notes.** The linear-shrinkage risk is a coordinatewise Gaussian
bias²+variance computation (`integral_id_gaussianReal`, `variance_id_gaussianReal` per coordinate,
`Measure.pi` Fubini); the Bayes risk integrates it against `N(0,τ²)`; the argmin is a real
quadratic-in-`c` minimization (`nlinarith`/completing the square). The James–Stein risk identity
uses the Gaussian integration-by-parts (Stein's lemma) built from
`ForMathlib.GaussianDeriv.hasDerivAt_gaussianPDFReal` and the pinned interval/improper IBP; the
`p ≥ 3` hypothesis is what makes `E‖X‖⁻²` finite. Dominance is the risk identity plus positivity.

**Bibliographic comments.** The inadmissibility of the sample mean in dimension `≥ 3` is C. Stein
("Inadmissibility of the usual estimator for the mean of a multivariate normal distribution,"
*Proc. Third Berkeley Symp.* 1 (1956), 197–206); the explicit dominating estimator and its risk are
W. James and C. Stein ("Estimation with quadratic loss," *Proc. Fourth Berkeley Symp.* 1 (1961),
361–379). The empirical-Bayes reading — shrinkage toward a data-estimated prior mean — is B. Efron
and C. Morris (1973) and underlies Robert §10.5.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.Bayesian

/-- The **linear-shrinkage estimator** `x ↦ c·x` (shrinkage toward the origin). -/
noncomputable def linearShrinkage (c : ℝ) {p : ℕ} (x : Fin p → ℝ) : Fin p → ℝ := fun i => c * x i

/-- The **James–Stein estimator** `x ↦ (1 − (p−2)σ²/‖x‖²)·x` (James and Stein 1961). -/
noncomputable def jamesSteinEstimator (σ2 : ℝ) {p : ℕ} (x : Fin p → ℝ) : Fin p → ℝ :=
  fun i => (1 - ((p : ℝ) - 2) * σ2 / (∑ j, (x j) ^ 2)) * x i

/-- Integrability of a shrunken square `y ↦ (c·y − b)²` against any real Gaussian (it is the square
of an `L²` function, a degree-2 polynomial). -/
private lemma gaussian_shrink_integrable (c b m : ℝ) (σ2 : ℝ≥0) :
    Integrable (fun y => (c * y - b) ^ 2) (gaussianReal m σ2) := by
  have h2 : MemLp (fun y => c * y - b) 2 (gaussianReal m σ2) :=
    ((memLp_id_gaussianReal 2).const_mul c).sub (memLp_const b)
  simpa using h2.integrable_sq

/-- Integrability of `y ↦ y²` against any real Gaussian (second moment). -/
private lemma gaussian_sq_integrable (m : ℝ) (σ2 : ℝ≥0) :
    Integrable (fun y => y ^ 2) (gaussianReal m σ2) := by
  simpa using (memLp_id_gaussianReal 2).integrable_sq

/-- The centred second moment of a real Gaussian: `∫ (y − θ)² ∂N(θ, σ²) = σ²` (its variance). -/
private lemma gaussian_centred_sq (θ : ℝ) (σ2 : ℝ≥0) :
    ∫ y, (y - θ) ^ 2 ∂(gaussianReal θ σ2) = (σ2 : ℝ) := by
  rw [← variance_id_gaussianReal (μ := θ) (v := σ2), variance_eq_integral aemeasurable_id]
  simp only [id_eq, integral_id_gaussianReal]

/-- The centred first moment of a real Gaussian: `∫ (y − θ) ∂N(θ, σ²) = 0`. -/
private lemma gaussian_centred (θ : ℝ) (σ2 : ℝ≥0) :
    ∫ y, (y - θ) ∂(gaussianReal θ σ2) = 0 := by
  have hy : Integrable (fun y : ℝ => y) (gaussianReal θ σ2) :=
    (memLp_id_gaussianReal 2).integrable (by norm_num)
  calc ∫ y, (y - θ) ∂(gaussianReal θ σ2)
      = (∫ y, y ∂(gaussianReal θ σ2)) - ∫ _y, θ ∂(gaussianReal θ σ2) :=
        integral_sub hy (integrable_const θ)
    _ = 0 := by rw [integral_id_gaussianReal, integral_const]; simp

/-- The second moment of a mean-zero real Gaussian: `∫ y² ∂N(0, τ²) = τ²`. -/
private lemma gaussian_sq_mean_zero (τ2 : ℝ≥0) :
    ∫ y, y ^ 2 ∂(gaussianReal 0 τ2) = (τ2 : ℝ) := by
  have h := gaussian_centred_sq 0 τ2
  simpa using h

/-- The **coordinatewise linear-shrinkage risk**: `∫ (c·y − θ)² ∂N(θ, σ²) = (1−c)²θ² + c²σ²`
(bias² + variance). This holds for every `σ² ≥ 0`, so the nondegeneracy hypothesis of the
headline theorem is not needed here. -/
private lemma gaussian_shrink_coord (c θ : ℝ) (σ2 : ℝ≥0) :
    ∫ y, (c * y - θ) ^ 2 ∂(gaussianReal θ σ2)
      = (1 - c) ^ 2 * θ ^ 2 + c ^ 2 * (σ2 : ℝ) := by
  have hlin : Integrable (fun y => y - θ) (gaussianReal θ σ2) :=
    ((memLp_id_gaussianReal 2).integrable (by norm_num)).sub (integrable_const θ)
  have hsq : Integrable (fun y => (y - θ) ^ 2) (gaussianReal θ σ2) := by
    have h2 : MemLp (fun y => y - θ) 2 (gaussianReal θ σ2) :=
      (memLp_id_gaussianReal 2).sub (memLp_const θ)
    simpa using h2.integrable_sq
  calc ∫ y, (c * y - θ) ^ 2 ∂(gaussianReal θ σ2)
      = ∫ y, (c ^ 2 * (y - θ) ^ 2
          + ((2 * c * (c - 1) * θ) * (y - θ) + (c - 1) ^ 2 * θ ^ 2)) ∂(gaussianReal θ σ2) := by
        apply integral_congr_ae; filter_upwards with y; ring
    _ = (∫ y, c ^ 2 * (y - θ) ^ 2 ∂(gaussianReal θ σ2))
          + ∫ y, ((2 * c * (c - 1) * θ) * (y - θ) + (c - 1) ^ 2 * θ ^ 2) ∂(gaussianReal θ σ2) :=
        integral_add (hsq.const_mul _) ((hlin.const_mul _).add (integrable_const _))
    _ = c ^ 2 * (∫ y, (y - θ) ^ 2 ∂(gaussianReal θ σ2))
          + ((2 * c * (c - 1) * θ) * (∫ y, (y - θ) ∂(gaussianReal θ σ2)) + (c - 1) ^ 2 * θ ^ 2) := by
        rw [integral_const_mul, integral_add (hlin.const_mul _) (integrable_const _),
          integral_const_mul, integral_const]
        simp
    _ = (1 - c) ^ 2 * θ ^ 2 + c ^ 2 * (σ2 : ℝ) := by
        rw [gaussian_centred_sq, gaussian_centred]; ring

/-- The linear-shrinkage frequentist risk value, computed without the nondegeneracy hypothesis so
that both the headline theorem and the Bayes-risk theorem can invoke it. -/
private lemma linearShrinkage_risk_value (c : ℝ) {p : ℕ} (θ : Fin p → ℝ) (σ2 : ℝ≥0) :
    (∫ x, ∑ i, (linearShrinkage c x i - θ i) ^ 2 ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      = ∑ i, ((1 - c) ^ 2 * (θ i) ^ 2 + c ^ 2 * (σ2 : ℝ)) := by
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [linearShrinkage]
    rw [show (∫ x, (c * x i - θ i) ^ 2 ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
          = ∫ y, (c * y - θ i) ^ 2 ∂(gaussianReal (θ i) σ2) from
        integral_comp_eval (μ := fun i => gaussianReal (θ i) σ2) (i := i)
          (f := fun y => (c * y - θ i) ^ 2)
          (gaussian_shrink_integrable c (θ i) (θ i) σ2).aestronglyMeasurable]
    exact gaussian_shrink_coord c (θ i) σ2
  · intro i _
    simp only [linearShrinkage]
    exact integrable_comp_eval (μ := fun i => gaussianReal (θ i) σ2) (i := i)
      (f := fun y => (c * y - θ i) ^ 2) (gaussian_shrink_integrable c (θ i) (θ i) σ2)

/-- **Frequentist risk of linear shrinkage** (3D.1): `R(θ, c·X) = ∑ᵢ((1−c)²θᵢ² + c²σ²)`. -/
theorem normalMeans_linearShrinkage_risk (c : ℝ) {p : ℕ} (θ : Fin p → ℝ) (σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Robert Note 2.8.2
    (hσ : σ2 ≠ 0) :
    (∫ x, ∑ i, (linearShrinkage c x i - θ i) ^ 2 ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      = ∑ i, ((1 - c) ^ 2 * (θ i) ^ 2 + c ^ 2 * (σ2 : ℝ)) :=
  linearShrinkage_risk_value c θ σ2

/-- **Bayes risk of linear shrinkage** (3D.2) under `θ ∼ N(0, τ²)`: `p·((1−c)²τ² + c²σ²)`. The
minimized value `p·σ²τ²/(σ²+τ²)` is `StatLean.MultipleTesting.empiricalBayes_risk`. -/
theorem normalMeans_linearShrinkage_bayesRisk (c : ℝ) (p : ℕ) (τ2 σ2 : ℝ≥0) :
    (∫ θ, (∫ x, ∑ i, (linearShrinkage c x i - θ i) ^ 2
        ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      ∂(Measure.pi fun _ : Fin p => gaussianReal 0 τ2))
      = (p : ℝ) * ((1 - c) ^ 2 * (τ2 : ℝ) + c ^ 2 * (σ2 : ℝ)) := by
  have hsq : ∀ i : Fin p, Integrable (fun θ : Fin p → ℝ => (θ i) ^ 2)
      (Measure.pi fun _ : Fin p => gaussianReal 0 τ2) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin p => gaussianReal 0 τ2) (i := i)
      (f := fun y => y ^ 2) (gaussian_sq_integrable 0 τ2)
  calc (∫ θ, (∫ x, ∑ i, (linearShrinkage c x i - θ i) ^ 2
          ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
        ∂(Measure.pi fun _ : Fin p => gaussianReal 0 τ2))
      = ∫ θ, (∑ i, ((1 - c) ^ 2 * (θ i) ^ 2 + c ^ 2 * (σ2 : ℝ)))
          ∂(Measure.pi fun _ : Fin p => gaussianReal 0 τ2) := by
        apply integral_congr_ae; filter_upwards with θ
        exact linearShrinkage_risk_value c θ σ2
    _ = ∑ i, ∫ θ, ((1 - c) ^ 2 * (θ i) ^ 2 + c ^ 2 * (σ2 : ℝ))
          ∂(Measure.pi fun _ : Fin p => gaussianReal 0 τ2) := by
        rw [integral_finset_sum]
        intro i _
        exact ((hsq i).const_mul _).add (integrable_const _)
    _ = ∑ _i : Fin p, ((1 - c) ^ 2 * (τ2 : ℝ) + c ^ 2 * (σ2 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_add ((hsq i).const_mul _) (integrable_const _), integral_const_mul,
          integral_const,
          show (∫ θ, (θ i) ^ 2 ∂(Measure.pi fun _ : Fin p => gaussianReal 0 τ2))
              = ∫ y, y ^ 2 ∂(gaussianReal 0 τ2) from
            integral_comp_eval (μ := fun _ : Fin p => gaussianReal 0 τ2) (i := i)
              (f := fun y => y ^ 2) (gaussian_sq_integrable 0 τ2).aestronglyMeasurable,
          gaussian_sq_mean_zero]
        simp
    _ = (p : ℝ) * ((1 - c) ^ 2 * (τ2 : ℝ) + c ^ 2 * (σ2 : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The oracle weight minimizes the Bayes risk** (3D.2): `c* = τ²/(σ²+τ²)` is the argmin. -/
theorem normalMeans_linearShrinkage_bayesRisk_argmin (p : ℕ) (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate variances; Robert §10.4.2
    (hσ : σ2 ≠ 0) (hτ : τ2 ≠ 0) (c : ℝ) :
    (p : ℝ) * ((1 - (τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))) ^ 2 * (τ2 : ℝ)
        + ((τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))) ^ 2 * (σ2 : ℝ))
      ≤ (p : ℝ) * ((1 - c) ^ 2 * (τ2 : ℝ) + c ^ 2 * (σ2 : ℝ)) := by
  have hτ0 : (0 : ℝ) < (τ2 : ℝ) := NNReal.coe_pos.mpr (zero_lt_iff.mpr hτ)
  have hd : (0 : ℝ) < (σ2 : ℝ) + (τ2 : ℝ) :=
    add_pos_of_nonneg_of_pos (NNReal.coe_nonneg σ2) hτ0
  have hne : (σ2 : ℝ) + (τ2 : ℝ) ≠ 0 := ne_of_gt hd
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg p)
  have hcstar : (1 - (τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))) ^ 2 * (τ2 : ℝ)
        + ((τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ))) ^ 2 * (σ2 : ℝ)
      = (σ2 : ℝ) * (τ2 : ℝ) / ((σ2 : ℝ) + (τ2 : ℝ)) := by
    field_simp
    ring
  rw [hcstar, div_le_iff₀ hd]
  nlinarith [sq_nonneg (((σ2 : ℝ) + (τ2 : ℝ)) * c - (τ2 : ℝ))]

/-! ### James–Stein risk (3D.4): the Gaussian Stein's-lemma development -/

/-- Derivative of the one-coordinate slice `s ↦ s/(s²+c)` of the James–Stein vector field
`x ↦ xᵢ/‖x‖²` (with `c = ∑_{j≠i} xⱼ²` the fixed contribution of the other coordinates). -/
private lemma hasDerivAt_jsSlice (c t : ℝ) (h : t ^ 2 + c ≠ 0) :
    HasDerivAt (fun s => s / (s ^ 2 + c)) ((c - t ^ 2) / (t ^ 2 + c) ^ 2) t := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + c) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).add_const c
  have h2 : HasDerivAt (fun s : ℝ => s / (s ^ 2 + c))
      ((1 * (t ^ 2 + c) - t * (2 * t)) / (t ^ 2 + c) ^ 2) t := (hasDerivAt_id t).div h1 h
  have heq : (1 * (t ^ 2 + c) - t * (2 * t)) / (t ^ 2 + c) ^ 2
      = (c - t ^ 2) / (t ^ 2 + c) ^ 2 := by
    rw [div_eq_div_iff (pow_ne_zero 2 h) (pow_ne_zero 2 h)]; ring
  rwa [heq] at h2

/-- The **divergence identity** `∑ᵢ (S − 2xᵢ²)/S² = (p−2)/S` with `S = ‖x‖²` — the pointwise
content of `∑ᵢ ∂ᵢ(xᵢ/‖x‖²) = (p−2)/‖x‖²`. Holds unconditionally (`ℝ`-division by `0` is `0`). -/
private lemma js_div_sum {p : ℕ} (x : Fin p → ℝ) :
    ∑ i, ((∑ j, (x j) ^ 2) - 2 * (x i) ^ 2) / (∑ j, (x j) ^ 2) ^ 2
      = ((p : ℝ) - 2) / (∑ j, (x j) ^ 2) := by
  set S : ℝ := ∑ j, (x j) ^ 2 with hSdef
  rcases eq_or_ne S 0 with hS | hS
  · simp [hS]
  · rw [← Finset.sum_div]
    have hnum : ∑ i, (S - 2 * (x i) ^ 2) = (p : ℝ) * S - 2 * S := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum, ← hSdef]
    rw [hnum, div_eq_div_iff (pow_ne_zero 2 hS) hS]
    ring

/-- Integrability of `t ↦ h t · gaussianPDFReal m σ² t` for bounded `h` (bounded × integrable
density). -/
private lemma integrable_bdd_mul_gaussianPDFReal (m : ℝ) (σ2 : ℝ≥0) {h : ℝ → ℝ}
    (hm : Measurable h) {C : ℝ} (hC : ∀ t, |h t| ≤ C) :
    Integrable (fun t => h t * gaussianPDFReal m σ2 t) := by
  refine ((integrable_gaussianPDFReal m σ2).const_mul C).mono'
    (hm.aestronglyMeasurable.mul (measurable_gaussianPDFReal m σ2).aestronglyMeasurable) ?_
  refine ae_of_all _ fun t => ?_
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg m σ2 t)]
  exact mul_le_mul_of_nonneg_right (hC t) (gaussianPDFReal_nonneg m σ2 t)

/-- Integrability of the Gaussian score `t ↦ (m − t) · gaussianPDFReal m σ² t` (first-moment
integrability). -/
private lemma integrable_score_gaussianPDFReal (m : ℝ) (σ2 : ℝ≥0) (hσ : σ2 ≠ 0) :
    Integrable (fun t => (m - t) * gaussianPDFReal m σ2 t) := by
  have hid : Integrable (fun t => t * gaussianPDFReal m σ2 t) := by
    have h1 : Integrable (id : ℝ → ℝ) (gaussianReal m σ2) :=
      (memLp_id_gaussianReal 1).integrable (by norm_num)
    rw [gaussianReal_of_var_ne_zero m hσ, integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF m σ2) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at h1
    simpa [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg m σ2 _), smul_eq_mul,
      mul_comm] using h1
  have : (fun t => (m - t) * gaussianPDFReal m σ2 t)
      = (fun t => m * gaussianPDFReal m σ2 t - t * gaussianPDFReal m σ2 t) := by
    funext t; ring
  rw [this]
  exact ((integrable_gaussianPDFReal m σ2).const_mul m).sub hid

/-- **One-dimensional Gaussian Stein identity**: `∫ (t−m)·h ∂N(m,σ²) = σ²·∫ h' ∂N(m,σ²)` for a
differentiable `h` with `h` and `h'` bounded. The integration-by-parts boundary terms vanish by
Gaussian decay; integrability is the bounded-times-density and score lemmas above. -/
private lemma gaussian_stein_1d (m : ℝ) (σ2 : ℝ≥0) (hσ : σ2 ≠ 0) {h h' : ℝ → ℝ}
    (hm : Measurable h) (hm' : Measurable h') (hd : ∀ t, HasDerivAt h (h' t) t)
    {C : ℝ} (hhC : ∀ t, |h t| ≤ C) (hh'C : ∀ t, |h' t| ≤ C) :
    ∫ t, (t - m) * h t ∂(gaussianReal m σ2) = (σ2 : ℝ) * ∫ t, h' t ∂(gaussianReal m σ2) := by
  set pdf := gaussianPDFReal m σ2 with hpdfdef
  have hderiv : ∀ t, HasDerivAt pdf ((m - t) / (σ2 : ℝ) * pdf t) t := fun t =>
    hasDerivAt_gaussianPDFReal m σ2 hσ t
  have huv : Integrable (fun t => h t * pdf t) := integrable_bdd_mul_gaussianPDFReal m σ2 hm hhC
  have hu'v : Integrable (fun t => h' t * pdf t) := integrable_bdd_mul_gaussianPDFReal m σ2 hm' hh'C
  have hscore : Integrable (fun t => (m - t) * pdf t) := integrable_score_gaussianPDFReal m σ2 hσ
  have huv' : Integrable (fun t => h t * ((m - t) / (σ2 : ℝ) * pdf t)) := by
    have hrw : (fun t => h t * ((m - t) / (σ2 : ℝ) * pdf t))
        = fun t => (σ2 : ℝ)⁻¹ * (h t * ((m - t) * pdf t)) := by
      funext t; field_simp; ring
    rw [hrw]
    exact (hscore.bdd_mul hm.aestronglyMeasurable
      ⟨C, fun t => by rw [Real.norm_eq_abs]; exact hhC t⟩).const_mul _
  have hibp : (∫ t, h t * ((m - t) / (σ2 : ℝ) * pdf t)) = -∫ t, h' t * pdf t := by
    have key := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
      (L := ContinuousLinearMap.mul ℝ ℝ) (u := h) (u' := h') (v := pdf)
      (v' := fun t => (m - t) / (σ2 : ℝ) * pdf t)
      (fun x _ => hd x) (fun x _ => hderiv x)
      (by simpa only [ContinuousLinearMap.mul_apply'] using huv')
      (by simpa only [ContinuousLinearMap.mul_apply'] using hu'v)
      (by simpa only [ContinuousLinearMap.mul_apply'] using huv)
    simpa only [ContinuousLinearMap.mul_apply'] using key
  rw [integral_gaussianReal_eq_integral_smul hσ, integral_gaussianReal_eq_integral_smul hσ]
  simp only [smul_eq_mul]
  have hpt : (fun t => pdf t * ((t - m) * h t))
      = fun t => -(σ2 : ℝ) * (h t * ((m - t) / (σ2 : ℝ) * pdf t)) := by
    funext t; field_simp; ring
  rw [hpt, integral_const_mul, hibp, neg_mul_neg]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun t => mul_comm (h' t) (pdf t))

theorem jamesStein_risk_difference {p : ℕ}
    -- USER-INPUT: the Stein effect requires dimension ≥ 3; James–Stein 1961
    (hp : 3 ≤ p) (θ : Fin p → ℝ) (σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Robert Note 2.8.2
    (hσ : σ2 ≠ 0) :
    (∫ x, ∑ i, (jamesSteinEstimator (σ2 : ℝ) x i - θ i) ^ 2
        ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      = (p : ℝ) * (σ2 : ℝ) - ((p : ℝ) - 2) ^ 2 * (σ2 : ℝ) ^ 2
          * (∫ x, 1 / (∑ i, (x i) ^ 2) ∂(Measure.pi fun i => gaussianReal (θ i) σ2)) := by
  -- DOCUMENTED SORRY (3D.4 stretch, James–Stein 1961).  Expanding the loss,
  --   (δ_JS − θ)² = (X − θ)² − 2(p−2)σ²·⟨X − θ, X/‖X‖²⟩ + (p−2)²σ⁴/‖X‖²,
  -- and integrating termwise gives `p·σ²` (target 3D.1 with `c = 1`) for the first term and the
  -- last term as stated; the cross term is where Stein's multivariate integration by parts is
  -- required: `∫ (xᵢ − θᵢ)·gᵢ(x) ∂N = σ²·∫ ∂ᵢgᵢ ∂N` for `gᵢ(x) = xᵢ/‖x‖²`, summed over `i` using
  -- `∑ᵢ ∂ᵢ(xᵢ/‖x‖²) = (p−2)/‖x‖²`, turning the cross term into `2(p−2)²σ⁴·E‖X‖⁻²`.  This needs the
  -- coordinatewise IBP built from `ForMathlib.GaussianDeriv.hasDerivAt_gaussianPDFReal` together
  -- with the improper/interval `MeasureTheory.integral_deriv_mul_eq_sub`, handling the singularity
  -- of `xᵢ/‖x‖²` at the origin and the finiteness of `E‖X‖⁻²` (which holds precisely for `p ≥ 3`).
  -- The one-dimensional Stein primitive is present; the multivariate assembly is a deep analysis
  -- task beyond the current touch-set budget, and the frozen statement forbids conditioning on the
  -- scalar identity.  Core 3D (3D.1–3D.3) is fully proved above.
  sorry

/-- **James–Stein dominates the MLE** (3D.4, stretch): in dimension `p ≥ 3` the James–Stein risk is
strictly below the MLE risk `p·σ²` for every `θ` (the Stein effect). -/
theorem jamesStein_dominates_mle {p : ℕ}
    -- USER-INPUT: the Stein effect requires dimension ≥ 3; James–Stein 1961
    (hp : 3 ≤ p) (θ : Fin p → ℝ) (σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Robert Note 2.8.2
    (hσ : σ2 ≠ 0) :
    (∫ x, ∑ i, (jamesSteinEstimator (σ2 : ℝ) x i - θ i) ^ 2
        ∂(Measure.pi fun i => gaussianReal (θ i) σ2))
      < (p : ℝ) * (σ2 : ℝ) := by
  -- DOCUMENTED SORRY (3D.4 stretch).  Immediate from `jamesStein_risk_difference`: the subtracted
  -- term `((p:ℝ)−2)²·σ⁴·E‖X‖⁻²` is strictly positive for `p ≥ 3` (so `(p−2)² > 0`), `σ² ≠ 0`, and
  -- the integrand `1/‖x‖² > 0` on the full-measure set `{x ≠ 0}`, giving `E‖X‖⁻² > 0`.  It rests on
  -- the risk identity above; see the note there.  Core 3D (3D.1–3D.3) is fully proved above.
  sorry

end StatLean.Bayesian
