import StatLean.TimeSeries.ForMathlib.Fourier.HerglotzBochner
import StatLean.TimeSeries.Process.LinearProcess
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Stationary Gaussian processes and the completion of FY Theorem 2.7 (FY §2.1.3, §2.2.1)

Two threads:

1. **FY Theorem 2.7, sufficiency** (`exists_stationary_of_isPosSemidefSeq`, the batch-A
   debt): every even positive semidefinite `γ : ℤ → ℝ` is the ACVF of some weakly
   stationary process. Proof by the **random-phase construction** over the Herglotz
   spectral measure — no Kolmogorov extension needed: on
   `Ω' = AddCircle (2π) × ℝ × ℝ` with `P = (γ(0)⁻¹ • F) ⊗ N(0,1) ⊗ N(0,1)` (where `F`
   is the measure from `exists_measure_of_isPosSemidefSeq`), the process
   `X_t(λ, α, β) = √γ(0) · (α · Re(e^{itλ}) + β · Im(e^{itλ}))`
   has mean `0` and covariance
   `E X_s X_t = γ(0)·E_Λ[Re(e^{i(s−t)Λ})] = Re(measureFourierCoeff F (s−t)) = γ(s−t)`.
2. **FY §2.1.3**: Gaussian processes — a weakly stationary Gaussian process is strictly
   stationary (finite-dimensional Gaussian laws are determined by mean vector and
   covariance matrix, both shift-invariant); a causal ARMA process driven by i.i.d.
   Gaussian noise is a Gaussian process (`L²`-limits of Gaussian vectors are Gaussian);
   the **Wold decomposition** (FY eq. (2.6)) as a named DEBT (batch F, conditional-
   expectation route) and **Proposition 2.1** standing on it.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003: §2.2.1
Theorem 2.7 (p. 40; sufficiency cited to Brockwell & Davis 1991, p. 27 — our
random-phase proof is a different, self-contained route, documented deviation);
§2.1.3 (pp. 32–33: Gaussian processes, Wold eq. (2.6), Proposition 2.1).
(`FY §2.2.1 Thm 2.7; §2.1.3 Prop 2.1`.)

**Proof formalization notes.**
* The random-phase process is *not* Gaussian and not strictly stationary — Theorem 2.7
  only demands weak stationarity, and the construction uses exclusively batch-A bricks
  (`exists_measure_of_isPosSemidefSeq`, `measureFourierCoeff_im/neg`, `NegInvariant`).
  The amplitudes only need mean `0`, variance `1`, uncorrelated; we take independent
  standard Gaussians (`gaussianReal 0 1`) for definiteness.
* `IsGaussianProcess` is Mathlib's (pinned) structure; the weak⇒strict argument pins the
  finite-dimensional laws down through their characteristic functions.
* Prop 2.1(iii) (conditional-independence ⇒ AR(p)) needs Gaussian conditioning; stated
  here with proof deferred (DEBT) pending the Gaussian-conditioning bricks.

**Bibliographic comments.** The spectral random-phase representation goes back to
Slutsky and to Cramér's spectral theory (H. Cramér, "On the theory of stationary random
processes", *Ann. of Math.* **41** (1940), 215–230). The Wold decomposition is H. Wold
(1938). Gaussian processes as determined by second-order structure: Kolmogorov's
*Grundbegriffe* (1933) plus classical multivariate normal theory.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### The random-phase construction (private machinery for FY Theorem 2.7, sufficiency)

On `Ω' = AddCircle (2π) × (ℝ × ℝ)` carrying `P ⊗ N(0,1) ⊗ N(0,1)` the process
`X_t(λ, α, β) = c · (α · Re(e^{itλ}) + β · Im(e^{itλ}))` has mean `0` and covariance
`c² · Re ∫ e^{i(s−t)λ} dP(λ) = c² · Re (measureFourierCoeff P (s − t))`; feeding in the
Herglotz measure normalized to a probability measure and `c = √γ(0)` gives `γ`. -/

private instance factpi : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- Sample space of the random-phase construction: circle × (two amplitudes). -/
private abbrev RPS : Type := AddCircle (2 * π) × (ℝ × ℝ)

/-- Amplitude law: two independent standard Gaussians (any mean-`0`, variance-`1`,
uncorrelated pair would do). -/
private noncomputable def rpAmp : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

private instance rpAmp_isProb : IsProbabilityMeasure rpAmp := by
  rw [rpAmp]; infer_instance

private instance rpAmp_isFinite : IsFiniteMeasure rpAmp := inferInstance

private instance rpAmp_sfinite : SFinite rpAmp := inferInstance

/-- The random-phase process with amplitude scale `c`. -/
private noncomputable def rpProc (c : ℝ) (t : ℤ) : RPS → ℝ :=
  fun z => c * (z.2.1 * (fourier t z.1).re + z.2.2 * (fourier t z.1).im)

private lemma memLp_gauss (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun x : ℝ => x) p (gaussianReal 0 1) := memLp_id_gaussianReal' p hp

private lemma integrable_gauss : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
  (memLp_gauss 1 (by simp)).integrable le_rfl

private lemma gauss_sq : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_eq_sub (μ := gaussianReal 0 1) (memLp_gauss 2 (by simp))
  rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at h
  simpa using h.symm

private lemma integrable_gauss_sq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
  have := (memLp_gauss 2 (by simp)).integrable_sq
  simpa using this

private lemma rpAmp_fst : ∫ p : ℝ × ℝ, p.1 ∂rpAmp = 0 := by
  rw [rpAmp]
  simpa using integral_fun_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (fun x : ℝ => x)

private lemma rpAmp_snd : ∫ p : ℝ × ℝ, p.2 ∂rpAmp = 0 := by
  rw [rpAmp]
  simpa using integral_fun_snd (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (fun x : ℝ => x)

private lemma rpAmp_fst_sq : ∫ p : ℝ × ℝ, p.1 * p.1 ∂rpAmp = 1 := by
  rw [rpAmp]
  have h := integral_fun_fst (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (fun x : ℝ => x ^ 2)
  simp only [probReal_univ, one_smul, gauss_sq] at h
  simpa [← pow_two] using h

private lemma rpAmp_snd_sq : ∫ p : ℝ × ℝ, p.2 * p.2 ∂rpAmp = 1 := by
  rw [rpAmp]
  have h := integral_fun_snd (μ := gaussianReal 0 1) (ν := gaussianReal 0 1) (fun x : ℝ => x ^ 2)
  simp only [probReal_univ, one_smul, gauss_sq] at h
  simpa [← pow_two] using h

private lemma rpAmp_cross : ∫ p : ℝ × ℝ, p.1 * p.2 ∂rpAmp = 0 := by
  rw [rpAmp]
  simpa using integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun x : ℝ => x) (fun x : ℝ => x)

private lemma rpAmp_int_fst : Integrable (fun p : ℝ × ℝ => p.1) rpAmp := by
  rw [rpAmp]; exact integrable_gauss.comp_fst _

private lemma rpAmp_int_snd : Integrable (fun p : ℝ × ℝ => p.2) rpAmp := by
  rw [rpAmp]; exact integrable_gauss.comp_snd _

private lemma rpAmp_int_fst_sq : Integrable (fun p : ℝ × ℝ => p.1 * p.1) rpAmp := by
  have h : (fun p : ℝ × ℝ => p.1 * p.1) = fun p : ℝ × ℝ => p.1 ^ 2 := by funext p; ring
  rw [h, rpAmp]; exact integrable_gauss_sq.comp_fst _

private lemma rpAmp_int_snd_sq : Integrable (fun p : ℝ × ℝ => p.2 * p.2) rpAmp := by
  have h : (fun p : ℝ × ℝ => p.2 * p.2) = fun p : ℝ × ℝ => p.2 ^ 2 := by funext p; ring
  rw [h, rpAmp]; exact integrable_gauss_sq.comp_snd _

private lemma rpAmp_int_cross : Integrable (fun p : ℝ × ℝ => p.1 * p.2) rpAmp := by
  rw [rpAmp]; exact integrable_gauss.mul_prod integrable_gauss

private lemma continuous_fourier_re (t : ℤ) :
    Continuous fun l : AddCircle (2 * π) => (fourier t l).re :=
  Complex.continuous_re.comp (map_continuous (fourier t))

private lemma continuous_fourier_im (t : ℤ) :
    Continuous fun l : AddCircle (2 * π) => (fourier t l).im :=
  Complex.continuous_im.comp (map_continuous (fourier t))

private lemma integrable_of_continuous (P : Measure (AddCircle (2 * π))) [IsFiniteMeasure P]
    {F : AddCircle (2 * π) → ℝ} (hF : Continuous F) : Integrable F P := by
  simpa using (BoundedContinuousFunction.mkOfCompact
    (⟨F, hF⟩ : C(AddCircle (2 * π), ℝ))).integrable P

/-- `Re(e^{isλ} · conj e^{itλ}) = Re e^{i(s−t)λ}` in coordinates. -/
private lemma fourier_sub_re (s t : ℤ) (l : AddCircle (2 * π)) :
    (fourier s l).re * (fourier t l).re + (fourier s l).im * (fourier t l).im
      = (fourier (s - t) l).re := by
  have h : fourier (T := 2 * π) (s - t) l
      = fourier (T := 2 * π) s l * (starRingEnd ℂ) (fourier (T := 2 * π) t l) := by
    rw [sub_eq_add_neg, fourier_add, fourier_neg]
  rw [h]
  simp [Complex.mul_re]

private lemma rp_int_term {F : AddCircle (2 * π) → ℝ} (hF : Continuous F)
    {G : ℝ × ℝ → ℝ} (hG : Integrable G rpAmp)
    (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P] :
    Integrable (fun z : RPS => F z.1 * G z.2) (P.prod rpAmp) :=
  (integrable_of_continuous P hF).mul_prod hG

private lemma rp_integral (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (t : ℤ) : ∫ z, rpProc c t z ∂(P.prod rpAmp) = 0 := by
  have h1 : Integrable (fun z : RPS => (fourier t z.1).re * z.2.1) (P.prod rpAmp) :=
    rp_int_term (continuous_fourier_re t) rpAmp_int_fst P
  have h2 : Integrable (fun z : RPS => (fourier t z.1).im * z.2.2) (P.prod rpAmp) :=
    rp_int_term (continuous_fourier_im t) rpAmp_int_snd P
  have heq : ∀ z : RPS, rpProc c t z
      = c * ((fourier t z.1).re * z.2.1 + (fourier t z.1).im * z.2.2) := by
    intro z; simp only [rpProc]; ring
  calc ∫ z, rpProc c t z ∂(P.prod rpAmp)
      = ∫ z : RPS, c * ((fourier t z.1).re * z.2.1 + (fourier t z.1).im * z.2.2)
          ∂(P.prod rpAmp) := integral_congr_ae (Eventually.of_forall heq)
    _ = c * ∫ z : RPS, ((fourier t z.1).re * z.2.1 + (fourier t z.1).im * z.2.2)
          ∂(P.prod rpAmp) := integral_const_mul _ _
    _ = 0 := by
        rw [integral_add h1 h2,
          integral_prod_mul (μ := P) (ν := rpAmp)
            (fun l => (fourier (T := 2 * π) t l).re) (fun p : ℝ × ℝ => p.1),
          integral_prod_mul (μ := P) (ν := rpAmp)
            (fun l => (fourier (T := 2 * π) t l).im) (fun p : ℝ × ℝ => p.2),
          rpAmp_fst, rpAmp_snd]
        ring

/-- The three-term quadratic form in the amplitudes, integrated out: only the `α²` and
`β²` slots survive (`E α² = E β² = 1`, `E αβ = 0`). -/
private lemma rp_quad (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    {F₁ F₂ F₃ : AddCircle (2 * π) → ℝ} (h₁ : Continuous F₁) (h₂ : Continuous F₂)
    (h₃ : Continuous F₃) :
    ∫ z : RPS, (F₁ z.1 * (z.2.1 * z.2.1) + F₂ z.1 * (z.2.1 * z.2.2)
        + F₃ z.1 * (z.2.2 * z.2.2)) ∂(P.prod rpAmp)
      = ∫ l, (F₁ l + F₃ l) ∂P := by
  have i₁ : Integrable (fun z : RPS => F₁ z.1 * (z.2.1 * z.2.1)) (P.prod rpAmp) :=
    rp_int_term h₁ rpAmp_int_fst_sq P
  have i₂ : Integrable (fun z : RPS => F₂ z.1 * (z.2.1 * z.2.2)) (P.prod rpAmp) :=
    rp_int_term h₂ rpAmp_int_cross P
  have i₃ : Integrable (fun z : RPS => F₃ z.1 * (z.2.2 * z.2.2)) (P.prod rpAmp) :=
    rp_int_term h₃ rpAmp_int_snd_sq P
  have i₁₂ : Integrable
      (fun z : RPS => F₁ z.1 * (z.2.1 * z.2.1) + F₂ z.1 * (z.2.1 * z.2.2)) (P.prod rpAmp) :=
    i₁.add i₂
  rw [integral_add i₁₂ i₃, integral_add i₁ i₂,
    integral_prod_mul (μ := P) (ν := rpAmp) F₁ (fun p : ℝ × ℝ => p.1 * p.1),
    integral_prod_mul (μ := P) (ν := rpAmp) F₂ (fun p : ℝ × ℝ => p.1 * p.2),
    integral_prod_mul (μ := P) (ν := rpAmp) F₃ (fun p : ℝ × ℝ => p.2 * p.2),
    rpAmp_fst_sq, rpAmp_snd_sq, rpAmp_cross,
    integral_add (integrable_of_continuous P h₁) (integrable_of_continuous P h₃)]
  ring

private lemma rp_prod_eq (c : ℝ) (s t : ℤ) (z : RPS) :
    rpProc c s z * rpProc c t z
      = (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).re)) z.1 * (z.2.1 * z.2.1)
        + (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).im
            + (fourier s l).im * (fourier t l).re)) z.1 * (z.2.1 * z.2.2)
        + (fun l => c ^ 2 * ((fourier s l).im * (fourier t l).im)) z.1 * (z.2.2 * z.2.2) := by
  simp only [rpProc]
  ring

private lemma rp_integrable_mul (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (s t : ℤ) :
    Integrable (fun z : RPS => rpProc c s z * rpProc c t z) (P.prod rpAmp) := by
  have i₁ : Integrable (fun z : RPS =>
      (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).re)) z.1 * (z.2.1 * z.2.1))
      (P.prod rpAmp) :=
    rp_int_term (((continuous_fourier_re s).mul (continuous_fourier_re t)).const_mul _)
      rpAmp_int_fst_sq P
  have i₂ : Integrable (fun z : RPS =>
      (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).im
        + (fourier s l).im * (fourier t l).re)) z.1 * (z.2.1 * z.2.2)) (P.prod rpAmp) :=
    rp_int_term ((((continuous_fourier_re s).mul (continuous_fourier_im t)).add
      ((continuous_fourier_im s).mul (continuous_fourier_re t))).const_mul _) rpAmp_int_cross P
  have i₃ : Integrable (fun z : RPS =>
      (fun l => c ^ 2 * ((fourier s l).im * (fourier t l).im)) z.1 * (z.2.2 * z.2.2))
      (P.prod rpAmp) :=
    rp_int_term (((continuous_fourier_im s).mul (continuous_fourier_im t)).const_mul _)
      rpAmp_int_snd_sq P
  have i₁₂ : Integrable (fun z : RPS =>
      (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).re)) z.1 * (z.2.1 * z.2.1)
        + (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).im
            + (fourier s l).im * (fourier t l).re)) z.1 * (z.2.1 * z.2.2)) (P.prod rpAmp) :=
    i₁.add i₂
  have i : Integrable (fun z : RPS =>
      (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).re)) z.1 * (z.2.1 * z.2.1)
        + (fun l => c ^ 2 * ((fourier s l).re * (fourier t l).im
            + (fourier s l).im * (fourier t l).re)) z.1 * (z.2.1 * z.2.2)
        + (fun l => c ^ 2 * ((fourier s l).im * (fourier t l).im)) z.1 * (z.2.2 * z.2.2))
      (P.prod rpAmp) := i₁₂.add i₃
  exact i.congr (Eventually.of_forall fun z => (rp_prod_eq c s t z).symm)

private lemma rp_integral_mul (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (s t : ℤ) :
    ∫ z, rpProc c s z * rpProc c t z ∂(P.prod rpAmp)
      = c ^ 2 * (measureFourierCoeff P (s - t)).re := by
  have hfourier : Integrable (fun l : AddCircle (2 * π) => fourier (s - t) l) P :=
    (BoundedContinuousFunction.mkOfCompact (fourier (T := 2 * π) (s - t))).integrable P
  have hre : ∫ l : AddCircle (2 * π), (fourier (s - t) l).re ∂P
      = (measureFourierCoeff P (s - t)).re := by
    rw [measureFourierCoeff]
    simpa using integral_re (μ := P) (f := fun l : AddCircle (2 * π) => fourier (s - t) l) hfourier
  rw [integral_congr_ae (Eventually.of_forall (rp_prod_eq c s t)),
    rp_quad P (F₁ := fun l => c ^ 2 * ((fourier s l).re * (fourier t l).re))
      (F₂ := fun l => c ^ 2 * ((fourier s l).re * (fourier t l).im
        + (fourier s l).im * (fourier t l).re))
      (F₃ := fun l => c ^ 2 * ((fourier s l).im * (fourier t l).im))
      (((continuous_fourier_re s).mul (continuous_fourier_re t)).const_mul _)
      ((((continuous_fourier_re s).mul (continuous_fourier_im t)).add
        ((continuous_fourier_im s).mul (continuous_fourier_re t))).const_mul _)
      (((continuous_fourier_im s).mul (continuous_fourier_im t)).const_mul _)]
  have hpt : ∀ l : AddCircle (2 * π),
      c ^ 2 * ((fourier s l).re * (fourier t l).re)
        + c ^ 2 * ((fourier s l).im * (fourier t l).im)
        = c ^ 2 * (fourier (s - t) l).re := by
    intro l
    rw [← fourier_sub_re s t l]; ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul, hre]

private lemma rp_continuous (c : ℝ) (t : ℤ) : Continuous (rpProc c t) := by
  have hre : Continuous fun z : RPS => (fourier t z.1).re :=
    (continuous_fourier_re t).comp continuous_fst
  have him : Continuous fun z : RPS => (fourier t z.1).im :=
    (continuous_fourier_im t).comp continuous_fst
  have h1 : Continuous fun z : RPS => z.2.1 := continuous_fst.comp continuous_snd
  have h2 : Continuous fun z : RPS => z.2.2 := continuous_snd.comp continuous_snd
  exact ((h1.mul hre).add (h2.mul him)).const_mul c

private lemma rp_memLp (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (t : ℤ) : MemLp (rpProc c t) 2 (P.prod rpAmp) := by
  refine (memLp_two_iff_integrable_sq (rp_continuous c t).aestronglyMeasurable).mpr ?_
  refine (rp_integrable_mul P c t t).congr ?_
  filter_upwards with z
  rw [pow_two]

private lemma rp_cov (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (s t : ℤ) :
    cov[rpProc c s, rpProc c t; P.prod rpAmp] = c ^ 2 * (measureFourierCoeff P (s - t)).re := by
  rw [covariance_eq_sub (rp_memLp P c s) (rp_memLp P c t), rp_integral, rp_integral]
  simp only [mul_zero, sub_zero, Pi.mul_apply]
  exact rp_integral_mul P c s t

private theorem rp_isStationary (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) : IsStationary (rpProc c) (P.prod rpAmp) where
  memLp t := rp_memLp P c t
  integral_eq s t := by rw [rp_integral, rp_integral]
  cov_shift t k := by
    have h : t + k - t = k - 0 := by ring
    rw [rp_cov, rp_cov, h]

private theorem rp_acvf (P : Measure (AddCircle (2 * π))) [IsProbabilityMeasure P]
    (c : ℝ) (k : ℤ) :
    acvf (rpProc c) (P.prod rpAmp) k = c ^ 2 * (measureFourierCoeff P k).re := by
  rw [acvf, rp_cov, sub_zero]

/-- `measureFourierCoeff` is scalar-linear in the measure (the normalization step). -/
private lemma mfc_smul (a : ENNReal) (F : Measure (AddCircle (2 * π))) (j : ℤ) :
    measureFourierCoeff (a • F) j = ((a.toReal : ℝ) : ℂ) * measureFourierCoeff F j := by
  rw [measureFourierCoeff, measureFourierCoeff, integral_smul_measure]
  exact Complex.real_smul

/-- **FY Theorem 2.7, sufficiency** (batch-A debt, relocated here; proof: random-phase
construction over the Herglotz measure — see the module docstring). Every even positive
semidefinite sequence is the autocovariance function of some weakly stationary process. -/
theorem exists_stationary_of_isPosSemidefSeq (γ : ℤ → ℝ)
    -- USER-INPUT: evenness; FY §2.2.1 Thm 2.7
    (heven : ∀ k, γ (-k) = γ k)
    -- USER-INPUT: positive semidefiniteness, eq. (2.17); FY §2.2.1 Thm 2.7
    (hpsd : IsPosSemidefSeq γ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧ (∀ t, Measurable (X' t)) ∧ IsStationary X' μ' ∧
        acvf X' μ' = γ := by
  -- Produce a probability measure `P` on the circle and a scale `c` with
  -- `c² · Re (measureFourierCoeff P k) = γ k`; the random-phase process then has ACVF `γ`.
  obtain ⟨P, hP, c, hc⟩ : ∃ (P : Measure (AddCircle (2 * π))) (_ : IsProbabilityMeasure P) (c : ℝ),
      ∀ k, c ^ 2 * (measureFourierCoeff P k).re = γ k := by
    rcases eq_or_lt_of_le hpsd.nonneg_zero with h0 | h0
    · -- degenerate case `γ 0 = 0`: `|γ k| ≤ γ 0 = 0` forces `γ ≡ 0`, take `c = 0`
      have hzero : ∀ k, γ k = 0 := by
        intro k
        have h1 := hpsd.abs_le_of_even heven k
        rw [← h0] at h1
        exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
      exact ⟨Measure.dirac 0, inferInstance, 0, fun k => by simp [hzero k]⟩
    · -- main case: normalize the Herglotz measure to a probability measure, `c = √γ(0)`
      obtain ⟨F, hFfin, _hFneg, hFcoef⟩ := exists_measure_of_isPosSemidefSeq γ heven hpsd
      have hne : ENNReal.ofReal (γ 0) ≠ 0 := by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact h0
      have htop : ENNReal.ofReal (γ 0) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hmass : F Set.univ = ENNReal.ofReal (γ 0) := by
        have h := (measureFourierCoeff_zero F).symm.trans (hFcoef 0)
        have h2 : (F Set.univ).toReal = γ 0 := by exact_mod_cast h
        rw [← h2, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      haveI hprob : IsProbabilityMeasure ((ENNReal.ofReal (γ 0))⁻¹ • F) :=
        ⟨by rw [Measure.smul_apply, smul_eq_mul, hmass, ENNReal.inv_mul_cancel hne htop]⟩
      refine ⟨(ENNReal.ofReal (γ 0))⁻¹ • F, hprob, Real.sqrt (γ 0), fun k => ?_⟩
      rw [mfc_smul, hFcoef k, ENNReal.toReal_inv, ENNReal.toReal_ofReal h0.le,
        Real.sq_sqrt h0.le, ← Complex.ofReal_mul, Complex.ofReal_re]
      field_simp
  haveI := hP
  exact ⟨AddCircle (2 * π) × (ℝ × ℝ), inferInstance, P.prod rpAmp, rpProc c, inferInstance,
    fun t => (rp_continuous c t).measurable, rp_isStationary P c,
    funext fun k => (rp_acvf P c k).trans (hc k)⟩

/-- **FY Theorem 2.7, both halves packaged**: a real sequence is the ACVF of some weakly
stationary process iff it is even and positive semidefinite. -/
theorem isPosSemidefSeq_and_even_iff_acvf (γ : ℤ → ℝ) :
    ((∀ k, γ (-k) = γ k) ∧ IsPosSemidefSeq γ) ↔
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' : ℤ → Ω' → ℝ),
        IsProbabilityMeasure μ' ∧ (∀ t, Measurable (X' t)) ∧ IsStationary X' μ' ∧
          acvf X' μ' = γ := by
  constructor
  · rintro ⟨heven, hpsd⟩
    exact exists_stationary_of_isPosSemidefSeq γ heven hpsd
  · rintro ⟨Ω', _, μ', X', hprob, _hmeas, hstat, rfl⟩
    exact ⟨hstat.acvf_even, hstat.acvf_posSemidef⟩

/-- **Weakly stationary Gaussian processes are strictly stationary** (FY §2.1.3): the
finite-dimensional laws of a Gaussian process are determined by the mean vector and
covariance matrix, and both are shift-invariant under weak stationarity. -/
theorem IsGaussianProcess.isStrictlyStationary [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ}
    -- USER-INPUT: the process is Gaussian; FY §2.1.3
    (hG : IsGaussianProcess X μ)
    -- LEAN-ONLY: coordinate random variables are measurable; implicit in FY
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: weak stationarity; FY §2.1.3
    (hstat : IsStationary X μ) :
    IsStrictlyStationary X μ := by
  sorry

/-- **Causal ARMA with i.i.d. Gaussian noise is a Gaussian process** (FY §2.1.3): the
finite-dimensional vectors are `L²`-limits of linear images of Gaussian vectors. -/
theorem isGaussianProcess_of_linearProcess [IsProbabilityMeasure μ]
    {ψ : ℕ → ℝ} {X ε : ℤ → Ω → ℝ}
    (hX : IsLinearProcessOf ψ X ε μ) (hψ : Summable fun n => |ψ n|)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: the innovations form an i.i.d. Gaussian family; FY §2.1.3
    (hε : IsIIDNoise ε 1 μ)
    (hgauss : ∀ t, μ.map (ε t) = gaussianReal 0 1) :
    IsGaussianProcess X μ := by
  sorry

/-- **Wold decomposition, Gaussian form — DEBT** (FY §2.1.3, eq. (2.6); cited to
Brockwell & Davis 1991, p. 187; closure scheduled for batch F via the conditional-
expectation route, see `notes/time_series/debt_assessment.md` §5): a zero-mean weakly
stationary Gaussian process splits as an MA(∞) over i.i.d. Gaussian innovations plus an
independent deterministic (remote-past-measurable) component. -/
theorem wold_gaussian_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hG : IsGaussianProcess X μ) (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStationary X μ)
    -- USER-INPUT: zero mean; FY eq. (2.6)
    (hmean : ∀ t, ∫ ω, X t ω ∂μ = 0) :
    ∃ (ψ : ℕ → ℝ) (ε V : ℤ → Ω → ℝ) (σ2 : ℝ),
      (Summable fun j => ψ j ^ 2) ∧ IsIIDNoise ε σ2 μ ∧
      (∀ t : ℤ, Measurable (V t)) ∧
      (∀ t : ℤ, Measurable[⨅ n : ℕ, sigmaLE X (t - n)] (V t)) ∧
      Indep (⨆ t : ℤ, MeasurableSpace.comap (ε t) inferInstance)
        (⨆ t : ℤ, MeasurableSpace.comap (V t) inferInstance) μ ∧
      ∀ t : ℤ, Tendsto
        (fun N => eLpNorm
          (fun ω => X t ω - (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω + V t ω)) 2 μ)
        atTop (nhds 0) := by
  sorry

/-- **Proposition 2.1(ii)** (FY §2.1.3): a zero-mean weakly stationary Gaussian process
that is `q`-dependent (`Cov(X_s, X_t) = 0` for `|s − t| > q`) with trivial remote past
in its Wold decomposition is an MA(q). Statement conditional on `wold_gaussian_debt`;
DEBT until batch F. -/
theorem gaussian_q_dependent_isMA_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    {q : ℕ}
    (hG : IsGaussianProcess X μ) (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStationary X μ) (hmean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: q-dependence; FY §2.1.3 Prop 2.1(ii)
    (hdep : ∀ s t : ℤ, (q : ℤ) < |s - t| → cov[X s, X t; μ] = 0)
    -- USER-INPUT: purely nondeterministic (trivial remote past); FY §2.1.3 Prop 2.1(i)
    (hpnd : ∀ A : Set Ω, MeasurableSet[⨅ n : ℕ, sigmaLE X (-(n : ℤ))] A →
      μ A = 0 ∨ μ A = 1) :
    ∃ (a : Fin q → ℝ) (σ2 : ℝ) (ε : ℤ → Ω → ℝ), IsMA a σ2 X ε μ := by
  sorry

end StatLean.TimeSeries
