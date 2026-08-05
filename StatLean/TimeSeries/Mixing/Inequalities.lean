import StatLean.TimeSeries.Mixing.Defs
import StatLean.TimeSeries.Process.Stationary
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Covariance and moment inequalities under mixing (FY §2.6.2, pp. 71–73)

The quantitative toolbox for α-mixing processes:

* **Proposition 2.5(ii) (Billingsley)**: bounded case, `|Cov(f, g)| ≤ 4 α C₁ C₂`, plus
  the complex version with constant `16` — the workhorse of Proposition 2.6;
* **Proposition 2.5(i) (Davydov)**: `1/p + 1/q < 1` ⇒
  `|Cov(f, g)| ≤ 8 α^{1 − 1/p − 1/q} ‖f‖_p ‖g‖_q` — **built here in full** (FY cites
  Doukhan §1.2.2; truncation of both factors against the bounded case);
* **Proposition 2.6 (Volkonskii–Rozanov)**: complex unit-bounded blocks with α-gaps,
  `|E ∏ ξ_l − ∏ E ξ_l| ≤ 16 (k − 1) a` — the factorization engine of both CLT proofs
  (Theorems 2.21(ii) and 2.22);
* the **fourth-moment bound** (the `q = 4` instance of FY Proposition 2.7(ii) that the
  Bernstein-block CLT consumes): bounded, zero-mean, strictly stationary,
  `α(n) ≤ K n⁻²` ⇒ `E S_n⁴ ≤ C n²`;
* **Theorems 2.18/2.19 (Bosq exponential inequalities)** — literature DEBTS (used only
  by ch. 5 KDE uniform rates, outside the current scope).

**Scope note.** FY's Theorem 2.17 (Doukhan–Louhichi moment bounds via the
covariance-decay functional `M_{r,q}`) and the general-`q` Proposition 2.7 are *not*
stated: their only consumers in scope — Theorems 2.20(i)/2.21(i) — are themselves
cited-out literature debts carrying their own hypotheses, and the CLT proofs consume
only the `q = 4` instance stated here.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.2,
Propositions 2.5–2.7 and Theorems 2.17–2.19 (pp. 71–73). (`FY §2.6.2`.)

**Proof formalization notes.**
* Billingsley: with `η = sgn(E[f g | split])`-free classical argument: write the
  covariance against centered factors and pass to the four-event correlation via
  `f = ∫ (1_{f > t} − 1_{f < −t}) dt`-free discretization — the standard route is
  by the identity `Cov(f, g) = ∫∫ [P(f > s, g > t) − P(f > s)P(g > t)] ds dt`
  (Hoeffding), each integrand bounded by `α`; totals `4 α C₁ C₂` after splitting signs.
* Davydov: truncate at levels `C₁, C₂`, apply the bounded case to the truncations and
  Hölder/Markov to the tails; optimize the levels (`C_i = ‖·‖ · α^{-1/(...)}`) to get
  the exponent `1 − 1/p − 1/q` and constant `8`.
* Volkonskii–Rozanov: induction on `k`; each step peels the last factor with the
  complex bounded inequality (constant 16) against the cumulative-past σ-algebra.
* Fourth moment: expand `E S⁴` over index 4-tuples, split each expectation at the
  largest gap `g` (Billingsley pairs), count tuples with largest gap `g` as `O(n g²)`;
  `Σ_g n g² · g⁻² = O(n²)`, and the paired products contribute `(n Σ α)² = O(n²)`.

**Bibliographic comments.** Prop 2.5(i) is Yu. A. Davydov (1968); (ii) is
P. Billingsley, *Convergence of Probability Measures* (1968), Lemma 1 of §20;
Prop 2.6 is Volkonskii & Rozanov (1959, Lemma 4.3 in Bradley's numbering). The
exponential inequalities are D. Bosq, *Nonparametric Statistics for Stochastic
Processes* (1998), Thms 1.3–1.4. Hoeffding's covariance identity is from Hoeffding
(1940); its use here follows Doukhan (1994) §1.2.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

/-! ### Proposition 2.5(ii): the bounded (Billingsley) covariance inequality

Two-σ-algebra statements follow the Mathlib `condExp` binder convention (ambient `mΩ`
as a plain implicit bound after the sub-σ-algebras, before `μ`) — see
`Mixing/Relations.lean`. -/

section TwoAlgebras

variable {Ω : Type*}

/-- Every element of the α description set is dominated by `α` itself: the description set
is bounded above by `1` on a probability space, so `le_csSup` applies. -/
private lemma le_alphaMixCoeff_of_measurableSet {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hA : MeasurableSet[m₁] A)
    (hB : MeasurableSet[m₂] B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ alphaMixCoeff μ m₁ m₂ := by
  refine le_csSup ⟨1, ?_⟩ ⟨A, B, hA, hB, rfl⟩
  rintro r ⟨A', B', -, -, rfl⟩
  have h1 : (μ (A' ∩ B')).toReal ≤ 1 := measureReal_le_one
  have h2 : (μ A').toReal ≤ 1 := measureReal_le_one
  have h3 : (μ B').toReal ≤ 1 := measureReal_le_one
  have h4 : (0:ℝ) ≤ (μ (A' ∩ B')).toReal := ENNReal.toReal_nonneg
  have h5 : (0:ℝ) ≤ (μ A').toReal := ENNReal.toReal_nonneg
  have h6 : (0:ℝ) ≤ (μ B').toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  refine ⟨by nlinarith, by nlinarith⟩

/-- The peeling step behind Billingsley's inequality: if the `m`-set discrepancies of `ψ`
are bounded by `K`, then `ψ` decorrelates from every `m`-measurable `φ` bounded by `C`,
with constant `2 C K`.

Proof: `∫ φ ψ = ∫ φ · E[ψ | m]` (pull-out property), so the left-hand side is
`∫ φ · W` with `W = E[ψ | m] − E ψ`; then `|∫ φ W| ≤ C ∫ |W|` and, splitting `Ω` at the
`m`-measurable sign event of `W`, `∫ |W| = ∫_A W − ∫_{Aᶜ} W ≤ 2 K` by hypothesis. -/
private lemma abs_integral_mul_sub_le_of_setIntegral_bound
    {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {φ ψ : Ω → ℝ} {C K : ℝ}
    (hφ : StronglyMeasurable[m] φ) (hφC : ∀ᵐ ω ∂μ, |φ ω| ≤ C)
    (hψ : Integrable ψ μ)
    (hK : ∀ A : Set Ω, MeasurableSet[m] A →
      |(∫ ω in A, ψ ω ∂μ) - (∫ ω, ψ ω ∂μ) * (μ A).toReal| ≤ K) :
    |(∫ ω, φ ω * ψ ω ∂μ) - (∫ ω, φ ω ∂μ) * ∫ ω, ψ ω ∂μ| ≤ 2 * C * K := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) hφC.exists.choose_spec
  have hφn : ∀ᵐ ω ∂μ, ‖φ ω‖ ≤ C := by simpa [Real.norm_eq_abs] using hφC
  have hφ' : StronglyMeasurable φ := hφ.mono hm
  have hφint : Integrable φ μ :=
    (memLp_top_of_bound hφ'.aestronglyMeasurable C hφn).integrable le_top
  set c : ℝ := ∫ ω, ψ ω ∂μ with hcdef
  set W : Ω → ℝ := fun ω => (μ[ψ|m]) ω - c with hWdef
  have hWm : StronglyMeasurable[m] W := stronglyMeasurable_condExp.sub stronglyMeasurable_const
  have hWint : Integrable W μ := integrable_condExp.sub (integrable_const c)
  have hpull : ∫ ω, φ ω * ψ ω ∂μ = ∫ ω, φ ω * (μ[ψ|m]) ω ∂μ := by
    have h1 : μ[φ * ψ|m] =ᵐ[μ] φ * μ[ψ|m] :=
      condExp_stronglyMeasurable_mul_of_bound hm hφ hψ C hφn
    calc ∫ ω, φ ω * ψ ω ∂μ = ∫ ω, (μ[φ * ψ|m]) ω ∂μ := (integral_condExp hm).symm
      _ = ∫ ω, (φ * μ[ψ|m]) ω ∂μ := integral_congr_ae h1
      _ = ∫ ω, φ ω * (μ[ψ|m]) ω ∂μ := rfl
  have hkey : (∫ ω, φ ω * ψ ω ∂μ) - (∫ ω, φ ω ∂μ) * c = ∫ ω, φ ω * W ω ∂μ := by
    rw [hpull]
    have h : ∀ ω, φ ω * W ω = φ ω * (μ[ψ|m]) ω - φ ω * c := by intro ω; ring
    simp_rw [h]
    rw [integral_sub (integrable_condExp.bdd_mul hφ'.aestronglyMeasurable hφn)
      (hφint.mul_const c), integral_mul_const]
  have hsetW : ∀ A : Set Ω, MeasurableSet[m] A →
      ∫ ω in A, W ω ∂μ = (∫ ω in A, ψ ω ∂μ) - c * (μ A).toReal := by
    intro A hA
    rw [hWdef]
    rw [integral_sub (integrable_condExp.restrict) (integrable_const c),
      setIntegral_condExp hm hψ hA, setIntegral_const, smul_eq_mul, mul_comm]
    rfl
  set A : Set Ω := {ω | 0 ≤ W ω} with hAdef
  have hA : MeasurableSet[m] A := hWm.measurable measurableSet_Ici
  have hsplit : ∫ ω, |W ω| ∂μ = (∫ ω in A, W ω ∂μ) - ∫ ω in Aᶜ, W ω ∂μ := by
    have h1 : ∫ ω in A, |W ω| ∂μ = ∫ ω in A, W ω ∂μ :=
      setIntegral_congr_fun (hm A hA) fun x hx => abs_of_nonneg hx
    have h2 : ∫ ω in Aᶜ, |W ω| ∂μ = -∫ ω in Aᶜ, W ω ∂μ := by
      rw [← integral_neg]
      exact setIntegral_congr_fun (hm A hA).compl fun x hx => abs_of_neg (not_le.mp hx)
    rw [← integral_add_compl (hm A hA) hWint.abs, h1, h2]
    ring
  have hbd1 : |∫ ω in A, W ω ∂μ| ≤ K := by rw [hsetW A hA]; exact hK A hA
  have hbd2 : |∫ ω in Aᶜ, W ω ∂μ| ≤ K := by rw [hsetW _ hA.compl]; exact hK _ hA.compl
  have hW2K : ∫ ω, |W ω| ∂μ ≤ 2 * K := by
    rw [hsplit]
    linarith [(abs_le.mp hbd1).2, (abs_le.mp hbd2).1]
  rw [hkey]
  calc |∫ ω, φ ω * W ω ∂μ| ≤ ∫ ω, |φ ω * W ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, C * |W ω| ∂μ := by
        refine integral_mono_ae ((hWint.bdd_mul hφ'.aestronglyMeasurable hφn).abs)
          (hWint.abs.const_mul C) ?_
        filter_upwards [hφC] with ω hω
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
    _ = C * ∫ ω, |W ω| ∂μ := integral_const_mul _ _
    _ ≤ C * (2 * K) := mul_le_mul_of_nonneg_left hW2K hC
    _ = 2 * C * K := by ring

/-- **FY Proposition 2.5(ii) (Billingsley)**: `m₁`/`m₂`-measurable bounded factors have
covariance at most `4 α C₁ C₂`. -/
theorem abs_covariance_le_of_bounded {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    {C₁ C₂ : ℝ}
    -- USER-INPUT: uniform bounds; FY Prop 2.5(ii)
    (hfC : ∀ᵐ ω ∂μ, |f ω| ≤ C₁) (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C₂) :
    |cov[f, g; μ]| ≤ 4 * alphaMixCoeff μ m₁ m₂ * C₁ * C₂ := by
  set α := alphaMixCoeff μ m₁ m₂ with hα
  have hC₁ : 0 ≤ C₁ := le_trans (abs_nonneg _) hfC.exists.choose_spec
  have hC₂ : 0 ≤ C₂ := le_trans (abs_nonneg _) hgC.exists.choose_spec
  have hfsm : StronglyMeasurable[m₁] f := hf.stronglyMeasurable
  have hgsm : StronglyMeasurable[m₂] g := hg.stronglyMeasurable
  have hfn : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C₁ := by simpa [Real.norm_eq_abs] using hfC
  have hgn : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ C₂ := by simpa [Real.norm_eq_abs] using hgC
  have hfLp : MemLp f 2 μ :=
    (memLp_top_of_bound (hfsm.mono h₁).aestronglyMeasurable C₁ hfn).mono_exponent le_top
  have hgLp : MemLp g 2 μ :=
    (memLp_top_of_bound (hgsm.mono h₂).aestronglyMeasurable C₂ hgn).mono_exponent le_top
  have hfint : Integrable f μ := hfLp.integrable one_le_two
  -- Step A: peel `f` against an arbitrary `m₂`-event; the discrepancies are the α set.
  have hstepA : ∀ B : Set Ω, MeasurableSet[m₂] B →
      |(∫ ω in B, f ω ∂μ) - (∫ ω, f ω ∂μ) * (μ B).toReal| ≤ 2 * C₁ * α := by
    intro B hB
    have hBΩ : MeasurableSet B := h₂ B hB
    have hind : Integrable (B.indicator (1 : Ω → ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator hBΩ
    have h := abs_integral_mul_sub_le_of_setIntegral_bound (m := m₁) (mΩ := mΩ) h₁
      hfsm hfC hind (K := α) ?_
    · have e1 : ∫ ω, f ω * B.indicator (1 : Ω → ℝ) ω ∂μ = ∫ ω in B, f ω ∂μ := by
        rw [← integral_indicator hBΩ]
        congr 1 with ω
        by_cases hω : ω ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
      have e2 : ∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ = (μ B).toReal := by
        rw [integral_indicator hBΩ]
        simp [measureReal_def]
      rw [e1, e2] at h
      exact h
    · intro A hA
      have e3 : ∫ ω in A, B.indicator (1 : Ω → ℝ) ω ∂μ = (μ (A ∩ B)).toReal := by
        rw [setIntegral_indicator hBΩ]
        simp [measureReal_def]
      have e4 : ∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ = (μ B).toReal := by
        rw [integral_indicator hBΩ]
        simp [measureReal_def]
      rw [e3, e4, mul_comm ((μ B).toReal) ((μ A).toReal)]
      exact le_alphaMixCoeff_of_measurableSet (mΩ := mΩ) (μ := μ) hA hB
  -- Step B: peel `g` against `f`, feeding Step A as the discrepancy bound.
  have hstepB := abs_integral_mul_sub_le_of_setIntegral_bound (m := m₂) (mΩ := mΩ) h₂
    hgsm hgC hfint (K := 2 * C₁ * α) hstepA
  rw [covariance_eq_sub hfLp hgLp]
  have e5 : ∫ ω, g ω * f ω ∂μ = ∫ ω, f ω * g ω ∂μ := by simp_rw [mul_comm]
  rw [e5] at hstepB
  have e6 : (∫ ω, f ω * g ω ∂μ) - (∫ ω, g ω ∂μ) * ∫ ω, f ω ∂μ
      = μ[f * g] - μ[f] * μ[g] := by
    simp only [Pi.mul_apply]
    ring
  rw [e6] at hstepB
  calc |μ[f * g] - μ[f] * μ[g]| ≤ 2 * C₂ * (2 * C₁ * α) := hstepB
    _ = 4 * α * C₁ * C₂ := by ring

/-- Billingsley's inequality in the `E[fg] − Ef·Eg` form (the shape the complex and
Volkonskii–Rozanov arguments consume). -/
private lemma abs_integral_mul_sub_mul_le_of_bounded {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g) {C₁ C₂ : ℝ}
    (hfC : ∀ᵐ ω ∂μ, |f ω| ≤ C₁) (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C₂) :
    |(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ|
      ≤ 4 * alphaMixCoeff μ m₁ m₂ * C₁ * C₂ := by
  have hfn : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C₁ := by simpa [Real.norm_eq_abs] using hfC
  have hgn : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ C₂ := by simpa [Real.norm_eq_abs] using hgC
  have hfLp : MemLp f 2 μ :=
    (memLp_top_of_bound ((hf.stronglyMeasurable.mono h₁)).aestronglyMeasurable C₁ hfn).mono_exponent
      le_top
  have hgLp : MemLp g 2 μ :=
    (memLp_top_of_bound ((hg.stronglyMeasurable.mono h₂)).aestronglyMeasurable C₂ hgn).mono_exponent
      le_top
  have h := abs_covariance_le_of_bounded h₁ h₂ hf hg hfC hgC
  rwa [covariance_eq_sub hfLp hgLp] at h

private lemma abs_comb_le {x y z w K : ℝ} (hx : |x| ≤ K) (hy : |y| ≤ K) (hz : |z| ≤ K)
    (hw : |w| ≤ K) : |x - y| + |z + w| ≤ 4 * K := by
  have h1 : |x - y| ≤ |x| + |y| := by
    have h := abs_add_le x (-y)
    rwa [abs_neg, ← sub_eq_add_neg] at h
  have h2 : |z + w| ≤ |z| + |w| := abs_add_le z w
  linarith

/-- **Complex Billingsley** (FY §2.6.2, constant 16): unit-modulus-bounded complex
factors. Stated with the real-bilinear covariance
`E[f·g] − E[f]·E[g]` in `ℂ`. -/
theorem norm_covariance_le_of_bounded_complex {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℂ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    {C₁ C₂ : ℝ}
    -- USER-INPUT: uniform bounds; FY §2.6.2 complex remark
    (hfC : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C₁) (hgC : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ C₂) :
    ‖(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ‖
      ≤ 16 * alphaMixCoeff μ m₁ m₂ * C₁ * C₂ := by
  have hre : Measurable (Complex.re) := Complex.continuous_re.measurable
  have him : Measurable (Complex.im) := Complex.continuous_im.measurable
  have hf₁ : Measurable[m₁] fun ω => (f ω).re := hre.comp hf
  have hf₂ : Measurable[m₁] fun ω => (f ω).im := him.comp hf
  have hg₁ : Measurable[m₂] fun ω => (g ω).re := hre.comp hg
  have hg₂ : Measurable[m₂] fun ω => (g ω).im := him.comp hg
  have hf₁C : ∀ᵐ ω ∂μ, |(f ω).re| ≤ C₁ := by
    filter_upwards [hfC] with ω hω using (Complex.abs_re_le_norm _).trans hω
  have hf₂C : ∀ᵐ ω ∂μ, |(f ω).im| ≤ C₁ := by
    filter_upwards [hfC] with ω hω using (Complex.abs_im_le_norm _).trans hω
  have hg₁C : ∀ᵐ ω ∂μ, |(g ω).re| ≤ C₂ := by
    filter_upwards [hgC] with ω hω using (Complex.abs_re_le_norm _).trans hω
  have hg₂C : ∀ᵐ ω ∂μ, |(g ω).im| ≤ C₂ := by
    filter_upwards [hgC] with ω hω using (Complex.abs_im_le_norm _).trans hω
  -- integrability
  have hfsm : StronglyMeasurable f := (hf.mono h₁ le_rfl).stronglyMeasurable
  have hf₁' : StronglyMeasurable fun ω => (f ω).re := (hf₁.mono h₁ le_rfl).stronglyMeasurable
  have hf₂' : StronglyMeasurable fun ω => (f ω).im := (hf₂.mono h₁ le_rfl).stronglyMeasurable
  have hg₁' : StronglyMeasurable fun ω => (g ω).re := (hg₁.mono h₂ le_rfl).stronglyMeasurable
  have hg₂' : StronglyMeasurable fun ω => (g ω).im := (hg₂.mono h₂ le_rfl).stronglyMeasurable
  have hgsm : StronglyMeasurable g := (hg.mono h₂ le_rfl).stronglyMeasurable
  have hfint : Integrable f μ :=
    (memLp_top_of_bound hfsm.aestronglyMeasurable C₁ hfC).integrable le_top
  have hgint : Integrable g μ :=
    (memLp_top_of_bound hgsm.aestronglyMeasurable C₂ hgC).integrable le_top
  have hfgint : Integrable (fun ω => f ω * g ω) μ :=
    hgint.bdd_mul hfsm.aestronglyMeasurable hfC
  have hcre : ∀ {F : Ω → ℂ}, Integrable F μ → (∫ ω, F ω ∂μ).re = ∫ ω, (F ω).re ∂μ := by
    intro F hF
    simpa using (integral_re hF).symm
  have hcim : ∀ {F : Ω → ℂ}, Integrable F μ → (∫ ω, F ω ∂μ).im = ∫ ω, (F ω).im ∂μ := by
    intro F hF
    simpa using (integral_im hF).symm
  have hint₁ : Integrable (fun ω => (f ω).re) μ :=
    (memLp_top_of_bound (hf₁').aestronglyMeasurable C₁
      (by simpa [Real.norm_eq_abs] using hf₁C)).integrable le_top
  have hint₂ : Integrable (fun ω => (f ω).im) μ :=
    (memLp_top_of_bound (hf₂').aestronglyMeasurable C₁
      (by simpa [Real.norm_eq_abs] using hf₂C)).integrable le_top
  have hint₃ : Integrable (fun ω => (g ω).re) μ :=
    (memLp_top_of_bound (hg₁').aestronglyMeasurable C₂
      (by simpa [Real.norm_eq_abs] using hg₁C)).integrable le_top
  have hint₄ : Integrable (fun ω => (g ω).im) μ :=
    (memLp_top_of_bound (hg₂').aestronglyMeasurable C₂
      (by simpa [Real.norm_eq_abs] using hg₂C)).integrable le_top
  have hprod : ∀ {u v : Ω → ℝ} {D : ℝ}, StronglyMeasurable u → Integrable v μ →
      (∀ᵐ ω ∂μ, |u ω| ≤ D) → Integrable (fun ω => u ω * v ω) μ := by
    intro u v D hu hv hb
    exact hv.bdd_mul hu.aestronglyMeasurable (by simpa [Real.norm_eq_abs] using hb)
  have e11 : Integrable (fun ω => (f ω).re * (g ω).re) μ := hprod hf₁' hint₃ hf₁C
  have e22 : Integrable (fun ω => (f ω).im * (g ω).im) μ := hprod hf₂' hint₄ hf₂C
  have e12 : Integrable (fun ω => (f ω).re * (g ω).im) μ := hprod hf₁' hint₄ hf₁C
  have e21 : Integrable (fun ω => (f ω).im * (g ω).re) μ := hprod hf₂' hint₃ hf₂C
  -- real and imaginary parts of the complex covariance
  have hRe : ((∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ).re
      = ((∫ ω, (f ω).re * (g ω).re ∂μ) - (∫ ω, (f ω).re ∂μ) * ∫ ω, (g ω).re ∂μ)
        - ((∫ ω, (f ω).im * (g ω).im ∂μ) - (∫ ω, (f ω).im ∂μ) * ∫ ω, (g ω).im ∂μ) := by
    rw [Complex.sub_re, Complex.mul_re, hcre hfgint, hcre hfint, hcre hgint, hcim hfint,
      hcim hgint]
    have : ∀ ω, (f ω * g ω).re = (f ω).re * (g ω).re - (f ω).im * (g ω).im := by
      intro ω; rw [Complex.mul_re]
    simp_rw [this]
    rw [integral_sub e11 e22]
    ring
  have hIm : ((∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ).im
      = ((∫ ω, (f ω).re * (g ω).im ∂μ) - (∫ ω, (f ω).re ∂μ) * ∫ ω, (g ω).im ∂μ)
        + ((∫ ω, (f ω).im * (g ω).re ∂μ) - (∫ ω, (f ω).im ∂μ) * ∫ ω, (g ω).re ∂μ) := by
    rw [Complex.sub_im, Complex.mul_im, hcim hfgint, hcre hfint, hcre hgint, hcim hfint,
      hcim hgint]
    have : ∀ ω, (f ω * g ω).im = (f ω).re * (g ω).im + (f ω).im * (g ω).re := by
      intro ω; rw [Complex.mul_im]
    simp_rw [this]
    rw [integral_add e12 e21]
    ring
  have b11 := abs_integral_mul_sub_mul_le_of_bounded (mΩ := mΩ) h₁ h₂ hf₁ hg₁ hf₁C hg₁C
  have b22 := abs_integral_mul_sub_mul_le_of_bounded (mΩ := mΩ) h₁ h₂ hf₂ hg₂ hf₂C hg₂C
  have b12 := abs_integral_mul_sub_mul_le_of_bounded (mΩ := mΩ) h₁ h₂ hf₁ hg₂ hf₁C hg₂C
  have b21 := abs_integral_mul_sub_mul_le_of_bounded (mΩ := mΩ) h₁ h₂ hf₂ hg₁ hf₂C hg₁C
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [hRe, hIm]
  refine (abs_comb_le b11 b22 b12 b21).trans ?_
  ring_nf
  rfl


/-! ### Proposition 2.5(i): the Davydov covariance inequality -/

/-- **FY Proposition 2.5(i) (Davydov)**: for `p, q > 1` with `1/p + 1/q < 1`,
`|Cov(f, g)| ≤ 8 α^{1 − 1/p − 1/q} ‖f‖_p ‖g‖_q`. Built in full (truncation against the
bounded case; FY cites Doukhan §1.2.2). -/
theorem abs_covariance_le_davydov {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    {p q : ℝ}
    -- USER-INPUT: integrability exponents; FY Prop 2.5(i)
    (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q < 1)
    (hfLp : MemLp f (ENNReal.ofReal p) μ) (hgLq : MemLp g (ENNReal.ofReal q) μ) :
    |cov[f, g; μ]|
      ≤ 8 * alphaMixCoeff μ m₁ m₂ ^ (1 - 1 / p - 1 / q)
        * (eLpNorm f (ENNReal.ofReal p) μ).toReal
        * (eLpNorm g (ENNReal.ofReal q) μ).toReal := by
  sorry

/-! ### Proposition 2.6: the Volkonskii–Rozanov factorization -/

/-- **FY Proposition 2.6 (Volkonskii–Rozanov)**: complex unit-bounded blocks measured
against an increasing family with α-gaps at most `a` factorize up to `16 (k − 1) a`.
The gap hypothesis is abstract: the α-coefficient between the cumulative past
`⨆_{j ≤ l} m j` and the next block `m (l+1)` is at most `a` — process-level
applications supply it via `IsStrictlyStationary.alphaMixCoeff_shift` and
monotonicity. -/
theorem norm_integral_prod_sub_prod_integral_le {k : ℕ}
    {m : Fin k → MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hle : ∀ l, m l ≤ mΩ)
    (ξ : Fin k → Ω → ℂ) (hmeas : ∀ l, Measurable[m l] (ξ l))
    -- USER-INPUT: unit modulus bound; FY Prop 2.6
    (hbdd : ∀ l, ∀ᵐ ω ∂μ, ‖ξ l ω‖ ≤ 1)
    {a : ℝ}
    -- USER-INPUT: α-gap bound between cumulative past and next block; FY Prop 2.6
    (hgap : ∀ l : Fin k, ∀ hl : (l : ℕ) + 1 < k,
      alphaMixCoeff μ (⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ l, m j) (m ⟨(l : ℕ) + 1, hl⟩) ≤ a) :
    ‖(∫ ω, ∏ l, ξ l ω ∂μ) - ∏ l, ∫ ω, ξ l ω ∂μ‖
      ≤ 16 * ((k : ℝ) - 1) * a := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- **FALSE CORNER OF THE FROZEN STATEMENT.** For `k = 0` every hypothesis is vacuous
    -- (`Fin 0` is empty), the left-hand side is exactly `‖1 − 1‖ = 0` (empty products,
    -- `∫ 1 = 1`), and the right-hand side is `16 · (0 − 1) · a = −16 a`, which is
    -- negative for every `a > 0`. So the claim `0 ≤ −16 a` is refutable; the statement
    -- is true exactly for `k ≥ 1`, which is what the branch below proves in full.
    -- Reported, not repaired: the statement is frozen.
    subst hk0
    sorry
  · classical
    have hbdd' : ∀ᵐ ω ∂μ, ∀ l, ‖ξ l ω‖ ≤ 1 := ae_all_iff.mpr hbdd
    set S : ℕ → Finset (Fin k) := fun n => Finset.univ.filter (fun j : Fin k => (j : ℕ) < n)
      with hSdef
    -- the cumulative product is bounded by 1
    have hPbdd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖∏ j ∈ S n, ξ j ω‖ ≤ 1 := by
      intro n
      filter_upwards [hbdd'] with ω hω
      rw [norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hω i)
    have hint : ∀ l : Fin k, ‖∫ ω, ξ l ω ∂μ‖ ≤ 1 := by
      intro l
      have h := norm_integral_le_of_norm_le_const (μ := μ) (hbdd l)
      simpa using h
    have main : ∀ n : ℕ, 1 ≤ n → n ≤ k →
        ‖(∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) - ∏ j ∈ S n, ∫ ω, ξ j ω ∂μ‖ ≤ 16 * ((n : ℝ) - 1) * a := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base =>
        intro _
        have h1 : S 1 = ({⟨0, hk⟩} : Finset (Fin k)) := by
          ext j
          simp [hSdef, Fin.ext_iff]
        rw [h1]
        simp
      | succ n hn ih =>
        intro hnk
        have hnk' : n < k := by omega
        have ihb := ih (by omega)
        set l : Fin k := ⟨n - 1, by omega⟩ with hl
        set l' : Fin k := ⟨n, hnk'⟩ with hl'
        have hln : (l : ℕ) + 1 = n := by simp [hl]; omega
        have hMle : (⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (l : ℕ), m j) ≤ mΩ :=
          iSup_le fun j => iSup_le fun _ => hle j
        have hmem : ∀ j ∈ S n, m j ≤ ⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (l : ℕ), m j := by
          intro j hj
          simp only [hSdef, Finset.mem_filter] at hj
          exact le_iSup₂ (f := fun (j : Fin k) (_ : (j : ℕ) ≤ (l : ℕ)) => m j) j (by omega)
        have hPmeas : Measurable[⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (l : ℕ), m j]
            (fun ω => ∏ j ∈ S n, ξ j ω) :=
          Finset.measurable_prod _ fun j hj => (hmeas j).mono (hmem j hj) le_rfl
        -- the α-gap bound transported to the cumulative past and the next block
        have hα : alphaMixCoeff μ (⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (l : ℕ), m j) (m l') ≤ a := by
          have h := hgap l (by omega)
          have he : (⟨(l : ℕ) + 1, by omega⟩ : Fin k) = l' := by
            apply Fin.ext; simp [hl', hln]
          rw [he] at h
          exact h
        have hcov := norm_covariance_le_of_bounded_complex
          (m₁ := ⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (l : ℕ), m j) (m₂ := m l') (mΩ := mΩ)
          hMle (hle l') hPmeas (hmeas l') (hPbdd n) (hbdd l')
        -- the recursion
        have hnot : (l' : Fin k) ∉ S n := by simp [hSdef, hl']
        have hins : S (n + 1) = insert l' (S n) := by
          ext j
          simp [hSdef, hl', Fin.ext_iff]
          omega
        have hP1 : ∀ ω, ∏ j ∈ S (n + 1), ξ j ω = (∏ j ∈ S n, ξ j ω) * ξ l' ω := by
          intro ω
          rw [hins, Finset.prod_insert hnot, mul_comm]
        have hP2 : ∏ j ∈ S (n + 1), (∫ ω, ξ j ω ∂μ)
            = (∏ j ∈ S n, ∫ ω, ξ j ω ∂μ) * ∫ ω, ξ l' ω ∂μ := by
          rw [hins, Finset.prod_insert hnot, mul_comm]
        have hexp : (∫ ω, ∏ j ∈ S (n + 1), ξ j ω ∂μ) - ∏ j ∈ S (n + 1), ∫ ω, ξ j ω ∂μ
            = ((∫ ω, (∏ j ∈ S n, ξ j ω) * ξ l' ω ∂μ)
                - (∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) * ∫ ω, ξ l' ω ∂μ)
              + ((∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) - ∏ j ∈ S n, ∫ ω, ξ j ω ∂μ)
                * (∫ ω, ξ l' ω ∂μ) := by
          simp_rw [hP1]
          rw [hP2]
          ring
        rw [hexp]
        refine (norm_add_le _ _).trans ?_
        have hb1 : ‖(∫ ω, (∏ j ∈ S n, ξ j ω) * ξ l' ω ∂μ)
            - (∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) * ∫ ω, ξ l' ω ∂μ‖ ≤ 16 * a := by
          refine hcov.trans ?_
          nlinarith [hα]
        have hb2 : ‖((∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) - ∏ j ∈ S n, ∫ ω, ξ j ω ∂μ)
            * (∫ ω, ξ l' ω ∂μ)‖ ≤ 16 * ((n : ℝ) - 1) * a := by
          rw [norm_mul]
          calc ‖(∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) - ∏ j ∈ S n, ∫ ω, ξ j ω ∂μ‖ * ‖∫ ω, ξ l' ω ∂μ‖
              ≤ (16 * ((n : ℝ) - 1) * a) * 1 := by
                refine mul_le_mul ihb (hint l') (norm_nonneg _) ?_
                exact le_trans (norm_nonneg _) ihb
            _ = 16 * ((n : ℝ) - 1) * a := by ring
        have : (16 : ℝ) * (((n : ℝ) + 1) - 1) * a = 16 * a + 16 * ((n : ℝ) - 1) * a := by ring
        push_cast
        rw [this]
        linarith
    have hSk : S k = Finset.univ := by
      ext j
      simp [hSdef]
    have := main k hk le_rfl
    rwa [hSk] at this


end TwoAlgebras

/-! ### The fourth-moment bound (FY Proposition 2.7(ii) at `q = 4`) -/

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **FY Proposition 2.7(ii), `q = 4` instance** (the one the Bernstein-block CLT
consumes): a bounded zero-mean strictly stationary α-mixing process with
`α(n) ≤ K n⁻²` has `E S_n⁴ ≤ C n²`. -/
theorem moment4_partial_sum_le [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    {C : ℝ}
    -- USER-INPUT: uniform bound; FY Prop 2.7(ii)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    -- USER-INPUT: zero mean; FY Prop 2.7
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {K : ℝ}
    -- USER-INPUT: α-decay of order n⁻²; FY Prop 2.7(ii) with q = 4
    (hα : ∀ n : ℕ, 1 ≤ n → alphaCoeff X μ n ≤ K / (n : ℝ) ^ 2) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ n : ℕ,
      ∫ ω, (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) ^ 4 ∂μ ≤ C' * (n : ℝ) ^ 2 := by
  sorry

/-! ### Theorems 2.18/2.19: Bosq exponential inequalities (literature DEBTS) -/

/-- **DEBT (Bosq 1998 Thm 1.3; FY Theorem 2.18)**: bounded zero-mean strictly
stationary process; for every `ε > 0` and integer `1 ≤ qb ≤ n/2`,
`P(|S_n/n| > ε) ≤ 4 exp(−ε² qb/(8 b²)) + 22 (1 + 4b/ε)^{1/2} qb α([n/(2 qb)])`.
Used only by ch. 5 KDE uniform rates (outside current scope). -/
theorem bosq_exponential_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    {b : ℝ} (hb : 0 < b)
    -- USER-INPUT: uniform bound; FY Thm 2.18
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ b)
    -- USER-INPUT: zero mean; FY Thm 2.18
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {ε : ℝ} (hε : 0 < ε) {n qb : ℕ} (hq1 : 1 ≤ qb) (hqn : 2 * qb ≤ n) :
    (μ {ω | ε < |(n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω|}).toReal
      ≤ 4 * Real.exp (-(ε ^ 2 * qb) / (8 * b ^ 2))
        + 22 * (1 + 4 * b / ε) ^ ((1 : ℝ) / 2) * qb * alphaCoeff X μ (n / (2 * qb)) := by
  sorry

/-- **DEBT (Bosq 1998 Thm 1.4; FY Theorem 2.19, eq. (2.62))**: under Cramér's condition
`E|X_t|^k ≤ C^{k−2} k! E X_t²` (all `k ≥ 3`), for any `n ≥ 2`, `k ≥ 3`,
`1 ≤ qb ≤ n/2` and `ε > 0`, with `μ(ε) = ε²/(25 E X_t² + 5Cε)`:
`P(|S_n| > nε) ≤ 2(1 + n/qb + μ(ε)) e^{−qb·μ(ε)}
  + 11 n (1 + 5 ε⁻¹ (E|X_t|^k)^{1/(2k+1)}) α([n/(qb+1)])^{2k/(2k+1)}`.
(The book prints `E X_t^k` in the second factor; we state the weaker bound with
`E|X_t|^k ≥ E X_t^k`, which the cited result implies.) -/
theorem bosq_cramer_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    {C : ℝ} (hC : 0 < C)
    -- USER-INPUT: zero mean; FY Thm 2.19
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hL2 : MemLp (X 0) 2 μ)
    -- USER-INPUT: Cramér's condition (2.62); FY Thm 2.19
    (hcram : ∀ k : ℕ, 3 ≤ k →
      ∫ ω, |X 0 ω| ^ k ∂μ ≤ C ^ (k - 2) * (Nat.factorial k : ℝ) * ∫ ω, X 0 ω ^ 2 ∂μ)
    {ε : ℝ} (hε : 0 < ε) {n k qb : ℕ} (hn : 2 ≤ n) (hk : 3 ≤ k)
    (hq1 : 1 ≤ qb) (hqn : 2 * qb ≤ n) :
    (μ {ω | ε < |(n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω|}).toReal
      ≤ 2 * (1 + (n : ℝ) / qb + ε ^ 2 / (25 * ∫ ω, X 0 ω ^ 2 ∂μ + 5 * C * ε))
          * Real.exp (-(qb : ℝ) * (ε ^ 2 / (25 * ∫ ω, X 0 ω ^ 2 ∂μ + 5 * C * ε)))
        + 11 * n * (1 + 5 * ε⁻¹ * (∫ ω, |X 0 ω| ^ k ∂μ) ^ ((1 : ℝ) / (2 * k + 1)))
          * alphaCoeff X μ (n / (qb + 1)) ^ ((2 * k : ℝ) / (2 * k + 1)) := by
  sorry

end Process

end StatLean.TimeSeries
