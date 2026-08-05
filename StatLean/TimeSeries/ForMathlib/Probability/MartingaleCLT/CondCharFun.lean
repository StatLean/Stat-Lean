import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.Defs
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Conditional characteristic-function calculus for MDS arrays

The analytic bricks of the Brown/Hall–Heyde martingale CLT
(`MartingaleCLT/BrownCLT.lean` assembles them):

* the **conditional Taylor estimate**: a.e.,
  `‖E[e^{iuX} | 𝓖] − (1 − u²/2 · E[X² | 𝓖])‖` is controlled by the conditional
  Lindeberg mass at any level `ε` plus `|u|³ ε · E[X² | 𝓖]`;
* the **tower telescope**: for an MDS row, the gap between `E[e^{iuS_n}]` and
  `E[∏_i (1 − u²/2 · E[X_i²|𝓕_i])]` is at most the summed conditional Taylor errors
  (peel factors from the right by the tower property; the martingale-difference
  property kills the linear terms);
* the **product comparison**: on the event where the conditional variance process is
  close to `σ²` and the summands are uniformly small,
  `∏_i (1 − u²/2 · E[X_i²|𝓕_i])` is close to `e^{−u²σ²/2}`.

**Reference.** Hall & Heyde (1980), §3.2 (proof of Thm 3.2), after Brown (1971) §3.
(`Hall–Heyde §3.2` in tags.)

**Proof formalization notes.**
* Conditional expectations of complex-valued integrands are taken componentwise
  (`Complex.re/im` through Mathlib's real `condExp`); the statements below pre-split
  them so the closure sessions never need a ℂ-valued `condExp` API.
* All statements are a.e. inequalities between real quantities — no conditional
  independence is ever invoked (that is the point of the martingale method).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

section CondTaylor

variable {Ω : Type*}

open Complex in
/-- **Uniform third-order remainder bound for `e^{iy}`** — the pointwise input to the
conditional Taylor estimate: `‖exp (I y) − (1 + I y − y²/2)‖ ≤ min (|y|³/6) (y²)`.
Both halves are elementary: the cubic one by integrating the exponential's remainder
three times, the quadratic one from `‖exp (I y) − 1 − I y‖ ≤ y²/2` and the triangle
inequality (Mathlib only provides the non-uniform `taylor_charFun_two`). -/
private lemma norm_cexp_sub_taylor_le (y : ℝ) :
    ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2)‖ ≤ min (|y| ^ 3 / 6) (y ^ 2) := by
  have he : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w))
      (Complex.exp (I * ↑u) * I) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using (h1.cexp).comp_ofReal
  have hnorme : ∀ u : ℝ, ‖Complex.exp (I * ↑u)‖ = 1 := by
    intro u; rw [Complex.norm_exp]; simp
  have hIu : ∀ u : ℝ, HasDerivAt (fun w : ℝ => I * ↑w) I u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using h1.comp_ofReal
  have hcontI : Continuous (fun u : ℝ => Complex.exp (I * ↑u) * I) := by fun_prop
  have hcont1 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1) * I) := by fun_prop
  have hcont2 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1 - I * ↑u) * I) := by fun_prop
  have hL0 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1‖ ≤ z := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I) = Complex.exp (I * ↑z) - 1 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => he u)
        (hcontI.intervalIntegrable 0 z)]
      simp
    rw [← hInt]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := z)
      (C := 1) (f := fun u => Complex.exp (I * ↑u) * I)
      (fun u _ => by rw [norm_mul, Complex.norm_I, mul_one]; exact le_of_eq (hnorme u))
    calc ‖∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I‖ ≤ 1 * |z - 0| := hbnd
      _ = z := by rw [sub_zero, abs_of_nonneg hz, one_mul]
  have hd1 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w)
      ((Complex.exp (I * ↑u) - 1) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1) * I = Complex.exp (I * ↑u) * I - 0 - I := by ring
    rw [heq]
    exact ((he u).sub (hasDerivAt_const u (1 : ℂ))).sub (hIu u)
  have hL1 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ z ^ 2 / 2 := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1) * I)
        = Complex.exp (I * ↑z) - 1 - I * ↑z := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd1 u)
        (hcont1.intervalIntegrable 0 z)]
      simp
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ ∫ u in (0:ℝ)..z, u := by
      rw [← hInt]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        (continuous_id.intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL0 u hu.1.le
    rw [integral_id] at hb
    simpa using hb
  have hsq : ∀ u : ℝ, HasDerivAt (fun w : ℝ => (↑w * ↑w / 2 : ℂ)) (↑u : ℂ) u := by
    intro u
    have hof : HasDerivAt (fun w : ℝ => (↑w : ℂ)) 1 u := by
      simpa using (hasDerivAt_id (↑u : ℂ)).comp_ofReal
    have heq : (↑u : ℂ) = (1 * ↑u + ↑u * 1) / 2 := by ring
    rw [heq]
    exact (hof.mul hof).div_const 2
  have hd2 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w + ↑w * ↑w / 2)
      ((Complex.exp (I * ↑u) - 1 - I * ↑u) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1 - I * ↑u) * I
        = (Complex.exp (I * ↑u) - 1) * I + ↑u := by
      have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
      linear_combination (-(↑u : ℂ)) * hI2
    rw [heq]
    exact (hd1 u).add (hsq u)
  have hA2z : ∀ z : ℝ, (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1 - I * ↑u) * I)
      = Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2 := by
    intro z
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd2 u)
      (hcont2.intervalIntegrable 0 z)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  have key : ∀ z : ℝ, 0 ≤ z →
      ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖ ≤ min (z ^ 3 / 6) (z ^ 2) := by
    intro z hz
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖
        ≤ ∫ u in (0:ℝ)..z, u ^ 2 / 2 := by
      rw [← hA2z z]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 / 2)).intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL1 u hu.1.le
    have hintval : (∫ u in (0:ℝ)..z, u ^ 2 / 2) = z ^ 3 / 6 := by
      rw [intervalIntegral.integral_div, integral_pow]; push_cast; ring
    refine le_min (hb.trans (le_of_eq hintval)) ?_
    have h1 := hL1 z hz
    have hcast : (↑z * ↑z / 2 : ℂ) = ((z * z / 2 : ℝ) : ℂ) := by push_cast; ring
    have hz2 : ‖(↑z * ↑z / 2 : ℂ)‖ = z ^ 2 / 2 := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    have hsplit : Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2
        = (Complex.exp (I * ↑z) - 1 - I * ↑z) + ↑z * ↑z / 2 := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [hz2]; linarith
  have hEq : Complex.exp (I * ↑y) - (1 + I * ↑y - (↑y : ℂ) ^ 2 / 2)
      = Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2 := by ring
  rw [hEq]
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact key y hy
  · have hz : (0:ℝ) ≤ -y := by linarith
    have hexp : (starRingEnd ℂ) (Complex.exp (I * ↑y)) = Complex.exp (I * ↑(-y)) := by
      rw [← Complex.exp_conj]; congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
    have hconj : (starRingEnd ℂ) (Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2)
        = Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2 := by
      simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
        Complex.conj_ofReal, hexp, Complex.ofReal_neg]
      ring
    have hnn : ‖Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2‖
        = ‖Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2‖ := by
      rw [← hconj, Complex.norm_conj]
    rw [hnn, abs_of_neg hy, show (y : ℝ) ^ 2 = (-y) ^ 2 from by ring]
    exact key (-y) hz

/-- **Conditional Taylor estimate** (Hall–Heyde Lemma 3.1-adjacent): for a
square-integrable `X` with `E[X | 𝓖] = 0` and any `ε > 0`, a.e.
`‖(E[cos uX | 𝓖] + i E[sin uX | 𝓖]) − (1 − u²/2 E[X²|𝓖])‖
  ≤ u² E[X² 1_{|X| ≥ ε} | 𝓖] + |u|³ ε E[X² | 𝓖]`.

Binder convention: ambient `mΩ` is a plain implicit bound after `m` and before `μ`
(see `Mixing/Relations.lean`). -/
theorem norm_condexp_exp_sub_one_sub_le {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable X) (hL2 : MemLp X 2 μ)
    (hcond : μ[X | m] =ᵐ[μ] 0) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ,
      ‖(⟨μ[fun ω' => Real.cos (u * X ω') | m] ω,
          μ[fun ω' => Real.sin (u * X ω') | m] ω⟩ : ℂ)
          - (1 - u ^ 2 / 2 * μ[fun ω' => X ω' ^ 2 | m] ω)‖
        ≤ u ^ 2 * μ[fun ω' => X ω' ^ 2 * Set.indicator {x : Ω | ε ≤ |X x|}
              (fun _ => (1 : ℝ)) ω' | m] ω
          + |u| ^ 3 * ε * μ[fun ω' => X ω' ^ 2 | m] ω := by
  classical
  have hXint : Integrable X μ := hL2.integrable one_le_two
  have hX2 : Integrable (fun ω => X ω ^ 2) μ := hL2.integrable_sq
  have hXabs : Measurable fun x => |X x| := continuous_abs.measurable.comp hX
  set S : Set Ω := {x : Ω | ε ≤ |X x|} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const hXabs
  have hindeq : (fun ω => X ω ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω)
      = S.indicator (fun ω => X ω ^ 2) := by
    funext ω
    by_cases h : ω ∈ S <;> simp [h]
  have hind : Integrable (fun ω => X ω ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω) μ := by
    rw [hindeq]; exact hX2.indicator hSm
  have hofX : Measurable fun ω => ((u * X ω : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_const.mul hX)
  -- the exponential, its Taylor polynomial, and the error
  set Z : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((u * X ω : ℝ) : ℂ)) with hZdef
  set P : Ω → ℂ := fun ω => 1 + Complex.I * ((u * X ω : ℝ) : ℂ)
      - ((u * X ω : ℝ) : ℂ) ^ 2 / 2 with hPdef
  set W : Ω → ℂ := fun ω => Z ω - P ω with hWdef
  set g : Ω → ℝ := fun ω => u ^ 2 * (X ω ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω)
      + |u| ^ 3 * ε * X ω ^ 2 with hgdef
  have hgint : Integrable g μ := (hind.const_mul _).add (hX2.const_mul _)
  -- (i) the pointwise Taylor estimate, split at the level `ε`
  have hWbound : ∀ ω, ‖W ω‖ ≤ g ω := by
    intro ω
    have h : ‖W ω‖ ≤ min (|u * X ω| ^ 3 / 6) ((u * X ω) ^ 2) :=
      norm_cexp_sub_taylor_le (u * X ω)
    by_cases hcase : ω ∈ S
    · have hi : S.indicator (fun _ => (1 : ℝ)) ω = 1 := Set.indicator_of_mem hcase 1
      have h2 : ‖W ω‖ ≤ (u * X ω) ^ 2 := h.trans (min_le_right _ _)
      have hnn : 0 ≤ |u| ^ 3 * ε * X ω ^ 2 := by positivity
      simp only [hgdef, hi, mul_one]
      nlinarith [h2]
    · have hi : S.indicator (fun _ => (1 : ℝ)) ω = 0 := Set.indicator_of_notMem hcase _
      have hlt : |X ω| < ε := by
        simpa [hSdef, Set.mem_setOf_eq, not_le] using hcase
      have h2 : ‖W ω‖ ≤ |u * X ω| ^ 3 / 6 := h.trans (min_le_left _ _)
      have habs : |u * X ω| ^ 3 = |u| ^ 3 * (|X ω| * X ω ^ 2) := by
        rw [abs_mul, mul_pow, show |X ω| ^ 3 = |X ω| * |X ω| ^ 2 by ring, sq_abs]
      have hu3 : (0 : ℝ) ≤ |u| ^ 3 := by positivity
      have hcube : |X ω| * X ω ^ 2 ≤ ε * X ω ^ 2 :=
        mul_le_mul_of_nonneg_right hlt.le (sq_nonneg _)
      have step1 : |u| ^ 3 * (|X ω| * X ω ^ 2) ≤ |u| ^ 3 * (ε * X ω ^ 2) :=
        mul_le_mul_of_nonneg_left hcube hu3
      have step2 : (0 : ℝ) ≤ |u| ^ 3 * (ε * X ω ^ 2) := by positivity
      have step3 : |u| ^ 3 * ε * X ω ^ 2 = |u| ^ 3 * (ε * X ω ^ 2) := by ring
      simp only [hgdef, hi, mul_zero, zero_add]
      rw [habs] at h2
      linarith
  -- (ii) integrability
  have hZint : Integrable Z μ := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun ω => ?_)
    · exact ((Complex.measurable_exp.comp (measurable_const.mul hofX))).aestronglyMeasurable
    · simp [hZdef, Complex.norm_exp]
  have hofXint : Integrable (fun ω => ((X ω : ℝ) : ℂ)) μ := by
    simpa using Complex.ofRealCLM.integrable_comp hXint
  have hofX2int : Integrable (fun ω => ((X ω ^ 2 : ℝ) : ℂ)) μ := by
    simpa using Complex.ofRealCLM.integrable_comp hX2
  have hPeq : P = (fun _ => (1 : ℂ)) + (Complex.I * (u : ℂ)) • (fun ω => ((X ω : ℝ) : ℂ))
      - ((u : ℂ) ^ 2 / 2) • (fun ω => ((X ω ^ 2 : ℝ) : ℂ)) := by
    funext ω
    simp only [hPdef, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hPint : Integrable P μ := by
    rw [hPeq]
    exact ((integrable_const _).add (hofXint.smul _)).sub (hofX2int.smul _)
  have hWint : Integrable W μ := hZint.sub hPint
  -- (iii) conditional Jensen for the modulus + conditional monotonicity
  have hJensen : ∀ᵐ ω ∂μ, ‖μ[W | m] ω‖ ≤ μ[g | m] ω := by
    have h1 := _root_.AEStronglyMeasurable.norm_condExp_le (m := m) hWint.aestronglyMeasurable
    have h2 := condExp_mono (m := m) hWint.norm hgint (ae_of_all _ hWbound)
    filter_upwards [h1, h2] with ω hh1 hh2 using hh1.trans hh2
  -- (iv) the conditional expectation of the majorant
  have hgcond : μ[g | m] =ᵐ[μ] fun ω =>
      u ^ 2 * μ[fun ω' => X ω' ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω' | m] ω
        + |u| ^ 3 * ε * μ[fun ω' => X ω' ^ 2 | m] ω := by
    have hgeq : g = (u ^ 2) • (fun ω => X ω ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω)
        + (|u| ^ 3 * ε) • (fun ω => X ω ^ 2) := by
      funext ω; simp [hgdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hgeq]
    have h1 := condExp_add (μ := μ) (m := m) (hind.smul (u ^ 2)) (hX2.smul (|u| ^ 3 * ε))
    have h2 := condExp_smul (μ := μ) (m := m) (u ^ 2)
      (fun ω => X ω ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω)
    have h3 := condExp_smul (μ := μ) (m := m) (|u| ^ 3 * ε) (fun ω => X ω ^ 2)
    filter_upwards [h1, h2, h3] with ω e1 e2 e3
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
    rw [e1, e2, e3]
  -- (v) the conditional expectation of `Z` is the pair of the real conditional expectations
  have hcosint : Integrable (fun ω => Real.cos (u * X ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun ω => ?_)
    · exact (Real.measurable_cos.comp (measurable_const.mul hX)).aestronglyMeasurable
    · simpa using Real.abs_cos_le_one _
  have hsinint : Integrable (fun ω => Real.sin (u * X ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun ω => ?_)
    · exact (Real.measurable_sin.comp (measurable_const.mul hX)).aestronglyMeasurable
    · simpa using Real.abs_sin_le_one _
  have hZre : (fun ω => (μ[Z | m] ω).re) =ᵐ[μ] μ[fun ω => Real.cos (u * X ω) | m] := by
    have h := Complex.reCLM.comp_condExp_comm (m := m) hZint
    have hcomp : (⇑Complex.reCLM ∘ Z) = fun ω => Real.cos (u * X ω) := by
      funext ω
      simp only [hZdef, Function.comp_apply, Complex.reCLM_apply]
      rw [mul_comm, Complex.exp_ofReal_mul_I_re]
    rw [hcomp] at h
    exact h
  have hZim : (fun ω => (μ[Z | m] ω).im) =ᵐ[μ] μ[fun ω => Real.sin (u * X ω) | m] := by
    have h := Complex.imCLM.comp_condExp_comm (m := m) hZint
    have hcomp : (⇑Complex.imCLM ∘ Z) = fun ω => Real.sin (u * X ω) := by
      funext ω
      simp only [hZdef, Function.comp_apply, Complex.imCLM_apply]
      rw [mul_comm, Complex.exp_ofReal_mul_I_im]
    rw [hcomp] at h
    exact h
  -- (vi) the conditional expectation of the Taylor polynomial
  have hofRe : ∀ f : Ω → ℝ, Integrable f μ →
      μ[fun ω => ((f ω : ℝ) : ℂ) | m] =ᵐ[μ] fun ω => ((μ[f | m] ω : ℝ) : ℂ) := by
    intro f hf
    have h := Complex.ofRealCLM.comp_condExp_comm (m := m) hf
    have hcomp : (⇑Complex.ofRealCLM ∘ f) = fun ω => ((f ω : ℝ) : ℂ) := rfl
    rw [hcomp] at h
    exact h.symm
  have hcondP : μ[P | m] =ᵐ[μ] fun ω =>
      (1 : ℂ) - (u : ℂ) ^ 2 / 2 * ((μ[fun ω' => X ω' ^ 2 | m] ω : ℝ) : ℂ) := by
    rw [hPeq]
    have h1 := condExp_add (μ := μ) (m := m) (integrable_const (1 : ℂ))
      (hofXint.smul (Complex.I * (u : ℂ)))
    have h2 := condExp_sub (μ := μ) (m := m)
      ((integrable_const (1 : ℂ)).add (hofXint.smul (Complex.I * (u : ℂ))))
      (hofX2int.smul ((u : ℂ) ^ 2 / 2))
    have h3 := condExp_smul (μ := μ) (m := m) (Complex.I * (u : ℂ))
      (fun ω => ((X ω : ℝ) : ℂ))
    have h4 := condExp_smul (μ := μ) (m := m) ((u : ℂ) ^ 2 / 2)
      (fun ω => ((X ω ^ 2 : ℝ) : ℂ))
    have h5 := hofRe X hXint
    have h6 := hofRe (fun ω => X ω ^ 2) hX2
    have h7 : μ[fun _ : Ω => (1 : ℂ) | m] = fun _ => (1 : ℂ) := condExp_const hm _
    filter_upwards [h1, h2, h3, h4, h5, h6, hcond] with ω e1 e2 e3 e4 e5 e6 e7
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 ⊢
    rw [e2, e1, e3, e4, e5, e6, h7]
    simp only [e7, Pi.zero_apply, Complex.ofReal_zero, mul_zero, add_zero]
  -- (vii) assembly
  have hcondW : μ[W | m] =ᵐ[μ] μ[Z | m] - μ[P | m] := condExp_sub hZint hPint m
  filter_upwards [hJensen, hgcond, hZre, hZim, hcondP, hcondW] with ω h1 h2 h3 h4 h5 h6
  have hEq : (⟨μ[fun ω' => Real.cos (u * X ω') | m] ω,
      μ[fun ω' => Real.sin (u * X ω') | m] ω⟩ : ℂ)
      - (1 - u ^ 2 / 2 * μ[fun ω' => X ω' ^ 2 | m] ω) = μ[W | m] ω := by
    rw [h6]
    simp only [Pi.sub_apply, h5]
    apply Complex.ext
    · simp [← h3]
    · simp [← h4]
  rw [hEq, ← h2]
  exact h1

end CondTaylor

section Arrays

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Tower telescope** (the heart of Brown's proof): for an MDS row, peeling the
factors of `e^{iuS}` from the right against the filtration replaces each by its
conditional Taylor polynomial, at total cost the summed conditional errors. -/
theorem norm_integral_exp_rowSum_sub_prod_le [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) (n : ℕ) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ‖(∫ ω, Complex.exp (Complex.I * (u * mdsRowSum k X n ω : ℝ)) ∂μ)
        - ∫ ω, ∏ i, (1 - (u ^ 2 / 2 : ℂ) * (μ[fun ω' => X n i ω' ^ 2
            | F n i.castSucc] ω : ℝ)) ∂μ‖
      ≤ ∑ i, (u ^ 2 * ∫ ω, X n i ω ^ 2 * Set.indicator {x : Ω | ε ≤ |X n i x|}
            (fun _ => (1 : ℝ)) ω ∂μ)
        + ∑ i, (|u| ^ 3 * ε * ∫ ω, X n i ω ^ 2 ∂μ) := by
  sorry

/-- **Product comparison**: if the conditional variance process converges to `σ²` in
probability and the individual conditional variances are uniformly asymptotically
negligible, the Taylor product converges to the Gaussian factor. -/
theorem tendsto_integral_prod_one_sub_condVar [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    -- USER-INPUT: conditional variance → σ² in probability; Brown's condition
    (hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | δ ≤ |mdsCondVariance k X F μ n ω - σ2|}).toReal)
        atTop (𝓝 0))
    -- USER-INPUT: uniform asymptotic negligibility of the conditional variances
    (hunif : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | ∃ i, δ ≤ μ[fun ω' => X n i ω' ^ 2
          | F n i.castSucc] ω}).toReal) atTop (𝓝 0))
    -- LEAN-ONLY: a uniform L¹ bound on the variance process, ruling out mass escape
    (hbdd : ∃ B : ℝ, ∀ n, ∫ ω, mdsCondVariance k X F μ n ω ∂μ ≤ B)
    (u : ℝ) :
    Tendsto (fun n => ∫ ω, ∏ i, (1 - (u ^ 2 / 2 : ℂ) *
        (μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℝ)) ∂μ) atTop
      (𝓝 (Complex.exp (-(u ^ 2 * σ2 / 2 : ℝ)))) := by
  sorry

end Arrays

end StatLean.TimeSeries
