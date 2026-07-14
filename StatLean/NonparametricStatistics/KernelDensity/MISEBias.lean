import StatLean.NonparametricStatistics.KernelDensity.LawTransfer
import StatLean.NonparametricStatistics.ForMathlib.MinkowskiIntegral
import StatLean.NonparametricStatistics.ForMathlib.TranslationL2
import StatLean.NonparametricStatistics.SmoothnessClasses.NikolskiTaylor

/-!
# Exact asymptotics of the integrated squared bias

For a differentiable density whose derivative is absolutely continuous with square-integrable
a.e. second derivative `w`, and a kernel of order `1` with finite second moment:
$$ \Bigl|\ \int b^2(x)\,dx \;-\; \frac{h^4}{4}\,S_K^2 \int w^2 \ \Bigr| \;\le\; \varepsilon\,h^4
   \qquad (0 < h < h_0(\varepsilon)),\qquad S_K = \int u^2 K(u)\,du. $$
This is the bias half of the exact asymptotic MISE: as `h → 0`, `∫b² ~ (h⁴/4)·S_K²·∫w²`.

**Proof formalization notes.** From the order-`2` integral remainder (with `ℓ = 2` playing the
role of `holderIndex` at `β = 2`),
`b(x) = h²∫u²K(u)∫₀¹(1−τ)·w(x+τuh) dτ du` (a.e. `x`); compare with the constant-`w` surrogate
`h²·(S_K/2)·w(x)` whose squared `L²` norm is exactly `(h⁴/4)S_K²∫w²`. The difference is
controlled by two generalized Minkowski applications and the `L²`-continuity of translation
(`tendsto_lintegral_sq_sub_translate`) applied to `w`, with a split of the `u`-integral at
`|u| ≤ h^{-1/2}` and the envelope `u²|K(u)|` for the far range. This is the analytically
hardest step of the exact MISE; the split thresholds and the `ε`-bookkeeping follow the
classical appendix computation.

The absolute continuity of `p'` is encoded by the explicit a.e.-derivative witness
`w` with `deriv p b − deriv p a = ∫_a^b w` — the honest rendering of "`p'` absolutely
continuous with `p'' = w ∈ L²`".

**Bibliographic comments.** The exact MISE expansion is due to G. S. Watson and
M. R. Leadbetter, *Ann. Math. Statist.* **34** (1963), 480–491; the second-order form with
the `(h⁴/4)S_K²∫(p'')²` bias constant is the classical optimal-bandwidth computation of
M. S. Bartlett, *Sankhyā Ser. A* **25** (1963), 245–254, and V. A. Epanechnikov, *Theory
Probab. Appl.* **14** (1969), 153–158.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- Local integrability of `w` on every bounded interval, from `MemLp w 2` via the domination
`|w| ≤ (w² + 1)/2`. -/
private lemma intervalIntegrable_of_memLp_two {w : ℝ → ℝ} (hw_meas : Measurable w)
    (hw2 : MemLp w 2 volume) (a b : ℝ) : IntervalIntegrable w volume a b := by
  have hsq : IntegrableOn (fun x => w x ^ 2) (Set.uIoc a b) volume :=
    hw2.integrable_sq.integrableOn
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.uIoc a b) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hdom : IntegrableOn (fun x => (w x ^ 2 + 1) / 2) (Set.uIoc a b) volume :=
    ((hsq.add hc).div_const 2)
  rw [intervalIntegrable_iff]
  refine hdom.mono' hw_meas.aestronglyMeasurable.restrict (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|w x| - 1), sq_abs (w x), abs_nonneg (w x)]

/-- Triangle Fubini for `0 ≤ t`: `∫₀ᵗ ∫₀ˢ f = ∫₀ᵗ (t−r) f(r)`. -/
private lemma triangle_double_integral_nonneg {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, f r) = ∫ r in (0 : ℝ)..t, (t - r) * f r := by
  have hfon : IntegrableOn f (Set.Ioc 0 t) volume := by
    have := hf 0 t; rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at this
  haveI : Fact (volume (Set.Ioc (0 : ℝ) t) < ⊤) := ⟨measure_Ioc_lt_top⟩
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t) with hμdef
  set F : ℝ → ℝ → ℝ := fun s r => {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p => f p.2) (s, r)
    with hFdef
  have hFmeas : Measurable (Function.uncurry F) := by
    have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
      measurableSet_le measurable_snd measurable_fst
    exact (hfm.comp measurable_snd).indicator hset
  -- Inner integral over the fixed interval with the indicator.
  have hinner : ∀ s ∈ Set.Ioc (0 : ℝ) t, (∫ r in (0 : ℝ)..s, f r) = ∫ r in Set.Ioc (0:ℝ) t, F s r
      := by
    intro s hs
    rw [intervalIntegral.integral_of_le hs.1.le,
      ← MeasureTheory.integral_indicator measurableSet_Ioc,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [hFdef, Set.indicator_apply, Set.mem_Ioc, Set.mem_setOf_eq]
    by_cases h1 : 0 < r ∧ r ≤ s
    · have h2 : 0 < r ∧ r ≤ t := ⟨h1.1, h1.2.trans hs.2⟩
      rw [if_pos h1, if_pos h2, if_pos h1.2]
    · by_cases h2 : 0 < r ∧ r ≤ t
      · have hrs : ¬ r ≤ s := by
          rcases not_and_or.1 h1 with h | h; exacts [absurd h2.1 h, h]
        rw [if_neg h1, if_pos h2, if_neg hrs]
      · rw [if_neg h1, if_neg h2]
  -- Outer-`s` integral of `F s r` for fixed `r ∈ Ioc 0 t`.
  have houter : ∀ r ∈ Set.Ioc (0 : ℝ) t, (∫ s in Set.Ioc (0:ℝ) t, F s r) = (t - r) * f r := by
    intro r hr
    have hFr : (fun s => F s r) = (Set.Ici r).indicator (fun _ => f r) := by
      funext s
      simp only [hFdef, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ici]
    have hint_eq : Set.Ioc (0:ℝ) t ∩ Set.Ici r = Set.Icc r t := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_lt_of_le hr.1 h1, h2⟩, h1⟩
    rw [hFr, ← MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [show (fun s => (Set.Ioc (0:ℝ) t).indicator ((Set.Ici r).indicator (fun _ => f r)) s)
        = (Set.Ioc (0:ℝ) t ∩ Set.Ici r).indicator (fun _ => f r) by
      rw [Set.indicator_indicator]]
    rw [MeasureTheory.integral_indicator (measurableSet_Ioc.inter measurableSet_Ici),
      MeasureTheory.setIntegral_const, hint_eq, MeasureTheory.measureReal_def,
      Real.volume_Icc, smul_eq_mul, ENNReal.toReal_ofReal (by linarith [hr.2]), mul_comm]
  -- Integrability of `F` on the square.
  have hFint : Integrable (Function.uncurry F) (μ.prod μ) := by
    have hg : Integrable (fun p : ℝ × ℝ => |f p.2|) (μ.prod μ) := hfon.abs.comp_snd μ
    refine hg.mono' hFmeas.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, hFdef, Set.indicator_apply, Real.norm_eq_abs]
    split_ifs with h
    · exact le_refl _
    · simp [abs_nonneg]
  -- Assemble.
  rw [intervalIntegral.integral_of_le ht,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hinner,
    MeasureTheory.integral_integral_swap hFint,
    intervalIntegral.integral_of_le ht,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc houter]

/-- Triangle Fubini: `∫₀ᵗ ∫₀ˢ f = ∫₀ᵗ (t−s) f(s)` for any real `t`. -/
private lemma triangle_double_integral {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : ∀ a b : ℝ, IntervalIntegrable f volume a b) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, f r) = ∫ s in (0 : ℝ)..t, (t - s) * f s := by
  rcases le_total 0 t with ht | ht
  · exact triangle_double_integral_nonneg hfm hf ht
  · -- Reflect: apply the nonneg case to `g r = f (-r)` at `-t ≥ 0`.
    set g : ℝ → ℝ := fun r => f (-r) with hgdef
    have hgm : Measurable g := hfm.comp measurable_neg
    have hgii : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
      intro a b
      have h := (IntervalIntegrable.iff_comp_neg (f := f)).mp (hf (-a) (-b))
      simpa only [neg_neg, hgdef] using h
    have hnt : (0 : ℝ) ≤ -t := by linarith
    have hkey := triangle_double_integral_nonneg hgm hgii hnt
    -- inner reflection: `∫ r in 0..s, g r = -(∫ r in 0..(-s), f r)`.
    have hinnref : ∀ s : ℝ, (∫ r in (0:ℝ)..s, g r) = -(∫ r in (0:ℝ)..(-s), f r) := by
      intro s
      have := intervalIntegral.integral_comp_neg (a := 0) (b := s) f
      simp only [neg_zero, hgdef] at this ⊢
      rw [this, intervalIntegral.integral_symm]
    -- Generic reflection of an `∫ 0..(-t)` integral into an `∫ 0..t` one.
    have hrefl : ∀ φ : ℝ → ℝ, (∫ s in (0:ℝ)..(-t), φ s) = -(∫ x in (0:ℝ)..t, φ (-x)) := by
      intro φ
      have := intervalIntegral.integral_comp_neg (a := 0) (b := t) φ
      simp only [neg_zero] at this
      rw [this, intervalIntegral.integral_symm]
    have hL : (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, f r)
        = ∫ s in (0 : ℝ)..(-t), ∫ r in (0 : ℝ)..s, g r := by
      rw [hrefl (fun s => ∫ r in (0:ℝ)..s, g r)]
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      show (∫ r in (0:ℝ)..x, f r) = -(∫ r in (0:ℝ)..(-x), g r)
      rw [hinnref (-x), neg_neg, neg_neg]
    have hR : (∫ s in (0 : ℝ)..t, (t - s) * f s)
        = ∫ s in (0 : ℝ)..(-t), (-t - s) * g s := by
      rw [hrefl (fun s => (-t - s) * g s)]
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hgdef, neg_neg]; ring
    rw [hL, hR, hkey]

/-- Continuity of `deriv p` from the a.e.-second-derivative witness. -/
private lemma continuous_deriv_of_hpw {p w : ℝ → ℝ} (hw_meas : Measurable w)
    (hw2 : MemLp w 2 volume) (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s) :
    Continuous (deriv p) := by
  have hii : ∀ a b : ℝ, IntervalIntegrable w volume a b :=
    fun a b => intervalIntegrable_of_memLp_two hw_meas hw2 a b
  have hcont : Continuous (fun b => ∫ s in (0 : ℝ)..b, w s) :=
    intervalIntegral.continuous_primitive hii 0
  have heq : deriv p = fun b => deriv p 0 + ∫ s in (0 : ℝ)..b, w s := by
    funext b; have := hpw 0 b; linarith
  rw [heq]; exact continuous_const.add hcont

/-- **Step A**: the second-order integral remainder for `p` (whose derivative is absolutely
continuous with a.e. second derivative `w`):
`p(x+t) − p x − t·deriv p x = t²·∫₀¹ (1−τ)·w(x+τ·t) dτ`. -/
private lemma second_order_remainder {p w : ℝ → ℝ} (hp1 : Differentiable ℝ p)
    (hw_meas : Measurable w) (hw2 : MemLp w 2 volume)
    (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s) (x t : ℝ) :
    p (x + t) - p x - t * deriv p x
      = t ^ 2 * ∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * t) := by
  have hdc : Continuous (deriv p) := continuous_deriv_of_hpw hw_meas hw2 hpw
  have hii : ∀ a b : ℝ, IntervalIntegrable w volume a b :=
    fun a b => intervalIntegrable_of_memLp_two hw_meas hw2 a b
  -- FTC: `p(x+t) − p x = ∫ 0..t deriv p (x+s) ds`.
  have hFTC : p (x + t) - p x = ∫ s in (0 : ℝ)..t, deriv p (x + s) := by
    have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (fun s => p (x + s)) (deriv p (x + s)) s := by
      intro s _
      have hin : HasDerivAt (fun s : ℝ => x + s) 1 s := by simpa using (hasDerivAt_id s).const_add x
      have hout : HasDerivAt p (deriv p (x + s)) (x + s) := (hp1 (x + s)).hasDerivAt
      simpa using hout.comp s hin
    have hcont : Continuous (fun s : ℝ => deriv p (x + s)) := hdc.comp (by fun_prop)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 t)
    simp only [add_zero] at this
    rw [this]
  -- `deriv p (x+s) = deriv p x + ∫ 0..s w (x+r) dr`.
  have hdsub : ∀ s : ℝ, deriv p (x + s) = deriv p x + ∫ r in (0 : ℝ)..s, w (x + r) := by
    intro s
    have h1 := hpw x (x + s)
    have h2 : (∫ r in x..(x + s), w r) = ∫ r in (0 : ℝ)..s, w (x + r) := by
      have := intervalIntegral.integral_comp_add_left w x (a := 0) (b := s)
      simp only [add_zero] at this; rw [this]
    rw [h2] at h1; linarith
  rw [hFTC]
  rw [intervalIntegral.integral_congr (g := fun s => deriv p x + ∫ r in (0 : ℝ)..s, w (x + r))
    (fun s _ => hdsub s)]
  -- The double integral over the triangle equals `∫₀ᵗ (t−s) w(x+s) ds` (Fubini).
  set f : ℝ → ℝ := fun r => w (x + r) with hfdef
  have hfm : Measurable f := hw_meas.comp (by fun_prop)
  have hfii : ∀ a b : ℝ, IntervalIntegrable f volume a b := by
    intro a b
    have h := (hii (x + a) (x + b)).comp_add_left x
    simpa only [hfdef, add_sub_cancel_left] using h
  have hWcont : Continuous (fun s : ℝ => ∫ r in (0 : ℝ)..s, f r) :=
    intervalIntegral.continuous_primitive hfii 0
  rw [intervalIntegral.integral_add (intervalIntegrable_const)
    (hWcont.intervalIntegrable 0 t), intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have htri : (∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, f r)
      = ∫ s in (0 : ℝ)..t, (t - s) * f s := triangle_double_integral hfm hfii t
  rw [htri]
  -- Change of variables `s = τ·t`.
  have hcov : (∫ s in (0 : ℝ)..t, (t - s) * f s)
      = t ^ 2 * ∫ τ in (0 : ℝ)..1, (1 - τ) * w (x + τ * t) := by
    rcases eq_or_ne t 0 with ht0 | ht0
    · simp [ht0]
    · have hc := intervalIntegral.integral_comp_mul_left (fun s => (t - s) * f s) ht0
        (a := 0) (b := 1)
      rw [mul_zero, mul_one] at hc
      have hval : (∫ s in (0:ℝ)..t, (t - s) * f s)
          = t • ∫ τ in (0:ℝ)..1, (t - t * τ) * f (t * τ) := by
        rw [hc, smul_smul, mul_inv_cancel₀ ht0, one_smul]
      have hrw : (∫ τ in (0:ℝ)..1, (t - t * τ) * f (t * τ))
          = t * ∫ τ in (0:ℝ)..1, (1 - τ) * w (x + τ * t) := by
        rw [← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun τ _ => ?_
        simp only [hfdef]; ring_nf
      rw [hval, hrw, smul_eq_mul]; ring
  rw [hcov]; ring

/-- **Integrated squared bias, exact asymptotics**: under the second-order smoothness
hypotheses, for every `ε > 0` there is `h₀ > 0` such that for all `0 < h < h₀`, `n ≥ 1`:
`ofReal ((h⁴/4)·S_K²·∫w² − ε·h⁴) ≤ ∫ b² ≤ ofReal ((h⁴/4)·S_K²·∫w² + ε·h⁴)`. -/
theorem kde_integrated_sq_bias_asymptotic {p K w : ℝ → ℝ}
    -- USER-INPUT: `p` is a probability density; the sampling model
    (hp_meas : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∫ x, p x = 1)
    -- USER-INPUT: `p` is differentiable; second-order smoothness input
    (hp1 : Differentiable ℝ p)
    -- USER-INPUT: `p'` is absolutely continuous with a.e. derivative `w`; second-order
    -- smoothness input (the classical `p'' = w`)
    (hw_meas : Measurable w)
    (hpw : ∀ a b : ℝ, deriv p b - deriv p a = ∫ s in a..b, w s)
    -- USER-INPUT: square-integrable second derivative; second-order smoothness input
    (hw2 : MemLp w 2 volume)
    -- USER-INPUT: kernel of order 1; classical input of the second-order expansion
    (hK : IsKernelOfOrder K 1)
    -- LEAN-ONLY: measurability of the kernel; standard regularity
    (hKmeas : Measurable K)
    -- USER-INPUT: finite second moment of the kernel; classical input
    (hKu2 : Integrable fun u => u ^ 2 * |K u|) :
    ∀ ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {n : ℕ} (X : Fin n → Ω → ℝ), 1 ≤ n →
        IsIIDSample P X (densityMeasure p) → (∀ i, Measurable (X i)) →
        ∀ h : ℝ, 0 < h → h < h₀ →
          ENNReal.ofReal (h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) - ε * h ^ 4)
              ≤ (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2)) ∧
            (∫⁻ x, ENNReal.ofReal ((kdeBiasAt P X K h p x) ^ 2))
              ≤ ENNReal.ofReal
                  (h ^ 4 / 4 * (∫ u, u ^ 2 * K u) ^ 2 * (∫ x, (w x) ^ 2) + ε * h ^ 4) := by
  sorry

end StatLean.NonparametricStatistics
