import StatLean.TimeSeries.Mixing.Defs
import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Mixing of Markov chains: the Davydov identity and its consequences (FY §2.6.1(vi)–(vii))

The bridge between the Markov layer (`ForMathlib/Markov/*`) and the mixing coefficients:

* **eq. (2.58) (Davydov 1973)** — for a strictly stationary Markov process with kernel
  `κ` and marginal `F`, the β-coefficient is the mean total-variation distance of the
  `n`-step transition law from the marginal: `β(n) = ∫ ‖κⁿ(x, ·) − F‖_TV dF(x)`.
  Literature DEBT (needs the conditional-probability description of β against
  `condDistrib`).
* **eq. (2.59)** — a geometric-ergodicity envelope `‖κⁿ(x,·) − F‖_TV ≤ A(x) ρⁿ` with
  `∫ A dF < ∞` gives exponential β-mixing: `β(n) ≤ ρⁿ ∫ A dF`. **Derived here** from
  the (2.58) debt by monotone integration.
* **Bradley reduction (FY §2.6.1(vi), cited Bradley Thms 4.1–4.2)** — for stationary
  Markov chains the process coefficients collapse to the two-marginal coefficients of
  `(X_0, X_n)`. The α-case is **proved here** (2026-08-09) over the single named brick
  `condExp_sigmaGE_indicator_brick`.

**Open bricks (2026-08-09).** All three remaining `sorry`s sit in named `private` lemmas,
and both public theorems of this file are assembled from them:
`condExp_sigmaGE_indicator_brick` (the Markov property for the whole future σ-algebra —
`IsMarkovOf` only supplies it one coordinate at a time), `betaMixCoeff_two_marginal_brick`
(the same content in its β-form) and
`betaMixCoeff_two_marginal_eq_integral_tvDist_brick` (Davydov's identity proper; its
docstring records the *verified* calibration demanded below and the proof of each
direction).

**Normalization warning (for the closure session).** `tvDist` is the sup-over-events
distance `sup_B |P(B) − Q(B)|`; the book's `‖·‖_TV` is twice that. FY's (2.58) is
stated for the conditional form of β, which in the sup-over-events normalization reads
`β(n) = ∫ tvDist (κⁿ x) F dF(x)` with **no factor 2** — verify this calibration against
the finite-partition definition of `betaMixCoeff` before proving anything downstream
of the debt.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.1,
eqs. (2.58)–(2.59) (p. 70). (`FY §2.6.1 (2.58)–(2.59)`.)

**Bibliographic comments.** The identity (2.58) is Yu. A. Davydov, *Mixing conditions
for Markov chains* (Theory Probab. Appl. 1973); the reduction of mixing coefficients to
two marginals is R. C. Bradley, *Introduction to Strong Mixing Conditions*, Thms 4.1
and 4.2 (vol. 1); the geometric-ergodicity route to β-mixing is standard from
Nummelin–Tuominen and Meyn–Tweedie ch. 16.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

/-! ### Measure-theoretic bricks for the two-marginal reduction

Pure two-σ-algebra material, stated in the `Mixing/Relations.lean` binder convention (the
ambient σ-algebra `mΩ` is a plain implicit bound *after* the sub-σ-algebras, so that the
sub-σ-algebra hypotheses do not shadow it as local instances). -/

section Helpers
variable {Ω : Type*}

private lemma le_alphaMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet[m₁] A) (hB : MeasurableSet[m₂] B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ alphaMixCoeff μ m₁ m₂ := by
  refine le_csSup ⟨1, ?_⟩ ⟨A, B, hA, hB, rfl⟩
  rintro r ⟨A', B', -, -, rfl⟩
  have h1 : (μ (A' ∩ B')).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top μ Set.univ)
      (measure_mono (Set.subset_univ (A' ∩ B')))
  have h2 : (μ A').toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ A'))
  have h3 : (μ B').toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ B'))
  have h0 : (0 : ℝ) ≤ (μ (A' ∩ B')).toReal := ENNReal.toReal_nonneg
  have h0a : (0 : ℝ) ≤ (μ A').toReal := ENNReal.toReal_nonneg
  have h0b : (0 : ℝ) ≤ (μ B').toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> nlinarith

private lemma alphaMixCoeff_mono' {m₁ m₂ m₁' m₂' mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁' ≤ m₁) (h₂ : m₂' ≤ m₂) :
    alphaMixCoeff μ m₁' m₂' ≤ alphaMixCoeff μ m₁ m₂ := by
  refine Real.sSup_le ?_ ?_
  · rintro r ⟨A, B, hA, hB, rfl⟩
    exact le_alphaMixCoeff (mΩ := mΩ) (h₁ _ hA) (h₂ _ hB)
  · have := le_alphaMixCoeff (mΩ := mΩ) (μ := μ) (m₁ := m₁) (m₂ := m₂)
      (@MeasurableSet.empty Ω m₁) (@MeasurableSet.empty Ω m₂)
    simpa using this

/-- `∫ 1_A * (1_B - P B) = P(A ∩ B) - P A * P B`. -/
private lemma integral_centred_indicator_mul {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ ω, (A.indicator (fun _ => (1:ℝ)) ω) * (B.indicator (fun _ => (1:ℝ)) ω - (μ B).toReal) ∂μ
      = (μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal := by
  have hfun : (fun ω => (A.indicator (fun _ => (1:ℝ)) ω)
        * (B.indicator (fun _ => (1:ℝ)) ω - (μ B).toReal))
      = fun ω => (A ∩ B).indicator (fun _ => (1:ℝ)) ω
          - (μ B).toReal * A.indicator (fun _ => (1:ℝ)) ω := by
    funext ω
    by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ B <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]
  rw [hfun, integral_sub ((integrable_const (1:ℝ)).indicator (hA.inter hB))
      (((integrable_const (1:ℝ)).indicator hA).const_mul _),
    integral_indicator_const (1:ℝ) (hA.inter hB), integral_const_mul,
    integral_indicator_const (1:ℝ) hA]
  simp [Measure.real]
  ring

private lemma integral_centred_indicator {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : Set Ω} (hB : MeasurableSet B) :
    ∫ ω, (B.indicator (fun _ => (1:ℝ)) ω - (μ B).toReal) ∂μ = 0 := by
  rw [integral_sub ((integrable_const (1:ℝ)).indicator hB) (integrable_const _),
    integral_indicator_const (1:ℝ) hB, integral_const]
  simp [Measure.real]

private lemma integrable_centred_indicator {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : Set Ω} (hB : MeasurableSet B) :
    Integrable (fun ω => B.indicator (fun _ => (1:ℝ)) ω - (μ B).toReal) μ :=
  ((integrable_const (1:ℝ)).indicator hB).sub (integrable_const _)

end Helpers

section LemmaL
variable {Ω : Type*}

/-- **One-sided optimisation.** For an integrable mean-zero `h`, an `m`-measurable `Y` with
values in `[0,1]`, and any `m`-measurable version `p` of `μ[h|m]`,
`|∫ Y h| ≤ ∫_{p > 0} h`. -/
private lemma abs_integral_mul_le_setIntegral {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {h : Ω → ℝ} (hh : Integrable h μ) (hh0 : ∫ ω, h ω ∂μ = 0)
    {p : Ω → ℝ} (hp : StronglyMeasurable[m] p) (hpe : μ[h|m] =ᵐ[μ] p)
    {Y : Ω → ℝ} (hY : StronglyMeasurable[m] Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hY1 : ∀ ω, Y ω ≤ 1) :
    |∫ ω, Y ω * h ω ∂μ| ≤ ∫ ω in {ω | 0 < p ω}, h ω ∂μ := by
  have hYm : AEStronglyMeasurable Y μ := (hY.mono hm).aestronglyMeasurable
  have hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ (1:ℝ) :=
    Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hY0 ω)]; exact hY1 ω
  have hpI : Integrable p μ := integrable_condExp.congr hpe
  -- (1) `∫ Y h = ∫ Y p`
  have hpull : μ[Y * h|m] =ᵐ[μ] Y * μ[h|m] :=
    condExp_stronglyMeasurable_mul_of_bound₀ hm hY.aestronglyMeasurable hh 1 hYb
  have hstep1 : ∫ ω, Y ω * h ω ∂μ = ∫ ω, Y ω * p ω ∂μ := by
    have e0 : ∫ ω, (Y * h) ω ∂μ = ∫ ω, (μ[Y * h|m]) ω ∂μ := (integral_condExp hm).symm
    have e1 : ∫ ω, (μ[Y * h|m]) ω ∂μ = ∫ ω, Y ω * (μ[h|m]) ω ∂μ :=
      integral_congr_ae (by filter_upwards [hpull] with ω hω using hω)
    have e2 : ∫ ω, Y ω * (μ[h|m]) ω ∂μ = ∫ ω, Y ω * p ω ∂μ :=
      integral_congr_ae (by filter_upwards [hpe] with ω hω using by rw [hω])
    calc ∫ ω, Y ω * h ω ∂μ = ∫ ω, (Y * h) ω ∂μ := rfl
      _ = ∫ ω, (μ[Y * h|m]) ω ∂μ := e0
      _ = ∫ ω, Y ω * (μ[h|m]) ω ∂μ := e1
      _ = ∫ ω, Y ω * p ω ∂μ := e2
  -- (2) `∫ p = 0`
  have hp0 : ∫ ω, p ω ∂μ = 0 := by
    rw [← integral_congr_ae hpe, integral_condExp hm, hh0]
  -- (3) the two-sided bound against the positive part
  have hposI : Integrable (fun ω => max (p ω) 0) μ := hpI.pos_part
  have hnegI : Integrable (fun ω => max (-p ω) 0) μ := hpI.neg.pos_part
  have hYpI : Integrable (fun ω => Y ω * p ω) μ := hpI.bdd_mul hYm hYb
  have hsplit : ∫ ω, max (p ω) 0 ∂μ = ∫ ω, max (-p ω) 0 ∂μ := by
    have hd : ∫ ω, (max (p ω) 0 - max (-p ω) 0) ∂μ = ∫ ω, p ω ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show max (p ω) 0 - max (-p ω) 0 = p ω
      rcases le_total (p ω) 0 with hle | hle
      · rw [max_eq_right hle, max_eq_left (by linarith)]; ring
      · rw [max_eq_left hle, max_eq_right (by linarith)]; ring
    rw [integral_sub hposI hnegI, hp0] at hd
    linarith
  have hub : ∫ ω, Y ω * p ω ∂μ ≤ ∫ ω, max (p ω) 0 ∂μ := by
    refine integral_mono hYpI hposI fun ω => ?_
    rcases le_total (p ω) 0 with hle | hle
    · have : Y ω * p ω ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hY0 ω) hle
      exact this.trans (le_max_right _ _)
    · have : Y ω * p ω ≤ 1 * p ω := mul_le_mul_of_nonneg_right (hY1 ω) hle
      rw [one_mul] at this
      exact this.trans (le_max_left _ _)
  have hlb : -∫ ω, max (p ω) 0 ∂μ ≤ ∫ ω, Y ω * p ω ∂μ := by
    rw [hsplit]
    have : ∫ ω, Y ω * (-p ω) ∂μ ≤ ∫ ω, max (-p ω) 0 ∂μ := by
      refine integral_mono (hpI.neg.bdd_mul hYm hYb) hnegI fun ω => ?_
      rcases le_total (-p ω) 0 with hle | hle
      · have : Y ω * (-p ω) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hY0 ω) hle
        exact this.trans (le_max_right _ _)
      · have : Y ω * (-p ω) ≤ 1 * (-p ω) := mul_le_mul_of_nonneg_right (hY1 ω) hle
        rw [one_mul] at this
        exact this.trans (le_max_left _ _)
    have he : ∫ ω, Y ω * (-p ω) ∂μ = -∫ ω, Y ω * p ω ∂μ := by
      rw [← integral_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [he] at this
    linarith
  -- (4) the positive part is a set integral of `h`
  have hAm : MeasurableSet[m] {ω | 0 < p ω} := hp.measurable (measurableSet_Ioi (a := (0:ℝ)))
  have hposeq : (fun ω => max (p ω) 0) = {ω | 0 < p ω}.indicator p := by
    funext ω
    by_cases hx : 0 < p ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | 0 < p ω} from hx) p, max_eq_left hx.le]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | 0 < p ω} from hx) p,
        max_eq_right (not_lt.1 hx)]
  have hfin : ∫ ω, max (p ω) 0 ∂μ = ∫ ω in {ω | 0 < p ω}, h ω ∂μ := by
    rw [hposeq, integral_indicator (hm _ hAm)]
    calc ∫ ω in {ω | 0 < p ω}, p ω ∂μ = ∫ ω in {ω | 0 < p ω}, (μ[h|m]) ω ∂μ :=
          setIntegral_congr_ae (hm _ hAm)
            (by filter_upwards [hpe] with ω hω using fun _ => hω.symm)
      _ = ∫ ω in {ω | 0 < p ω}, h ω ∂μ := setIntegral_condExp hm hh hAm
  rw [hstep1, abs_le]
  constructor
  · rw [← hfin]; linarith
  · rw [← hfin]; linarith

end LemmaL

section Assembly
variable {Ω : Type*}

private lemma alphaMixCoeff_nonneg' {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] : 0 ≤ alphaMixCoeff μ m₁ m₂ := by
  have := le_alphaMixCoeff (mΩ := mΩ) (μ := μ) (m₁ := m₁) (m₂ := m₂)
    (@MeasurableSet.empty Ω m₁) (@MeasurableSet.empty Ω m₂)
  simpa using this

private lemma setIntegral_eq_indicator_mul {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {s : Set Ω}
    (hs : MeasurableSet s) (f : Ω → ℝ) :
    ∫ ω in s, f ω ∂μ = ∫ ω, s.indicator (fun _ => (1:ℝ)) ω * f ω ∂μ := by
  rw [← integral_indicator hs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases hx : ω ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

private lemma indicator_one_nonneg (S : Set Ω) (ω : Ω) :
    (0:ℝ) ≤ S.indicator (fun _ => (1:ℝ)) ω := by
  by_cases hx : ω ∈ S
  · simp only [Set.indicator_of_mem hx]; norm_num
  · simp only [Set.indicator_of_notMem hx]; exact le_rfl

private lemma indicator_one_le_one (S : Set Ω) (ω : Ω) :
    S.indicator (fun _ => (1:ℝ)) ω ≤ 1 := by
  by_cases hx : ω ∈ S
  · simp only [Set.indicator_of_mem hx]; exact le_rfl
  · simp only [Set.indicator_of_notMem hx]; norm_num

private lemma norm_centred_indicator_le_one {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (S : Set Ω) (ω : Ω) :
    ‖S.indicator (fun _ => (1:ℝ)) ω - (μ S).toReal‖ ≤ 1 := by
  have h1 : (0:ℝ) ≤ (μ S).toReal := ENNReal.toReal_nonneg
  have h2 : (μ S).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ S))
  have h3 := indicator_one_nonneg S ω
  have h4 := indicator_one_le_one S ω
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

end Assembly

section PullOut
variable {Ω : Type*}

private lemma norm_condExp_indicator_le_one {𝒢 mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ mΩ) {U : Set Ω} (hU : MeasurableSet U) :
    ∀ᵐ ω ∂μ, ‖(μ[U.indicator (fun _ => (1 : ℝ))|𝒢]) ω‖ ≤ 1 := by
  have h0 : (0 : Ω → ℝ) ≤ᵐ[μ] μ[U.indicator (fun _ => (1 : ℝ))|𝒢] :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => by
      by_cases hx : ω ∈ U <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx])
  have h1 : μ[U.indicator (fun _ => (1 : ℝ))|𝒢] ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    have h := condExp_mono (m := 𝒢) ((integrable_const (μ := μ) (1 : ℝ)).indicator hU)
      (integrable_const (μ := μ) (1 : ℝ)) (Filter.Eventually.of_forall fun ω => by
        by_cases hx : ω ∈ U <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx])
    rwa [condExp_const (μ := μ) h𝒢] at h
  filter_upwards [h0, h1] with ω e0 e1
  rw [Real.norm_eq_abs, abs_of_nonneg e0]
  exact e1

/-- **The symmetric pull-out**: `∫_D E[1_A|𝒢] = ∫_A E[1_D|𝒢]` — both sides are
`∫ E[1_A|𝒢] · E[1_D|𝒢]`. -/
private lemma setIntegral_condExp_indicator_symm {𝒢 mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h𝒢 : 𝒢 ≤ mΩ)
    {A D : Set Ω} (hA : MeasurableSet A) (hD : MeasurableSet D) :
    ∫ ω in D, (μ[A.indicator (fun _ => (1 : ℝ))|𝒢]) ω ∂μ
      = ∫ ω in A, (μ[D.indicator (fun _ => (1 : ℝ))|𝒢]) ω ∂μ := by
  have key : ∀ U V : Set Ω, MeasurableSet U → MeasurableSet V →
      ∫ ω in V, (μ[U.indicator (fun _ => (1 : ℝ))|𝒢]) ω ∂μ
        = ∫ ω, (μ[U.indicator (fun _ => (1 : ℝ))|𝒢]) ω
            * (μ[V.indicator (fun _ => (1 : ℝ))|𝒢]) ω ∂μ := by
    intro U V hU hV
    have hpull : μ[(μ[U.indicator (fun _ => (1 : ℝ))|𝒢]) * V.indicator (fun _ => (1 : ℝ))|𝒢]
        =ᵐ[μ] (μ[U.indicator (fun _ => (1 : ℝ))|𝒢]) * μ[V.indicator (fun _ => (1 : ℝ))|𝒢] :=
      condExp_stronglyMeasurable_mul_of_bound₀ h𝒢
        stronglyMeasurable_condExp.aestronglyMeasurable
        ((integrable_const (μ := μ) (1 : ℝ)).indicator hV) 1
        (norm_condExp_indicator_le_one h𝒢 hU)
    calc ∫ ω in V, (μ[U.indicator (fun _ => (1 : ℝ))|𝒢]) ω ∂μ
        = ∫ ω, V.indicator (fun _ => (1 : ℝ)) ω * (μ[U.indicator (fun _ => (1 : ℝ))|𝒢]) ω ∂μ :=
          setIntegral_eq_indicator_mul hV _
      _ = ∫ ω, ((μ[U.indicator (fun _ => (1 : ℝ))|𝒢]) * V.indicator (fun _ => (1 : ℝ))) ω ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => by
            simp only [Pi.mul_apply]; ring)
      _ = ∫ ω, (μ[(μ[U.indicator (fun _ => (1 : ℝ))|𝒢])
            * V.indicator (fun _ => (1 : ℝ))|𝒢]) ω ∂μ := (integral_condExp h𝒢).symm
      _ = ∫ ω, (μ[U.indicator (fun _ => (1 : ℝ))|𝒢]) ω
            * (μ[V.indicator (fun _ => (1 : ℝ))|𝒢]) ω ∂μ :=
          integral_congr_ae (by filter_upwards [hpull] with ω hω using hω)
  rw [key A D hA hD, key D A hD hA]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

end PullOut

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **Markov representation** hypothesis tying a real-valued process to a kernel:
the conditional law of `X_{t+n}` given the past through time `t` is `κⁿ(X_t, ·)`,
expressed through conditional expectations of indicators. -/
def IsMarkovOf (X : ℤ → Ω → ℝ) (κ : ProbabilityTheory.Kernel ℝ ℝ) (μ : Measure Ω) :
    Prop :=
  ∀ (t : ℤ) (n : ℕ) (B : Set ℝ), MeasurableSet B →
    (μ[fun ω => (B.indicator (fun _ => (1 : ℝ)) (X (t + n) ω)) | sigmaLE X t])
      =ᵐ[μ] fun ω => (((κ ^ n) (X t ω)) B).toReal

section MarkovFuture

/-- Powers of a Markov kernel are Markov. -/
private theorem isMarkovKernel_pow' {S : Type*} [MeasurableSpace S] (κ : Kernel S S)
    [IsMarkovKernel κ] : ∀ n : ℕ, IsMarkovKernel (κ ^ n)
  | 0 => by rw [pow_zero]; exact (inferInstance : IsMarkovKernel (Kernel.id : Kernel S S))
  | n + 1 => by
      haveI := isMarkovKernel_pow' κ n
      rw [pow_succ]
      exact Kernel.IsMarkovKernel.comp (κ ^ n) κ

/-- A bounded measurable function of a random variable is integrable on a finite measure
space. -/
private lemma integrable_bdd_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) [IsFiniteMeasure ν] {Y : α → β} (hY : Measurable Y) {f : β → ℝ}
    (hf : Measurable f) {M : ℝ} (hfb : ∀ y, |f y| ≤ M) :
    Integrable (fun ω => f (Y ω)) ν := by
  refine Integrable.mono (integrable_const M) ((hf.comp hY).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (hfb _).trans (le_abs_self M)

private lemma sigmaLE_le {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaLE X t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

/-- The `n`-step kernel average of a bounded measurable function is measurable. -/
private lemma measurable_kernel_integral {κ : Kernel ℝ ℝ} (n : ℕ) {f : ℝ → ℝ}
    (hf : Measurable f) : Measurable fun x => ∫ y, f y ∂((κ ^ n) x) :=
  (hf.stronglyMeasurable.integral_kernel (κ := κ ^ n)).measurable

private lemma abs_kernel_integral_le {κ : Kernel ℝ ℝ} [IsMarkovKernel κ] (n : ℕ) {f : ℝ → ℝ}
    {M : ℝ} (hfb : ∀ y, |f y| ≤ M) (x : ℝ) : |∫ y, f y ∂((κ ^ n) x)| ≤ M := by
  haveI := isMarkovKernel_pow' κ n
  have h := norm_integral_le_of_norm_le_const (μ := (κ ^ n) x) (C := M)
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hfb y)
  simpa [Measure.real, measure_univ] using h

/-- **Step 1**: the set-integral form of the Markov property against a bounded measurable
test function. -/
private lemma markov_setIntegral_eq [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    {κ : Kernel ℝ ℝ} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ)
    (t : ℤ) (n : ℕ) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hfb : ∀ y, |f y| ≤ M)
    {A : Set Ω} (hA : MeasurableSet[sigmaLE X t] A) :
    ∫ ω in A, (∫ y, f y ∂((κ ^ n) (X t ω))) ∂μ = ∫ ω in A, f (X (t + n) ω) ∂μ := by
  haveI := isMarkovKernel_pow' κ n
  have hm := sigmaLE_le hmeas t
  have hAΩ : MeasurableSet A := hm _ hA
  set lam : Measure Ω := μ.restrict A with hlam
  haveI : IsFiniteMeasure lam := by rw [hlam]; infer_instance
  set κ' : Kernel Ω ℝ := (κ ^ n).comap (X t) (hmeas t) with hκ'
  haveI : IsMarkovKernel κ' := by rw [hκ']; infer_instance
  -- (a) the one-event Markov identity, in `ℝ≥0∞`
  have hone : ∀ B : Set ℝ, MeasurableSet B →
      lam (X (t + n) ⁻¹' B) = ∫⁻ ω, (κ' ω) B ∂lam := by
    intro B hB
    have hbd1 : ∀ y : ℝ, |B.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := fun y => by
      by_cases hy : y ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
    have hint : Integrable (fun ω => B.indicator (fun _ => (1 : ℝ)) (X (t + n) ω)) μ :=
      integrable_bdd_comp μ (hmeas _) (measurable_const.indicator hB) hbd1
    have hsi := setIntegral_condExp hm hint hA
    have hcond : ∫ ω in A, (μ[fun ω => B.indicator (fun _ => (1 : ℝ)) (X (t + n) ω)
        | sigmaLE X t]) ω ∂μ = ∫ ω in A, (((κ ^ n) (X t ω)) B).toReal ∂μ :=
      setIntegral_congr_ae hAΩ (by filter_upwards [hmarkov t n B hB] with ω hω using fun _ => hω)
    have hrhs : ∫ ω in A, B.indicator (fun _ => (1 : ℝ)) (X (t + n) ω) ∂μ
        = (lam (X (t + n) ⁻¹' B)).toReal := by
      have hfe : (fun ω => B.indicator (fun _ => (1 : ℝ)) (X (t + n) ω))
          = (X (t + n) ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
        funext ω
        by_cases hy : X (t + n) ω ∈ B <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy, Set.mem_preimage]
      rw [hfe, integral_indicator_const (1 : ℝ) ((hmeas _) hB)]
      simp [hlam, Measure.real, Measure.restrict_apply ((hmeas _) hB), Set.inter_comm]
    have hkey : (lam (X (t + n) ⁻¹' B)).toReal
        = ∫ ω in A, (((κ ^ n) (X t ω)) B).toReal ∂μ := by rw [← hrhs, ← hsi, hcond]
    have hgm : Measurable fun ω => (((κ ^ n) (X t ω)) B).toReal :=
      (((κ ^ n).measurable_coe hB).comp (hmeas t)).ennreal_toReal
    have hg1 : ∀ ω, (((κ ^ n) (X t ω)) B).toReal ≤ 1 := fun ω => by
      simpa using ENNReal.toReal_mono (measure_ne_top ((κ ^ n) (X t ω)) Set.univ)
        (measure_mono (Set.subset_univ B))
    have hgint : IntegrableOn (fun ω => (((κ ^ n) (X t ω)) B).toReal) A μ := by
      refine Integrable.mono (integrable_const (1 : ℝ)) hgm.aestronglyMeasurable.restrict
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg zero_le_one,
        abs_of_nonneg ENNReal.toReal_nonneg]
      exact hg1 ω
    have hlint : ∫⁻ ω, (κ' ω) B ∂lam
        = ENNReal.ofReal (∫ ω in A, (((κ ^ n) (X t ω)) B).toReal ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hgint
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg), hlam]
      refine lintegral_congr fun ω => ?_
      rw [hκ', Kernel.comap_apply, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [hlint, ← hkey, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  -- (b) the pushforward identity
  have hmap : lam.map (X (t + n)) = (lam ⊗ₘ κ').map Prod.snd := by
    ext B hB
    rw [Measure.map_apply (hmeas _) hB, Measure.map_apply measurable_snd hB,
      Measure.compProd_apply (measurable_snd hB), hone B hB]
    rfl
  -- (c) integrate `f`
  have hfint : Integrable (fun z : Ω × ℝ => f z.2) (lam ⊗ₘ κ') :=
    integrable_bdd_comp _ measurable_snd hf hfb
  have e1 : ∫ ω in A, (∫ y, f y ∂((κ ^ n) (X t ω))) ∂μ = ∫ ω, (∫ y, f y ∂(κ' ω)) ∂lam := by
    simp only [hκ', Kernel.comap_apply, hlam]
  have e2 : ∫ ω, (∫ y, f y ∂(κ' ω)) ∂lam = ∫ z, f z.2 ∂(lam ⊗ₘ κ') :=
    (MeasureTheory.Measure.integral_compProd hfint).symm
  have e3 : ∫ z, f z.2 ∂(lam ⊗ₘ κ') = ∫ y, f y ∂((lam ⊗ₘ κ').map Prod.snd) :=
    (integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable).symm
  have e4 : ∫ y, f y ∂(lam.map (X (t + n))) = ∫ ω, f (X (t + n) ω) ∂lam :=
    integral_map (hmeas _).aemeasurable hf.aestronglyMeasurable
  rw [e1, e2, e3, ← hmap, e4, hlam]

/-- **Step 1′**: the Markov property against a bounded measurable test function. -/
private lemma condExp_bdd_eq_kernel_integral [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    {κ : Kernel ℝ ℝ} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ)
    (t : ℤ) (n : ℕ) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hfb : ∀ y, |f y| ≤ M) :
    μ[fun ω => f (X (t + n) ω) | sigmaLE X t]
      =ᵐ[μ] fun ω => ∫ y, f y ∂((κ ^ n) (X t ω)) := by
  have hm := sigmaLE_le hmeas t
  have hFm : Measurable fun x : ℝ => ∫ y, f y ∂((κ ^ n) x) :=
    measurable_kernel_integral n hf
  have hcomap : MeasurableSpace.comap (X t) inferInstance ≤ sigmaLE X t :=
    le_iSup₂_of_le t (Set.mem_Iic.mpr le_rfl) le_rfl
  have hgm : StronglyMeasurable[sigmaLE X t] fun ω => ∫ y, f y ∂((κ ^ n) (X t ω)) := by
    refine StronglyMeasurable.mono ?_ hcomap
    exact (hFm.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm
    (integrable_bdd_comp μ (hmeas _) hf hfb) (fun s _ _ => ?_) (fun s hs _ => ?_)
    hgm.aestronglyMeasurable).symm
  · exact (integrable_bdd_comp μ (hmeas t) hFm (abs_kernel_integral_le n hfb)).integrableOn
  · exact markov_setIntegral_eq hmeas hmarkov t n hf hfb hs


/-- **Step 2**: the conditional expectation, given the past up to `t`, of a finite product
of bounded measurable functions of the coordinates at times `≥ t` is a function of `X t`. -/
private lemma condExp_prod_future [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    {κ : Kernel ℝ ℝ} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ) (t : ℤ) (S : Finset ℕ) :
    ∀ f : ℕ → ℝ → ℝ, (∀ s, Measurable (f s)) → (∀ s y, |f s y| ≤ 1) →
      ∃ G : ℝ → ℝ, Measurable G ∧ (∀ x, |G x| ≤ 1) ∧
        μ[fun ω => ∏ s ∈ S, f s (X (t + (s : ℤ)) ω) | sigmaLE X t]
          =ᵐ[μ] fun ω => G (X t ω) := by
  classical
  have hmt := sigmaLE_le hmeas t
  refine Finset.induction_on_max S ?_ ?_
  · intro f hfm hfb
    refine ⟨fun _ => 1, measurable_const, fun _ => by norm_num, ?_⟩
    simp only [Finset.prod_empty]
    rw [condExp_const hmt (1 : ℝ)]
  · intro a S hlt ih f hfm hfb
    have haS : a ∉ S := fun h => lt_irrefl a (hlt a h)
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · refine ⟨fun x => ∫ y, f a y ∂((κ ^ a) x), measurable_kernel_integral a (hfm a),
        fun x => abs_kernel_integral_le a (hfb a) x, ?_⟩
      have hfun : (fun ω => ∏ s ∈ insert a (∅ : Finset ℕ), f s (X (t + (s : ℤ)) ω))
          = fun ω => f a (X (t + (a : ℤ)) ω) := by
        funext ω; simp
      rw [hfun]
      exact condExp_bdd_eq_kernel_integral hmeas hmarkov t a (hfm a) (hfb a)
    · obtain ⟨hbmem, hbmax⟩ : (S.max' hSne) ∈ S ∧ ∀ s ∈ S, s ≤ S.max' hSne :=
        ⟨S.max'_mem hSne, fun s hs => S.le_max' s hs⟩
      set b : ℕ := S.max' hSne with hbdef
      have hba : b < a := hlt b hbmem
      have hmb := sigmaLE_le hmeas (t + (b : ℤ))
      have hmono : sigmaLE X t ≤ sigmaLE X (t + (b : ℤ)) :=
        iSup₂_le fun s hs => le_iSup₂_of_le s
          (Set.mem_Iic.mpr (le_trans (Set.mem_Iic.mp hs) (by omega))) le_rfl
      set Δ : ℕ := a - b with hΔ
      have hcast : t + (a : ℤ) = (t + (b : ℤ)) + (Δ : ℤ) := by
        have h1 : (Δ : ℤ) = (a : ℤ) - (b : ℤ) := by rw [hΔ, Nat.cast_sub hba.le]
        omega
      set g : ℝ → ℝ := fun x => ∫ y, f a y ∂((κ ^ Δ) x) with hg
      have hgm : Measurable g := measurable_kernel_integral Δ (hfm a)
      have hgb : ∀ x, |g x| ≤ 1 := fun x => abs_kernel_integral_le Δ (hfb a) x
      set f' : ℕ → ℝ → ℝ := fun s => if s = b then (fun x => f b x * g x) else f s with hf'
      have hf'm : ∀ s, Measurable (f' s) := by
        intro s
        by_cases hs : s = b
        · simp only [hf', hs, if_pos rfl]; exact (hfm b).mul hgm
        · simp only [hf', if_neg hs]; exact hfm s
      have hf'b : ∀ s y, |f' s y| ≤ 1 := by
        intro s y
        by_cases hs : s = b
        · simp only [hf', hs, if_pos rfl, abs_mul]
          have h1 := hfb b y
          have h2 := hgb y
          nlinarith [abs_nonneg (f b y), abs_nonneg (g y)]
        · simp only [hf', if_neg hs]; exact hfb s y
      obtain ⟨G, hGm, hGb, hGe⟩ := ih f' hf'm hf'b
      refine ⟨G, hGm, hGb, ?_⟩
      set P : Ω → ℝ := fun ω => ∏ s ∈ S, f s (X (t + (s : ℤ)) ω) with hP
      set Q : Ω → ℝ := fun ω => f a (X (t + (a : ℤ)) ω) with hQ
      have hPmeas : StronglyMeasurable[sigmaLE X (t + (b : ℤ))] P := by
        refine Measurable.stronglyMeasurable ?_
        rw [hP]
        refine Finset.measurable_prod S fun s hs => ?_
        have hcs : MeasurableSpace.comap (X (t + (s : ℤ))) inferInstance
            ≤ sigmaLE X (t + (b : ℤ)) :=
          le_iSup₂_of_le (t + (s : ℤ)) (Set.mem_Iic.mpr (by
            have := hbmax s hs; omega)) le_rfl
        exact (hfm s).comp (Measurable.of_comap_le hcs)
      have hPb : ∀ ω, |P ω| ≤ 1 := by
        intro ω
        rw [hP]
        calc |∏ s ∈ S, f s (X (t + (s : ℤ)) ω)| = ∏ s ∈ S, |f s (X (t + (s : ℤ)) ω)| :=
              Finset.abs_prod _ _
          _ ≤ 1 := Finset.prod_le_one (fun s _ => abs_nonneg _) (fun s _ => hfb s _)
      have hQint : Integrable Q μ := by
        rw [hQ]; exact integrable_bdd_comp μ (hmeas _) (hfm a) (hfb a)
      have hpull : μ[P * Q | sigmaLE X (t + (b : ℤ))]
          =ᵐ[μ] P * μ[Q | sigmaLE X (t + (b : ℤ))] :=
        condExp_stronglyMeasurable_mul_of_bound₀ hmb hPmeas.aestronglyMeasurable hQint 1
          (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hPb ω)
      have hQc : μ[Q | sigmaLE X (t + (b : ℤ))] =ᵐ[μ] fun ω => g (X (t + (b : ℤ)) ω) := by
        rw [hQ, hcast, hg]
        exact condExp_bdd_eq_kernel_integral hmeas hmarkov (t + (b : ℤ)) Δ (hfm a) (hfb a)
      have hprod : ∀ ω, P ω * g (X (t + (b : ℤ)) ω)
          = ∏ s ∈ S, f' s (X (t + (s : ℤ)) ω) := by
        intro ω
        have hPw : P ω = ∏ s ∈ S, f s (X (t + (s : ℤ)) ω) := rfl
        rw [hPw, ← Finset.mul_prod_erase S (fun s => f' s (X (t + (s : ℤ)) ω)) hbmem,
          ← Finset.mul_prod_erase S (fun s => f s (X (t + (s : ℤ)) ω)) hbmem]
        have herase : ∏ s ∈ S.erase b, f' s (X (t + (s : ℤ)) ω)
            = ∏ s ∈ S.erase b, f s (X (t + (s : ℤ)) ω) :=
          Finset.prod_congr rfl fun s hs => by
            simp only [hf', if_neg (Finset.ne_of_mem_erase hs)]
        rw [herase]
        simp only [hf', if_pos rfl]
        ring
      have hY : (fun ω => ∏ s ∈ insert a S, f s (X (t + (s : ℤ)) ω)) = P * Q := by
        funext ω
        simp only [Pi.mul_apply, hP, hQ, Finset.prod_insert haS]
        ring
      rw [hY]
      refine Filter.EventuallyEq.trans ?_ hGe
      refine Filter.EventuallyEq.trans (condExp_condExp_of_le hmono hmb).symm ?_
      refine condExp_congr_ae ?_
      filter_upwards [hpull, hQc] with ω h1 h2
      calc (μ[P * Q | sigmaLE X (t + (b : ℤ))]) ω
          = P ω * (μ[Q | sigmaLE X (t + (b : ℤ))]) ω := h1
        _ = P ω * g (X (t + (b : ℤ)) ω) := by rw [h2]
        _ = ∏ s ∈ S, f' s (X (t + (s : ℤ)) ω) := hprod ω

/-- The π-system of finite-dimensional cylinders on the coordinates at times `≥ t`. -/
private def futureCyl (X : ℤ → Ω → ℝ) (t : ℤ) : Set (Set Ω) :=
  {A | ∃ (S : Finset ℕ) (B : ℕ → Set ℝ), (∀ s, MeasurableSet (B s)) ∧
    A = ⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)}

omit [MeasurableSpace Ω] in
private lemma isPiSystem_futureCyl (X : ℤ → Ω → ℝ) (t : ℤ) : IsPiSystem (futureCyl X t) := by
  classical
  rintro A ⟨S₁, B₁, hB₁, rfl⟩ D ⟨S₂, B₂, hB₂, rfl⟩ -
  refine ⟨S₁ ∪ S₂, fun s => (if s ∈ S₁ then B₁ s else Set.univ)
    ∩ (if s ∈ S₂ then B₂ s else Set.univ), fun s => ?_, ?_⟩
  · exact MeasurableSet.inter (by by_cases h : s ∈ S₁ <;> simp [h, hB₁ s])
      (by by_cases h : s ∈ S₂ <;> simp [h, hB₂ s])
  · ext ω
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩ s hs
      refine ⟨?_, ?_⟩
      · by_cases h : s ∈ S₁
        · simpa only [if_pos h] using h1 s h
        · simp [h]
      · by_cases h : s ∈ S₂
        · simpa only [if_pos h] using h2 s h
        · simp [h]
    · intro h
      refine ⟨fun s hs => ?_, fun s hs => ?_⟩
      · have := (h s (Or.inl hs)).1
        simpa only [if_pos hs] using this
      · have := (h s (Or.inr hs)).2
        simpa only [if_pos hs] using this

private lemma measurableSet_futureCyl {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    {t : ℤ} {A : Set Ω} (hA : A ∈ futureCyl X t) : MeasurableSet A := by
  obtain ⟨S, B, hB, rfl⟩ := hA
  exact Finset.measurableSet_biInter S fun s _ => (hmeas _) (hB s)

private lemma sigmaGE_eq_generateFrom {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaGE X t = MeasurableSpace.generateFrom (futureCyl X t) := by
  refine le_antisymm (iSup₂_le fun s hs => ?_) (MeasurableSpace.generateFrom_le fun A hA => ?_)
  · intro A hA
    obtain ⟨B, hB, rfl⟩ := hA
    have hn : t + (((s - t).toNat : ℕ) : ℤ) = s := by
      have := Set.mem_Ici.mp hs; omega
    refine MeasurableSpace.measurableSet_generateFrom
      ⟨{(s - t).toNat}, fun _ => B, fun _ => hB, ?_⟩
    simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left]
    rw [hn]
  · obtain ⟨S, B, hB, rfl⟩ := hA
    refine Finset.measurableSet_biInter S fun s _ => ?_
    have hle : MeasurableSpace.comap (X (t + (s : ℤ))) inferInstance ≤ sigmaGE X t :=
      le_iSup₂_of_le (t + (s : ℤ)) (Set.mem_Ici.mpr (by omega)) le_rfl
    exact hle _ ⟨B s, hB s, rfl⟩

omit [MeasurableSpace Ω] in
private lemma indicator_biInter_eq_prod {X : ℤ → Ω → ℝ} (t : ℤ) (S : Finset ℕ) (B : ℕ → Set ℝ)
    (ω : Ω) :
    (⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)).indicator (fun _ => (1 : ℝ)) ω
      = ∏ s ∈ S, (B s).indicator (fun _ => (1 : ℝ)) (X (t + (s : ℤ)) ω) := by
  by_cases h : ω ∈ ⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)
  · rw [Set.indicator_of_mem h]
    refine (Finset.prod_eq_one fun s hs => ?_).symm
    have hm := Set.mem_iInter₂.mp h s hs
    simp [Set.indicator_of_mem (Set.mem_preimage.mp hm)]
  · rw [Set.indicator_of_notMem h]
    obtain ⟨s, hs, hns⟩ : ∃ s ∈ S, X (t + (s : ℤ)) ω ∉ B s := by
      by_contra hc
      refine h (Set.mem_iInter₂.mpr fun s hs => ?_)
      by_contra hns
      exact hc ⟨s, hs, hns⟩
    exact (Finset.prod_eq_zero hs (by simp [Set.indicator_of_notMem hns])).symm

private lemma setIntegral_condExp_indicator_all [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    {κ : Kernel ℝ ℝ} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ) (t : ℤ) :
    ∀ A : Set Ω, MeasurableSet[sigmaGE X t] A →
      ∀ D : Set Ω, MeasurableSet[sigmaLE X t] D →
        ∫ ω in A, (μ[D.indicator (fun _ => (1 : ℝ))
            | MeasurableSpace.comap (X t) inferInstance]) ω ∂μ = (μ (A ∩ D)).toReal := by
  have hmt := sigmaLE_le hmeas t
  have hGE : sigmaGE X t ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup₂_le fun s _ => (hmeas s).comap_le
  have hG : MeasurableSpace.comap (X t) (inferInstance : MeasurableSpace ℝ)
      ≤ (inferInstance : MeasurableSpace Ω) := (hmeas t).comap_le
  have hGt : MeasurableSpace.comap (X t) (inferInstance : MeasurableSpace ℝ) ≤ sigmaLE X t :=
    le_iSup₂_of_le t (Set.mem_Iic.mpr le_rfl) le_rfl
  refine MeasurableSpace.induction_on_inter
    (C := fun A _ => ∀ D : Set Ω, MeasurableSet[sigmaLE X t] D →
      ∫ ω in A, (μ[D.indicator (fun _ => (1 : ℝ))
          | MeasurableSpace.comap (X t) inferInstance]) ω ∂μ = (μ (A ∩ D)).toReal)
    (sigmaGE_eq_generateFrom hmeas t) (isPiSystem_futureCyl X t) ?_ ?_ ?_ ?_
  · intro D _; simp
  · rintro A ⟨S, B, hB, rfl⟩ D hD
    have hAm : MeasurableSet (⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)) :=
      measurableSet_futureCyl hmeas ⟨S, B, hB, rfl⟩
    have hDm : MeasurableSet D := hmt _ hD
    obtain ⟨G, hGm, hGb, hGe⟩ := condExp_prod_future hmeas hmarkov t S
      (fun s => (B s).indicator (fun _ => (1 : ℝ)))
      (fun s => measurable_const.indicator (hB s))
      (fun s y => by
        by_cases hy : y ∈ B s <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy])
    have hind : (⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)).indicator (fun _ => (1 : ℝ))
        = fun ω => ∏ s ∈ S, (B s).indicator (fun _ => (1 : ℝ)) (X (t + (s : ℤ)) ω) :=
      funext fun ω => indicator_biInter_eq_prod t S B ω
    have hcond_mt : μ[(⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)).indicator (fun _ => (1 : ℝ))
        | sigmaLE X t] =ᵐ[μ] fun ω => G (X t ω) := by rw [hind]; exact hGe
    have hGsm : StronglyMeasurable[MeasurableSpace.comap (X t) inferInstance]
        fun ω => G (X t ω) :=
      (hGm.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
    have hGint : Integrable (fun ω => G (X t ω)) μ := integrable_bdd_comp μ (hmeas t) hGm hGb
    have hcond_G : μ[(⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)).indicator (fun _ => (1 : ℝ))
        | MeasurableSpace.comap (X t) inferInstance] =ᵐ[μ] fun ω => G (X t ω) := by
      refine Filter.EventuallyEq.trans (condExp_condExp_of_le hGt hmt).symm ?_
      refine Filter.EventuallyEq.trans (condExp_congr_ae hcond_mt) ?_
      rw [condExp_of_stronglyMeasurable hG hGsm hGint]
    have hIAint : Integrable ((⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)).indicator
        (fun _ => (1 : ℝ))) μ := (integrable_const (1 : ℝ)).indicator hAm
    calc ∫ ω in ⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s),
            (μ[D.indicator (fun _ => (1 : ℝ))
              | MeasurableSpace.comap (X t) inferInstance]) ω ∂μ
        = ∫ ω in D, (μ[(⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)).indicator (fun _ => (1 : ℝ))
              | MeasurableSpace.comap (X t) inferInstance]) ω ∂μ :=
          (setIntegral_condExp_indicator_symm hG hAm hDm).symm
      _ = ∫ ω in D, (μ[(⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)).indicator (fun _ => (1 : ℝ))
              | sigmaLE X t]) ω ∂μ := by
          refine setIntegral_congr_ae hDm ?_
          filter_upwards [hcond_G, hcond_mt] with ω e1 e2 using fun _ => by rw [e1, e2]
      _ = ∫ ω in D, (⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)).indicator (fun _ => (1 : ℝ)) ω ∂μ :=
          setIntegral_condExp hmt hIAint hD
      _ = (μ ((⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)) ∩ D)).toReal := by
          rw [integral_indicator_const (1 : ℝ) hAm]
          simp [Measure.real, Measure.restrict_apply hAm, Set.inter_comm]
  · intro A hAs ih D hD
    have hAm : MeasurableSet A := hGE _ hAs
    have hDm : MeasurableSet D := hmt _ hD
    have hhint : Integrable (μ[D.indicator (fun _ => (1 : ℝ))
        | MeasurableSpace.comap (X t) inferInstance]) μ := integrable_condExp
    have htot : ∫ ω, (μ[D.indicator (fun _ => (1 : ℝ))
        | MeasurableSpace.comap (X t) inferInstance]) ω ∂μ = (μ D).toReal := by
      rw [integral_condExp hG, integral_indicator_const (1 : ℝ) hDm]
      simp [Measure.real]
    have hsplit := integral_add_compl hAm hhint
    have hmsplit : (μ (A ∩ D)).toReal + (μ (Aᶜ ∩ D)).toReal = (μ D).toReal := by
      have h1 : μ (D ∩ A) + μ (D \ A) = μ D := measure_inter_add_diff D hAm
      have h2 : D \ A = Aᶜ ∩ D := by ext ω; simp [Set.mem_diff, and_comm]
      rw [h2, Set.inter_comm D A] at h1
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h1]
    rw [ih D hD, htot] at hsplit
    linarith
  · intro fs hdisj hfm ih D hD
    have hDm : MeasurableSet D := hmt _ hD
    have hfmΩ : ∀ i, MeasurableSet (fs i) := fun i => hGE _ (hfm i)
    have hhint : Integrable (μ[D.indicator (fun _ => (1 : ℝ))
        | MeasurableSpace.comap (X t) inferInstance]) μ := integrable_condExp
    rw [integral_iUnion hfmΩ hdisj hhint.integrableOn, tsum_congr fun i => ih i D hD,
      Set.iUnion_inter,
      measure_iUnion (fun i j hij => (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left)
        (fun i => (hfmΩ i).inter hDm)]
    exact (ENNReal.tsum_toReal_eq fun i => measure_ne_top _ _).symm


end MarkovFuture

/-- **BRICK — the two-marginal reduction for `β`** (Bradley Thms 4.1–4.2, the β-analogue of
`alphaCoeff_eq_two_marginal_debt`).

Its content is *exactly* `condExp_sigmaGE_indicator_brick` again — the Markov property for
the whole future σ-algebra — combined with the β-version of the one-sided optimisation: for
a partition pair the sum `Σ_{ij} |P(A_i ∩ B_j) − P(A_i)P(B_j)|` is `Σ_i P(A_i) · ‖P(· | A_i)
− P‖` on the future, and each conditional law only sees `X_0` once the brick is available.
Recorded separately so that the two halves of the (2.58) debt are visible. -/
private lemma betaMixCoeff_two_marginal_brick [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {κ : ProbabilityTheory.Kernel ℝ ℝ} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ) (n : ℕ) :
    betaMixCoeff μ (sigmaLE X 0) (sigmaGE X (n : ℤ))
      = betaMixCoeff μ (MeasurableSpace.comap (X 0) inferInstance)
          (MeasurableSpace.comap (X (n : ℤ)) inferInstance) := by
  sorry

/-- **BRICK — Davydov's identity at the two-marginal level** (FY eq. (2.58) proper).

`β(σ(X_0), σ(X_n)) = ∫ tvDist (κⁿ x) F dF(x)`.

**Calibration (checked).** `betaMixCoeff` is the half-sum `½ sup Σ_{ij} |P(A_i ∩ B_j) −
P(A_i)P(B_j)|` and `tvDist` is the *sup-over-events* distance `sup_B (P B − Q B)`, i.e.
half of the total-mass norm. Writing `P(A_i ∩ B_j) = ∫_{U_i} (κⁿ x)(V_j) dF(x)` with
`A_i = X_0⁻¹(U_i)`, `B_j = X_n⁻¹(V_j)` and `P(B_j) = F(V_j)` (strict stationarity), the
partition sum is `Σ_j Σ_i |∫_{U_i} ((κⁿ x)(V_j) − F(V_j)) dF(x)| ≤ ∫ Σ_j |(κⁿ x)(V_j) −
F(V_j)| dF(x) ≤ ∫ 2 · tvDist (κⁿ x) F dF(x)`, so the half-sum is `≤ ∫ tvDist dF`: the
statement carries **no factor 2**, confirming the module docstring's warning.

**Intended proof.**
* `≤` — the display above. Its ingredients are all available: `IsMarkovOf` at `t = 0`
  gives `μ[1_{V}(X_n) | 𝓕_{-∞}^0] = (κⁿ (X_0))(V)` and hence, by `setIntegral_condExp` on
  `A_i ∈ σ(X_0) ⊆ 𝓕_{-∞}^0` and the change of variables along `X_0`, the displayed formula
  for `P(A_i ∩ B_j)`; the `U_i` (resp. `V_j`) may be taken pairwise disjoint after
  replacing `U_i` by `U_i \ ⋃_{i' < i} U_{i'}` (preimages are unchanged, by disjointness of
  the `A_i`); and `Σ_j |P(V_j) − Q(V_j)| ≤ 2 · tvDist P Q` for a disjoint family follows by
  splitting the `j`'s by sign and applying the definition of `tvDist` to the two unions
  (using `tvDist_comm` on the negative half).
* `≥` — for each `x`, a Hahn set `H_x` for `κⁿ(x, ·) − F` attains `tvDist`; the set
  `⋃_x {x} × H_x` is measurable by `measurable_tvDist_kernel`-style arguments and is
  approximated in `F ⊗ F`-measure by finite unions of rectangles `U_i × V_j`, whose
  induced two-cell partitions realise the supremum in the limit. This half is the genuinely
  hard one (it is where the finite-partition formula meets the disintegration). -/
private lemma betaMixCoeff_two_marginal_eq_integral_tvDist_brick [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {κ : ProbabilityTheory.Kernel ℝ ℝ} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ) (n : ℕ) :
    betaMixCoeff μ (MeasurableSpace.comap (X 0) inferInstance)
        (MeasurableSpace.comap (X (n : ℤ)) inferInstance)
      = (∫⁻ x, StatLean.Minimaxity.tvDist ((κ ^ n) x) (μ.map (X 0))
          ∂(μ.map (X 0))).toReal := by
  sorry

/-- **DEBT (Davydov 1973; FY eq. (2.58))**: for a strictly stationary Markov process
with kernel `κ` and time-`0` marginal `F = μ ∘ X_0⁻¹`,
`β(n) = ∫ tvDist (κⁿ x) F dF(x)` (sup-over-events normalization — see the module
docstring's calibration warning).

**Status (2026-08-09).** Split into its two independent halves,
`betaMixCoeff_two_marginal_brick` (Bradley's collapse to the two marginals — the *same*
Markov-property content as `condExp_sigmaGE_indicator_brick`) and
`betaMixCoeff_two_marginal_eq_integral_tvDist_brick` (Davydov's identity proper, whose
docstring records the verified calibration and the proof of each direction). -/
theorem betaCoeff_eq_integral_tvDist_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {κ : ProbabilityTheory.Kernel ℝ ℝ} [ProbabilityTheory.IsMarkovKernel κ]
    -- USER-INPUT: Markov representation; FY §2.6.1(vi) setting
    (hmarkov : IsMarkovOf X κ μ) (n : ℕ) :
    betaCoeff X μ n
      = (∫⁻ x, StatLean.Minimaxity.tvDist ((κ ^ n) x) (μ.map (X 0))
          ∂(μ.map (X 0))).toReal := by
  rw [betaCoeff, betaMixCoeff_two_marginal_brick hmeas hstat hmarkov n,
    betaMixCoeff_two_marginal_eq_integral_tvDist_brick hmeas hstat hmarkov n]

/-- **FY eq. (2.59), derived from the (2.58) debt**: a pointwise geometric envelope
`tvDist (κⁿ x) F ≤ A(x) ρⁿ` with `A` integrable gives `β(n) ≤ ρⁿ ∫ A dF`; in
particular the process is (exponentially) β-mixing. -/
theorem isBetaMixing_of_geometric_envelope [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {κ : ProbabilityTheory.Kernel ℝ ℝ} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ)
    {A : ℝ → ℝ} (hA : Measurable A) (hA0 : ∀ x, 0 ≤ A x)
    (hAint : Integrable A (μ.map (X 0)))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    -- USER-INPUT: geometric TV envelope; FY eq. (2.59)
    (henv : ∀ (x : ℝ) (n : ℕ),
      StatLean.Minimaxity.tvDist ((κ ^ n) x) (μ.map (X 0))
        ≤ ENNReal.ofReal (A x * ρ ^ n)) :
    (∀ n : ℕ, betaCoeff X μ n ≤ (∫ x, A x ∂(μ.map (X 0))) * ρ ^ n) ∧
      IsBetaMixing X μ := by
  set F : Measure ℝ := μ.map (X 0) with hF
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ (∫ x, A x ∂F) * ρ ^ n := fun n =>
    mul_nonneg (integral_nonneg hA0) (pow_nonneg hρ0 n)
  -- (2.59): integrate the pointwise envelope of (2.58).
  have hkey : ∀ n : ℕ, betaCoeff X μ n ≤ (∫ x, A x ∂F) * ρ ^ n := by
    intro n
    rw [betaCoeff_eq_integral_tvDist_debt hmeas hstat hmarkov n]
    have hmono : (∫⁻ x, StatLean.Minimaxity.tvDist ((κ ^ n) x) F ∂F)
        ≤ ∫⁻ x, ENNReal.ofReal (A x * ρ ^ n) ∂F :=
      lintegral_mono fun x => henv x n
    have heq : (∫⁻ x, ENNReal.ofReal (A x * ρ ^ n) ∂F)
        = ENNReal.ofReal ((∫ x, A x ∂F) * ρ ^ n) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hAint.mul_const _)
        (Filter.Eventually.of_forall fun x => mul_nonneg (hA0 x) (pow_nonneg hρ0 n)),
        integral_mul_const]
    have hfin : (∫⁻ x, ENNReal.ofReal (A x * ρ ^ n) ∂F) ≠ ∞ := by
      rw [heq]; exact ENNReal.ofReal_ne_top
    calc (∫⁻ x, StatLean.Minimaxity.tvDist ((κ ^ n) x) F ∂F).toReal
        ≤ (∫⁻ x, ENNReal.ofReal (A x * ρ ^ n) ∂F).toReal := ENNReal.toReal_mono hfin hmono
      _ = (∫ x, A x ∂F) * ρ ^ n := by rw [heq, ENNReal.toReal_ofReal (hnn n)]
  refine ⟨hkey, ?_⟩
  refine squeeze_zero (fun n => ?_) hkey ?_
  · rw [betaCoeff_eq_integral_tvDist_debt hmeas hstat hmarkov n]
    exact ENNReal.toReal_nonneg
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul (∫ x, A x ∂F)
    simpa using this

/-- **BRICK — the Markov property for the whole future σ-algebra** (the only open input of
`alphaCoeff_eq_two_marginal_debt`).

For `B` in the *full* future σ-algebra `𝓕_t^∞ = σ{X_s : s ≥ t}`, the conditional
probability `P(B | 𝓕_{-∞}^t)` is a function of `X_t` alone. The hypothesis `IsMarkovOf`
supplies exactly this for the **one-coordinate** events `B = X_{t+n}⁻¹(B')` (its right-hand
side `(κⁿ (X t ω)) B'` is `σ(X_t)`-measurable by `Kernel.measurable_coe`); the brick is the
extension of that to the σ-algebra they generate.

**Intended proof (three steps).**
1. *Finite intersections.* By induction on the (finite) set `S ⊆ [t, ∞)` of consumed times,
   for `Y = ∏_{s ∈ S} 1_{B_s}(X_s)` the conditional expectation `E[Y | 𝓕_{-∞}^t]` is a.e.
   `σ(X_t)`-measurable: condition first on `𝓕_{-∞}^{s'}`, where `s'` is the second largest
   element of `S`, so that the largest factor collapses by `IsMarkovOf` to
   `g(X_{s'})` with `g x = ((κ^{max S - s'}) x) B_{max S}`; approximate the *bounded
   measurable* `g` by finite-range functions (level-set decomposition), which turns
   `Y' g(X_{s'})` into a finite linear combination of products over `S \ {max S}` (merge the
   level set into `B_{s'}`), and pass to the limit through the `L¹`-contractivity of
   `condExp`.
2. *π-system.* Those products form a π-system generating `sigmaGE X t`.
3. *Dynkin.* The `B`'s satisfying the conclusion form a λ-system (`condExp` is linear,
   monotone and continuous along monotone limits), so `MeasurableSpace.induction_on_inter`
   upgrades step 1 to all of `sigmaGE X t`.

This is the classical statement that the past and the future of a Markov chain are
conditionally independent given the present (Bradley, *Introduction to Strong Mixing
Conditions*, ch. 7); it is genuinely the analytic content of the two-marginal reduction and
is left as a single named debt. Everything else in
`alphaCoeff_eq_two_marginal_debt` is proved from it. -/
private lemma condExp_sigmaGE_indicator_brick [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    {κ : ProbabilityTheory.Kernel ℝ ℝ} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ) (t : ℤ) {B : Set Ω} (hB : MeasurableSet[sigmaGE X t] B) :
    ∃ p : Ω → ℝ, StronglyMeasurable[MeasurableSpace.comap (X t) inferInstance] p ∧
      μ[B.indicator (fun _ => (1:ℝ)) | sigmaLE X t] =ᵐ[μ] p := by
  have hmt := sigmaLE_le hmeas t
  have hGE : sigmaGE X t ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup₂_le fun s _ => (hmeas s).comap_le
  have hG : MeasurableSpace.comap (X t) (inferInstance : MeasurableSpace ℝ)
      ≤ (inferInstance : MeasurableSpace Ω) := (hmeas t).comap_le
  have hGt : MeasurableSpace.comap (X t) (inferInstance : MeasurableSpace ℝ) ≤ sigmaLE X t :=
    le_iSup₂_of_le t (Set.mem_Iic.mpr le_rfl) le_rfl
  have hBm : MeasurableSet B := hGE _ hB
  refine ⟨μ[B.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap (X t) inferInstance],
    stronglyMeasurable_condExp, ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq hmt
    ((integrable_const (1 : ℝ)).indicator hBm)
    (fun s _ _ => integrable_condExp.integrableOn) (fun D hD _ => ?_)
    (stronglyMeasurable_condExp.mono hGt).aestronglyMeasurable).symm
  have hDm : MeasurableSet D := hmt _ hD
  rw [setIntegral_condExp_indicator_symm hG hBm hDm,
    setIntegral_condExp_indicator_all hmeas hmarkov t B hB D hD,
    integral_indicator_const (1 : ℝ) hBm]
  simp [Measure.real, Measure.restrict_apply hBm]

/-- **DEBT (Bradley Thms 4.1–4.2; FY §2.6.1(vi))**: for a strictly stationary Markov
process the α-coefficient collapses to the two-marginal coefficient of `(X_0, X_n)`:
`α(σ{X_s : s ≤ 0}, σ{X_s : s ≥ n}) = α(σ(X_0), σ(X_n))`. (Same statement holds for
β, ρ, φ, ψ; α is the consumed one.)

**Status (2026-08-09).** PROVED over the single named brick
`condExp_sigmaGE_indicator_brick` (the Markov property for the whole future σ-algebra).
The reduction is:

* `≥` is monotonicity of `alphaMixCoeff` in both σ-algebra arguments;
* `≤` is a *two-step one-sided optimisation* (`abs_integral_mul_le_setIntegral`): for
  `A ∈ 𝓕_{-∞}^0`, `B ∈ 𝓕_n^∞`, first replace `A` by
  `A* = {P(B | 𝓕_{-∞}^0) > P(B)} ∈ σ(X_0)` (the brick at `t = 0` puts `A*` in `σ(X_0)`),
  then smooth `1_B` to `w = P(B | 𝓕_{-∞}^n)` — which the brick at `t = n` makes
  `σ(X_n)`-measurable and which lies in `[0,1]` — and replace `B` by
  `B* = {P(A* | σ(X_n)) > P(A*)} ∈ σ(X_n)`. No layer-cake/Fubini and no reverse Markov
  property are needed: the optimisation lemma is stated for an arbitrary `[0,1]`-valued
  test function, which covers both the indicator `1_A` and the conditional probability
  `w`. -/
theorem alphaCoeff_eq_two_marginal_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {κ : ProbabilityTheory.Kernel ℝ ℝ} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ) (n : ℕ) :
    alphaCoeff X μ n
      = alphaMixCoeff μ (MeasurableSpace.comap (X 0) inferInstance)
          (MeasurableSpace.comap (X n) inferInstance) := by
  have hLEΩ : ∀ t : ℤ, sigmaLE X t ≤ (inferInstance : MeasurableSpace Ω) :=
    fun t => iSup₂_le fun s _ => (hmeas s).comap_le
  have hGEΩ : ∀ t : ℤ, sigmaGE X t ≤ (inferInstance : MeasurableSpace Ω) :=
    fun t => iSup₂_le fun s _ => (hmeas s).comap_le
  have hm0le : MeasurableSpace.comap (X 0) inferInstance ≤ sigmaLE X 0 :=
    le_iSup₂_of_le (0 : ℤ) (Set.mem_Iic.mpr le_rfl) le_rfl
  have hm0leN : MeasurableSpace.comap (X 0) inferInstance ≤ sigmaLE X (n : ℤ) :=
    le_iSup₂_of_le (0 : ℤ) (Set.mem_Iic.mpr (Int.natCast_nonneg n)) le_rfl
  have hmnle : MeasurableSpace.comap (X (n : ℤ)) inferInstance ≤ sigmaGE X (n : ℤ) :=
    le_iSup₂_of_le (n : ℤ) (Set.mem_Ici.mpr le_rfl) le_rfl
  have hmnΩ : MeasurableSpace.comap (X (n : ℤ)) inferInstance
      ≤ (inferInstance : MeasurableSpace Ω) := (hmeas _).comap_le
  have hm0Ω : MeasurableSpace.comap (X 0) inferInstance
      ≤ (inferInstance : MeasurableSpace Ω) := (hmeas _).comap_le
  have hGEmono : sigmaGE X (n : ℤ) ≤ sigmaGE X 0 :=
    iSup₂_le fun s hs => le_iSup₂_of_le s
      (Set.mem_Ici.mpr (le_trans (Int.natCast_nonneg n) (Set.mem_Ici.mp hs))) le_rfl
  refine le_antisymm ?_ (alphaMixCoeff_mono' (mΩ := inferInstance) hm0le hmnle)
  refine Real.sSup_le ?_ (alphaMixCoeff_nonneg' (mΩ := inferInstance))
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hAm : MeasurableSet A := hLEΩ 0 _ hA
  have hBm : MeasurableSet B := hGEΩ (n : ℤ) _ hB
  set hB' : Ω → ℝ := fun ω => B.indicator (fun _ => (1:ℝ)) ω - (μ B).toReal with hB'def
  have hB'int : Integrable hB' μ := integrable_centred_indicator hBm
  have hB'0 : ∫ ω, hB' ω ∂μ = 0 := integral_centred_indicator hBm
  -- Step 1: replace `A` by an event of `σ(X 0)`
  obtain ⟨p₀, hp₀m, hp₀e⟩ :=
    condExp_sigmaGE_indicator_brick hmeas hmarkov 0 (hGEmono _ hB)
  have hcond0 : μ[hB'|sigmaLE X 0] =ᵐ[μ] fun ω => p₀ ω - (μ B).toReal := by
    have h1 := condExp_sub (μ := μ) ((integrable_const (1:ℝ)).indicator hBm)
      (integrable_const ((μ B).toReal)) (sigmaLE X 0)
    have h2 : μ[fun _ : Ω => (μ B).toReal|sigmaLE X 0] = fun _ => (μ B).toReal :=
      condExp_const (hLEΩ 0) _
    filter_upwards [h1, hp₀e] with ω e1 e2
    simp only [Pi.sub_apply] at e1
    rw [show hB' = (B.indicator (fun _ => (1:ℝ)) - fun _ => (μ B).toReal) from rfl, e1, h2, e2]
  set A' : Set Ω := {ω | 0 < p₀ ω - (μ B).toReal} with hA'def
  have hA'm₀ : MeasurableSet[MeasurableSpace.comap (X 0) inferInstance] A' :=
    (hp₀m.sub (stronglyMeasurable_const (α := Ω) (b := (μ B).toReal))).measurable
      (measurableSet_Ioi (a := (0:ℝ)))
  have hA'Ω : MeasurableSet A' := hm0Ω _ hA'm₀
  have hstep1 : |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
      ≤ (μ (A' ∩ B)).toReal - (μ A').toReal * (μ B).toReal := by
    have hp₀'m : StronglyMeasurable[MeasurableSpace.comap (X 0) inferInstance]
        (fun ω => p₀ ω - (μ B).toReal) :=
      hp₀m.sub (stronglyMeasurable_const (α := Ω) (b := (μ B).toReal))
    have hL := abs_integral_mul_le_setIntegral (hLEΩ 0) hB'int hB'0
      (hp₀'m.mono hm0le) hcond0
      (stronglyMeasurable_const.indicator hA) (indicator_one_nonneg A)
      (indicator_one_le_one A)
    rw [integral_centred_indicator_mul hAm hBm] at hL
    rw [setIntegral_eq_indicator_mul hA'Ω, integral_centred_indicator_mul hA'Ω hBm] at hL
    exact hL
  -- Step 2: replace `B` by an event of `σ(X n)`
  set hA'' : Ω → ℝ := fun ω => A'.indicator (fun _ => (1:ℝ)) ω - (μ A').toReal with hA''def
  have hA''int : Integrable hA'' μ := integrable_centred_indicator hA'Ω
  have hA''0 : ∫ ω, hA'' ω ∂μ = 0 := integral_centred_indicator hA'Ω
  have hA''sm : StronglyMeasurable[sigmaLE X (n : ℤ)] hA'' :=
    (stronglyMeasurable_const.indicator (hm0leN _ hA'm₀)).sub stronglyMeasurable_const
  obtain ⟨pn, hpnm, hpne⟩ := condExp_sigmaGE_indicator_brick hmeas hmarkov (n : ℤ) hB
  -- `w := μ[1_B | 𝓕_{≤n}]` lies in `[0,1]` a.e.
  have hw0 : (0 : Ω → ℝ) ≤ᵐ[μ] μ[B.indicator (fun _ => (1:ℝ))|sigmaLE X (n : ℤ)] :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => indicator_one_nonneg B ω)
  have hw1 : μ[B.indicator (fun _ => (1:ℝ))|sigmaLE X (n : ℤ)] ≤ᵐ[μ] fun _ => (1:ℝ) := by
    have := condExp_mono (m := sigmaLE X (n : ℤ))
      ((integrable_const (μ := μ) (1:ℝ)).indicator hBm) (integrable_const (μ := μ) (1:ℝ))
      (Filter.Eventually.of_forall fun ω => indicator_one_le_one B ω)
    rw [condExp_const (μ := μ) (hLEΩ (n : ℤ))] at this
    exact this
  set Y : Ω → ℝ := fun ω => max 0 (min 1 (pn ω)) with hYdef
  have hYsm : StronglyMeasurable[MeasurableSpace.comap (X (n : ℤ)) inferInstance] Y :=
    (Measurable.max measurable_const (Measurable.min measurable_const hpnm.measurable)).stronglyMeasurable
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => le_max_left _ _
  have hY1 : ∀ ω, Y ω ≤ 1 := fun ω => max_le zero_le_one (min_le_left _ _)
  have hYw : Y =ᵐ[μ] μ[B.indicator (fun _ => (1:ℝ))|sigmaLE X (n : ℤ)] := by
    filter_upwards [hw0, hw1, hpne] with ω e0 e1 e2
    have e0' : (0:ℝ) ≤ pn ω := by rw [← e2]; exact e0
    have e1' : pn ω ≤ 1 := by rw [← e2]; exact e1
    rw [hYdef]
    simp only
    rw [min_eq_right e1', max_eq_right e0', e2]
  -- transfer the covariance onto `Y`
  have hkey : (μ (A' ∩ B)).toReal - (μ A').toReal * (μ B).toReal = ∫ ω, Y ω * hA'' ω ∂μ := by
    have e1 : ∫ ω, hA'' ω * B.indicator (fun _ => (1:ℝ)) ω ∂μ
        = ∫ ω, hA'' ω * (μ[B.indicator (fun _ => (1:ℝ))|sigmaLE X (n : ℤ)]) ω ∂μ := by
      have hpull := condExp_stronglyMeasurable_mul_of_bound₀ (hLEΩ (n : ℤ))
        hA''sm.aestronglyMeasurable ((integrable_const (μ := μ) (1:ℝ)).indicator hBm) 1
        (Filter.Eventually.of_forall fun ω => norm_centred_indicator_le_one A' ω)
      calc ∫ ω, hA'' ω * B.indicator (fun _ => (1:ℝ)) ω ∂μ
          = ∫ ω, (μ[hA'' * B.indicator (fun _ => (1:ℝ))|sigmaLE X (n : ℤ)]) ω ∂μ :=
            (integral_condExp (hLEΩ (n : ℤ))).symm
        _ = ∫ ω, hA'' ω * (μ[B.indicator (fun _ => (1:ℝ))|sigmaLE X (n : ℤ)]) ω ∂μ :=
            integral_congr_ae (by filter_upwards [hpull] with ω hω using hω)
    have e2 : ∫ ω, hA'' ω * (μ[B.indicator (fun _ => (1:ℝ))|sigmaLE X (n : ℤ)]) ω ∂μ
        = ∫ ω, Y ω * hA'' ω ∂μ :=
      integral_congr_ae (by filter_upwards [hYw] with ω hω using by rw [hω]; ring)
    rw [← e2, ← e1]
    have := integral_centred_indicator_mul (μ := μ) hBm hA'Ω
    rw [Set.inter_comm B A'] at this
    rw [show (fun ω => hA'' ω * B.indicator (fun _ => (1:ℝ)) ω)
        = fun ω => B.indicator (fun _ => (1:ℝ)) ω * hA'' ω from funext fun ω => mul_comm _ _]
    rw [this]
    ring
  -- final one-sided optimisation on the `n`-side
  have hL2 := abs_integral_mul_le_setIntegral hmnΩ hA''int hA''0
    (stronglyMeasurable_condExp) (Filter.EventuallyEq.refl _ _) hYsm hY0 hY1
  set B' : Set Ω := {ω | 0 < (μ[hA''|MeasurableSpace.comap (X (n : ℤ)) inferInstance]) ω}
    with hB'sdef
  have hB'm : MeasurableSet[MeasurableSpace.comap (X (n : ℤ)) inferInstance] B' :=
    stronglyMeasurable_condExp.measurable (measurableSet_Ioi (a := (0:ℝ)))
  have hB'Ω : MeasurableSet B' := hmnΩ _ hB'm
  rw [setIntegral_eq_indicator_mul hB'Ω, integral_centred_indicator_mul hB'Ω hA'Ω] at hL2
  refine hstep1.trans ?_
  rw [hkey]
  refine (le_abs_self _).trans (hL2.trans ?_)
  have := le_alphaMixCoeff (mΩ := (inferInstance : MeasurableSpace Ω)) (μ := μ)
    hA'm₀ hB'm
  rw [abs_le] at this
  rw [Set.inter_comm B' A', mul_comm]
  exact this.2

end StatLean.TimeSeries
