import StatLean.TimeSeries.Mixing.Defs
import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity

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

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **Markov representation** hypothesis tying a real-valued process to a kernel:
the conditional law of `X_{t+n}` given the past through time `t` is `κⁿ(X_t, ·)`,
expressed through conditional expectations of indicators. -/
def IsMarkovOf (X : ℤ → Ω → ℝ) (κ : ProbabilityTheory.Kernel ℝ ℝ) (μ : Measure Ω) :
    Prop :=
  ∀ (t : ℤ) (n : ℕ) (B : Set ℝ), MeasurableSet B →
    (μ[fun ω => (B.indicator (fun _ => (1 : ℝ)) (X (t + n) ω)) | sigmaLE X t])
      =ᵐ[μ] fun ω => (((κ ^ n) (X t ω)) B).toReal

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
  sorry

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
