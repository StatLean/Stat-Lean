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
  `(X_0, X_n)`. **Both the α- and the β-case are proved here** (2026-08-09; the β-case
  2026-08-09, wave 4).

**Status (2026-08-09, wave 5): the whole bridge is now stated over an arbitrary measurable
state space `E`** (`IsMarkovOf : (ℤ → Ω → E) → Kernel E E → Measure Ω → Prop`, with
`sigmaLE'`/`sigmaGE'` the state-space-free forms of `Process/Defs.lean`'s
`sigmaLE`/`sigmaGE`, definitionally equal to them at `E = ℝ`). Nothing in the proofs used
any property of `ℝ` beyond measurability, so the generalisation is a change of statements
only; the frozen real-valued theorems (`alphaCoeff_eq_two_marginal_debt`,
`betaCoeff_eq_integral_tvDist_debt`, `isBetaMixing_of_geometric_envelope`) are kept as
`E = ℝ` corollaries. Two by-products of the generalisation:

* strict stationarity turned out to be **unused** by the Bradley reduction (α and β), and
  Davydov's identity only needs *equality of the one-dimensional marginals*, so both are
  now stated with `hmarg : ∀ s t, μ.map (X s) = μ.map (X t)`, which
  `map_eq_map_of_isStrictlyStationary` supplies in the scalar case;
* new, **`sorry`-free α- and β-routes** to the model statements —
  `alphaMixCoeff_two_marginal_le_of_envelope` (the inequality half of (2.58) at the α
  level), `alphaMixCoeff_le_of_measurable_state` (process σ-algebras sit inside state
  σ-algebras) and their composite `alphaCoeff_le_of_state_envelope`, which turns a
  geometric TV envelope for the state kernel into `α_Y(n) ≤ C ρ^{n−1}` for the observed
  series, plus the β-analogues `betaMixCoeff_two_marginal_le_of_envelope` (the `≤` half of
  (2.58), which needs no Hahn selection) and `betaCoeff_le_of_state_envelope`. **Neither
  route passes through the open Davydov brick.**

**Status (2026-08-09, wave 4).** Two of the three bricks are now **PROVED** and
`alphaCoeff_eq_two_marginal_debt` is axiom-clean:

* `condExp_sigmaGE_indicator_brick` — the Markov property for the whole future σ-algebra
  (`IsMarkovOf` only supplies it one coordinate at a time). Proved in three layers inside
  `section MarkovFuture`: the bounded-test-function form of the Markov property
  (`condExp_bdd_eq_kernel_integral`, obtained *without* simple-function approximation by
  identifying two measures on `ℝ` and integrating against the equal measures), the
  finite-product induction over the consumed offsets (`condExp_prod_future`, run by
  `Finset.induction_on_max`, merging each collapsed kernel average into the coefficient at
  the second largest time), and a Dynkin step carried in the *set-integral* form
  `∫_A E[1_D|σ(X_t)] = P(A ∩ D)` (`setIntegral_condExp_indicator_all`), which is countably
  additive in `A` as a plain integral and therefore needs no L¹ limit of conditional
  expectations. The two forms are exchanged by the symmetric pull-out
  `∫_D E[1_A|𝒢] = ∫ E[1_A|𝒢]·E[1_D|𝒢] = ∫_A E[1_D|𝒢]`.
* `betaMixCoeff_two_marginal_brick` — the β-form of the Bradley reduction. Proved in
  `section BetaShrink` from two *shrinking* lemmas plus a sign-pattern partition:
  `beta_shrink_left` replaces the past-side partition by the σ(X_0)-partition cut out by
  the signs of the conditional probabilities of the future cells, and `beta_shrink_right`
  replaces the future-side partition by the σ(X_n)-partition cut out by the signs of the
  σ(X_n)-conditioned first-side covariances — the second step goes through the *partition
  of unity* `r_j = E[1_{B_j} | 𝓕_{≤n}]` (which is σ(X_n)-measurable by the Markov property
  at time `n`, sums to `1`, and is nonnegative), so **no reverse Markov property is
  needed**. Both steps only *increase* the partition sum, so the sup collapses.

**Status (2026-08-09, wave 6): the one open brick is FALSE AS FROZEN.**
`betaMixCoeff_two_marginal_eq_integral_tvDist_brick`, and with it the public
`betaMixCoeff_eq_integral_tvDist_of_markov`, are refuted at a general state space by the
countable–cocountable witness of `section DavydovWitness`
(`betaMixCoeff_two_marginal_eq_integral_tvDist_false`,
`betaMixCoeff_eq_integral_tvDist_of_markov_false`, both axiom-clean): the two sides come
out `0` and `1`. The repair is to add `[MeasurableSpace.CountablyGenerated E]` — the
hypothesis under which the `≥` half's jointly measurable Hahn selection exists. Since the
statements are frozen the `sorry` stays; it is a statement debt, not a proof debt. Nothing
downstream uses the identity (the model routes use the *inequality*
`betaMixCoeff_two_marginal_le_of_envelope`, which is correct at a general `E`).

**The one open brick** is `betaMixCoeff_two_marginal_eq_integral_tvDist_brick` (Davydov's
identity proper — note that wave 5's `betaMixCoeff_two_marginal_le_of_envelope` proves its
`≤` half in envelope form, so nothing downstream depends on it any more; its docstring records the *verified* calibration demanded below and the
proof of each direction — the `≥` half, which needs a measurable Hahn decomposition for
`κⁿ(x,·) − F` approximated by rectangles, is the genuinely hard one).

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

section BetaShrink
variable {Ω : Type*}

/-- Integrating over the cells of a finite measurable partition recovers the integral. -/
private lemma sum_setIntegral_partition {𝒩 mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (h𝒩 : 𝒩 ≤ mΩ) {K : ℕ} {S : Fin K → Set Ω} (hSm : ∀ k, MeasurableSet[𝒩] (S k))
    (hSd : Pairwise fun k k' => Disjoint (S k) (S k')) (hSc : (⋃ k, S k) = Set.univ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∑ k, ∫ ω in S k, f ω ∂μ = ∫ ω, f ω ∂μ := by
  classical
  have hSmΩ : ∀ k, MeasurableSet (S k) := fun k => h𝒩 _ (hSm k)
  calc ∑ k, ∫ ω in S k, f ω ∂μ = ∑ k, ∫ ω, (S k).indicator f ω ∂μ :=
        Finset.sum_congr rfl fun k _ => (integral_indicator (hSmΩ k)).symm
    _ = ∫ ω, ∑ k, (S k).indicator f ω ∂μ :=
        (integral_finset_sum _ fun k _ => hf.indicator (hSmΩ k)).symm
    _ = ∫ ω, f ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        show ∑ k, (S k).indicator f ω = f ω
        obtain ⟨k, hk⟩ : ∃ k, ω ∈ S k := by
          have hu : ω ∈ ⋃ k, S k := hSc ▸ Set.mem_univ ω
          simpa using hu
        rw [Finset.sum_eq_single k]
        · rw [Set.indicator_of_mem hk]
        · intro k' _ hne
          exact Set.indicator_of_notMem (Set.disjoint_left.mp (hSd (Ne.symm hne)) hk) f
        · intro hc; exact absurd (Finset.mem_univ k) hc

private lemma sum_abs_setIntegral_le {𝒩 mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (h𝒩 : 𝒩 ≤ mΩ) {K : ℕ} {S : Fin K → Set Ω} (hSm : ∀ k, MeasurableSet[𝒩] (S k))
    (hSd : Pairwise fun k k' => Disjoint (S k) (S k')) (hSc : (⋃ k, S k) = Set.univ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∑ k, |∫ ω in S k, f ω ∂μ| ≤ ∫ ω, |f ω| ∂μ := by
  calc ∑ k, |∫ ω in S k, f ω ∂μ| ≤ ∑ k, ∫ ω in S k, |f ω| ∂μ :=
        Finset.sum_le_sum fun k _ => abs_integral_le_integral_abs
    _ = ∫ ω, |f ω| ∂μ := sum_setIntegral_partition h𝒩 hSm hSd hSc hf.abs

/-! ### Sign sets -/

/-- The two sign half-spaces of a real function, indexed by a `Bool`. -/
private def signSet (f : Ω → ℝ) (u : Bool) : Set Ω :=
  if u then {ω | 0 ≤ f ω} else {ω | f ω < 0}

private lemma signSet_true (f : Ω → ℝ) : signSet f true = {ω | 0 ≤ f ω} := by
  simp [signSet]

private lemma signSet_false (f : Ω → ℝ) : signSet f false = {ω | f ω < 0} := by
  simp [signSet]

private lemma measurableSet_signSet {𝒩 : MeasurableSpace Ω} {f : Ω → ℝ}
    (hf : Measurable[𝒩] f) (u : Bool) : MeasurableSet[𝒩] (signSet f u) := by
  cases u
  · rw [signSet_false]; exact hf measurableSet_Iio
  · rw [signSet_true]; exact hf measurableSet_Ici

private lemma disjoint_signSet (f : Ω → ℝ) {u v : Bool} (huv : u ≠ v) :
    Disjoint (signSet f u) (signSet f v) := by
  cases u <;> cases v
  · exact absurd rfl huv
  · rw [signSet_false, signSet_true]
    refine Set.disjoint_left.mpr fun ω hω hω' => ?_
    simp only [Set.mem_setOf_eq] at hω hω'
    linarith
  · rw [signSet_true, signSet_false]
    refine Set.disjoint_left.mpr fun ω hω hω' => ?_
    simp only [Set.mem_setOf_eq] at hω hω'
    linarith
  · exact absurd rfl huv

private lemma mem_signSet_decide (f : Ω → ℝ) (ω : Ω) :
    ω ∈ signSet f (decide (0 ≤ f ω)) := by
  by_cases hx : 0 ≤ f ω
  · rw [decide_eq_true hx, signSet_true]; exact hx
  · rw [decide_eq_false hx, signSet_false]; exact not_le.mp hx

/-- **The sign-pattern partition.** For a finite family of `𝒩`-measurable integrable
functions there is a finite `𝒩`-measurable partition on whose cells every member of the
family has a constant sign; consequently the cellwise integrals recover the `L¹` norms. -/
private lemma exists_sign_partition {𝒩 mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (h𝒩 : 𝒩 ≤ mΩ) {J : ℕ} {h : Fin J → Ω → ℝ}
    (hhm : ∀ j, Measurable[𝒩] (h j)) (hhi : ∀ j, Integrable (h j) μ) :
    ∃ (K : ℕ) (C : Fin K → Set Ω), (∀ k, MeasurableSet[𝒩] (C k)) ∧
      (Pairwise fun k k' => Disjoint (C k) (C k')) ∧ (⋃ k, C k) = Set.univ ∧
      ∀ j, ∑ k, |∫ ω in C k, h j ω ∂μ| = ∫ ω, |h j ω| ∂μ := by
  classical
  set e := Fintype.equivFin (Fin J → Bool) with hedef
  set D : (Fin J → Bool) → Set Ω := fun b => ⋂ j, signSet (h j) (b j) with hDdef
  have hDsub : ∀ (b : Fin J → Bool) (j : Fin J), D b ⊆ signSet (h j) (b j) := by
    intro b j ω hω
    exact Set.mem_iInter.mp hω j
  have hDm : ∀ b, MeasurableSet[𝒩] (D b) :=
    fun b => MeasurableSet.iInter fun j => measurableSet_signSet (hhm j) (b j)
  have hdisj : Pairwise fun k k' => Disjoint (D (e.symm k)) (D (e.symm k')) := by
    intro k k' hne
    have hbne : e.symm k ≠ e.symm k' := fun hc => hne (e.symm.injective hc)
    obtain ⟨j, hj⟩ : ∃ j, (e.symm k) j ≠ (e.symm k') j := Function.ne_iff.mp hbne
    exact (disjoint_signSet (h j) hj).mono (hDsub _ j) (hDsub _ j)
  have hcover : (⋃ k, D (e.symm k)) = Set.univ := by
    refine Set.eq_univ_of_forall fun ω => ?_
    refine Set.mem_iUnion.mpr ⟨e (fun j => decide (0 ≤ h j ω)), ?_⟩
    rw [Equiv.symm_apply_apply]
    exact Set.mem_iInter.mpr fun j => mem_signSet_decide (h j) ω
  refine ⟨Fintype.card (Fin J → Bool), fun k => D (e.symm k), fun k => hDm _, hdisj, hcover, ?_⟩
  intro j
  have hcell : ∀ k : Fin (Fintype.card (Fin J → Bool)),
      |∫ ω in D (e.symm k), h j ω ∂μ| = ∫ ω in D (e.symm k), |h j ω| ∂μ := by
    intro k
    have hnn : (0 : ℝ) ≤ ∫ ω in D (e.symm k), |h j ω| ∂μ :=
      setIntegral_nonneg (h𝒩 _ (hDm _)) fun ω _ => abs_nonneg _
    cases hb : (e.symm k) j
    · have heq : ∫ ω in D (e.symm k), h j ω ∂μ = -∫ ω in D (e.symm k), |h j ω| ∂μ := by
        rw [← integral_neg]
        refine setIntegral_congr_fun (h𝒩 _ (hDm _)) fun ω hω => ?_
        have hs : ω ∈ signSet (h j) false := hb ▸ hDsub _ j hω
        rw [signSet_false] at hs
        rw [abs_of_neg hs, neg_neg]
      rw [heq, abs_neg, abs_of_nonneg hnn]
    · have heq : ∫ ω in D (e.symm k), h j ω ∂μ = ∫ ω in D (e.symm k), |h j ω| ∂μ := by
        refine setIntegral_congr_fun (h𝒩 _ (hDm _)) fun ω hω => ?_
        have hs : ω ∈ signSet (h j) true := hb ▸ hDsub _ j hω
        rw [signSet_true] at hs
        rw [abs_of_nonneg hs]
      rw [heq, abs_of_nonneg hnn]
  rw [Finset.sum_congr rfl fun k _ => hcell k]
  exact sum_setIntegral_partition h𝒩 (fun k => hDm _) hdisj hcover (hhi j).abs

/-! ### Shrinking the two sides of a partition pair -/

private lemma setIntegral_indicator_one {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {S A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω in S, A.indicator (fun _ => (1 : ℝ)) ω ∂μ = (μ (S ∩ A)).toReal := by
  rw [integral_indicator_const (1 : ℝ) hA]
  simp [Measure.real, Measure.restrict_apply hA, Set.inter_comm]

/-- **Shrinking the first side.** If the conditional probabilities of the second-side sets
given `𝒮` admit `𝒩`-measurable versions, then any `𝒮`-partition can be replaced by an
`𝒩`-partition without decreasing the β partition sum. -/
private lemma beta_shrink_left {𝒩 𝒮 mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h𝒮 : 𝒮 ≤ mΩ) (h𝒩𝒮 : 𝒩 ≤ 𝒮)
    {I J : ℕ} {A : Fin I → Set Ω} {B : Fin J → Set Ω}
    (hAm : ∀ i, MeasurableSet[𝒮] (A i))
    (hAd : Pairwise fun i i' => Disjoint (A i) (A i'))
    (hAc : (⋃ i, A i) = Set.univ)
    (hBm : ∀ j, MeasurableSet (B j))
    {q : Fin J → Ω → ℝ} (hqm : ∀ j, Measurable[𝒩] (q j))
    (hq : ∀ j, μ[(B j).indicator (fun _ => (1 : ℝ)) | 𝒮] =ᵐ[μ] q j) :
    ∃ (K : ℕ) (A' : Fin K → Set Ω), (∀ k, MeasurableSet[𝒩] (A' k)) ∧
      (Pairwise fun k k' => Disjoint (A' k) (A' k')) ∧ (⋃ k, A' k) = Set.univ ∧
      ∑ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
        ≤ ∑ k, ∑ j, |(μ (A' k ∩ B j)).toReal - (μ (A' k)).toReal * (μ (B j)).toReal| := by
  have h𝒩 : 𝒩 ≤ mΩ := h𝒩𝒮.trans h𝒮
  set h : Fin J → Ω → ℝ := fun j ω => q j ω - (μ (B j)).toReal with hhdef
  have hqint : ∀ j, Integrable (q j) μ := fun j => integrable_condExp.congr (hq j)
  have hhi : ∀ j, Integrable (h j) μ := fun j => (hqint j).sub (integrable_const _)
  have hhm : ∀ j, Measurable[𝒩] (h j) := fun j => (hqm j).sub measurable_const
  -- the covariance of any `𝒮`-set with `B j` is a set integral of `h j`
  have hcov : ∀ (S : Set Ω), MeasurableSet[𝒮] S → ∀ j,
      (μ (S ∩ B j)).toReal - (μ S).toReal * (μ (B j)).toReal = ∫ ω in S, h j ω ∂μ := by
    intro S hS j
    have hSΩ : MeasurableSet S := h𝒮 _ hS
    have e1 : ∫ ω in S, q j ω ∂μ = (μ (S ∩ B j)).toReal := by
      have e0 : ∫ ω in S, q j ω ∂μ
          = ∫ ω in S, (μ[(B j).indicator (fun _ => (1 : ℝ)) | 𝒮]) ω ∂μ :=
        setIntegral_congr_ae hSΩ (by filter_upwards [hq j] with ω hω using fun _ => hω.symm)
      rw [e0, setIntegral_condExp h𝒮 ((integrable_const (1 : ℝ)).indicator (hBm j)) hS,
        setIntegral_indicator_one (hBm j)]
    rw [hhdef]
    rw [integral_sub (hqint j).integrableOn (integrable_const _), integral_const, e1]
    simp [Measure.real]
  obtain ⟨K, A', hA'm, hA'd, hA'c, hA'eq⟩ := exists_sign_partition (μ := μ) h𝒩 hhm hhi
  refine ⟨K, A', hA'm, hA'd, hA'c, ?_⟩
  have hle : ∀ j, ∑ i, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      ≤ ∑ k, |(μ (A' k ∩ B j)).toReal - (μ (A' k)).toReal * (μ (B j)).toReal| := by
    intro j
    have hL : ∑ i, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
        = ∑ i, |∫ ω in A i, h j ω ∂μ| :=
      Finset.sum_congr rfl fun i _ => by rw [hcov (A i) (hAm i) j]
    have hR : ∑ k, |(μ (A' k ∩ B j)).toReal - (μ (A' k)).toReal * (μ (B j)).toReal|
        = ∑ k, |∫ ω in A' k, h j ω ∂μ| :=
      Finset.sum_congr rfl fun k _ => by rw [hcov (A' k) (h𝒩𝒮 _ (hA'm k)) j]
    rw [hL, hR, hA'eq j]
    exact sum_abs_setIntegral_le h𝒮 hAm hAd hAc (hhi j)
  calc ∑ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      = ∑ j, ∑ i, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal| :=
        Finset.sum_comm
    _ ≤ ∑ j, ∑ k, |(μ (A' k ∩ B j)).toReal - (μ (A' k)).toReal * (μ (B j)).toReal| :=
        Finset.sum_le_sum fun j _ => hle j
    _ = ∑ k, ∑ j, |(μ (A' k ∩ B j)).toReal - (μ (A' k)).toReal * (μ (B j)).toReal| :=
        Finset.sum_comm

private lemma sum_indicator_partition {J : ℕ} {B : Fin J → Set Ω}
    (hBd : Pairwise fun j j' => Disjoint (B j) (B j')) (hBc : (⋃ j, B j) = Set.univ) (ω : Ω) :
    ∑ j, (B j).indicator (fun _ => (1 : ℝ)) ω = 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, ω ∈ B j := by
    have hu : ω ∈ ⋃ j, B j := hBc ▸ Set.mem_univ ω
    simpa using hu
  rw [Finset.sum_eq_single j]
  · rw [Set.indicator_of_mem hj]
  · intro j' _ hne
    exact Set.indicator_of_notMem (Set.disjoint_left.mp (hBd (Ne.symm hne)) hj) _
  · intro hc; exact absurd (Finset.mem_univ j) hc

private lemma integrable_indicator_one_mul {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {S : Set Ω} (hS : MeasurableSet S) {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (fun ω => S.indicator (fun _ => (1 : ℝ)) ω * f ω) μ := by
  refine (hf.indicator hS).congr ?_
  filter_upwards with ω
  by_cases hx : ω ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-- **Shrinking the second side.** The `𝒩`-measurable versions of the conditional
probabilities of the second-side cells given `𝒮` form a partition of unity; smoothing the
first-side covariances against it replaces the second-side partition by an `𝒩`-partition
without decreasing the β partition sum. -/
private lemma beta_shrink_right {𝒩 𝒮 mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h𝒮 : 𝒮 ≤ mΩ) (h𝒩 : 𝒩 ≤ mΩ)
    {K J : ℕ} {A : Fin K → Set Ω} {B : Fin J → Set Ω}
    (hAm : ∀ k, MeasurableSet[𝒮] (A k))
    (hBm : ∀ j, MeasurableSet (B j))
    (hBd : Pairwise fun j j' => Disjoint (B j) (B j'))
    (hBc : (⋃ j, B j) = Set.univ)
    {r : Fin J → Ω → ℝ} (hrm : ∀ j, Measurable[𝒩] (r j))
    (hr : ∀ j, μ[(B j).indicator (fun _ => (1 : ℝ)) | 𝒮] =ᵐ[μ] r j) :
    ∃ (L : ℕ) (C : Fin L → Set Ω), (∀ l, MeasurableSet[𝒩] (C l)) ∧
      (Pairwise fun l l' => Disjoint (C l) (C l')) ∧ (⋃ l, C l) = Set.univ ∧
      ∑ k, ∑ j, |(μ (A k ∩ B j)).toReal - (μ (A k)).toReal * (μ (B j)).toReal|
        ≤ ∑ k, ∑ l, |(μ (A k ∩ C l)).toReal - (μ (A k)).toReal * (μ (C l)).toReal| := by
  classical
  have hAmΩ : ∀ k, MeasurableSet (A k) := fun k => h𝒮 _ (hAm k)
  have hrint : ∀ j, Integrable (r j) μ := fun j => integrable_condExp.congr (hr j)
  have hrmΩ : ∀ j, Measurable (r j) := fun j => (hrm j).mono h𝒩 le_rfl
  have hrnn : ∀ j, ∀ᵐ ω ∂μ, (0 : ℝ) ≤ r j ω := by
    intro j
    filter_upwards [condExp_nonneg (μ := μ) (m := 𝒮)
      (Filter.Eventually.of_forall fun ω => indicator_one_nonneg (B j) ω), hr j] with ω e0 e1
    have e0' : (0 : ℝ) ≤ (μ[(B j).indicator (fun _ => (1 : ℝ)) | 𝒮]) ω := e0
    rw [← e1]; exact e0'
  have hrb : ∀ j, ∀ᵐ ω ∂μ, ‖r j ω‖ ≤ 1 := by
    intro j
    filter_upwards [norm_condExp_indicator_le_one h𝒮 (hBm j), hr j] with ω e0 e1
    rw [← e1]; exact e0
  have hrsum : ∀ᵐ ω ∂μ, ∑ j, r j ω = 1 := by
    have hcs := condExp_finset_sum (μ := μ) (m := 𝒮) (s := (Finset.univ : Finset (Fin J)))
      (f := fun j => (B j).indicator (fun _ => (1 : ℝ)))
      (fun j _ => (integrable_const (1 : ℝ)).indicator (hBm j))
    have hlhs : μ[∑ j ∈ (Finset.univ : Finset (Fin J)),
        (B j).indicator (fun _ => (1 : ℝ)) | 𝒮] =ᵐ[μ] fun _ => (1 : ℝ) := by
      have he : (∑ j ∈ (Finset.univ : Finset (Fin J)), (B j).indicator (fun _ => (1 : ℝ)))
          = fun _ => (1 : ℝ) := by
        funext ω
        rw [Finset.sum_apply]
        exact sum_indicator_partition hBd hBc ω
      rw [he, condExp_const h𝒮]
    filter_upwards [hcs, hlhs, ae_all_iff.mpr fun j => hr j] with ω e1 e2 e3
    have he : ∑ j, r j ω = ∑ j, (μ[(B j).indicator (fun _ => (1 : ℝ)) | 𝒮]) ω :=
      Finset.sum_congr rfl fun j _ => (e3 j).symm
    rw [he, ← Finset.sum_apply, ← e1, e2]
  set g : Fin K → Ω → ℝ :=
    fun k ω => (A k).indicator (fun _ => (1 : ℝ)) ω - (μ (A k)).toReal with hgdef
  have hgint : ∀ k, Integrable (g k) μ := fun k =>
    ((integrable_const (1 : ℝ)).indicator (hAmΩ k)).sub (integrable_const _)
  set G : Fin K → Ω → ℝ := fun k => μ[g k | 𝒩] with hGdef
  have hGm : ∀ k, Measurable[𝒩] (G k) := fun k => stronglyMeasurable_condExp.measurable
  have hGint : ∀ k, Integrable (G k) μ := fun k => integrable_condExp
  -- (a) the covariance against the partition of unity
  have hcov : ∀ (k : Fin K) (j : Fin J),
      (μ (A k ∩ B j)).toReal - (μ (A k)).toReal * (μ (B j)).toReal
        = ∫ ω, r j ω * g k ω ∂μ := by
    intro k j
    have hri : Integrable (fun ω => (A k).indicator (fun _ => (1 : ℝ)) ω * r j ω) μ :=
      integrable_indicator_one_mul (hAmΩ k) (hrint j)
    have e1 : ∫ ω, (A k).indicator (fun _ => (1 : ℝ)) ω * r j ω ∂μ
        = (μ (A k ∩ B j)).toReal := by
      rw [← setIntegral_eq_indicator_mul (hAmΩ k)]
      have e0 : ∫ ω in A k, r j ω ∂μ
          = ∫ ω in A k, (μ[(B j).indicator (fun _ => (1 : ℝ)) | 𝒮]) ω ∂μ :=
        setIntegral_congr_ae (hAmΩ k)
          (by filter_upwards [hr j] with ω hω using fun _ => hω.symm)
      rw [e0, setIntegral_condExp h𝒮 ((integrable_const (1 : ℝ)).indicator (hBm j)) (hAm k),
        setIntegral_indicator_one (hBm j)]
    have e2 : ∫ ω, r j ω ∂μ = (μ (B j)).toReal := by
      have e0 : ∫ ω, r j ω ∂μ = ∫ ω, (μ[(B j).indicator (fun _ => (1 : ℝ)) | 𝒮]) ω ∂μ :=
        integral_congr_ae (by filter_upwards [hr j] with ω hω using hω.symm)
      rw [e0, integral_condExp h𝒮, integral_indicator_const (1 : ℝ) (hBm j)]
      simp [Measure.real]
    have e3 : (fun ω => r j ω * g k ω)
        = fun ω => (A k).indicator (fun _ => (1 : ℝ)) ω * r j ω
            - (μ (A k)).toReal * r j ω := by
      funext ω; simp only [hgdef]; ring
    rw [e3, integral_sub hri ((hrint j).const_mul _), e1, integral_const_mul, e2]
  -- (b) smoothing by `𝒩`-conditioning
  have hsm : ∀ (k : Fin K) (j : Fin J),
      ∫ ω, r j ω * g k ω ∂μ = ∫ ω, r j ω * G k ω ∂μ := by
    intro k j
    have hpull : μ[r j * g k | 𝒩] =ᵐ[μ] r j * μ[g k | 𝒩] :=
      condExp_stronglyMeasurable_mul_of_bound₀ h𝒩
        (hrm j).stronglyMeasurable.aestronglyMeasurable (hgint k) 1 (hrb j)
    calc ∫ ω, r j ω * g k ω ∂μ = ∫ ω, (r j * g k) ω ∂μ := rfl
      _ = ∫ ω, (μ[r j * g k | 𝒩]) ω ∂μ := (integral_condExp h𝒩).symm
      _ = ∫ ω, r j ω * G k ω ∂μ :=
          integral_congr_ae (by filter_upwards [hpull] with ω hω using hω)
  -- (c) the `L¹` bound
  have hbound : ∀ k, ∑ j, |∫ ω, r j ω * G k ω ∂μ| ≤ ∫ ω, |G k ω| ∂μ := by
    intro k
    have hint2 : ∀ j, Integrable (fun ω => r j ω * |G k ω|) μ :=
      fun j => (hGint k).abs.bdd_mul (hrmΩ j).aestronglyMeasurable (hrb j)
    have hstep : ∀ j, |∫ ω, r j ω * G k ω ∂μ| ≤ ∫ ω, r j ω * |G k ω| ∂μ := by
      intro j
      calc |∫ ω, r j ω * G k ω ∂μ| ≤ ∫ ω, |r j ω * G k ω| ∂μ := abs_integral_le_integral_abs
        _ = ∫ ω, r j ω * |G k ω| ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [hrnn j] with ω hω
            rw [abs_mul, abs_of_nonneg hω]
    calc ∑ j, |∫ ω, r j ω * G k ω ∂μ| ≤ ∑ j, ∫ ω, r j ω * |G k ω| ∂μ :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = ∫ ω, ∑ j, r j ω * |G k ω| ∂μ := (integral_finset_sum _ fun j _ => hint2 j).symm
      _ = ∫ ω, |G k ω| ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hrsum] with ω hω
          rw [← Finset.sum_mul, hω, one_mul]
  -- (d) the sign partition of the smoothed covariances
  obtain ⟨L, C, hCm, hCd, hCc, hCeq⟩ := exists_sign_partition (μ := μ) h𝒩 hGm hGint
  refine ⟨L, C, hCm, hCd, hCc, ?_⟩
  have hCcov : ∀ (k : Fin K) (l : Fin L), ∫ ω in C l, G k ω ∂μ
      = (μ (A k ∩ C l)).toReal - (μ (A k)).toReal * (μ (C l)).toReal := by
    intro k l
    rw [hGdef]
    rw [setIntegral_condExp h𝒩 (hgint k) (hCm l)]
    have e3 : g k = fun ω => (A k).indicator (fun _ => (1 : ℝ)) ω - (μ (A k)).toReal := rfl
    rw [e3, integral_sub ((integrable_const (1 : ℝ)).indicator (hAmΩ k)).integrableOn
      (integrable_const _), setIntegral_indicator_one (hAmΩ k), integral_const]
    simp [Measure.real, Set.inter_comm]
    ring
  calc ∑ k, ∑ j, |(μ (A k ∩ B j)).toReal - (μ (A k)).toReal * (μ (B j)).toReal|
      = ∑ k, ∑ j, |∫ ω, r j ω * G k ω ∂μ| :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by
          rw [hcov k j, hsm k j]
    _ ≤ ∑ k, ∫ ω, |G k ω| ∂μ := Finset.sum_le_sum fun k _ => hbound k
    _ = ∑ k, ∑ l, |∫ ω in C l, G k ω ∂μ| :=
        Finset.sum_congr rfl fun k _ => (hCeq k).symm
    _ = ∑ k, ∑ l, |(μ (A k ∩ C l)).toReal - (μ (A k)).toReal * (μ (C l)).toReal| :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by rw [hCcov k l]

/-! ### β-coefficient plumbing (re-derived here: `Mixing/Relations.lean` is downstream) -/

private lemma sum_measure_inter_partition {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {J : ℕ} {B : Fin J → Set Ω}
    (hBm : ∀ j, MeasurableSet[m] (B j)) (hBd : Pairwise fun j j' => Disjoint (B j) (B j'))
    (hBc : (⋃ j, B j) = Set.univ) {S : Set Ω} (hS : MeasurableSet S) :
    ∑ j, (μ (S ∩ B j)).toReal = (μ S).toReal := by
  have h1 : ∑ j, (μ (S ∩ B j)).toReal
      = ∫ ω in S, ∑ j, (B j).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
    rw [integral_finset_sum _ fun j _ =>
      ((integrable_const (1 : ℝ)).indicator (hm _ (hBm j))).integrableOn]
    exact Finset.sum_congr rfl fun j _ => (setIntegral_indicator_one (hm _ (hBm j))).symm
  rw [h1, integral_congr_ae
    (Filter.Eventually.of_forall fun ω => sum_indicator_partition hBd hBc ω), integral_const]
  simp [Measure.real, Measure.restrict_apply_univ]

private lemma beta_partition_sum_le_two {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {I J : ℕ} {A : Fin I → Set Ω} {B : Fin J → Set Ω}
    (hAm : ∀ i, MeasurableSet[m₁] (A i)) (hBm : ∀ j, MeasurableSet[m₂] (B j))
    (hAd : Pairwise fun i i' => Disjoint (A i) (A i')) (hAc : (⋃ i, A i) = Set.univ)
    (hBd : Pairwise fun j j' => Disjoint (B j) (B j')) (hBc : (⋃ j, B j) = Set.univ) :
    ∑ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal| ≤ 2 := by
  have hAsum : ∑ i, (μ (A i)).toReal = 1 := by
    have h := sum_measure_inter_partition (μ := μ) h₁ hAm hAd hAc (S := Set.univ) MeasurableSet.univ
    simpa using h
  have hBsum : ∑ j, (μ (B j)).toReal = 1 := by
    have h := sum_measure_inter_partition (μ := μ) h₂ hBm hBd hBc (S := Set.univ) MeasurableSet.univ
    simpa using h
  have hrow : ∀ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      ≤ (μ (A i)).toReal + (μ (A i)).toReal * 1 := by
    intro i
    have hi := sum_measure_inter_partition (μ := μ) h₂ hBm hBd hBc (h₁ _ (hAm i))
    calc ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
        ≤ ∑ j, ((μ (A i ∩ B j)).toReal + (μ (A i)).toReal * (μ (B j)).toReal) :=
          Finset.sum_le_sum fun j _ => by
            have h1 : (0 : ℝ) ≤ (μ (A i ∩ B j)).toReal := ENNReal.toReal_nonneg
            have h2 : (0 : ℝ) ≤ (μ (A i)).toReal * (μ (B j)).toReal :=
              mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
            rw [abs_le]; constructor <;> linarith
      _ = (μ (A i)).toReal + (μ (A i)).toReal * 1 := by
          rw [Finset.sum_add_distrib, hi, ← Finset.mul_sum, hBsum]
  calc ∑ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      ≤ ∑ i, ((μ (A i)).toReal + (μ (A i)).toReal * 1) := Finset.sum_le_sum fun i _ => hrow i
    _ = 2 := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, hAsum]; norm_num

private lemma betaMixCoeff_bddAbove {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    BddAbove {r : ℝ | ∃ (I J : ℕ) (A : Fin I → Set Ω) (B : Fin J → Set Ω),
      (∀ i, MeasurableSet[m₁] (A i)) ∧ (∀ j, MeasurableSet[m₂] (B j)) ∧
      (Pairwise fun i i' => Disjoint (A i) (A i')) ∧
      (Pairwise fun j j' => Disjoint (B j) (B j')) ∧
      (⋃ i, A i) = Set.univ ∧ (⋃ j, B j) = Set.univ ∧
      r = (1 / 2) * ∑ i, ∑ j,
        |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨I, J, A, B, hA, hB, hdA, hdB, hcA, hcB, rfl⟩
  have := beta_partition_sum_le_two (μ := μ) h₁ h₂ hA hB hdA hcA hdB hcB
  linarith

private lemma betaMixCoeff_zero_mem {m₁ m₂ mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] : (0 : ℝ) ∈ {r : ℝ | ∃ (I J : ℕ) (A : Fin I → Set Ω) (B : Fin J → Set Ω),
      (∀ i, MeasurableSet[m₁] (A i)) ∧ (∀ j, MeasurableSet[m₂] (B j)) ∧
      (Pairwise fun i i' => Disjoint (A i) (A i')) ∧
      (Pairwise fun j j' => Disjoint (B j) (B j')) ∧
      (⋃ i, A i) = Set.univ ∧ (⋃ j, B j) = Set.univ ∧
      r = (1 / 2) * ∑ i, ∑ j,
        |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|} := by
  refine ⟨1, 1, fun _ => Set.univ, fun _ => Set.univ, fun _ => MeasurableSet.univ,
    fun _ => MeasurableSet.univ, fun i i' h => absurd (Subsingleton.elim i i') h,
    fun j j' h => absurd (Subsingleton.elim j j') h,
    Set.univ_subset_iff.mp (Set.subset_iUnion (fun _ : Fin 1 => (Set.univ : Set Ω)) 0),
    Set.univ_subset_iff.mp (Set.subset_iUnion (fun _ : Fin 1 => (Set.univ : Set Ω)) 0), ?_⟩
  simp

private lemma betaMixCoeff_nonneg' {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) : 0 ≤ betaMixCoeff μ m₁ m₂ :=
  le_csSup (betaMixCoeff_bddAbove h₁ h₂) (betaMixCoeff_zero_mem (mΩ := mΩ) μ)

/-- `β ≤ 1` (the partition sum is at most `2` and `betaMixCoeff` is its half). -/
theorem betaMixCoeff_le_one {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) : betaMixCoeff μ m₁ m₂ ≤ 1 := by
  refine Real.sSup_le ?_ zero_le_one
  rintro r ⟨I, J, A, B, hA, hB, hdA, hdB, hcA, hcB, rfl⟩
  have := beta_partition_sum_le_two (μ := μ) h₁ h₂ hA hB hdA hcA hdB hcB
  linarith

private lemma le_betaMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {I J : ℕ} {A : Fin I → Set Ω} {B : Fin J → Set Ω}
    (hAm : ∀ i, MeasurableSet[m₁] (A i)) (hBm : ∀ j, MeasurableSet[m₂] (B j))
    (hAd : Pairwise fun i i' => Disjoint (A i) (A i')) (hAc : (⋃ i, A i) = Set.univ)
    (hBd : Pairwise fun j j' => Disjoint (B j) (B j')) (hBc : (⋃ j, B j) = Set.univ) :
    (1 / 2) * ∑ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      ≤ betaMixCoeff μ m₁ m₂ :=
  le_csSup (betaMixCoeff_bddAbove h₁ h₂) ⟨I, J, A, B, hAm, hBm, hAd, hBd, hAc, hBc, rfl⟩

private lemma betaMixCoeff_mono' {m₁ m₂ m₁' m₂' mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hb₁ : m₁ ≤ mΩ) (hb₂ : m₂ ≤ mΩ) (h₁ : m₁' ≤ m₁) (h₂ : m₂' ≤ m₂) :
    betaMixCoeff μ m₁' m₂' ≤ betaMixCoeff μ m₁ m₂ := by
  refine Real.sSup_le ?_ (betaMixCoeff_nonneg' (mΩ := mΩ) hb₁ hb₂)
  rintro r ⟨I, J, A, B, hA, hB, hdA, hdB, hcA, hcB, rfl⟩
  exact le_betaMixCoeff (mΩ := mΩ) hb₁ hb₂ (fun i => h₁ _ (hA i)) (fun j => h₂ _ (hB j))
    hdA hcA hdB hcB

end BetaShrink

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {E : Type*} [MeasurableSpace E]

/-! ### The state σ-algebras of a process with values in an arbitrary measurable space

`Process/Defs.lean`'s `sigmaLE`/`sigmaGE` are frozen at real-valued processes. The Markov
bridge below is run on the **state** of a model (the ARMA companion vector, the GARCH
volatility vector), so it needs the same two σ-algebras for an arbitrary measurable state
space `E`. The definitions are literally the same expressions, hence `sigmaLE'_eq_sigmaLE`
and `sigmaGE'_eq_sigmaGE` below are `rfl`: nothing in the scalar layer changes. -/

/-- `σ{V_s : s ≤ n}` for a process with values in an arbitrary measurable space
(`Process/Defs.lean`'s `sigmaLE`, freed of `ℝ`). -/
@[reducible] noncomputable def sigmaLE' (V : ℤ → Ω → E) (n : ℤ) : MeasurableSpace Ω :=
  ⨆ s ∈ Set.Iic n, MeasurableSpace.comap (V s) inferInstance

/-- `σ{V_s : s ≥ n}` for a process with values in an arbitrary measurable space
(`Process/Defs.lean`'s `sigmaGE`, freed of `ℝ`). -/
@[reducible] noncomputable def sigmaGE' (V : ℤ → Ω → E) (n : ℤ) : MeasurableSpace Ω :=
  ⨆ s ∈ Set.Ici n, MeasurableSpace.comap (V s) inferInstance

@[simp] lemma sigmaLE'_eq_sigmaLE (X : ℤ → Ω → ℝ) (n : ℤ) : sigmaLE' X n = sigmaLE X n := rfl

@[simp] lemma sigmaGE'_eq_sigmaGE (X : ℤ → Ω → ℝ) (n : ℤ) : sigmaGE' X n = sigmaGE X n := rfl

/-- Shifting the process shifts the past σ-algebra. -/
lemma sigmaLE'_shift (V : ℤ → Ω → E) (k n : ℤ) :
    sigmaLE' (fun s => V (s + k)) n = sigmaLE' V (n + k) := by
  refine le_antisymm (iSup₂_le fun s hs => le_iSup₂_of_le (s + k) ?_ le_rfl)
    (iSup₂_le fun s hs => le_iSup₂_of_le (s - k) ?_ ?_)
  · exact Set.mem_Iic.mpr (by have := Set.mem_Iic.mp hs; omega)
  · exact Set.mem_Iic.mpr (by have := Set.mem_Iic.mp hs; omega)
  · simpa using le_rfl

/-- Shifting the process shifts the future σ-algebra. -/
lemma sigmaGE'_shift (V : ℤ → Ω → E) (k n : ℤ) :
    sigmaGE' (fun s => V (s + k)) n = sigmaGE' V (n + k) := by
  refine le_antisymm (iSup₂_le fun s hs => le_iSup₂_of_le (s + k) ?_ le_rfl)
    (iSup₂_le fun s hs => le_iSup₂_of_le (s - k) ?_ ?_)
  · exact Set.mem_Ici.mpr (by have := Set.mem_Ici.mp hs; omega)
  · exact Set.mem_Ici.mpr (by have := Set.mem_Ici.mp hs; omega)
  · simpa using le_rfl

/-- The **Markov representation** hypothesis tying a process with values in a measurable
space `E` to a kernel on `E`: the conditional law of `X_{t+n}` given the past through time
`t` is `κⁿ(X_t, ·)`, expressed through conditional expectations of indicators.

**Generalized (2026-08-09, wave 5)** from `Kernel ℝ ℝ` to `Kernel E E`. The scalar case
`E = ℝ` is unchanged (`sigmaLE'` is definitionally `sigmaLE`); the vector case is what the
model debts of `Mixing/Relations.lean` consume, since the Markov object of an ARMA or a
GARCH is its *state* vector, not the observed scalar series. -/
def IsMarkovOf (X : ℤ → Ω → E) (κ : ProbabilityTheory.Kernel E E) (μ : Measure Ω) :
    Prop :=
  ∀ (t : ℤ) (n : ℕ) (B : Set E), MeasurableSet B →
    (μ[fun ω => (B.indicator (fun _ => (1 : ℝ)) (X (t + n) ω)) | sigmaLE' X t])
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

private lemma sigmaLE_le {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaLE' X t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

/-- The `n`-step kernel average of a bounded measurable function is measurable. -/
private lemma measurable_kernel_integral {κ : Kernel E E} (n : ℕ) {f : E → ℝ}
    (hf : Measurable f) : Measurable fun x => ∫ y, f y ∂((κ ^ n) x) :=
  (hf.stronglyMeasurable.integral_kernel (κ := κ ^ n)).measurable

private lemma abs_kernel_integral_le {κ : Kernel E E} [IsMarkovKernel κ] (n : ℕ) {f : E → ℝ}
    {M : ℝ} (hfb : ∀ y, |f y| ≤ M) (x : E) : |∫ y, f y ∂((κ ^ n) x)| ≤ M := by
  haveI := isMarkovKernel_pow' κ n
  have h := norm_integral_le_of_norm_le_const (μ := (κ ^ n) x) (C := M)
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hfb y)
  simpa [Measure.real, measure_univ] using h

/-- **Step 1**: the set-integral form of the Markov property against a bounded measurable
test function. -/
private lemma markov_setIntegral_eq [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    {κ : Kernel E E} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ)
    (t : ℤ) (n : ℕ) {f : E → ℝ} (hf : Measurable f) {M : ℝ} (hfb : ∀ y, |f y| ≤ M)
    {A : Set Ω} (hA : MeasurableSet[sigmaLE' X t] A) :
    ∫ ω in A, (∫ y, f y ∂((κ ^ n) (X t ω))) ∂μ = ∫ ω in A, f (X (t + n) ω) ∂μ := by
  haveI := isMarkovKernel_pow' κ n
  have hm := sigmaLE_le hmeas t
  have hAΩ : MeasurableSet A := hm _ hA
  set lam : Measure Ω := μ.restrict A with hlam
  haveI : IsFiniteMeasure lam := by rw [hlam]; infer_instance
  set κ' : Kernel Ω E := (κ ^ n).comap (X t) (hmeas t) with hκ'
  haveI : IsMarkovKernel κ' := by rw [hκ']; infer_instance
  -- (a) the one-event Markov identity, in `ℝ≥0∞`
  have hone : ∀ B : Set E, MeasurableSet B →
      lam (X (t + n) ⁻¹' B) = ∫⁻ ω, (κ' ω) B ∂lam := by
    intro B hB
    have hbd1 : ∀ y : E, |B.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := fun y => by
      by_cases hy : y ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]
    have hint : Integrable (fun ω => B.indicator (fun _ => (1 : ℝ)) (X (t + n) ω)) μ :=
      integrable_bdd_comp μ (hmeas _) (measurable_const.indicator hB) hbd1
    have hsi := setIntegral_condExp hm hint hA
    have hcond : ∫ ω in A, (μ[fun ω => B.indicator (fun _ => (1 : ℝ)) (X (t + n) ω)
        | sigmaLE' X t]) ω ∂μ = ∫ ω in A, (((κ ^ n) (X t ω)) B).toReal ∂μ :=
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
  have hfint : Integrable (fun z : Ω × E => f z.2) (lam ⊗ₘ κ') :=
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
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    {κ : Kernel E E} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ)
    (t : ℤ) (n : ℕ) {f : E → ℝ} (hf : Measurable f) {M : ℝ} (hfb : ∀ y, |f y| ≤ M) :
    μ[fun ω => f (X (t + n) ω) | sigmaLE' X t]
      =ᵐ[μ] fun ω => ∫ y, f y ∂((κ ^ n) (X t ω)) := by
  have hm := sigmaLE_le hmeas t
  have hFm : Measurable fun x : E => ∫ y, f y ∂((κ ^ n) x) :=
    measurable_kernel_integral n hf
  have hcomap : MeasurableSpace.comap (X t) inferInstance ≤ sigmaLE' X t :=
    le_iSup₂_of_le t (Set.mem_Iic.mpr le_rfl) le_rfl
  have hgm : StronglyMeasurable[sigmaLE' X t] fun ω => ∫ y, f y ∂((κ ^ n) (X t ω)) := by
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
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    {κ : Kernel E E} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ) (t : ℤ) (S : Finset ℕ) :
    ∀ f : ℕ → E → ℝ, (∀ s, Measurable (f s)) → (∀ s y, |f s y| ≤ 1) →
      ∃ G : E → ℝ, Measurable G ∧ (∀ x, |G x| ≤ 1) ∧
        μ[fun ω => ∏ s ∈ S, f s (X (t + (s : ℤ)) ω) | sigmaLE' X t]
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
      have hmono : sigmaLE' X t ≤ sigmaLE' X (t + (b : ℤ)) :=
        iSup₂_le fun s hs => le_iSup₂_of_le s
          (Set.mem_Iic.mpr (le_trans (Set.mem_Iic.mp hs) (by omega))) le_rfl
      set Δ : ℕ := a - b with hΔ
      have hcast : t + (a : ℤ) = (t + (b : ℤ)) + (Δ : ℤ) := by
        have h1 : (Δ : ℤ) = (a : ℤ) - (b : ℤ) := by rw [hΔ, Nat.cast_sub hba.le]
        omega
      set g : E → ℝ := fun x => ∫ y, f a y ∂((κ ^ Δ) x) with hg
      have hgm : Measurable g := measurable_kernel_integral Δ (hfm a)
      have hgb : ∀ x, |g x| ≤ 1 := fun x => abs_kernel_integral_le Δ (hfb a) x
      set f' : ℕ → E → ℝ := fun s => if s = b then (fun x => f b x * g x) else f s with hf'
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
      have hPmeas : StronglyMeasurable[sigmaLE' X (t + (b : ℤ))] P := by
        refine Measurable.stronglyMeasurable ?_
        rw [hP]
        refine Finset.measurable_prod S fun s hs => ?_
        have hcs : MeasurableSpace.comap (X (t + (s : ℤ))) inferInstance
            ≤ sigmaLE' X (t + (b : ℤ)) :=
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
      have hpull : μ[P * Q | sigmaLE' X (t + (b : ℤ))]
          =ᵐ[μ] P * μ[Q | sigmaLE' X (t + (b : ℤ))] :=
        condExp_stronglyMeasurable_mul_of_bound₀ hmb hPmeas.aestronglyMeasurable hQint 1
          (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hPb ω)
      have hQc : μ[Q | sigmaLE' X (t + (b : ℤ))] =ᵐ[μ] fun ω => g (X (t + (b : ℤ)) ω) := by
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
      calc (μ[P * Q | sigmaLE' X (t + (b : ℤ))]) ω
          = P ω * (μ[Q | sigmaLE' X (t + (b : ℤ))]) ω := h1
        _ = P ω * g (X (t + (b : ℤ)) ω) := by rw [h2]
        _ = ∏ s ∈ S, f' s (X (t + (s : ℤ)) ω) := hprod ω

/-- The π-system of finite-dimensional cylinders on the coordinates at times `≥ t`. -/
private def futureCyl (X : ℤ → Ω → E) (t : ℤ) : Set (Set Ω) :=
  {A | ∃ (S : Finset ℕ) (B : ℕ → Set E), (∀ s, MeasurableSet (B s)) ∧
    A = ⋂ s ∈ S, (X (t + (s : ℤ))) ⁻¹' (B s)}

omit [MeasurableSpace Ω] in
private lemma isPiSystem_futureCyl (X : ℤ → Ω → E) (t : ℤ) : IsPiSystem (futureCyl X t) := by
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

private lemma measurableSet_futureCyl {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    {t : ℤ} {A : Set Ω} (hA : A ∈ futureCyl X t) : MeasurableSet A := by
  obtain ⟨S, B, hB, rfl⟩ := hA
  exact Finset.measurableSet_biInter S fun s _ => (hmeas _) (hB s)

private lemma sigmaGE_eq_generateFrom {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaGE' X t = MeasurableSpace.generateFrom (futureCyl X t) := by
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
    have hle : MeasurableSpace.comap (X (t + (s : ℤ))) inferInstance ≤ sigmaGE' X t :=
      le_iSup₂_of_le (t + (s : ℤ)) (Set.mem_Ici.mpr (by omega)) le_rfl
    exact hle _ ⟨B s, hB s, rfl⟩

omit [MeasurableSpace Ω] in
private lemma indicator_biInter_eq_prod {X : ℤ → Ω → E} (t : ℤ) (S : Finset ℕ) (B : ℕ → Set E)
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
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    {κ : Kernel E E} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ) (t : ℤ) :
    ∀ A : Set Ω, MeasurableSet[sigmaGE' X t] A →
      ∀ D : Set Ω, MeasurableSet[sigmaLE' X t] D →
        ∫ ω in A, (μ[D.indicator (fun _ => (1 : ℝ))
            | MeasurableSpace.comap (X t) inferInstance]) ω ∂μ = (μ (A ∩ D)).toReal := by
  have hmt := sigmaLE_le hmeas t
  have hGE : sigmaGE' X t ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup₂_le fun s _ => (hmeas s).comap_le
  have hG : MeasurableSpace.comap (X t) (inferInstance : MeasurableSpace E)
      ≤ (inferInstance : MeasurableSpace Ω) := (hmeas t).comap_le
  have hGt : MeasurableSpace.comap (X t) (inferInstance : MeasurableSpace E) ≤ sigmaLE' X t :=
    le_iSup₂_of_le t (Set.mem_Iic.mpr le_rfl) le_rfl
  refine MeasurableSpace.induction_on_inter
    (C := fun A _ => ∀ D : Set Ω, MeasurableSet[sigmaLE' X t] D →
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
        | sigmaLE' X t] =ᵐ[μ] fun ω => G (X t ω) := by rw [hind]; exact hGe
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
              | sigmaLE' X t]) ω ∂μ := by
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


/-- The content of `condExp_sigmaGE_indicator_brick`, placed early so that the β-side
reduction below can consume it as well. -/
private lemma condExp_sigmaGE_versionable [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    {κ : ProbabilityTheory.Kernel E E} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ) (t : ℤ) {B : Set Ω} (hB : MeasurableSet[sigmaGE' X t] B) :
    ∃ p : Ω → ℝ, StronglyMeasurable[MeasurableSpace.comap (X t) inferInstance] p ∧
      μ[B.indicator (fun _ => (1 : ℝ)) | sigmaLE' X t] =ᵐ[μ] p := by
  have hmt := sigmaLE_le hmeas t
  have hGE : sigmaGE' X t ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup₂_le fun s _ => (hmeas s).comap_le
  have hG : MeasurableSpace.comap (X t) (inferInstance : MeasurableSpace E)
      ≤ (inferInstance : MeasurableSpace Ω) := (hmeas t).comap_le
  have hGt : MeasurableSpace.comap (X t) (inferInstance : MeasurableSpace E) ≤ sigmaLE' X t :=
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


end MarkovFuture

/-- **BRICK — the two-marginal reduction for `β`** (Bradley Thms 4.1–4.2, the β-analogue of
`alphaCoeff_eq_two_marginal_debt`).

**Status (2026-08-09, wave 4): PROVED.** `≥` is `betaMixCoeff_mono'`. For `≤`, a partition
pair `({A_i} ⊆ 𝓕_{≤0}, {B_j} ⊆ 𝓕_{≥n})` is pushed onto `(σ(X_0), σ(X_n))` in two steps that
only increase the partition sum:

* `beta_shrink_left` at `(𝒩, 𝒮) = (σ(X_0), 𝓕_{≤0})`. With
  `h_j := E[1_{B_j}|𝓕_{≤0}] − P(B_j)` (σ(X_0)-measurable by
  `condExp_sigmaGE_versionable` at `t = 0`) every covariance is the set integral
  `∫_{A_i} h_j`; `Σ_i |∫_{A_i} h_j| ≤ ∫ |h_j|`, and the σ(X_0)-partition cut out by the
  *joint sign pattern* of the finitely many `h_j` attains `∫ |h_j|` for every `j` at once.
* `beta_shrink_right` at `(𝒩, 𝒮) = (σ(X_n), 𝓕_{≤n})`. Here `r_j := E[1_{B_j}|𝓕_{≤n}]` is
  σ(X_n)-measurable (the same brick at `t = n`), nonnegative, and sums to `1`: a σ(X_n)
  partition of *unity*. Writing `g_k := 1_{A'_k} − P(A'_k)`, the covariance is
  `∫ r_j g_k = ∫ r_j E[g_k|σ(X_n)]`, so `Σ_j |·| ≤ ∫ |E[g_k|σ(X_n)]|`, again attained by
  the joint sign-pattern partition — this time of the `E[g_k|σ(X_n)]`. Note that **no
  reverse (time-symmetric) Markov property is used**: the future side is moved by
  conditioning the future cells on the *past* up to `n`. -/
theorem betaMixCoeff_two_marginal_of_markov [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    {κ : ProbabilityTheory.Kernel E E} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ) (n : ℕ) :
    betaMixCoeff μ (sigmaLE' X 0) (sigmaGE' X (n : ℤ))
      = betaMixCoeff μ (MeasurableSpace.comap (X 0) inferInstance)
          (MeasurableSpace.comap (X (n : ℤ)) inferInstance) := by
  classical
  have hLEΩ : ∀ t : ℤ, sigmaLE' X t ≤ (inferInstance : MeasurableSpace Ω) := sigmaLE_le hmeas
  have hGEΩ : ∀ t : ℤ, sigmaGE' X t ≤ (inferInstance : MeasurableSpace Ω) :=
    fun t => iSup₂_le fun s _ => (hmeas s).comap_le
  have hm0Ω : MeasurableSpace.comap (X 0) inferInstance
      ≤ (inferInstance : MeasurableSpace Ω) := (hmeas 0).comap_le
  have hmnΩ : MeasurableSpace.comap (X (n : ℤ)) inferInstance
      ≤ (inferInstance : MeasurableSpace Ω) := (hmeas _).comap_le
  have hm0le : MeasurableSpace.comap (X 0) inferInstance ≤ sigmaLE' X 0 :=
    le_iSup₂_of_le (0 : ℤ) (Set.mem_Iic.mpr le_rfl) le_rfl
  have hm0leN : MeasurableSpace.comap (X 0) inferInstance ≤ sigmaLE' X (n : ℤ) :=
    le_iSup₂_of_le (0 : ℤ) (Set.mem_Iic.mpr (Int.natCast_nonneg n)) le_rfl
  have hmnle : MeasurableSpace.comap (X (n : ℤ)) inferInstance ≤ sigmaGE' X (n : ℤ) :=
    le_iSup₂_of_le (n : ℤ) (Set.mem_Ici.mpr le_rfl) le_rfl
  have hGEmono : sigmaGE' X (n : ℤ) ≤ sigmaGE' X 0 :=
    iSup₂_le fun s hs => le_iSup₂_of_le s
      (Set.mem_Ici.mpr (le_trans (Int.natCast_nonneg n) (Set.mem_Ici.mp hs))) le_rfl
  refine le_antisymm ?_
    (betaMixCoeff_mono' (mΩ := (inferInstance : MeasurableSpace Ω)) (hLEΩ 0) (hGEΩ _)
      hm0le hmnle)
  refine Real.sSup_le ?_
    (betaMixCoeff_nonneg' (mΩ := (inferInstance : MeasurableSpace Ω)) hm0Ω hmnΩ)
  rintro s ⟨I, J, A, B, hA, hB, hdA, hdB, hcA, hcB, rfl⟩
  have hBΩ : ∀ j, MeasurableSet (B j) := fun j => hGEΩ (n : ℤ) _ (hB j)
  -- Step A: the first side collapses to `σ(X_0)` (Markov property at time `0`)
  have hbrick0 : ∀ j, ∃ p : Ω → ℝ,
      Measurable[MeasurableSpace.comap (X 0) inferInstance] p ∧
      μ[(B j).indicator (fun _ => (1 : ℝ)) | sigmaLE' X 0] =ᵐ[μ] p := by
    intro j
    obtain ⟨p, hpm, hpe⟩ := condExp_sigmaGE_versionable hmeas hmarkov 0 (hGEmono _ (hB j))
    exact ⟨p, hpm.measurable, hpe⟩
  choose q hqm hqe using hbrick0
  obtain ⟨K, A', hA'm, hA'd, hA'c, hstepA⟩ :=
    beta_shrink_left (μ := μ) (hLEΩ 0) hm0le hA hdA hcA hBΩ hqm hqe
  -- Step B: the second side collapses to `σ(X_n)` (Markov property at time `n`)
  have hbrickn : ∀ j, ∃ p : Ω → ℝ,
      Measurable[MeasurableSpace.comap (X (n : ℤ)) inferInstance] p ∧
      μ[(B j).indicator (fun _ => (1 : ℝ)) | sigmaLE' X (n : ℤ)] =ᵐ[μ] p := by
    intro j
    obtain ⟨p, hpm, hpe⟩ := condExp_sigmaGE_versionable hmeas hmarkov (n : ℤ) (hB j)
    exact ⟨p, hpm.measurable, hpe⟩
  choose rr hrrm hrre using hbrickn
  obtain ⟨L, C, hCm, hCd, hCc, hstepB⟩ :=
    beta_shrink_right (μ := μ) (hLEΩ (n : ℤ)) hmnΩ (fun k => hm0leN _ (hA'm k)) hBΩ hdB hcB
      hrrm hrre
  have hfin := le_betaMixCoeff (mΩ := (inferInstance : MeasurableSpace Ω)) (μ := μ) hm0Ω hmnΩ
    hA'm hCm hA'd hA'c hCd hCc
  have hchain : ∑ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      ≤ ∑ k, ∑ l, |(μ (A' k ∩ C l)).toReal - (μ (A' k)).toReal * (μ (C l)).toReal| :=
    hstepA.trans hstepB
  linarith

/-! ### REFUTATION of Davydov's identity at a general state space (2026-08-09, wave 6)

Davydov's identity is **false** as frozen: at an arbitrary measurable state space `E` the
`≥` half fails, and it fails by the maximal amount (`0 = β` against `1 = ∫ tvDist dF`).

**The witness.** Take `E = Ω = Set ℕ` with the **countable–cocountable** σ-algebra
`{A | A countable ∨ Aᶜ countable}`, `μ = F` the `0`–`1` measure (`F A = 0` if `A` is
countable, `= 1` if `Aᶜ` is), `X_t = id` for every `t`, and `κ = Kernel.id`, so
`κⁿ = Kernel.id` and `κⁿ(x, ·) = δ_x`. Then:

* `IsMarkovOf X κ μ` holds — every `sigmaLE' X t` is the whole σ-algebra, so the
  conditional expectation is the identity and `(κⁿ(X_t ω))(B) = 1_B(ω)` on the nose;
* the one-dimensional marginals are all `F`, so `hmarg` holds;
* **`tvDist (δ_x) F = 1` for every `x`** — the singleton `{x}` is measurable (countable)
  and separates `δ_x` from `F` — hence the right-hand side is `1`;
* **every finite measurable partition sum vanishes**, hence `β = 0`. Indeed `F` is a
  `0`–`1` measure, so in each partition exactly one cell `A_{i₀}` is cocountable and all
  the others are countable (`exists_big_cell` below); every product
  `F(A_i)·F(B_j)` and every `F(A_i ∩ B_j)` is then `0` except at `(i₀, j₀)`, where both
  are `1` (an intersection of two cocountable sets is cocountable). So each summand
  `|F(A_i ∩ B_j) − F(A_i)F(B_j)|` is `0`.

**Diagnosis.** `β` is a supremum over *finite* partitions of the two marginal
σ-algebras, i.e. over the algebra of measurable *rectangles*; `∫ tvDist dF` is the
`F`-average of a supremum taken **pointwise in `x`**, i.e. over the (much larger) product
σ-algebra of `E × E`. Turning the second into the first needs two things that hold only
for a countably generated (e.g. standard Borel) `E`: a **jointly measurable Hahn
selection** for `κⁿ(x,·) − F` (this is `ProbabilityTheory.Kernel.rnDerivAux`, which
Mathlib provides exactly under `[MeasurableSpace.CountablyGenerated]`), and the
**approximation of a product-measurable set by finite unions of rectangles**. In the
witness the Hahn set is the diagonal `{(x, x)}`, which the rectangle algebra of the
countable–cocountable σ-algebra cannot see at all.

**REPAIR (frozen, so not applied here).** Add `[MeasurableSpace.CountablyGenerated E]`
to `betaMixCoeff_two_marginal_eq_integral_tvDist_brick` and to its consumer
`betaMixCoeff_eq_integral_tvDist_of_markov`. The scalar corollary
`betaCoeff_eq_integral_tvDist_debt` (`E = ℝ`) is **unaffected in substance** — `ℝ` is
countably generated — but as long as it is derived from the general theorem it inherits
the defect, so the repair must be made upstream. Nothing else in this file, or in
`Mixing/Relations.lean`, depends on the identity: the model routes go through the
*inequality* `betaMixCoeff_two_marginal_le_of_envelope`, whose proof (a `≤` bound against
a supplied envelope) never inspects `tvDist` pointwise and is therefore correct at a
general `E`.

The two `theorem`s at the end of this section are the formalized witness. -/

section DavydovWitness

/-- Carrier of the Davydov witness: `Set ℕ` (uncountable, by Cantor's theorem), equipped
below with the countable–cocountable σ-algebra. -/
private def Cocnt : Type := Set ℕ

private instance instCocnt : MeasurableSpace Cocnt where
  MeasurableSet' A := A.Countable ∨ Aᶜ.Countable
  measurableSet_empty := Or.inl Set.countable_empty
  measurableSet_compl A h := by
    rcases h with h | h
    · exact Or.inr (by rwa [compl_compl])
    · exact Or.inl h
  measurableSet_iUnion f hf := by
    by_cases h : ∀ i, (f i).Countable
    · exact Or.inl (Set.countable_iUnion h)
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      rcases hf i with h' | h'
      · exact absurd h' hi
      · refine Or.inr (Set.Countable.mono ?_ h')
        rw [Set.compl_iUnion]
        exact Set.iInter_subset _ i

private lemma not_countable_univ_cocnt : ¬ (Set.univ : Set Cocnt).Countable := by
  rw [Set.countable_univ_iff]
  intro h
  obtain ⟨f, hf⟩ := exists_injective_nat Cocnt
  exact Function.cantor_injective f hf

private lemma not_countable_of_compl {A : Set Cocnt} (h : Aᶜ.Countable) : ¬ A.Countable := by
  intro hA
  refine not_countable_univ_cocnt ?_
  have hu : (Set.univ : Set Cocnt) = A ∪ Aᶜ := by simp
  rw [hu]
  exact hA.union h

open Classical in
/-- The `0`–`1` measure of the countable–cocountable σ-algebra. -/
private noncomputable def cocnt : Measure Cocnt :=
  Measure.ofMeasurable (fun A _ => if A.Countable then 0 else 1)
    (by simp)
    (by
      intro f hf hd
      show (if (⋃ i, f i).Countable then (0 : ℝ≥0∞) else 1)
        = ∑' i, (if (f i).Countable then (0 : ℝ≥0∞) else 1)
      by_cases h : ∀ i, (f i).Countable
      · rw [if_pos (Set.countable_iUnion h)]
        have hz : ∀ i, (if (f i).Countable then (0 : ℝ≥0∞) else 1) = 0 := fun i => if_pos (h i)
        simp [hz]
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        have hci : (f i)ᶜ.Countable := (hf i).resolve_left hi
        have h1 : ¬ (⋃ j, f j).Countable := fun hc => hi (hc.mono (Set.subset_iUnion f i))
        rw [if_neg h1]
        have hsingle : ∀ j, j ≠ i → (if (f j).Countable then (0 : ℝ≥0∞) else 1) = 0 := by
          intro j hj
          have hsub : f j ⊆ (f i)ᶜ := fun x hx => Set.disjoint_left.mp (hd hj) hx
          exact if_pos (hci.mono hsub)
        rw [tsum_eq_single i hsingle, if_neg hi])

open Classical in
private lemma cocnt_apply {A : Set Cocnt} (hA : MeasurableSet A) :
    cocnt A = if A.Countable then 0 else 1 :=
  Measure.ofMeasurable_apply A hA

private lemma cocnt_of_countable {A : Set Cocnt} (hA : A.Countable) : cocnt A = 0 := by
  classical
  rw [cocnt_apply (Or.inl hA), if_pos hA]

private lemma cocnt_of_cocountable {A : Set Cocnt} (hA : Aᶜ.Countable) : cocnt A = 1 := by
  classical
  rw [cocnt_apply (Or.inr hA), if_neg (not_countable_of_compl hA)]

private instance : IsProbabilityMeasure cocnt :=
  ⟨cocnt_of_cocountable (by simp)⟩

/-- The `n`-step law `δ_x` is at total-variation distance `1` from the witness marginal:
the singleton `{x}` is measurable and separates them. -/
private lemma tvDist_dirac_cocnt (x : Cocnt) :
    StatLean.Minimaxity.tvDist (Measure.dirac x) cocnt = 1 := by
  refine le_antisymm (StatLean.Minimaxity.tvDist_le_one _ _) ?_
  have hs : MeasurableSet ({x} : Set Cocnt) := Or.inl (Set.countable_singleton x)
  have h1 : (Measure.dirac x) ({x} : Set Cocnt) = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_singleton x)
  have h2 : cocnt ({x} : Set Cocnt) = 0 := cocnt_of_countable (Set.countable_singleton x)
  have hle : (Measure.dirac x) ({x} : Set Cocnt) - cocnt ({x} : Set Cocnt)
      ≤ StatLean.Minimaxity.tvDist (Measure.dirac x) cocnt :=
    le_iSup₂ (f := fun s (_ : MeasurableSet s) => (Measure.dirac x) s - cocnt s) {x} hs
  rw [h1, h2] at hle
  simpa using hle

/-- In a finite measurable partition of the witness space exactly one cell is
cocountable; all the others are countable. -/
private lemma exists_big_cell {I : ℕ} {A : Fin I → Set Cocnt}
    (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise fun i i' => Disjoint (A i) (A i'))
    (hc : (⋃ i, A i) = Set.univ) :
    ∃ i₀, (A i₀)ᶜ.Countable ∧ ∀ i, i ≠ i₀ → (A i).Countable := by
  by_cases h : ∀ i, (A i).Countable
  · exact absurd (hc ▸ Set.countable_iUnion h) not_countable_univ_cocnt
  · push_neg at h
    obtain ⟨i₀, hi₀⟩ := h
    have hci : (A i₀)ᶜ.Countable := (hA i₀).resolve_left hi₀
    refine ⟨i₀, hci, fun i hi => hci.mono fun x hx => ?_⟩
    exact Set.disjoint_left.mp (hd hi) hx

/-- **Every** finite partition sum of the witness vanishes: its β-coefficient is `0`. -/
private lemma betaMixCoeff_cocnt_eq_zero :
    betaMixCoeff cocnt instCocnt instCocnt = 0 := by
  have hdef : betaMixCoeff cocnt instCocnt instCocnt
      = sSup {r : ℝ | ∃ (I J : ℕ) (A : Fin I → Set Cocnt) (B : Fin J → Set Cocnt),
        (∀ i, MeasurableSet[instCocnt] (A i)) ∧ (∀ j, MeasurableSet[instCocnt] (B j)) ∧
        (Pairwise fun i i' => Disjoint (A i) (A i')) ∧
        (Pairwise fun j j' => Disjoint (B j) (B j')) ∧
        (⋃ i, A i) = Set.univ ∧ (⋃ j, B j) = Set.univ ∧
        r = (1 / 2) * ∑ i, ∑ j,
          |(cocnt (A i ∩ B j)).toReal - (cocnt (A i)).toReal * (cocnt (B j)).toReal|} := rfl
  have hset : {r : ℝ | ∃ (I J : ℕ) (A : Fin I → Set Cocnt) (B : Fin J → Set Cocnt),
      (∀ i, MeasurableSet[instCocnt] (A i)) ∧ (∀ j, MeasurableSet[instCocnt] (B j)) ∧
      (Pairwise fun i i' => Disjoint (A i) (A i')) ∧
      (Pairwise fun j j' => Disjoint (B j) (B j')) ∧
      (⋃ i, A i) = Set.univ ∧ (⋃ j, B j) = Set.univ ∧
      r = (1 / 2) * ∑ i, ∑ j,
        |(cocnt (A i ∩ B j)).toReal - (cocnt (A i)).toReal * (cocnt (B j)).toReal|}
      = {(0 : ℝ)} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨I, J, A, B, hA, hB, hdA, hdB, hcA, hcB, rfl⟩
      obtain ⟨i₀, hi₀, hiz⟩ := exists_big_cell hA hdA hcA
      obtain ⟨j₀, hj₀, hjz⟩ := exists_big_cell hB hdB hcB
      have hterm : ∀ i j, |(cocnt (A i ∩ B j)).toReal
          - (cocnt (A i)).toReal * (cocnt (B j)).toReal| = 0 := by
        intro i j
        by_cases hi : i = i₀
        · by_cases hj : j = j₀
          · subst hi; subst hj
            have hab : (A i ∩ B j)ᶜ.Countable := by
              rw [Set.compl_inter]; exact hi₀.union hj₀
            rw [cocnt_of_cocountable hab, cocnt_of_cocountable hi₀,
              cocnt_of_cocountable hj₀]
            simp
          · have hBj : (B j).Countable := hjz j hj
            rw [cocnt_of_countable hBj,
              cocnt_of_countable (hBj.mono Set.inter_subset_right)]
            simp
        · have hAi : (A i).Countable := hiz i hi
          rw [cocnt_of_countable hAi,
            cocnt_of_countable (hAi.mono Set.inter_subset_left)]
          simp
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_eq_zero fun j _ => hterm i j]
      simp
    · rintro rfl
      refine ⟨1, 1, fun _ => Set.univ, fun _ => Set.univ, fun _ => MeasurableSet.univ,
        fun _ => MeasurableSet.univ, ?_, ?_, Set.iUnion_const _, Set.iUnion_const _, ?_⟩
      · exact fun i i' h => absurd (Subsingleton.elim i i') h
      · exact fun j j' h => absurd (Subsingleton.elim j j') h
      · simp
  rw [hdef, hset, csSup_singleton]

/-- The witness process: the identity at every time. -/
private def Xw : ℤ → Cocnt → Cocnt := fun _ => id

private lemma comap_Xw (t : ℤ) :
    MeasurableSpace.comap (Xw t) instCocnt = instCocnt := MeasurableSpace.comap_id

private lemma sigmaLE'_Xw (t : ℤ) : sigmaLE' Xw t = instCocnt :=
  le_antisymm (iSup₂_le fun s _ => le_of_eq (comap_Xw s))
    (le_iSup₂_of_le t (Set.mem_Iic.mpr le_rfl) (le_of_eq (comap_Xw t).symm))

private lemma sigmaGE'_Xw (t : ℤ) : sigmaGE' Xw t = instCocnt :=
  le_antisymm (iSup₂_le fun s _ => le_of_eq (comap_Xw s))
    (le_iSup₂_of_le t (Set.mem_Ici.mpr le_rfl) (le_of_eq (comap_Xw t).symm))

private lemma kernelId_pow (n : ℕ) :
    ((Kernel.id : Kernel Cocnt Cocnt) ^ n) = Kernel.id := one_pow n

private lemma markov_Xw : IsMarkovOf Xw (Kernel.id : Kernel Cocnt Cocnt) cocnt := by
  intro t n B hB
  have hrhs : (fun ω => (((Kernel.id : Kernel Cocnt Cocnt) ^ n) (Xw t ω) B).toReal)
      = B.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    rw [kernelId_pow, Kernel.id_apply]
    by_cases hw : ω ∈ B <;>
      simp [Xw, Measure.dirac_apply' _ hB, Set.indicator_apply, hw]
  have hlhs : (fun ω => B.indicator (fun _ => (1 : ℝ)) (Xw (t + n) ω))
      = B.indicator (fun _ => (1 : ℝ)) := rfl
  have hsm : StronglyMeasurable[sigmaLE' Xw t] (B.indicator (fun _ => (1 : ℝ))) := by
    rw [sigmaLE'_Xw]
    exact (measurable_const.indicator hB).stronglyMeasurable
  have hint : Integrable (B.indicator (fun _ => (1 : ℝ))) cocnt :=
    (integrable_const (1 : ℝ)).indicator hB
  rw [hrhs, hlhs, condExp_of_stronglyMeasurable (le_of_eq (sigmaLE'_Xw t)) hsm hint]

private lemma map_Xw (t : ℤ) : cocnt.map (Xw t) = cocnt := Measure.map_id

private lemma davydov_rhs_eq_one (n : ℕ) :
    (∫⁻ x, StatLean.Minimaxity.tvDist (((Kernel.id : Kernel Cocnt Cocnt) ^ n) x)
      (cocnt.map (Xw 0)) ∂(cocnt.map (Xw 0))) = 1 := by
  simp_rw [map_Xw, kernelId_pow, Kernel.id_apply, tvDist_dirac_cocnt]
  simp

/-- **REFUTATION (formalized witness).** `betaMixCoeff_two_marginal_eq_integral_tvDist_brick`
is FALSE as frozen: at a general measurable state space its two sides are `0` and `1`.
See the section docstring for the diagnosis and the repair
(`[MeasurableSpace.CountablyGenerated E]`). -/
theorem betaMixCoeff_two_marginal_eq_integral_tvDist_false :
    ¬ ∀ {Ω : Type} [MeasurableSpace Ω] {E : Type} [MeasurableSpace E] {μ : Measure Ω}
        [IsProbabilityMeasure μ] {X : ℤ → Ω → E}, (∀ t, Measurable (X t)) →
        (∀ s t : ℤ, μ.map (X s) = μ.map (X t)) →
        ∀ {κ : Kernel E E} [IsMarkovKernel κ], IsMarkovOf X κ μ → ∀ n : ℕ,
        betaMixCoeff μ (MeasurableSpace.comap (X 0) inferInstance)
            (MeasurableSpace.comap (X ((n : ℤ))) inferInstance)
          = (∫⁻ x, StatLean.Minimaxity.tvDist ((κ ^ n) x) (μ.map (X 0))
              ∂(μ.map (X 0))).toReal := by
  intro h
  have hkey := h (μ := cocnt) (X := Xw) (fun _ => measurable_id) (fun _ _ => rfl)
    (κ := (Kernel.id : Kernel Cocnt Cocnt)) markov_Xw 1
  rw [comap_Xw, comap_Xw, betaMixCoeff_cocnt_eq_zero, davydov_rhs_eq_one] at hkey
  norm_num at hkey

/-- **REFUTATION (formalized witness).** The same witness refutes the *public* theorem
`betaMixCoeff_eq_integral_tvDist_of_markov` at a general state space — that theorem is
proved *over* the open brick, so nothing is unsound, but its statement needs the same
`[MeasurableSpace.CountablyGenerated E]` repair. -/
theorem betaMixCoeff_eq_integral_tvDist_of_markov_false :
    ¬ ∀ {Ω : Type} [MeasurableSpace Ω] {E : Type} [MeasurableSpace E] {μ : Measure Ω}
        [IsProbabilityMeasure μ] {X : ℤ → Ω → E}, (∀ t, Measurable (X t)) →
        (∀ s t : ℤ, μ.map (X s) = μ.map (X t)) →
        ∀ {κ : Kernel E E} [IsMarkovKernel κ], IsMarkovOf X κ μ → ∀ n : ℕ,
        betaMixCoeff μ (sigmaLE' X 0) (sigmaGE' X ((n : ℤ)))
          = (∫⁻ x, StatLean.Minimaxity.tvDist ((κ ^ n) x) (μ.map (X 0))
              ∂(μ.map (X 0))).toReal := by
  intro h
  have hkey := h (μ := cocnt) (X := Xw) (fun _ => measurable_id) (fun _ _ => rfl)
    (κ := (Kernel.id : Kernel Cocnt Cocnt)) markov_Xw 1
  rw [sigmaLE'_Xw, sigmaGE'_Xw, betaMixCoeff_cocnt_eq_zero, davydov_rhs_eq_one] at hkey
  norm_num at hkey

end DavydovWitness

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
  hard one (it is where the finite-partition formula meets the disintegration).

**Status (2026-08-09, wave 6): FALSE AS FROZEN — see the section
`REFUTATION of Davydov's identity at a general state space` immediately above, and the
formalized witness `betaMixCoeff_two_marginal_eq_integral_tvDist_false` (axiom-clean).**
At `E = Set ℕ` with the countable–cocountable σ-algebra, `μ = F` the `0`–`1` measure,
`X_t = id` and `κ = Kernel.id`, every hypothesis holds, the left-hand side is `0` and the
right-hand side is `1`. The `≤` half (the display below) is *not* what fails; the `≥` half
does, and it fails maximally. The repair is `[MeasurableSpace.CountablyGenerated E]` on
this brick and on `betaMixCoeff_eq_integral_tvDist_of_markov` — the hypothesis under which
Mathlib supplies the jointly measurable Hahn selection (`Kernel.rnDerivAux`) that the `≥`
half needs. Nothing downstream is affected: the model routes of `Mixing/Relations.lean`
go through the *inequality* `betaMixCoeff_two_marginal_le_of_envelope`, which is correct
at a general `E`. The `sorry` therefore stays, and it is not a debt of *proof* but of
*statement*. The wave-4/5 analysis is kept below as the record of the two halves.

**Status (2026-08-09, wave 4): the sole remaining `sorry` of this file.** The other two
bricks are now proved, so this is exactly what stands between the file and a `sorry`-free
`betaCoeff_eq_integral_tvDist_debt`. Sharpened assessment of the two halves:

* `≤` is now *within reach* with the machinery added in this wave. Its three inputs all
  exist: the one-event Markov identity `μ(X_0⁻¹U ∩ X_n⁻¹V) = ∫⁻_U (κⁿ x)(V) dF(x)` is the
  `hone` step inside `markov_setIntegral_eq`; `Σ_i |∫_{U_i} φ| ≤ ∫ |φ|` for an `F`-a.e.
  partition `{U_i}` is `sum_abs_setIntegral_le` (the `U_i` are `F`-a.e. disjoint because the
  `A_i = X_0⁻¹(U_i)` are disjoint); and `Σ_j |P V_j − Q V_j| ≤ 2 · tvDist P Q` follows by
  splitting the `j`'s by sign and applying `tvDist` to the two unions, after replacing
  `V_j` by `V_j \ ⋃_{j' < j} V_{j'}` — which changes neither the preimages `B_j` (they are
  disjoint) nor the values `F(V_j) = μ(B_j)` (strict stationarity gives
  `μ.map (X n) = μ.map (X 0) = F`).
* `≥` needs two ingredients that are *not* in the pin and are not measure-theoretic
  plumbing: (i) a **jointly measurable Hahn selection** for `κⁿ(x,·) − F`, i.e. a kernel
  Radon–Nikodym/Lebesgue decomposition (`ProbabilityTheory.Kernel.rnDeriv`-style) giving a
  product-measurable `H ⊆ ℝ × ℝ` with `tvDist (κⁿ x) F = (κⁿ x)(H_x) − F(H_x)` for
  `F`-a.e. `x`; and (ii) **approximation of a product-measurable set by finite unions of
  rectangles** in `F ⊗ F`-measure, together with the conversion of such a union into a
  *partition pair* (the finite algebra generated by the `U`'s and the `V`'s). Neither is
  a `sorry`-filling task; both are new `ForMathlib` bricks. -/
private lemma betaMixCoeff_two_marginal_eq_integral_tvDist_brick [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    -- only the equality of the one-dimensional marginals is used (wave 5: this replaces
    -- the frozen `IsStrictlyStationary`, which is unavailable for a vector state)
    (hmarg : ∀ s t : ℤ, μ.map (X s) = μ.map (X t))
    {κ : ProbabilityTheory.Kernel E E} [ProbabilityTheory.IsMarkovKernel κ]
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

**Status (2026-08-09, wave 5).** Split into its two independent halves, of which the
first is now **PROVED**: `betaMixCoeff_two_marginal_of_markov` (Bradley's collapse to the
two marginals) and `betaMixCoeff_two_marginal_eq_integral_tvDist_brick` (Davydov's identity
proper — the only remaining `sorry` of this file; its docstring records the verified
calibration and the proof of each direction).

**Status (2026-08-09, wave 6): FALSE AS FROZEN at a general `E`** — formalized witness
`betaMixCoeff_eq_integral_tvDist_of_markov_false` above. It is proved *over* the open
brick, so nothing is unsound; the statement needs
`[MeasurableSpace.CountablyGenerated E]`, which `ℝ` has, so the scalar corollary
`betaCoeff_eq_integral_tvDist_debt` is true in substance and only inherits the defect
through this general form.

Stated for a general state space `E`; the scalar form is
`betaCoeff_eq_integral_tvDist_debt` below. -/
theorem betaMixCoeff_eq_integral_tvDist_of_markov [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    (hmarg : ∀ s t : ℤ, μ.map (X s) = μ.map (X t))
    {κ : ProbabilityTheory.Kernel E E} [ProbabilityTheory.IsMarkovKernel κ]
    -- USER-INPUT: Markov representation; FY §2.6.1(vi) setting
    (hmarkov : IsMarkovOf X κ μ) (n : ℕ) :
    betaMixCoeff μ (sigmaLE' X 0) (sigmaGE' X (n : ℤ))
      = (∫⁻ x, StatLean.Minimaxity.tvDist ((κ ^ n) x) (μ.map (X 0))
          ∂(μ.map (X 0))).toReal := by
  rw [betaMixCoeff_two_marginal_of_markov hmeas hmarkov n,
    betaMixCoeff_two_marginal_eq_integral_tvDist_brick hmeas hmarg hmarkov n]

/-- **FY eq. (2.59), derived from the (2.58) debt**, general state space: a pointwise
geometric envelope `tvDist (κⁿ x) F ≤ A(x) ρⁿ` with `A` integrable gives
`β(n) ≤ ρⁿ ∫ A dF`. -/
theorem betaMixCoeff_le_of_geometric_envelope [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    (hmarg : ∀ s t : ℤ, μ.map (X s) = μ.map (X t))
    {κ : ProbabilityTheory.Kernel E E} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ)
    {A : E → ℝ} (hA0 : ∀ x, 0 ≤ A x)
    (hAint : Integrable A (μ.map (X 0)))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    -- USER-INPUT: geometric TV envelope; FY eq. (2.59)
    (henv : ∀ (x : E) (n : ℕ),
      StatLean.Minimaxity.tvDist ((κ ^ n) x) (μ.map (X 0))
        ≤ ENNReal.ofReal (A x * ρ ^ n)) :
    ∀ n : ℕ, betaMixCoeff μ (sigmaLE' X 0) (sigmaGE' X (n : ℤ))
      ≤ (∫ x, A x ∂(μ.map (X 0))) * ρ ^ n := by
  set F : Measure E := μ.map (X 0) with hF
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ (∫ x, A x ∂F) * ρ ^ n := fun n =>
    mul_nonneg (integral_nonneg hA0) (pow_nonneg hρ0 n)
  -- (2.59): integrate the pointwise envelope of (2.58).
  · intro n
    rw [betaMixCoeff_eq_integral_tvDist_of_markov hmeas hmarg hmarkov n]
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

/-! ### Scalar corollaries (`E = ℝ`)

The bridge above is stated for an arbitrary measurable state space; `sigmaLE'`/`sigmaGE'`
are definitionally `Process/Defs.lean`'s `sigmaLE`/`sigmaGE` at `E = ℝ`, so the frozen
real-valued statements of FY §2.6.1 are immediate specialisations. The only work is
extracting the *equality of one-dimensional marginals* from strict stationarity. -/

/-- Strict stationarity equalises the one-dimensional marginals. -/
lemma map_eq_map_of_isStrictlyStationary [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    (s t : ℤ) : μ.map (X s) = μ.map (X t) := by
  have h := hstat 1 (fun _ => t) (s - t)
  have hts : t + (s - t) = s := by ring
  simp only [hts] at h
  have hm1 : Measurable fun ω (_ : Fin 1) => X s ω :=
    measurable_pi_lambda _ fun _ => hmeas _
  have hm2 : Measurable fun ω (_ : Fin 1) => X t ω :=
    measurable_pi_lambda _ fun _ => hmeas _
  have hev : Measurable fun f : Fin 1 → ℝ => f 0 := measurable_pi_apply 0
  have e1 : (μ.map fun ω (_ : Fin 1) => X s ω).map (fun f : Fin 1 → ℝ => f 0)
      = μ.map (X s) := by rw [Measure.map_map hev hm1]; rfl
  have e2 : (μ.map fun ω (_ : Fin 1) => X t ω).map (fun f : Fin 1 → ℝ => f 0)
      = μ.map (X t) := by rw [Measure.map_map hev hm2]; rfl
  rw [← e1, ← e2, h]

/-- **DEBT (Davydov 1973; FY eq. (2.58))**, scalar form: for a strictly stationary Markov
process with kernel `κ` and time-`0` marginal `F = μ ∘ X_0⁻¹`,
`β(n) = ∫ tvDist (κⁿ x) F dF(x)`. Specialisation of
`betaMixCoeff_eq_integral_tvDist_of_markov`. -/
theorem betaCoeff_eq_integral_tvDist_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {κ : ProbabilityTheory.Kernel ℝ ℝ} [ProbabilityTheory.IsMarkovKernel κ]
    -- USER-INPUT: Markov representation; FY §2.6.1(vi) setting
    (hmarkov : IsMarkovOf X κ μ) (n : ℕ) :
    betaCoeff X μ n
      = (∫⁻ x, StatLean.Minimaxity.tvDist ((κ ^ n) x) (μ.map (X 0))
          ∂(μ.map (X 0))).toReal :=
  betaMixCoeff_eq_integral_tvDist_of_markov hmeas
    (map_eq_map_of_isStrictlyStationary hmeas hstat) hmarkov n

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
  have hkey : ∀ n : ℕ, betaCoeff X μ n ≤ (∫ x, A x ∂(μ.map (X 0))) * ρ ^ n :=
    betaMixCoeff_le_of_geometric_envelope hmeas
      (map_eq_map_of_isStrictlyStationary hmeas hstat) hmarkov hA0 hAint hρ0 henv
  refine ⟨hkey, ?_⟩
  refine squeeze_zero (fun n => ?_) hkey ?_
  · rw [betaCoeff_eq_integral_tvDist_debt hmeas hstat hmarkov n]
    exact ENNReal.toReal_nonneg
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul
      (∫ x, A x ∂(μ.map (X 0)))
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
2. *π-system.* Those products form a π-system generating `sigmaGE' X t`.
3. *Dynkin.* The `B`'s satisfying the conclusion form a λ-system (`condExp` is linear,
   monotone and continuous along monotone limits), so `MeasurableSpace.induction_on_inter`
   upgrades step 1 to all of `sigmaGE' X t`.

This is the classical statement that the past and the future of a Markov chain are
conditionally independent given the present (Bradley, *Introduction to Strong Mixing
Conditions*, ch. 7); it is genuinely the analytic content of the two-marginal reduction and
is left as a single named debt. Everything else in
`alphaCoeff_eq_two_marginal_debt` is proved from it. -/
private lemma condExp_sigmaGE_indicator_brick [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    {κ : ProbabilityTheory.Kernel E E} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ) (t : ℤ) {B : Set Ω} (hB : MeasurableSet[sigmaGE' X t] B) :
    ∃ p : Ω → ℝ, StronglyMeasurable[MeasurableSpace.comap (X t) inferInstance] p ∧
      μ[B.indicator (fun _ => (1:ℝ)) | sigmaLE' X t] =ᵐ[μ] p :=
  condExp_sigmaGE_versionable hmeas hmarkov t hB

/-- **Bradley Thms 4.1–4.2; FY §2.6.1(vi)**, general state space: for a Markov
process the α-coefficient collapses to the two-marginal coefficient of `(X_0, X_n)`:
`α(σ{X_s : s ≤ 0}, σ{X_s : s ≥ n}) = α(σ(X_0), σ(X_n))`. (Same statement holds for
β, ρ, φ, ψ; α is the consumed one.)

**Status (2026-08-09, wave 5).** PROVED, and axiom-clean; generalized from `Kernel ℝ ℝ`
to `Kernel E E` (strict stationarity was never used, and is dropped). Its single input
`condExp_sigmaGE_indicator_brick` (the Markov property for the whole future σ-algebra) is
itself now proved (see the module docstring).
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
theorem alphaMixCoeff_two_marginal_of_markov [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    {κ : ProbabilityTheory.Kernel E E} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ) (n : ℕ) :
    alphaMixCoeff μ (sigmaLE' X 0) (sigmaGE' X (n : ℤ))
      = alphaMixCoeff μ (MeasurableSpace.comap (X 0) inferInstance)
          (MeasurableSpace.comap (X n) inferInstance) := by
  have hLEΩ : ∀ t : ℤ, sigmaLE' X t ≤ (inferInstance : MeasurableSpace Ω) :=
    fun t => iSup₂_le fun s _ => (hmeas s).comap_le
  have hGEΩ : ∀ t : ℤ, sigmaGE' X t ≤ (inferInstance : MeasurableSpace Ω) :=
    fun t => iSup₂_le fun s _ => (hmeas s).comap_le
  have hm0le : MeasurableSpace.comap (X 0) inferInstance ≤ sigmaLE' X 0 :=
    le_iSup₂_of_le (0 : ℤ) (Set.mem_Iic.mpr le_rfl) le_rfl
  have hm0leN : MeasurableSpace.comap (X 0) inferInstance ≤ sigmaLE' X (n : ℤ) :=
    le_iSup₂_of_le (0 : ℤ) (Set.mem_Iic.mpr (Int.natCast_nonneg n)) le_rfl
  have hmnle : MeasurableSpace.comap (X (n : ℤ)) inferInstance ≤ sigmaGE' X (n : ℤ) :=
    le_iSup₂_of_le (n : ℤ) (Set.mem_Ici.mpr le_rfl) le_rfl
  have hmnΩ : MeasurableSpace.comap (X (n : ℤ)) inferInstance
      ≤ (inferInstance : MeasurableSpace Ω) := (hmeas _).comap_le
  have hm0Ω : MeasurableSpace.comap (X 0) inferInstance
      ≤ (inferInstance : MeasurableSpace Ω) := (hmeas _).comap_le
  have hGEmono : sigmaGE' X (n : ℤ) ≤ sigmaGE' X 0 :=
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
  have hcond0 : μ[hB'|sigmaLE' X 0] =ᵐ[μ] fun ω => p₀ ω - (μ B).toReal := by
    have h1 := condExp_sub (μ := μ) ((integrable_const (1:ℝ)).indicator hBm)
      (integrable_const ((μ B).toReal)) (sigmaLE' X 0)
    have h2 : μ[fun _ : Ω => (μ B).toReal|sigmaLE' X 0] = fun _ => (μ B).toReal :=
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
  have hA''sm : StronglyMeasurable[sigmaLE' X (n : ℤ)] hA'' :=
    (stronglyMeasurable_const.indicator (hm0leN _ hA'm₀)).sub stronglyMeasurable_const
  obtain ⟨pn, hpnm, hpne⟩ := condExp_sigmaGE_indicator_brick hmeas hmarkov (n : ℤ) hB
  -- `w := μ[1_B | 𝓕_{≤n}]` lies in `[0,1]` a.e.
  have hw0 : (0 : Ω → ℝ) ≤ᵐ[μ] μ[B.indicator (fun _ => (1:ℝ))|sigmaLE' X (n : ℤ)] :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => indicator_one_nonneg B ω)
  have hw1 : μ[B.indicator (fun _ => (1:ℝ))|sigmaLE' X (n : ℤ)] ≤ᵐ[μ] fun _ => (1:ℝ) := by
    have := condExp_mono (m := sigmaLE' X (n : ℤ))
      ((integrable_const (μ := μ) (1:ℝ)).indicator hBm) (integrable_const (μ := μ) (1:ℝ))
      (Filter.Eventually.of_forall fun ω => indicator_one_le_one B ω)
    rw [condExp_const (μ := μ) (hLEΩ (n : ℤ))] at this
    exact this
  set Y : Ω → ℝ := fun ω => max 0 (min 1 (pn ω)) with hYdef
  have hYsm : StronglyMeasurable[MeasurableSpace.comap (X (n : ℤ)) inferInstance] Y :=
    (Measurable.max measurable_const
      (Measurable.min measurable_const hpnm.measurable)).stronglyMeasurable
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => le_max_left _ _
  have hY1 : ∀ ω, Y ω ≤ 1 := fun ω => max_le zero_le_one (min_le_left _ _)
  have hYw : Y =ᵐ[μ] μ[B.indicator (fun _ => (1:ℝ))|sigmaLE' X (n : ℤ)] := by
    filter_upwards [hw0, hw1, hpne] with ω e0 e1 e2
    have e0' : (0:ℝ) ≤ pn ω := by rw [← e2]; exact e0
    have e1' : pn ω ≤ 1 := by rw [← e2]; exact e1
    rw [hYdef]
    simp only
    rw [min_eq_right e1', max_eq_right e0', e2]
  -- transfer the covariance onto `Y`
  have hkey : (μ (A' ∩ B)).toReal - (μ A').toReal * (μ B).toReal = ∫ ω, Y ω * hA'' ω ∂μ := by
    have e1 : ∫ ω, hA'' ω * B.indicator (fun _ => (1:ℝ)) ω ∂μ
        = ∫ ω, hA'' ω * (μ[B.indicator (fun _ => (1:ℝ))|sigmaLE' X (n : ℤ)]) ω ∂μ := by
      have hpull := condExp_stronglyMeasurable_mul_of_bound₀ (hLEΩ (n : ℤ))
        hA''sm.aestronglyMeasurable ((integrable_const (μ := μ) (1:ℝ)).indicator hBm) 1
        (Filter.Eventually.of_forall fun ω => norm_centred_indicator_le_one A' ω)
      calc ∫ ω, hA'' ω * B.indicator (fun _ => (1:ℝ)) ω ∂μ
          = ∫ ω, (μ[hA'' * B.indicator (fun _ => (1:ℝ))|sigmaLE' X (n : ℤ)]) ω ∂μ :=
            (integral_condExp (hLEΩ (n : ℤ))).symm
        _ = ∫ ω, hA'' ω * (μ[B.indicator (fun _ => (1:ℝ))|sigmaLE' X (n : ℤ)]) ω ∂μ :=
            integral_congr_ae (by filter_upwards [hpull] with ω hω using hω)
    have e2 : ∫ ω, hA'' ω * (μ[B.indicator (fun _ => (1:ℝ))|sigmaLE' X (n : ℤ)]) ω ∂μ
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


/-- **DEBT (Bradley Thms 4.1–4.2; FY §2.6.1(vi))**, scalar form: for a strictly stationary
Markov process the α-coefficient collapses to the two-marginal coefficient of `(X_0, X_n)`.
Specialisation of `alphaMixCoeff_two_marginal_of_markov` (which needs neither `ℝ` nor
stationarity); `hstat` is kept because it is part of the frozen FY statement. -/
theorem alphaCoeff_eq_two_marginal_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {κ : ProbabilityTheory.Kernel ℝ ℝ} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ) (n : ℕ) :
    alphaCoeff X μ n
      = alphaMixCoeff μ (MeasurableSpace.comap (X 0) inferInstance)
          (MeasurableSpace.comap (X n) inferInstance) :=
  alphaMixCoeff_two_marginal_of_markov hmeas hmarkov n

/-! ### The α-envelope and the process-vs-state comparison (wave 5)

Two additions the model debts of `Mixing/Relations.lean` consume, and which do **not**
depend on the open Davydov identity:

* `alphaMixCoeff_two_marginal_le_of_envelope` — the *inequality* half of (2.58) at the α
  level. Only `IsMarkovOf` at one time and a change of variables along `X_k` are used; no
  finite-partition formula, and in particular no measurable Hahn selection (the ingredient
  that keeps `betaMixCoeff_two_marginal_eq_integral_tvDist_brick` open). This is why the
  α-route to the model statements is available while the β-route is not.
* `alphaMixCoeff_le_of_measurable_state` / `alphaCoeff_le_of_state_envelope` — the
  process-vs-state comparison. If each observed `Y_s` is a measurable function of the state
  at time `s + d` (`d = 1` in the models: `Y_s` is recovered from the *next* state, which
  records the fresh innovation), then `α_Y(n) ≤ α_V(n − d)`. Composed with the anchored
  two-marginal reduction and the envelope this reads
  `α_Y(n) ≤ (∫ A dF) ρ^{n−1}` — FY §2.6.1(v)/(x)'s conclusion, over the two model-side
  inputs "the state is a Markov chain with kernel `κ`" and "`κ` has a geometric TV
  envelope". -/

/-- Two probability measures differ on a set by at most their total-variation distance. -/
private lemma abs_toReal_sub_le_tvDist {P Q : Measure E} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {W : Set E} (hW : MeasurableSet W) :
    |(P W).toReal - (Q W).toReal| ≤ (StatLean.Minimaxity.tvDist P Q).toReal := by
  have hne : StatLean.Minimaxity.tvDist P Q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (StatLean.Minimaxity.tvDist_le_one P Q)
  have hne' : StatLean.Minimaxity.tvDist Q P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (StatLean.Minimaxity.tvDist_le_one Q P)
  have key : ∀ (P' Q' : Measure E), P' W - Q' W ≤ StatLean.Minimaxity.tvDist P' Q' := by
    intro P' Q'
    exact le_iSup₂ (f := fun (s : Set E) (_ : MeasurableSet s) => P' s - Q' s) W hW
  rcases le_total (Q W) (P W) with h | h
  · have h1 : (P W).toReal - (Q W).toReal = (P W - Q W).toReal :=
      (ENNReal.toReal_sub_of_le h (measure_ne_top _ _)).symm
    have h2 : (P W - Q W).toReal ≤ (StatLean.Minimaxity.tvDist P Q).toReal :=
      ENNReal.toReal_mono hne (key P Q)
    rw [abs_of_nonneg (by rw [h1]; exact ENNReal.toReal_nonneg), h1]
    exact h2
  · have h1 : (Q W).toReal - (P W).toReal = (Q W - P W).toReal :=
      (ENNReal.toReal_sub_of_le h (measure_ne_top _ _)).symm
    have h2 : (Q W - P W).toReal ≤ (StatLean.Minimaxity.tvDist Q P).toReal :=
      ENNReal.toReal_mono hne' (key Q P)
    rw [StatLean.Minimaxity.tvDist_comm] at h2
    rw [abs_sub_comm, abs_of_nonneg (by rw [h1]; exact ENNReal.toReal_nonneg), h1]
    exact h2


private theorem markovPow {S : Type*} [MeasurableSpace S] (κ : Kernel S S)
    [IsMarkovKernel κ] : ∀ n : ℕ, IsMarkovKernel (κ ^ n)
  | 0 => by rw [pow_zero]; exact (inferInstance : IsMarkovKernel (Kernel.id : Kernel S S))
  | n + 1 => by
      haveI := isMarkovKernel_pow' κ n
      rw [pow_succ]
      exact Kernel.IsMarkovKernel.comp (κ ^ n) κ

theorem alphaMixCoeff_two_marginal_le_of_envelope [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    (hmarg : ∀ s t : ℤ, μ.map (X s) = μ.map (X t))
    {κ : Kernel E E} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ)
    {A : E → ℝ} (hA0 : ∀ x, 0 ≤ A x)
    (hAint : Integrable A (μ.map (X 0)))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (henv : ∀ (x : E) (m : ℕ),
      StatLean.Minimaxity.tvDist ((κ ^ m) x) (μ.map (X 0))
        ≤ ENNReal.ofReal (A x * ρ ^ m))
    (k : ℤ) (n : ℕ) :
    alphaMixCoeff μ (MeasurableSpace.comap (X k) inferInstance)
        (MeasurableSpace.comap (X (k + n)) inferInstance)
      ≤ (∫ x, A x ∂(μ.map (X 0))) * ρ ^ n := by
  classical
  haveI hFprob : IsProbabilityMeasure (μ.map (X 0)) :=
    Measure.isProbabilityMeasure_map (hmeas 0).aemeasurable
  haveI := isMarkovKernel_pow' κ n
  have hTot0 : (0:ℝ) ≤ (∫ x, A x ∂(μ.map (X 0))) * ρ ^ n :=
    mul_nonneg (integral_nonneg hA0) (pow_nonneg hρ0 n)
  have hAρ : Integrable (fun x => A x * ρ ^ n) (μ.map (X 0)) := hAint.mul_const _
  refine Real.sSup_le ?_ hTot0
  rintro r ⟨A0, B0, hA0m, hB0m, rfl⟩
  obtain ⟨U, hU, rfl⟩ := hA0m
  obtain ⟨W, hW, rfl⟩ := hB0m
  -- the kernel evaluation, as a bounded measurable function of the state
  have hgm : Measurable fun x : E => (((κ ^ n) x) W).toReal :=
    (((κ ^ n).measurable_coe hW)).ennreal_toReal
  have hg1 : ∀ x : E, (((κ ^ n) x) W).toReal ≤ 1 := fun x => by
    simpa using ENNReal.toReal_mono (measure_ne_top ((κ ^ n) x) Set.univ)
      (measure_mono (Set.subset_univ W))
  -- the two marginals
  have hmuA : μ (X k ⁻¹' U) = (μ.map (X 0)) U := by
    rw [← Measure.map_apply (hmeas k) hU, hmarg k 0]
  have hmuB : μ (X (k + n) ⁻¹' W) = (μ.map (X 0)) W := by
    rw [← Measure.map_apply (hmeas _) hW, hmarg (k + (n:ℤ)) 0]
  -- the joint, via the Markov property at time `k`
  have hkle : MeasurableSpace.comap (X k) inferInstance ≤ sigmaLE' X k :=
    le_iSup₂_of_le k (Set.mem_Iic.mpr le_rfl) le_rfl
  have hm : sigmaLE' X k ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup₂_le fun s _ => (hmeas s).comap_le
  have hAmk : MeasurableSet[sigmaLE' X k] (X k ⁻¹' U) := hkle _ ⟨U, hU, rfl⟩
  have hAΩ : MeasurableSet (X k ⁻¹' U) := (hmeas k) hU
  have hBΩ : MeasurableSet (X (k + n) ⁻¹' W) := (hmeas _) hW
  have hfe : (fun ω => W.indicator (fun _ => (1:ℝ)) (X (k + (n:ℤ)) ω))
      = (X (k + (n:ℤ)) ⁻¹' W).indicator (fun _ => (1:ℝ)) := by
    funext ω
    by_cases hy : X (k + (n:ℤ)) ω ∈ W <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy, Set.mem_preimage]
  have hint : Integrable (fun ω => W.indicator (fun _ => (1:ℝ)) (X (k + (n:ℤ)) ω)) μ := by
    rw [hfe]; exact (integrable_const (1:ℝ)).indicator hBΩ
  have hjoint : (μ (X k ⁻¹' U ∩ X (k + (n:ℤ)) ⁻¹' W)).toReal
      = ∫ x in U, (((κ ^ n) x) W).toReal ∂(μ.map (X 0)) := by
    have e1 : ∫ ω in X k ⁻¹' U,
        (μ[fun ω => W.indicator (fun _ => (1:ℝ)) (X (k + (n:ℤ)) ω) | sigmaLE' X k]) ω ∂μ
        = ∫ ω in X k ⁻¹' U, W.indicator (fun _ => (1:ℝ)) (X (k + (n:ℤ)) ω) ∂μ :=
      setIntegral_condExp hm hint hAmk
    have e2 : ∫ ω in X k ⁻¹' U,
        (μ[fun ω => W.indicator (fun _ => (1:ℝ)) (X (k + (n:ℤ)) ω) | sigmaLE' X k]) ω ∂μ
        = ∫ ω in X k ⁻¹' U, (((κ ^ n) (X k ω)) W).toReal ∂μ :=
      setIntegral_congr_ae hAΩ
        (by filter_upwards [hmarkov k n W hW] with ω hω using fun _ => hω)
    have e3 : ∫ ω in X k ⁻¹' U, W.indicator (fun _ => (1:ℝ)) (X (k + (n:ℤ)) ω) ∂μ
        = (μ (X k ⁻¹' U ∩ X (k + (n:ℤ)) ⁻¹' W)).toReal := by
      rw [hfe, integral_indicator_const (1:ℝ) hBΩ]
      simp [Measure.real, Measure.restrict_apply hBΩ, Set.inter_comm]
    have e4 : ∫ x in U, (((κ ^ n) x) W).toReal ∂(μ.map (X k))
        = ∫ ω in X k ⁻¹' U, (((κ ^ n) (X k ω)) W).toReal ∂μ :=
      setIntegral_map hU hgm.aestronglyMeasurable (hmeas k).aemeasurable
    rw [← e3, ← e1, e2, ← e4, hmarg k 0]
  -- the covariance as a set integral of the centred kernel evaluation
  have hcov : (μ (X k ⁻¹' U ∩ X (k + (n:ℤ)) ⁻¹' W)).toReal
        - (μ (X k ⁻¹' U)).toReal * (μ (X (k + (n:ℤ)) ⁻¹' W)).toReal
      = ∫ x in U, ((((κ ^ n) x) W).toReal - ((μ.map (X 0)) W).toReal) ∂(μ.map (X 0)) := by
    have hgint : IntegrableOn (fun x : E => (((κ ^ n) x) W).toReal) U (μ.map (X 0)) := by
      refine Integrable.mono (integrable_const (1:ℝ)) hgm.aestronglyMeasurable.restrict
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg zero_le_one,
        abs_of_nonneg ENNReal.toReal_nonneg]
      exact hg1 x
    rw [integral_sub hgint (integrable_const ((μ.map (X 0)) W).toReal).integrableOn,
      hjoint, hmuA, hmuB, setIntegral_const]
    simp [Measure.real]
  rw [hcov]
  -- and the envelope
  have hpt : ∀ x ∈ U, |(((κ ^ n) x) W).toReal - ((μ.map (X 0)) W).toReal| ≤ A x * ρ ^ n := by
    intro x _
    refine (abs_toReal_sub_le_tvDist (P := (κ ^ n) x) (Q := μ.map (X 0)) hW).trans ?_
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (henv x n)
    rwa [ENNReal.toReal_ofReal (mul_nonneg (hA0 x) (pow_nonneg hρ0 n))] at h2
  have habsm : Measurable fun x : E =>
      |(((κ ^ n) x) W).toReal - ((μ.map (X 0)) W).toReal| := by
    have h := hgm.sub (measurable_const (a := ((μ.map (X 0)) W).toReal))
    exact continuous_abs.measurable.comp h
  have habsi : IntegrableOn
      (fun x : E => |(((κ ^ n) x) W).toReal - ((μ.map (X 0)) W).toReal|) U (μ.map (X 0)) := by
    refine Integrable.mono (integrable_const (2:ℝ)) habsm.aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h1 := hg1 x
    have h2 : ((μ.map (X 0)) W).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top (μ.map (X 0)) Set.univ)
        (measure_mono (Set.subset_univ W))
    have h3 : (0:ℝ) ≤ (((κ ^ n) x) W).toReal := ENNReal.toReal_nonneg
    have h4 : (0:ℝ) ≤ ((μ.map (X 0)) W).toReal := ENNReal.toReal_nonneg
    rw [abs_le]; constructor <;> linarith
  calc |∫ x in U, ((((κ ^ n) x) W).toReal - ((μ.map (X 0)) W).toReal) ∂(μ.map (X 0))|
      ≤ ∫ x in U, |(((κ ^ n) x) W).toReal - ((μ.map (X 0)) W).toReal| ∂(μ.map (X 0)) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in U, A x * ρ ^ n ∂(μ.map (X 0)) :=
        setIntegral_mono_on habsi hAρ.integrableOn hU hpt
    _ ≤ ∫ x, A x * ρ ^ n ∂(μ.map (X 0)) :=
        setIntegral_le_integral hAρ
          (Filter.Eventually.of_forall fun x => mul_nonneg (hA0 x) (pow_nonneg hρ0 n))
    _ = (∫ x, A x ∂(μ.map (X 0))) * ρ ^ n := integral_mul_const _ _



lemma IsMarkovOf.shiftBy {X : ℤ → Ω → E} {κ : Kernel E E} (h : IsMarkovOf X κ μ) (k : ℤ) :
    IsMarkovOf (fun s => X (s + k)) κ μ := by
  intro t n B hB
  have h1 := h (t + k) n B hB
  have e : t + k + (n : ℤ) = t + (n : ℤ) + k := by ring
  rw [e] at h1
  rw [sigmaLE'_shift]
  exact h1

theorem alphaMixCoeff_two_marginal_of_markov_anchor [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    {κ : Kernel E E} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ) (k : ℤ) (n : ℕ) :
    alphaMixCoeff μ (sigmaLE' X k) (sigmaGE' X (k + n))
      = alphaMixCoeff μ (MeasurableSpace.comap (X k) inferInstance)
          (MeasurableSpace.comap (X (k + n)) inferInstance) := by
  have h := alphaMixCoeff_two_marginal_of_markov (X := fun s => X (s + k))
    (fun t => hmeas _) (hmarkov.shiftBy k) n
  rw [sigmaLE'_shift, sigmaGE'_shift] at h
  simp only [zero_add] at h
  rw [show k + (n : ℤ) = (n : ℤ) + k from add_comm _ _]
  exact h

theorem alphaMixCoeff_le_of_measurable_state [IsProbabilityMeasure μ]
    {Y : ℤ → Ω → ℝ} {V : ℤ → Ω → E} {d : ℤ}
    (hYV : ∀ s : ℤ, Measurable[MeasurableSpace.comap (V (s + d)) inferInstance] (Y s))
    {n m : ℤ} (hnm : m ≤ n + d) :
    alphaMixCoeff μ (sigmaLE Y 0) (sigmaGE Y n)
      ≤ alphaMixCoeff μ (sigmaLE' V d) (sigmaGE' V m) := by
  refine alphaMixCoeff_mono' (mΩ := (inferInstance : MeasurableSpace Ω)) ?_ ?_
  · exact iSup₂_le fun s hs => (hYV s).comap_le.trans
      (le_iSup₂_of_le (s + d) (Set.mem_Iic.mpr (by have := Set.mem_Iic.mp hs; omega)) le_rfl)
  · exact iSup₂_le fun s hs => (hYV s).comap_le.trans
      (le_iSup₂_of_le (s + d) (Set.mem_Ici.mpr (by have := Set.mem_Ici.mp hs; omega)) le_rfl)

/-- **Process-vs-state comparison, β version.** Same statement as
`alphaMixCoeff_le_of_measurable_state` for the β-coefficient; the proof is again pure
monotonicity in the two σ-algebra arguments. -/
theorem betaMixCoeff_le_of_measurable_state [IsProbabilityMeasure μ]
    {Y : ℤ → Ω → ℝ} {V : ℤ → Ω → E} (hV : ∀ t, Measurable (V t)) {d : ℤ}
    (hYV : ∀ s : ℤ, Measurable[MeasurableSpace.comap (V (s + d)) inferInstance] (Y s))
    {n m : ℤ} (hnm : m ≤ n + d) :
    betaMixCoeff μ (sigmaLE Y 0) (sigmaGE Y n)
      ≤ betaMixCoeff μ (sigmaLE' V d) (sigmaGE' V m) := by
  refine betaMixCoeff_mono' (mΩ := (inferInstance : MeasurableSpace Ω))
    (iSup₂_le fun s _ => (hV s).comap_le) (iSup₂_le fun s _ => (hV s).comap_le) ?_ ?_
  · exact iSup₂_le fun s hs => (hYV s).comap_le.trans
      (le_iSup₂_of_le (s + d) (Set.mem_Iic.mpr (by have := Set.mem_Iic.mp hs; omega)) le_rfl)
  · exact iSup₂_le fun s hs => (hYV s).comap_le.trans
      (le_iSup₂_of_le (s + d) (Set.mem_Ici.mpr (by have := Set.mem_Ici.mp hs; omega)) le_rfl)

theorem alphaCoeff_le_of_state_envelope [IsProbabilityMeasure μ]
    {Y : ℤ → Ω → ℝ} {V : ℤ → Ω → E} (hV : ∀ t, Measurable (V t))
    (hYV : ∀ s : ℤ, Measurable[MeasurableSpace.comap (V (s + 1)) inferInstance] (Y s))
    (hmarg : ∀ s t : ℤ, μ.map (V s) = μ.map (V t))
    {κ : Kernel E E} [IsMarkovKernel κ] (hmarkov : IsMarkovOf V κ μ)
    {A : E → ℝ} (hA0 : ∀ x, 0 ≤ A x) (hAint : Integrable A (μ.map (V 0)))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (henv : ∀ (x : E) (m : ℕ),
      StatLean.Minimaxity.tvDist ((κ ^ m) x) (μ.map (V 0)) ≤ ENNReal.ofReal (A x * ρ ^ m))
    {n : ℕ} (hn : 1 ≤ n) :
    alphaCoeff Y μ n ≤ (∫ x, A x ∂(μ.map (V 0))) * ρ ^ (n - 1) := by
  have hcast : (1 : ℤ) + ((n - 1 : ℕ) : ℤ) = (n : ℤ) := by omega
  have hstep1 : alphaCoeff Y μ n
      ≤ alphaMixCoeff μ (sigmaLE' V 1) (sigmaGE' V (n : ℤ)) :=
    alphaMixCoeff_le_of_measurable_state hYV (by omega)
  have hstep2 := alphaMixCoeff_two_marginal_of_markov_anchor hV hmarkov 1 (n - 1)
  rw [hcast] at hstep2
  have hstep3 :=
    alphaMixCoeff_two_marginal_le_of_envelope hV hmarg hmarkov hA0 hAint hρ0 henv 1 (n - 1)
  rw [hcast] at hstep3
  exact hstep1.trans (hstep2.le.trans hstep3)




/-! ### The β-envelope: the `≤` half of Davydov's identity

`betaMixCoeff_two_marginal_eq_integral_tvDist_brick` (the *equality*) is still open, because
its `≥` half needs a jointly measurable Hahn selection. The `≤` half needs none of that,
and it is what the model statements consume. Two points of the wave-4 proof sketch are
**simplified** here:

* the past-side sets need **no disjointification**: `sum_abs_setIntegral_le` is applied to
  the given `Ω`-partition `{A_i}` and the `σ(X_k)`-measurable integrand
  `h_j(ω) = κⁿ(X_k ω)(W_j) − F(W_j)` directly, so no `U_i`-level bookkeeping occurs;
* the future-side sets *are* disjointified, but only in the state space, and the sole fact
  used is `X_{k+n}⁻¹(W_j \ ⋃_{j' < j} W_{j'}) = B_j`, which holds because the `B_j` are
  disjoint.

The normalization comes out as promised in the module docstring: `Σ_j |P W_j − Q W_j| ≤ 2
tvDist P Q` for a disjoint family, and `betaMixCoeff` is the *half*-sum, so the final bound
carries **no factor 2**. -/

/-- For a pairwise disjoint finite family, the total discrepancy of two probability
measures is at most twice their total-variation distance. -/
private lemma sum_abs_toReal_sub_le_two_tvDist {P Q : Measure E} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {J : ℕ} {V : Fin J → Set E} (hVm : ∀ j, MeasurableSet (V j))
    (hVd : Pairwise fun j j' => Disjoint (V j) (V j')) :
    ∑ j, |(P (V j)).toReal - (Q (V j)).toReal|
      ≤ 2 * (StatLean.Minimaxity.tvDist P Q).toReal := by
  classical
  have key : ∀ (T : Finset (Fin J)) (P' Q' : Measure E), IsProbabilityMeasure P' →
      IsProbabilityMeasure Q' →
      ∑ j ∈ T, ((P' (V j)).toReal - (Q' (V j)).toReal)
        ≤ (StatLean.Minimaxity.tvDist P' Q').toReal := by
    intro T P' Q' hP' hQ'
    have hUm : MeasurableSet (⋃ j ∈ T, V j) := Finset.measurableSet_biUnion T fun j _ => hVm j
    have hsum : ∀ (R : Measure E) [IsProbabilityMeasure R],
        (R (⋃ j ∈ T, V j)).toReal = ∑ j ∈ T, (R (V j)).toReal := by
      intro R _
      rw [measure_biUnion_finset (fun i _ j _ hij => hVd hij) (fun j _ => hVm j)]
      exact ENNReal.toReal_sum fun j _ => measure_ne_top _ _
    have hd : ∑ j ∈ T, ((P' (V j)).toReal - (Q' (V j)).toReal)
        = (∑ j ∈ T, (P' (V j)).toReal) - ∑ j ∈ T, (Q' (V j)).toReal :=
      Finset.sum_sub_distrib _ _
    rw [hd, ← hsum P', ← hsum Q']
    exact le_trans (le_abs_self _) (abs_toReal_sub_le_tvDist hUm)
  have hsplit : ∑ j, |(P (V j)).toReal - (Q (V j)).toReal|
      = (∑ j ∈ Finset.univ.filter (fun j => (Q (V j)).toReal ≤ (P (V j)).toReal),
          ((P (V j)).toReal - (Q (V j)).toReal))
        + (∑ j ∈ Finset.univ.filter (fun j => ¬ (Q (V j)).toReal ≤ (P (V j)).toReal),
          ((Q (V j)).toReal - (P (V j)).toReal)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => (Q (V j)).toReal ≤ (P (V j)).toReal)
      (fun j => |(P (V j)).toReal - (Q (V j)).toReal|)]
    congr 1
    · exact Finset.sum_congr rfl fun j hj =>
        abs_of_nonneg (by have := (Finset.mem_filter.mp hj).2; linarith)
    · exact Finset.sum_congr rfl fun j hj => by
        have := (Finset.mem_filter.mp hj).2
        rw [abs_of_nonpos (by rw [not_le] at this; linarith)]; ring
  rw [hsplit]
  have h1 := key (Finset.univ.filter (fun j => (Q (V j)).toReal ≤ (P (V j)).toReal)) P Q
    inferInstance inferInstance
  have h2 := key (Finset.univ.filter (fun j => ¬ (Q (V j)).toReal ≤ (P (V j)).toReal)) Q P
    inferInstance inferInstance
  rw [StatLean.Minimaxity.tvDist_comm Q P] at h2
  linarith

/-- **The β-envelope** (the `≤` half of Davydov's identity, FY (2.58)–(2.59)): a geometric
total-variation envelope for the kernel bounds the two-marginal β-coefficient by
`(∫ A dF) ρⁿ` — with no factor 2, see the module docstring's calibration warning. -/
theorem betaMixCoeff_two_marginal_le_of_envelope [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    (hmarg : ∀ s t : ℤ, μ.map (X s) = μ.map (X t))
    {κ : Kernel E E} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ)
    {A : E → ℝ} (hA0 : ∀ x, 0 ≤ A x) (hAint : Integrable A (μ.map (X 0)))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (henv : ∀ (x : E) (m : ℕ),
      StatLean.Minimaxity.tvDist ((κ ^ m) x) (μ.map (X 0))
        ≤ ENNReal.ofReal (A x * ρ ^ m))
    (k : ℤ) (n : ℕ) :
    betaMixCoeff μ (MeasurableSpace.comap (X k) inferInstance)
        (MeasurableSpace.comap (X (k + n)) inferInstance)
      ≤ (∫ x, A x ∂(μ.map (X 0))) * ρ ^ n := by
  classical
  haveI hFprob : IsProbabilityMeasure (μ.map (X 0)) :=
    Measure.isProbabilityMeasure_map (hmeas 0).aemeasurable
  haveI := isMarkovKernel_pow' κ n
  have hkΩ : MeasurableSpace.comap (X k) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    (hmeas k).comap_le
  have hknΩ : MeasurableSpace.comap (X (k + n)) inferInstance
      ≤ (inferInstance : MeasurableSpace Ω) := (hmeas _).comap_le
  have hkle : MeasurableSpace.comap (X k) inferInstance ≤ sigmaLE' X k :=
    le_iSup₂_of_le k (Set.mem_Iic.mpr le_rfl) le_rfl
  have hm : sigmaLE' X k ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup₂_le fun s _ => (hmeas s).comap_le
  -- the integrable envelope, pulled back to `Ω`
  have hmapk : μ.map (X k) = μ.map (X 0) := hmarg k 0
  have hAsm : AEStronglyMeasurable A (μ.map (X k)) := by rw [hmapk]; exact hAint.1
  have hAintk : Integrable A (μ.map (X k)) := by rw [hmapk]; exact hAint
  have hAc : Integrable (fun ω => A (X k ω)) μ :=
    (integrable_map_measure hAsm (hmeas k).aemeasurable).mp hAintk
  have hAint_eq : ∫ ω, A (X k ω) ∂μ = ∫ x, A x ∂(μ.map (X 0)) := by
    rw [← hmapk]
    exact (integral_map (hmeas k).aemeasurable hAsm).symm
  have hTot0 : (0 : ℝ) ≤ (∫ x, A x ∂(μ.map (X 0))) * ρ ^ n :=
    mul_nonneg (integral_nonneg hA0) (pow_nonneg hρ0 n)
  refine Real.sSup_le ?_ hTot0
  rintro r ⟨I, J, Aset, Bset, hAm, hBm, hAd, hBd, hAc', hBc, rfl⟩
  -- the future-side sets, disjointified in the state space
  choose W hWm hWpre using hBm
  obtain ⟨W', hW'def⟩ : ∃ V : Fin J → Set E,
      V = fun j => W j \ ⋃ j' ∈ Finset.univ.filter (fun j' => j' < j), W j' := ⟨_, rfl⟩
  have hW'm : ∀ j, MeasurableSet (W' j) := fun j => by
    rw [hW'def]
    exact (hWm j).diff (Finset.measurableSet_biUnion _ fun j' _ => hWm j')
  have hW'sub : ∀ j, W' j ⊆ W j := fun j => by rw [hW'def]; exact Set.diff_subset
  have hW'd : Pairwise fun j j' => Disjoint (W' j) (W' j') := by
    intro j j' hjj
    rcases lt_or_gt_of_ne hjj with hlt | hlt
    · refine Set.disjoint_left.mpr fun x hx hx' => ?_
      rw [hW'def] at hx'
      exact hx'.2 (Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
        (hW'sub j hx))
    · refine Set.disjoint_left.mpr fun x hx hx' => ?_
      rw [hW'def] at hx
      exact hx.2 (Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
        (hW'sub j' hx'))
  have hW'pre : ∀ j, X (k + n) ⁻¹' (W' j) = Bset j := by
    intro j
    rw [hW'def]
    simp only [Set.preimage_diff, Set.preimage_iUnion, hWpre]
    refine Set.eq_of_subset_of_subset Set.diff_subset fun ω hω => ⟨hω, ?_⟩
    simp only [Set.mem_iUnion, not_exists]
    intro j' hj'
    have hne : j ≠ j' := fun hc => absurd (Finset.mem_filter.mp hj').2 (by rw [hc]; simp)
    exact Set.disjoint_left.mp (hBd hne) hω
  -- the covariance, as a set integral of a `σ(X_k)`-measurable function
  obtain ⟨hh, hhdef⟩ : ∃ H : Fin J → Ω → ℝ, H = fun j ω =>
      (((κ ^ n) (X k ω)) (W' j)).toReal - ((μ.map (X 0)) (W' j)).toReal := ⟨_, rfl⟩
  have hhm : ∀ j, Measurable[MeasurableSpace.comap (X k) inferInstance] (hh j) := by
    intro j
    rw [hhdef]
    refine Measurable.sub ?_ measurable_const
    exact ((((κ ^ n).measurable_coe (hW'm j)).ennreal_toReal).comp
      (Measurable.of_comap_le le_rfl))
  have hhi : ∀ j, Integrable (hh j) μ := by
    intro j
    refine Integrable.mono (integrable_const (2 : ℝ))
      ((hhm j).mono hkΩ le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hhdef]
    have h1 : (((κ ^ n) (X k ω)) (W' j)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top ((κ ^ n) (X k ω)) Set.univ)
        (measure_mono (Set.subset_univ (W' j)))
    have h2 : ((μ.map (X 0)) (W' j)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top (μ.map (X 0)) Set.univ)
        (measure_mono (Set.subset_univ (W' j)))
    have h3 : (0:ℝ) ≤ (((κ ^ n) (X k ω)) (W' j)).toReal := ENNReal.toReal_nonneg
    have h4 : (0:ℝ) ≤ ((μ.map (X 0)) (W' j)).toReal := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_le]
    constructor <;> linarith
  have hmuB : ∀ j, (μ (Bset j)).toReal = ((μ.map (X 0)) (W' j)).toReal := by
    intro j
    rw [← hW'pre j, ← Measure.map_apply (hmeas _) (hW'm j), hmarg (k + (n : ℤ)) 0]
  have hcov : ∀ (S : Set Ω), MeasurableSet[sigmaLE' X k] S → ∀ j,
      (μ (S ∩ Bset j)).toReal - (μ S).toReal * (μ (Bset j)).toReal
        = ∫ ω in S, hh j ω ∂μ := by
    intro S hS j
    have hSΩ : MeasurableSet S := hm _ hS
    have hBΩ : MeasurableSet (Bset j) := by rw [← hW'pre j]; exact (hmeas _) (hW'm j)
    have hfe : (fun ω => (W' j).indicator (fun _ => (1:ℝ)) (X (k + (n:ℤ)) ω))
        = (Bset j).indicator (fun _ => (1:ℝ)) := by
      funext ω
      by_cases hy : X (k + (n:ℤ)) ω ∈ W' j
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (by rw [← hW'pre j]; exact hy)]
      · rw [Set.indicator_of_notMem hy,
          Set.indicator_of_notMem (by rw [← hW'pre j]; exact hy)]
    have hint : Integrable (fun ω => (W' j).indicator (fun _ => (1:ℝ))
        (X (k + (n:ℤ)) ω)) μ := by
      rw [hfe]; exact (integrable_const (1:ℝ)).indicator hBΩ
    have e1 : ∫ ω in S, (μ[fun ω => (W' j).indicator (fun _ => (1:ℝ))
          (X (k + (n:ℤ)) ω) | sigmaLE' X k]) ω ∂μ
        = ∫ ω in S, (W' j).indicator (fun _ => (1:ℝ)) (X (k + (n:ℤ)) ω) ∂μ :=
      setIntegral_condExp hm hint hS
    have e2 : ∫ ω in S, (μ[fun ω => (W' j).indicator (fun _ => (1:ℝ))
          (X (k + (n:ℤ)) ω) | sigmaLE' X k]) ω ∂μ
        = ∫ ω in S, (((κ ^ n) (X k ω)) (W' j)).toReal ∂μ :=
      setIntegral_congr_ae hSΩ
        (by filter_upwards [hmarkov k n (W' j) (hW'm j)] with ω hω using fun _ => hω)
    have e3 : ∫ ω in S, (W' j).indicator (fun _ => (1:ℝ)) (X (k + (n:ℤ)) ω) ∂μ
        = (μ (S ∩ Bset j)).toReal := by
      rw [hfe, integral_indicator_const (1:ℝ) hBΩ]
      simp [Measure.real, Measure.restrict_apply hBΩ, Set.inter_comm]
    have hgint : IntegrableOn (fun ω => (((κ ^ n) (X k ω)) (W' j)).toReal) S μ := by
      have hgm : Measurable fun ω => (((κ ^ n) (X k ω)) (W' j)).toReal :=
        (((κ ^ n).measurable_coe (hW'm j)).ennreal_toReal).comp (hmeas k)
      refine Integrable.mono (integrable_const (1:ℝ)) hgm.aestronglyMeasurable.restrict
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg zero_le_one,
        abs_of_nonneg ENNReal.toReal_nonneg]
      simpa using ENNReal.toReal_mono (measure_ne_top ((κ ^ n) (X k ω)) Set.univ)
        (measure_mono (Set.subset_univ (W' j)))
    simp only [hhdef]
    rw [integral_sub hgint (integrable_const _).integrableOn, setIntegral_const,
      ← e2, e1, e3, hmuB j]
    simp [Measure.real]
  -- assemble
  have hrow : ∀ j, ∑ i, |(μ (Aset i ∩ Bset j)).toReal
      - (μ (Aset i)).toReal * (μ (Bset j)).toReal| ≤ ∫ ω, |hh j ω| ∂μ := by
    intro j
    have hL : ∑ i, |(μ (Aset i ∩ Bset j)).toReal
        - (μ (Aset i)).toReal * (μ (Bset j)).toReal| = ∑ i, |∫ ω in Aset i, hh j ω ∂μ| :=
      Finset.sum_congr rfl fun i _ => by rw [hcov (Aset i) (hkle _ (hAm i)) j]
    rw [hL]
    exact sum_abs_setIntegral_le hkΩ hAm hAd hAc' (hhi j)
  have hptw : ∀ ω, ∑ j, |hh j ω| ≤ 2 * (A (X k ω) * ρ ^ n) := by
    intro ω
    have h1 : ∑ j, |hh j ω|
        ≤ 2 * (StatLean.Minimaxity.tvDist ((κ ^ n) (X k ω)) (μ.map (X 0))).toReal := by
      rw [hhdef]
      exact sum_abs_toReal_sub_le_two_tvDist hW'm hW'd
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (henv (X k ω) n)
    rw [ENNReal.toReal_ofReal (mul_nonneg (hA0 _) (pow_nonneg hρ0 n))] at h2
    linarith
  have hcol : ∑ j, ∫ ω, |hh j ω| ∂μ ≤ 2 * ((∫ x, A x ∂(μ.map (X 0))) * ρ ^ n) := by
    have hsum : ∑ j, ∫ ω, |hh j ω| ∂μ = ∫ ω, ∑ j, |hh j ω| ∂μ :=
      (integral_finset_sum _ fun j _ => (hhi j).abs).symm
    rw [hsum]
    have hbdd : Integrable (fun ω => 2 * (A (X k ω) * ρ ^ n)) μ := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using (hAc.const_mul (2 * ρ ^ n))
    have := integral_mono (integrable_finset_sum _ fun j _ => (hhi j).abs) hbdd hptw
    refine this.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_mul_const, hAint_eq]
  have hchain : ∑ i, ∑ j, |(μ (Aset i ∩ Bset j)).toReal
      - (μ (Aset i)).toReal * (μ (Bset j)).toReal|
      ≤ 2 * ((∫ x, A x ∂(μ.map (X 0))) * ρ ^ n) := by
    calc ∑ i, ∑ j, |(μ (Aset i ∩ Bset j)).toReal
          - (μ (Aset i)).toReal * (μ (Bset j)).toReal|
        = ∑ j, ∑ i, |(μ (Aset i ∩ Bset j)).toReal
            - (μ (Aset i)).toReal * (μ (Bset j)).toReal| := Finset.sum_comm
      _ ≤ ∑ j, ∫ ω, |hh j ω| ∂μ := Finset.sum_le_sum fun j _ => hrow j
      _ ≤ 2 * ((∫ x, A x ∂(μ.map (X 0))) * ρ ^ n) := hcol
  linarith



/-- The two-marginal reduction for β at an arbitrary anchor (the β-analogue of
`alphaMixCoeff_two_marginal_of_markov_anchor`). -/
theorem betaMixCoeff_two_marginal_of_markov_anchor [IsProbabilityMeasure μ]
    {X : ℤ → Ω → E} (hmeas : ∀ t, Measurable (X t))
    {κ : Kernel E E} [IsMarkovKernel κ] (hmarkov : IsMarkovOf X κ μ) (k : ℤ) (n : ℕ) :
    betaMixCoeff μ (sigmaLE' X k) (sigmaGE' X (k + n))
      = betaMixCoeff μ (MeasurableSpace.comap (X k) inferInstance)
          (MeasurableSpace.comap (X (k + n)) inferInstance) := by
  have h := betaMixCoeff_two_marginal_of_markov (X := fun s => X (s + k))
    (fun t => hmeas _) (hmarkov.shiftBy k) n
  rw [sigmaLE'_shift, sigmaGE'_shift] at h
  simp only [zero_add] at h
  rw [show k + (n : ℤ) = (n : ℤ) + k from add_comm _ _]
  exact h

/-- **`β_Y(n) ≤ (∫ A dF) ρ^{n−1}`** — the β-analogue of `alphaCoeff_le_of_state_envelope`,
now available because the `≤` half of Davydov's identity is proved
(`betaMixCoeff_two_marginal_le_of_envelope`). -/
theorem betaCoeff_le_of_state_envelope [IsProbabilityMeasure μ]
    {Y : ℤ → Ω → ℝ} {V : ℤ → Ω → E} (hV : ∀ t, Measurable (V t))
    (hYV : ∀ s : ℤ, Measurable[MeasurableSpace.comap (V (s + 1)) inferInstance] (Y s))
    (hmarg : ∀ s t : ℤ, μ.map (V s) = μ.map (V t))
    {κ : Kernel E E} [IsMarkovKernel κ] (hmarkov : IsMarkovOf V κ μ)
    {A : E → ℝ} (hA0 : ∀ x, 0 ≤ A x) (hAint : Integrable A (μ.map (V 0)))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (henv : ∀ (x : E) (m : ℕ),
      StatLean.Minimaxity.tvDist ((κ ^ m) x) (μ.map (V 0)) ≤ ENNReal.ofReal (A x * ρ ^ m))
    {n : ℕ} (hn : 1 ≤ n) :
    betaCoeff Y μ n ≤ (∫ x, A x ∂(μ.map (V 0))) * ρ ^ (n - 1) := by
  have hcast : (1 : ℤ) + ((n - 1 : ℕ) : ℤ) = (n : ℤ) := by omega
  have hstep1 : betaCoeff Y μ n
      ≤ betaMixCoeff μ (sigmaLE' V 1) (sigmaGE' V (n : ℤ)) :=
    betaMixCoeff_le_of_measurable_state hV hYV (by omega)
  have hstep2 := betaMixCoeff_two_marginal_of_markov_anchor hV hmarkov 1 (n - 1)
  rw [hcast] at hstep2
  have hstep3 :=
    betaMixCoeff_two_marginal_le_of_envelope hV hmarg hmarkov hA0 hAint hρ0 henv 1 (n - 1)
  rw [hcast] at hstep3
  exact hstep1.trans (hstep2.le.trans hstep3)


end StatLean.TimeSeries
