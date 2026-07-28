import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Riemann–Lebesgue, uniformly over a family

The Riemann–Lebesgue lemma says that the oscillatory integral `∫ f(x) e^{isx} dx` of a fixed
`L¹` function tends to `0` as `|s| → ∞`. Several applications need the convergence to be
**uniform over a family of `L¹` functions** — most notably the multivariate Cramér condition
for a law carried by a curve, where the family is the set of projections of the law onto the
directions of a compact sphere.

Uniformity is false for an arbitrary family (translates `f(· − a)`, `a ∈ ℝ`, all have the same
modulus of transform, and the transform of a *single* function does not decay uniformly along
any family that is not relatively compact). It is true, and easy, on a **totally bounded**
subset of `L¹`: approximate every member of the family to within `ε/2` by one of finitely many
functions, apply Riemann–Lebesgue to each of those, and use that the transform is a contraction
from `L¹` to `L^∞`.

## Contents

* `fourierOsc` — the oscillatory integral `∫ e^{i x s} f(x) dx`, normalised exactly as `charFun`
  is, so that `charFun (volume.withDensity p) = fourierOsc p`;
* `tendsto_fourierOsc_cocompact` — the Riemann–Lebesgue lemma in this normalisation, obtained
  from Mathlib's `Real.tendsto_integral_exp_smul_cocompact` by the reparametrisation
  `s = −2πw`;
* `norm_fourierOsc_sub_le` — the contraction property `‖ℱf(s) − ℱg(s)‖ ≤ ‖f − g‖_{L¹}`,
  valid for every `s`;
* `eventually_norm_fourierOsc_le_of_totallyBounded` — **the headline**: Riemann–Lebesgue holds
  uniformly over any family admitting finite `ε`-nets in `L¹`;
* `exists_finset_l1Net_of_isCompact` — a family parametrised continuously (in `L¹`) by a
  compact set admits finite `ε`-nets;
* `eventually_norm_fourierOsc_le_of_isCompact` — the two combined, in the form applications
  consume;
* `quadPhaseInt`, `eventually_norm_quadPhaseInt_le` — the application to a **quadratic phase**:
  for a fixed `L¹` density `f`, `∫ f(y) e^{i(t₀y + t₁y²)} dy → 0` as `|t₀| → ∞`, uniformly over
  `|t₁| ≤ M`. This is the "linear regime" of the two-regime decomposition of the multivariate
  Cramér condition for a parabola-carried law; the complementary regime `|t₁| → ∞` is a
  genuinely different (van der Corput / autocorrelation) estimate and is not proved here.

## Proof formalization notes

* The `L¹`-continuity hypothesis of `exists_finset_l1Net_of_isCompact` is phrased elementarily,
  as `∀ δ > 0, ∃ U ∈ 𝓝[K] a, ∀ b ∈ U, ∫ ‖f b − f a‖ ≤ δ`, rather than through `MeasureTheory.Lp`
  and its quotient by a.e. equality. Nothing is lost — the applications produce exactly this
  statement, from dominated convergence — and it avoids having to lift a family of honest
  functions into the `Lp` quotient and back.
* The `ε`-net hypothesis is likewise stated as a `Finset` of *indices* rather than of `L¹`
  elements, which is what a finite subcover of a compact parameter set produces.
-/

open Filter MeasureTheory
open scoped Topology

namespace StatLean.HypothesisTesting

/-! ## The oscillatory integral and the Riemann–Lebesgue lemma -/

section FourierOsc

/-- The oscillatory integral `∫ e^{i x s} f(x) dx`, normalised exactly as `charFun` is: for a
density `p`, `charFun (volume.withDensity p) s = fourierOsc p s`. -/
noncomputable def fourierOsc (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp ((x * s : ℝ) * Complex.I) * f x

/-- `fourierOsc` is Mathlib's Fourier integral at the rescaled argument `w = −s/(2π)`. -/
lemma fourierOsc_eq_fourierIntegral (f : ℝ → ℂ) (s : ℝ) :
    fourierOsc f s = ∫ x : ℝ, Real.fourierChar (-(x * (-(2 * Real.pi)⁻¹ * s))) • f x := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hex : (2 * Real.pi * -(x * (-(2 * Real.pi)⁻¹ * s)) : ℝ) = x * s := by
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp
  change Complex.exp ((x * s : ℝ) * Complex.I) * f x
    = Real.fourierChar (-(x * (-(2 * Real.pi)⁻¹ * s))) • f x
  rw [Circle.smul_def, Real.fourierChar_apply, hex, smul_eq_mul]

/-- **The Riemann–Lebesgue lemma**, in the `charFun` normalisation: for any `f`, the
oscillatory integral `∫ e^{ixs} f(x) dx` tends to `0` as `s` leaves every compact set. -/
theorem tendsto_fourierOsc_cocompact (f : ℝ → ℂ) :
    Tendsto (fourierOsc f) (Filter.cocompact ℝ) (𝓝 0) := by
  have hRL : Tendsto (fun w : ℝ => ∫ x : ℝ, Real.fourierChar (-(x * w)) • f x)
      (Filter.cocompact ℝ) (𝓝 0) := Real.tendsto_integral_exp_smul_cocompact f
  have hc : (-(2 * Real.pi)⁻¹ : ℝ) ≠ 0 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    simp [hpi]
  have hmap : Tendsto (fun s : ℝ => -(2 * Real.pi)⁻¹ * s)
      (Filter.cocompact ℝ) (Filter.cocompact ℝ) :=
    le_of_eq (Homeomorph.mulLeft₀ (-(2 * Real.pi)⁻¹ : ℝ) hc).map_cocompact
  exact (hRL.comp hmap).congr fun s => (fourierOsc_eq_fourierIntegral f s).symm

/-- **The oscillatory integral is a contraction from `L¹` to `L^∞`**, uniformly in the
frequency: `‖ℱf(s) − ℱg(s)‖ ≤ ∫ ‖f − g‖` for every `s`. This is the only estimate the
uniformity argument uses, and it is what makes an `L¹` `ε`-net enough. -/
theorem norm_fourierOsc_sub_le {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (s : ℝ) :
    ‖fourierOsc f s - fourierOsc g s‖ ≤ ∫ x : ℝ, ‖f x - g x‖ := by
  have hnorm : ∀ (x : ℝ) (z : ℂ),
      ‖Complex.exp ((x * s : ℝ) * Complex.I) * z‖ = ‖z‖ := by
    intro x z
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hmul : ∀ h : ℝ → ℂ, Integrable h →
      Integrable fun x : ℝ => Complex.exp ((x * s : ℝ) * Complex.I) * h x := by
    intro h hh
    refine Integrable.mono' hh.norm ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_exp.comp
        (by fun_prop)).aestronglyMeasurable.mul hh.aestronglyMeasurable
    · exact le_of_eq (hnorm x (h x))
  rw [fourierOsc, fourierOsc, ← integral_sub (hmul f hf) (hmul g hg)]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change ‖Complex.exp ((x * s : ℝ) * Complex.I) * f x
    - Complex.exp ((x * s : ℝ) * Complex.I) * g x‖ = ‖f x - g x‖
  rw [← mul_sub, hnorm]

end FourierOsc

/-! ## Uniformity over a totally bounded family

The whole content of this section is the two-line estimate

`‖ℱf_i(s)‖ ≤ ‖ℱf_j(s)‖ + ‖f_i − f_j‖_{L¹}`,

with `j` ranging over a **finite** `ε`-net: the first term is eventually small by
Riemann–Lebesgue applied to each of the finitely many net elements, and the second is small by
the choice of the net. Total boundedness is exactly the hypothesis that makes the first
"eventually" uniform, since a finite intersection of eventualities is an eventuality. -/

section Uniform

variable {ι : Type*}

/-- **Riemann–Lebesgue holds uniformly over a totally bounded family of `L¹` functions.**

`S` is a set of indices, `f i` the corresponding functions, and the hypothesis `hnet` is total
boundedness of `{f i : i ∈ S}` in `L¹`, phrased as the existence of finite `δ`-nets *indexed by
`S`* — which is the form a finite subcover of a compact parameter set produces. -/
theorem eventually_norm_fourierOsc_le_of_totallyBounded (f : ι → ℝ → ℂ) (S : Set ι)
    (hf : ∀ i ∈ S, Integrable (f i))
    (hnet : ∀ δ : ℝ, 0 < δ → ∃ J : Finset ι, ↑J ⊆ S ∧
      ∀ i ∈ S, ∃ j ∈ J, (∫ x : ℝ, ‖f i x - f j x‖) ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in Filter.cocompact ℝ, ∀ i ∈ S, ‖fourierOsc (f i) s‖ ≤ ε := by
  obtain ⟨J, hJS, hJ⟩ := hnet (ε / 2) (by linarith)
  have hJev : ∀ j ∈ J, ∀ᶠ s in Filter.cocompact ℝ, ‖fourierOsc (f j) s‖ ≤ ε / 2 := by
    intro j _
    filter_upwards [NormedAddGroup.tendsto_nhds_zero.1
      (tendsto_fourierOsc_cocompact (f j)) (ε / 2) (by linarith)] with s hs
    exact hs.le
  filter_upwards [Filter.eventually_all_finset J |>.2 hJev] with s hs i hi
  obtain ⟨j, hjJ, hij⟩ := hJ i hi
  have hjS : j ∈ S := hJS (Finset.mem_coe.2 hjJ)
  have hsub := norm_fourierOsc_sub_le (hf i hi) (hf j hjS) s
  have htri : ‖fourierOsc (f i) s‖
      ≤ ‖fourierOsc (f i) s - fourierOsc (f j) s‖ + ‖fourierOsc (f j) s‖ := by
    simpa using norm_add_le (fourierOsc (f i) s - fourierOsc (f j) s) (fourierOsc (f j) s)
  have hj2 := hs j hjJ
  linarith

/-- **A family parametrised continuously in `L¹` by a compact set is totally bounded.**
The finite `δ`-net is a finite subcover of the parameter set by the neighbourhoods on which the
`L¹` modulus of continuity is below `δ`. -/
theorem exists_finset_l1Net_of_isCompact {α : Type*} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) (f : α → ℝ → ℂ)
    (hcont : ∀ a ∈ K, ∀ δ : ℝ, 0 < δ → ∃ U ∈ 𝓝 a, ∀ b ∈ U,
      (∫ x : ℝ, ‖f b x - f a x‖) ≤ δ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ J : Finset α, ↑J ⊆ K ∧ ∀ a ∈ K, ∃ j ∈ J, (∫ x : ℝ, ‖f a x - f j x‖) ≤ δ := by
  choose! U hUmem hUbd using fun a (ha : a ∈ K) => hcont a ha δ hδ
  obtain ⟨t, htK, htcover⟩ := hK.elim_nhds_subcover U (fun a ha => hUmem a ha)
  refine ⟨t, fun a ha => htK a (Finset.mem_coe.1 ha), fun a ha => ?_⟩
  obtain ⟨j, hjt, haU⟩ := Set.mem_iUnion₂.1 (htcover ha)
  exact ⟨j, hjt, hUbd j (htK j hjt) a haU⟩

/-- **Riemann–Lebesgue, uniformly over a compactly parametrised family.** The form the
applications consume: a compact parameter set `K`, an `L¹`-continuous dependence, and the
conclusion that `∫ e^{ixs} f_a(x) dx` is eventually below `ε` *simultaneously* for all `a ∈ K`.

This is the soft route to the uniformity statements that multivariate Cramér conditions need:
the directions form a compact sphere, and only the `L¹`-continuity of the projected densities
has to be checked. -/
theorem eventually_norm_fourierOsc_le_of_isCompact {α : Type*} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) (f : α → ℝ → ℂ) (hf : ∀ a ∈ K, Integrable (f a))
    (hcont : ∀ a ∈ K, ∀ δ : ℝ, 0 < δ → ∃ U ∈ 𝓝 a, ∀ b ∈ U,
      (∫ x : ℝ, ‖f b x - f a x‖) ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in Filter.cocompact ℝ, ∀ a ∈ K, ‖fourierOsc (f a) s‖ ≤ ε :=
  eventually_norm_fourierOsc_le_of_totallyBounded f K hf
    (fun _ hδ => exists_finset_l1Net_of_isCompact hK f hcont hδ) hε

end Uniform

/-! ## The application: an oscillatory integral with a quadratic phase

For a law carried by the parabola `y ↦ (y, y²)` — the law of `(X − μ, (X − μ)² − σ²)` that the
studentized Edgeworth expansion runs on — the characteristic function in the direction
`t = (t₀, t₁)` is, up to a unimodular factor, `∫ f(y) e^{i(t₀y + t₁y²)} dy` with `f` the density
of `X − μ`. A multivariate Cramér condition asks for this to stay away from `1` as `‖t‖ → ∞`,
uniformly.

Two regimes have to be treated separately, and only the first is a Riemann–Lebesgue statement:

* `|t₁|` bounded. Then `‖t‖ → ∞` forces `|t₀| → ∞`, and the integral is the Fourier transform,
  at frequency `t₀`, of the **twisted density** `y ↦ e^{it₁y²}f(y)`. The twists form a family
  parametrised by the compact interval `|t₁| ≤ M`, continuously in `L¹` — dominated convergence,
  with dominating function `2‖f‖` — so `eventually_norm_fourierOsc_le_of_isCompact` applies and
  gives decay uniform in `t₁`. That is `eventually_norm_quadPhaseInt_le` below.
* `|t₁| → ∞`. Here the phase is genuinely quadratic and no `L¹` family is compact: the twists
  `e^{it₁y²}f` oscillate away from each other in `L¹`. The classical estimates are van der
  Corput's second-derivative test, or the soft autocorrelation identity
  `|I|² = ∫ e^{i(t₀h + t₁h²)} ĝ_h(2t₁h) dh` with `g_h(z) = f(z + h)\overline{f(z)}`, which for
  compactly supported `f` confines `h` to a compact set and lets dominated convergence take
  `|t₁| → ∞`. Neither is proved here; see the note on `edgeworth_studentized_uniform`. -/

section QuadraticPhase

/-- The density twisted by the quadratic part of the phase: `y ↦ e^{i t y²} f(y)`. -/
noncomputable def quadTwist (f : ℝ → ℂ) (t : ℝ) : ℝ → ℂ :=
  fun y => Complex.exp ((t * y ^ 2 : ℝ) * Complex.I) * f y

/-- The oscillatory integral with a quadratic phase, `∫ f(y) e^{i(t₀y + t₁y²)} dy`. -/
noncomputable def quadPhaseInt (f : ℝ → ℂ) (t₀ t₁ : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp ((t₀ * y + t₁ * y ^ 2 : ℝ) * Complex.I) * f y

/-- Twisting the density turns a quadratic phase into a linear one. -/
lemma quadPhaseInt_eq_fourierOsc (f : ℝ → ℂ) (t₀ t₁ : ℝ) :
    quadPhaseInt f t₀ t₁ = fourierOsc (quadTwist f t₁) t₀ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change Complex.exp ((t₀ * y + t₁ * y ^ 2 : ℝ) * Complex.I) * f y
    = Complex.exp ((y * t₀ : ℝ) * Complex.I)
        * (Complex.exp ((t₁ * y ^ 2 : ℝ) * Complex.I) * f y)
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The twist does not change the modulus, hence preserves integrability. -/
lemma integrable_quadTwist {f : ℝ → ℂ} (hf : Integrable f) (t : ℝ) :
    Integrable (quadTwist f t) := by
  refine Integrable.mono' hf.norm ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · rw [quadTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **The twists depend on the quadratic coefficient continuously in `L¹`.** Dominated
convergence with the dominating function `2‖f‖`: this is what makes the family over a compact
range of coefficients totally bounded, and hence Riemann–Lebesgue uniform over it. -/
lemma exists_nhds_integral_norm_quadTwist_sub_le {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ U ∈ 𝓝 a, ∀ b ∈ U, (∫ y : ℝ, ‖quadTwist f b y - quadTwist f a y‖) ≤ δ := by
  set Φ : ℝ → ℝ → ℝ := fun b y => ‖quadTwist f b y - quadTwist f a y‖ with hΦ
  have hmeas : ∀ b : ℝ, AEStronglyMeasurable (Φ b) (volume : Measure ℝ) := by
    intro b
    exact (((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable).sub ((Complex.continuous_exp.comp
        (by fun_prop)).aestronglyMeasurable.mul hf.aestronglyMeasurable)).norm
  have hbd : ∀ b : ℝ, ∀ y : ℝ, ‖Φ b y‖ ≤ 2 * ‖f y‖ := by
    intro b y
    have h1 : ‖quadTwist f b y‖ = ‖f y‖ := by
      rw [quadTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have h2 : ‖quadTwist f a y‖ = ‖f y‖ := by
      rw [quadTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have := norm_sub_le (quadTwist f b y) (quadTwist f a y)
    rw [h1, h2] at this
    rw [hΦ, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    linarith
  have hcontpt : ∀ y : ℝ, ContinuousAt (fun b : ℝ => Φ b y) a := by
    intro y
    refine Continuous.continuousAt ?_
    exact ((Complex.continuous_exp.comp (by fun_prop)).mul continuous_const).sub
      continuous_const |>.norm
  have hCA : ContinuousAt (fun b : ℝ => ∫ y : ℝ, Φ b y) a :=
    continuousAt_of_dominated (Filter.Eventually.of_forall fun b => hmeas b)
      (Filter.Eventually.of_forall fun b =>
        Filter.Eventually.of_forall fun y => hbd b y)
      (hf.norm.const_mul 2) (Filter.Eventually.of_forall hcontpt)
  have hzero : (∫ y : ℝ, Φ a y) = 0 := by
    simp [hΦ]
  have hev : ∀ᶠ b in 𝓝 a, (∫ y : ℝ, Φ b y) ≤ δ := by
    have hlt := Metric.tendsto_nhds.1 hCA δ hδ
    filter_upwards [hlt] with b hb
    have hnn : 0 ≤ ∫ y : ℝ, Φ b y := integral_nonneg fun y => norm_nonneg _
    rw [Real.dist_eq, hzero, sub_zero, abs_of_nonneg hnn] at hb
    exact hb.le
  obtain ⟨U, hU, hUb⟩ := Filter.eventually_iff_exists_mem.1 hev
  exact ⟨U, hU, hUb⟩

/-- **The linear regime of the quadratic-phase estimate.**

For a fixed `L¹` function `f` and a fixed bound `M`, `∫ f(y)e^{i(t₀y + t₁y²)} dy → 0` as
`|t₀| → ∞`, **uniformly over `|t₁| ≤ M`**. This is Riemann–Lebesgue applied to the compactly
parametrised family of twisted densities `e^{it₁y²}f`, and it is one of the two regimes a
multivariate Cramér condition for a parabola-carried law decomposes into. -/
theorem eventually_norm_quadPhaseInt_le {f : ℝ → ℂ} (hf : Integrable f) (M : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ t₀ in Filter.cocompact ℝ, ∀ t₁ : ℝ, |t₁| ≤ M → ‖quadPhaseInt f t₀ t₁‖ ≤ ε := by
  have hmain := eventually_norm_fourierOsc_le_of_isCompact (K := Set.Icc (-M) M)
    isCompact_Icc (quadTwist f) (fun a _ => integrable_quadTwist hf a)
    (fun a _ δ hδ => exists_nhds_integral_norm_quadTwist_sub_le hf a hδ) hε
  filter_upwards [hmain] with t₀ ht₀ t₁ ht₁
  rw [quadPhaseInt_eq_fourierOsc]
  exact ht₀ t₁ (Set.mem_Icc.2 (abs_le.1 ht₁))

end QuadraticPhase

end StatLean.HypothesisTesting
