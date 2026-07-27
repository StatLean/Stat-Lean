import StatLean.AsymptoticStatistics.ForMathlib.Contiguity

/-!
# Le Cam's first lemma from an asymptotic integral comparison

`Contiguity.mutuallyContiguous_of_asymptotically_log_normal` requires the **exact**
change-of-measure identity `Q n = (P n).withDensity (exp ∘ L n)`, which for a
quadratic-mean-differentiable family holds only under a per-`n` common-support hypothesis.
This file proves the **support-free** version: the exact identity is replaced by the
asymptotic integral comparison
`|∫ g dQₙ − ∫ g · exp(Lₙ) dPₙ| ≤ C · ρₙ` (all measurable `|g| ≤ C`), with `ρₙ → 0` —
exactly the output shape of
`AsymptoticRepresentation.productMeasure_integral_comparison_boundedMeasurable`.

Main declarations:
* `Contiguity.Contiguous.comp_subseq` — contiguity restricts along a strictly monotone
  subsequence (events padded by `∅` off the subsequence);
* `Contiguity.mutuallyContiguous_of_log_normal_of_integral_comparison` — the headline
  support-free Le Cam first lemma.

**Proof formalization notes.** Direction `Q ⊲ P`: for events `Aₙ` with `Pₙ(Aₙ) → 0`,
`Qₙ(Aₙ) ≤ ∫_{Aₙ} exp(Lₙ) dPₙ + ρₙ`, and the first term `→ 0` by the uniform-integrability
argument already packaged in `Contiguity.uniform_integrability_exp_L_of_integral_tendsto_one`
(the total-mass comparison at `g ≡ 1` gives `∫ exp(Lₙ) dPₙ → 1`). Direction `P ⊲ Q`: split on
`{Lₙ ≥ −M}` for a continuity-point `M` of the Gaussian limit:
`Pₙ(Aₙ) ≤ Pₙ(Lₙ < −M) + e^M · (Qₙ(Aₙ) + ρₙ)`, and let first `n → ∞` then `M → ∞` along
continuity points (portmanteau for the weak limit of `Pₙ.map Lₙ`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics
namespace Contiguity

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-! ### LEAN-ONLY plumbing: transporting events along an index equality -/

/-- Transport a set along an equality of indices. -/
private def transportSet (α : ℕ → Type*) {a b : ℕ} (h : a = b) (s : Set (α a)) : Set (α b) :=
  h ▸ s

private lemma measurableSet_transportSet {α : ℕ → Type*} [∀ n, MeasurableSpace (α n)]
    {a b : ℕ} (h : a = b) {s : Set (α a)} (hs : MeasurableSet s) :
    MeasurableSet (transportSet α h s) := by
  subst h; exact hs

private lemma measure_transportSet {α : ℕ → Type*} [∀ n, MeasurableSpace (α n)]
    (μ : ∀ n, Measure (α n)) {a b : ℕ} (h : a = b) (s : Set (α a)) :
    μ b (transportSet α h s) = μ a s := by
  subst h; rfl

private lemma transportSet_comp {α : ℕ → Type*} {ψ : ℕ → ℕ} (hψ : Function.Injective ψ)
    {k n : ℕ} (h : ψ k = ψ n) (A : ∀ m, Set (α (ψ m))) :
    transportSet α h (A k) = A n := by
  have hkn : k = n := hψ h
  subst hkn
  rfl

/-! ### LEAN-ONLY plumbing: `ℝ≥0∞`-valued versus real-valued convergence to `0` -/

private lemma toReal_tendsto_zero {u : ℕ → ℝ≥0∞} (h : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => (u n).toReal) atTop (𝓝 0) := by
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa using this

private lemma tendsto_zero_of_toReal {u : ℕ → ℝ≥0∞} (hfin : ∀ n, u n ≠ ⊤)
    (h : Tendsto (fun n => (u n).toReal) atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  have h_of_real : Tendsto (fun n => ENNReal.ofReal (u n).toReal) atTop (𝓝 0) := by
    have h_comp := (ENNReal.continuous_ofReal.tendsto 0).comp h
    simpa using h_comp
  have h_eq : (fun n => ENNReal.ofReal (u n).toReal) = u := by
    funext n; rw [ENNReal.ofReal_toReal (hfin n)]
  rwa [h_eq] at h_of_real

/-- Bounded measurable real functions are integrable against a finite measure. -/
private lemma integrable_of_abs_le {β : Type*} [MeasurableSpace β] (μ : Measure β)
    [IsFiniteMeasure μ] {f : β → ℝ} (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ :=
  ⟨hf.aestronglyMeasurable,
    MeasureTheory.HasFiniteIntegral.of_bounded (C := C)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)⟩

/-! ### LEAN-ONLY plumbing: a continuous ramp majorizing a left half-line indicator -/

/-- The ramp `x ↦ max 0 (min 1 (a - x))`, a bounded continuous function that equals `1` on
`Iic (a - 1)` and vanishes on `Ici a`. -/
private noncomputable def rampBCF (a : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max 0 (min 1 (a - x)))
    (continuous_const.max (continuous_const.min (continuous_const.sub continuous_id)))
    1
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le zero_le_one (min_le_left _ _))

@[simp] private lemma rampBCF_apply (a x : ℝ) : rampBCF a x = max 0 (min 1 (a - x)) := rfl

private lemma rampBCF_abs_le_one (a x : ℝ) : |rampBCF a x| ≤ 1 := by
  rw [rampBCF_apply, abs_of_nonneg (le_max_left _ _)]
  exact max_le zero_le_one (min_le_left _ _)

private lemma tendsto_integral_rampBCF_atBot (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Tendsto (fun k : ℕ => ∫ x, rampBCF (-(k : ℝ)) x ∂ν) atTop (𝓝 0) := by
  have h_lim : ∀ᵐ x ∂ν, Tendsto (fun k : ℕ => rampBCF (-(k : ℝ)) x) atTop (𝓝 0) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈|x|⌉₊] with k hk
    have hx : |x| ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
    have hnx : -x ≤ (k : ℝ) := le_trans (neg_le_abs x) hx
    have hle : -(k : ℝ) - x ≤ 0 := by linarith
    rw [rampBCF_apply]
    exact (max_eq_left ((min_le_right _ _).trans hle)).symm
  have h_dom : ∀ k : ℕ, ∀ᵐ x ∂ν, ‖rampBCF (-(k : ℝ)) x‖ ≤ (1 : ℝ) :=
    fun k => Filter.Eventually.of_forall
      (fun x => by rw [Real.norm_eq_abs]; exact rampBCF_abs_le_one _ _)
  have h_tendsto := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun (k : ℕ) (x : ℝ) => rampBCF (-(k : ℝ)) x) (f := fun _ : ℝ => (0 : ℝ))
    (bound := fun _ : ℝ => (1 : ℝ))
    (fun k => (rampBCF (-(k : ℝ))).continuous.aestronglyMeasurable)
    (integrable_const (1 : ℝ)) h_dom h_lim
  simpa using h_tendsto

/-- **Uniform left-tail bound for an asymptotically weakly convergent statistic.** If
`(P n).map (L n) ⇝ ν` with `ν` a probability measure, the left tails
`P n {L n < -M}` are eventually uniformly small for `M` large. -/
private lemma exists_tail_prob_bound {α : ℕ → Type*} [∀ n, MeasurableSpace (α n)]
    (P : ∀ n, Measure (α n)) [∀ n, IsProbabilityMeasure (P n)]
    (L : ∀ n, α n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h_weak : WeakConverges (fun n => (P n).map (L n)) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ((P n) {ω | L n ω < -M}).toReal ≤ ε := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∫ x, rampBCF (-(k : ℝ)) x ∂ν < ε :=
    ((tendsto_integral_rampBCF_atBot ν) (Iio_mem_nhds hε)).exists
  refine ⟨(k : ℝ) + 1, by positivity, ?_⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((h_weak (rampBCF (-(k : ℝ)))) (Iio_mem_nhds hk))
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ∫ x, rampBCF (-(k : ℝ)) x ∂((P n).map (L n)) < ε := hN n hn
  have h2 : ∫ x, rampBCF (-(k : ℝ)) x ∂((P n).map (L n))
      = ∫ ω, rampBCF (-(k : ℝ)) (L n ω) ∂(P n) :=
    MeasureTheory.integral_map (hL_meas n).aemeasurable
      (rampBCF (-(k : ℝ))).continuous.aestronglyMeasurable
  rw [h2] at h1
  set S : Set (α n) := {ω | L n ω < -((k : ℝ) + 1)} with hS_def
  have hS_meas : MeasurableSet S := measurableSet_lt (hL_meas n) measurable_const
  have h3 : ((P n) S).toReal ≤ ∫ ω, rampBCF (-(k : ℝ)) (L n ω) ∂(P n) := by
    have hind : ((P n) S).toReal = ∫ ω, S.indicator (fun _ => (1 : ℝ)) ω ∂(P n) := by
      rw [MeasureTheory.integral_indicator hS_meas, MeasureTheory.setIntegral_const]
      simp [measureReal_def]
    rw [hind]
    refine MeasureTheory.integral_mono ((integrable_const (1 : ℝ)).indicator hS_meas)
      (integrable_of_abs_le (P n)
        ((rampBCF (-(k : ℝ))).continuous.measurable.comp (hL_meas n)) 1
        (fun ω => rampBCF_abs_le_one _ _)) (fun ω => ?_)
    by_cases hω : ω ∈ S
    · have hlt : L n ω < -((k : ℝ) + 1) := hω
      have hge : (1 : ℝ) ≤ -(k : ℝ) - L n ω := by linarith
      rw [Set.indicator_of_mem hω, rampBCF_apply]
      exact le_max_of_le_right (le_min le_rfl hge)
    · rw [Set.indicator_of_notMem hω, rampBCF_apply]
      exact le_max_left _ _
  linarith

/-- **Contiguity along a subsequence.** If `Q ⊲ P` along `atTop`, the same holds for the
subsequences `P ∘ φ`, `Q ∘ φ` for any strictly monotone `φ` (pad the events by `∅` off the
range of `φ`). -/
theorem Contiguous.comp_subseq {P Q : ∀ n, Measure (Ω n)}
    (hPQ : Contiguous (ι := ℕ) (Ω := Ω) atTop P Q) {φ : ℕ → ℕ}
    -- LEAN-ONLY: subsequence extraction (regularity of the index map)
    (hφ : StrictMono φ) :
    Contiguous (ι := ℕ) (Ω := fun n => Ω (φ n)) atTop
      (fun n => P (φ n)) (fun n => Q (φ n)) := by
  classical
  intro A hA_meas hA_tendsto
  -- Pad the events by `∅` off the range of `φ`.
  obtain ⟨B, hB_def⟩ : ∃ B : ∀ m, Set (Ω m), ∀ m, B m =
      if h : ∃ n, φ n = m then transportSet Ω h.choose_spec (A h.choose) else ∅ :=
    ⟨_, fun _ => rfl⟩
  have hB_at : ∀ n, B (φ n) = A n := by
    intro n
    have hex : ∃ k, φ k = φ n := ⟨n, rfl⟩
    rw [hB_def, dif_pos hex, transportSet_comp hφ.injective]
  have hB_meas : ∀ m, MeasurableSet (B m) := by
    intro m
    rw [hB_def]
    by_cases h : ∃ n, φ n = m
    · rw [dif_pos h]
      exact measurableSet_transportSet _ (hA_meas _)
    · rw [dif_neg h]
      exact MeasurableSet.empty
  have hB_empty : ∀ m, (¬ ∃ n, φ n = m) → B m = ∅ := by
    intro m h; rw [hB_def, dif_neg h]
  have hP_tendsto : Tendsto (fun m => (P m) (B m)) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    rw [ENNReal.tendsto_nhds_zero] at hA_tendsto
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hA_tendsto ε hε)
    refine Filter.eventually_atTop.mpr ⟨φ N, fun m hm => ?_⟩
    by_cases h : ∃ n, φ n = m
    · obtain ⟨n, rfl⟩ := h
      rw [hB_at n]
      exact hN n (hφ.le_iff_le.mp hm)
    · rw [hB_empty m h]
      simp
  have hQB := hPQ B hB_meas hP_tendsto
  have hcomp := hQB.comp hφ.tendsto_atTop
  simpa [Function.comp, hB_at] using hcomp

/-- **Le Cam's first lemma, support-free integral-comparison form.** Suppose

* `Lₙ` is a measurable "asymptotic log-likelihood" with
  `Pₙ.map Lₙ ⇝ N(−v/2, v)` (asymptotic log-normality), and
* the integral comparison holds: there is `ρₙ → 0` with
  `|∫ g dQₙ − ∫ g · exp(Lₙ) dPₙ| ≤ C · ρₙ` for every uniformly bounded measurable family
  `g` (bound `C`).

Then `P` and `Q` are mutually contiguous. This replaces the exact identity
`Qₙ = Pₙ.withDensity (exp ∘ Lₙ)` of `mutuallyContiguous_of_asymptotically_log_normal` by
asymptotic singular-mass control, which is what a DQM family actually provides (vdV §6.4,
Example 6.5, combined with the §7.2 remainder control). -/
theorem mutuallyContiguous_of_log_normal_of_integral_comparison
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ)
    -- LEAN-ONLY: measurability of the log-likelihood statistics (regularity)
    (hL_meas : ∀ n, Measurable (L n))
    -- USER-INPUT: asymptotic integral comparison replacing the exact change of measure;
    -- vdV §7.2 (supplied by `productMeasure_integral_comparison_boundedMeasurable`)
    (h_comparison : ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧
      ∀ (g : ∀ n, Ω n → ℝ) (C : ℝ), (∀ n, Measurable (g n)) → 0 ≤ C →
        (∀ n ω, |g n ω| ≤ C) → ∀ n,
        |∫ ω, g n ω ∂(Q n) - ∫ ω, g n ω * Real.exp (L n ω) ∂(P n)| ≤ C * ρ n)
    (v : NNReal)
    -- USER-INPUT: asymptotic log-normality of `Lₙ` under `Pₙ`; vdV Example 6.5
    (h_weak : WeakConverges (fun n => (P n).map (L n))
      (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    MutuallyContiguous (ι := ℕ) (Ω := Ω) atTop P Q := by
  obtain ⟨ρ, hρ_tendsto, hρ⟩ := h_comparison
  -- `ρ` is automatically nonnegative (test the comparison at `g ≡ 0`).
  have hρ_nonneg : ∀ n, 0 ≤ ρ n := by
    intro n
    have h := hρ (fun _ _ => (0 : ℝ)) 1 (fun _ => measurable_const) zero_le_one
      (fun _ _ => by simp) n
    simpa using h
  -- Comparison at indicators of measurable events.
  have h_ind : ∀ (A : ∀ n, Set (Ω n)), (∀ n, MeasurableSet (A n)) → ∀ n,
      |((Q n) (A n)).toReal - ∫ ω in A n, Real.exp (L n ω) ∂(P n)| ≤ ρ n := by
    intro A hA n
    have hmeas : ∀ m, Measurable ((A m).indicator (fun _ => (1 : ℝ))) :=
      fun m => measurable_const.indicator (hA m)
    have hbnd : ∀ (m : ℕ) (ω : Ω m), |(A m).indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := by
      intro m ω
      by_cases hω : ω ∈ A m
      · rw [Set.indicator_of_mem hω]; norm_num
      · rw [Set.indicator_of_notMem hω]; norm_num
    have h := hρ (fun m => (A m).indicator (fun _ => (1 : ℝ))) 1 hmeas zero_le_one hbnd n
    have hQ : ∫ ω, (A n).indicator (fun _ => (1 : ℝ)) ω ∂(Q n) = ((Q n) (A n)).toReal := by
      rw [MeasureTheory.integral_indicator (hA n), MeasureTheory.setIntegral_const]
      simp [measureReal_def]
    have hP : ∫ ω, (A n).indicator (fun _ => (1 : ℝ)) ω * Real.exp (L n ω) ∂(P n)
        = ∫ ω in A n, Real.exp (L n ω) ∂(P n) := by
      rw [← MeasureTheory.integral_indicator (hA n)]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      by_cases hω : ω ∈ A n
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, one_mul]
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
    simpa only [hQ, hP, one_mul] using h
  have h_bound : ∀ (A : ∀ n, Set (Ω n)), (∀ n, MeasurableSet (A n)) → ∀ n,
      ((Q n) (A n)).toReal ≤ ∫ ω in A n, Real.exp (L n ω) ∂(P n) + ρ n := by
    intro A hA n
    have h := abs_le.mp (h_ind A hA n)
    linarith [h.2]
  have h_bound' : ∀ (A : ∀ n, Set (Ω n)), (∀ n, MeasurableSet (A n)) → ∀ n,
      ∫ ω in A n, Real.exp (L n ω) ∂(P n) ≤ ((Q n) (A n)).toReal + ρ n := by
    intro A hA n
    have h := abs_le.mp (h_ind A hA n)
    linarith [h.1]
  -- Truncated mass control: `∫ min(exp Lₙ, k) dPₙ ≤ 1 + ρₙ` for every truncation level `k`.
  have h_trunc_le : ∀ (k n : ℕ),
      ∫ ω, min (Real.exp (L n ω)) (k : ℝ) ∂(P n) ≤ 1 + ρ n := by
    intro k n
    have hg_meas : ∀ m : ℕ, Measurable
        (fun ω : Ω m => min 1 ((k : ℝ) * Real.exp (-(L m ω)))) := fun m =>
      measurable_const.min (measurable_const.mul
        (Real.measurable_exp.comp (hL_meas m).neg))
    have hg_bound : ∀ (m : ℕ) (ω : Ω m),
        |min 1 ((k : ℝ) * Real.exp (-(L m ω)))| ≤ 1 := by
      intro m ω
      have h0 : (0 : ℝ) ≤ (k : ℝ) * Real.exp (-(L m ω)) :=
        mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
      rw [abs_of_nonneg (le_min zero_le_one h0)]
      exact min_le_left _ _
    have hcmp := hρ (fun m ω => min 1 ((k : ℝ) * Real.exp (-(L m ω)))) 1 hg_meas
      zero_le_one hg_bound n
    have hmul_pt : ∀ ω : Ω n,
        min 1 ((k : ℝ) * Real.exp (-(L n ω))) * Real.exp (L n ω)
          = min (Real.exp (L n ω)) (k : ℝ) := by
      intro ω
      have ht : (0 : ℝ) < Real.exp (L n ω) := Real.exp_pos _
      rw [Real.exp_neg]
      rcases le_total (1 : ℝ) ((k : ℝ) * (Real.exp (L n ω))⁻¹) with h | h
      · have hk' : Real.exp (L n ω) ≤ (k : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_right h ht.le
          rwa [one_mul, inv_mul_cancel_right₀ ht.ne'] at hmul
        rw [min_eq_left h, one_mul, min_eq_left hk']
      · have hk' : (k : ℝ) ≤ Real.exp (L n ω) := by
          have hmul := mul_le_mul_of_nonneg_right h ht.le
          rwa [one_mul, inv_mul_cancel_right₀ ht.ne'] at hmul
        rw [min_eq_right h, min_eq_right hk', inv_mul_cancel_right₀ ht.ne']
    have hQ_le : ∫ ω, min 1 ((k : ℝ) * Real.exp (-(L n ω))) ∂(Q n) ≤ 1 := by
      have hle := MeasureTheory.integral_mono
        (integrable_of_abs_le (Q n) (hg_meas n) 1 (hg_bound n))
        (integrable_const (1 : ℝ)) (fun ω => min_le_left _ _)
      simpa [measureReal_def] using hle
    have hcmp' : |∫ ω, min 1 ((k : ℝ) * Real.exp (-(L n ω))) ∂(Q n)
        - ∫ ω, min (Real.exp (L n ω)) (k : ℝ) ∂(P n)| ≤ ρ n := by
      simpa only [hmul_pt, one_mul] using hcmp
    have h := abs_le.mp hcmp'
    linarith [h.1, hQ_le]
  -- Integrability of `exp(Lₙ)` under `Pₙ`, by monotone convergence over truncations.
  have h_exp_int : ∀ n, Integrable (fun ω => Real.exp (L n ω)) (P n) := by
    intro n
    refine ⟨(Real.continuous_exp.measurable.comp (hL_meas n)).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun ω => (Real.exp_pos (L n ω)).le))]
    have hfun : (fun ω => ENNReal.ofReal (Real.exp (L n ω)))
        = fun ω => ⨆ k : ℕ, ENNReal.ofReal (min (Real.exp (L n ω)) (k : ℝ)) := by
      funext ω
      refine le_antisymm ?_ (iSup_le fun k => ENNReal.ofReal_le_ofReal (min_le_left _ _))
      refine le_iSup_of_le ⌈Real.exp (L n ω)⌉₊ ?_
      exact le_of_eq (by rw [min_eq_left (Nat.le_ceil _)])
    have hmono : Monotone
        (fun (k : ℕ) (ω : Ω n) => ENNReal.ofReal (min (Real.exp (L n ω)) (k : ℝ))) := by
      intro a b hab ω
      exact ENNReal.ofReal_le_ofReal
        (min_le_min le_rfl (by exact_mod_cast hab))
    have hmeask : ∀ k : ℕ, Measurable
        (fun ω : Ω n => ENNReal.ofReal (min (Real.exp (L n ω)) (k : ℝ))) := fun k =>
      ENNReal.measurable_ofReal.comp
        ((Real.continuous_exp.measurable.comp (hL_meas n)).min measurable_const)
    have hbound : ∫⁻ ω, ENNReal.ofReal (Real.exp (L n ω)) ∂(P n)
        ≤ ENNReal.ofReal (1 + ρ n) := by
      rw [hfun, MeasureTheory.lintegral_iSup hmeask hmono]
      refine iSup_le fun k => ?_
      have hint : Integrable (fun ω => min (Real.exp (L n ω)) (k : ℝ)) (P n) :=
        integrable_of_abs_le (P n)
          ((Real.continuous_exp.measurable.comp (hL_meas n)).min measurable_const) (k : ℝ)
          (fun ω => by
            rw [abs_of_nonneg (le_min (Real.exp_pos _).le (Nat.cast_nonneg _))]
            exact min_le_right _ _)
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun ω =>
          le_min (Real.exp_pos _).le (Nat.cast_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (h_trunc_le k n)
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  -- Asymptotic total mass: `∫ exp(Lₙ) dPₙ → 1`.
  have h_mass : Tendsto (fun n => ∫ ω, Real.exp (L n ω) ∂(P n)) atTop (𝓝 1) := by
    have hkey : ∀ n, ‖(∫ ω, Real.exp (L n ω) ∂(P n)) - 1‖ ≤ ρ n := by
      intro n
      have h := hρ (fun _ _ => (1 : ℝ)) 1 (fun _ => measurable_const) zero_le_one
        (fun _ _ => le_of_eq abs_one) n
      rw [Real.norm_eq_abs, abs_sub_comm]
      simpa [measureReal_def] using h
    have h0 : Tendsto (fun n => (∫ ω, Real.exp (L n ω) ∂(P n)) - 1) atTop (𝓝 0) :=
      squeeze_zero_norm hkey hρ_tendsto
    have h1 := h0.add (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)))
    simpa using h1
  have h_UI := uniform_integrability_exp_L_of_integral_tendsto_one P Q L hL_meas
    h_exp_int h_mass v h_weak
  refine ⟨?_, ?_⟩
  · -- `Q ⊲ P`: if `Pₙ(Aₙ) → 0` then `Qₙ(Aₙ) → 0`.
    intro A hA_meas hA_tendsto
    refine tendsto_zero_of_toReal (fun n => (measure_lt_top (Q n) _).ne) ?_
    have hA_real := toReal_tendsto_zero hA_tendsto
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨M, hM_nonneg, N₁, hN₁⟩ := h_UI (ε / 3) (by linarith)
    have hM1_pos : (0 : ℝ) < M + 1 := by linarith
    rw [Metric.tendsto_nhds] at hA_real
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
      (hA_real (ε / (3 * (M + 1))) (by positivity))
    have hρ_metric : Tendsto ρ atTop (𝓝 0) := hρ_tendsto
    rw [Metric.tendsto_nhds] at hρ_metric
    obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp (hρ_metric (ε / 3) (by linarith))
    rw [Filter.eventually_atTop]
    refine ⟨max (max N₁ N₂) N₃, fun n hn => ?_⟩
    have hn₁ : N₁ ≤ n := le_of_max_le_left (le_of_max_le_left hn)
    have hn₂ : N₂ ≤ n := le_of_max_le_right (le_of_max_le_left hn)
    have hn₃ : N₃ ≤ n := le_of_max_le_right hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (ENNReal.toReal_nonneg : 0 ≤ ((Q n) (A n)).toReal)]
    have h_exp_int_n := h_exp_int n
    have h_min_meas : Measurable (fun ω => min (Real.exp (L n ω)) M) :=
      (Real.continuous_exp.measurable.comp (hL_meas n)).min measurable_const
    have h_min_int : Integrable (fun ω => min (Real.exp (L n ω)) M) (P n) := by
      refine h_exp_int_n.mono' h_min_meas.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.exp_pos _).le hM_nonneg)]
      exact min_le_left _ _
    have h_diff_int : Integrable
        (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M) (P n) :=
      h_exp_int_n.sub h_min_int
    have h_diff_nonneg :
        0 ≤ᵐ[P n] fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M :=
      Filter.Eventually.of_forall (fun ω => sub_nonneg.mpr (min_le_left _ _))
    have h_int_decomp : ∫ ω in A n, Real.exp (L n ω) ∂(P n)
        = ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n)
          + ∫ ω in A n, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) := by
      rw [← MeasureTheory.integral_add h_min_int.restrict h_diff_int.restrict]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun ω => by ring))
    have h_T1 : ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n)
        ≤ M * ((P n) (A n)).toReal := by
      calc ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n)
          ≤ ∫ _ in A n, M ∂(P n) :=
            MeasureTheory.setIntegral_mono_on h_min_int.restrict
              (integrable_const M).restrict (hA_meas n) (fun ω _ => min_le_right _ _)
        _ = ((P n) (A n)).toReal * M := by rw [MeasureTheory.setIntegral_const]; rfl
        _ = M * ((P n) (A n)).toReal := by ring
    have h_T2 : ∫ ω in A n, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε / 3 :=
      le_trans (MeasureTheory.setIntegral_le_integral h_diff_int h_diff_nonneg) (hN₁ n hn₁)
    have hP_lt : ((P n) (A n)).toReal < ε / (3 * (M + 1)) := by
      have h := hN₂ n hn₂
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at h
    have hρ_lt : ρ n < ε / 3 := by
      have h := hN₃ n hn₃
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hρ_nonneg n)] at h
    have hMT : M * ((P n) (A n)).toReal < ε / 3 := by
      have hnn : (0 : ℝ) ≤ ((P n) (A n)).toReal := ENNReal.toReal_nonneg
      have ha : M * ((P n) (A n)).toReal ≤ (M + 1) * ((P n) (A n)).toReal := by nlinarith
      have hb : (M + 1) * ((P n) (A n)).toReal < (M + 1) * (ε / (3 * (M + 1))) :=
        mul_lt_mul_of_pos_left hP_lt hM1_pos
      have hc : (M + 1) * (ε / (3 * (M + 1))) = ε / 3 := by field_simp
      linarith
    linarith [h_bound A hA_meas n, h_int_decomp, h_T1, h_T2]
  · -- `P ⊲ Q`: if `Qₙ(Aₙ) → 0` then `Pₙ(Aₙ) → 0`.
    intro A hA_meas hA_tendsto
    refine tendsto_zero_of_toReal (fun n => (measure_lt_top (P n) _).ne) ?_
    have hA_real := toReal_tendsto_zero hA_tendsto
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨M, hM_nonneg, N₁, hN₁⟩ :=
      exists_tail_prob_bound P L hL_meas
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) h_weak
        (ε := ε / 2) (by linarith)
    have hlim : Tendsto (fun n => Real.exp M * (((Q n) (A n)).toReal + ρ n)) atTop (𝓝 0) := by
      have h := (hA_real.add hρ_tendsto).const_mul (Real.exp M)
      simpa using h
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
      (hlim (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by linarith)))
    rw [Filter.eventually_atTop]
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hn₁ : N₁ ≤ n := le_of_max_le_left hn
    have hn₂ : N₂ ≤ n := le_of_max_le_right hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (ENNReal.toReal_nonneg : 0 ≤ ((P n) (A n)).toReal)]
    have hSmeas : MeasurableSet ({ω | -M ≤ L n ω} : Set (Ω n)) :=
      measurableSet_le measurable_const (hL_meas n)
    have hTmeas : MeasurableSet ({ω | L n ω < -M} : Set (Ω n)) :=
      measurableSet_lt (hL_meas n) measurable_const
    have hsub : A n ⊆ (A n ∩ {ω | -M ≤ L n ω}) ∪ {ω | L n ω < -M} := by
      intro ω hω
      by_cases h : -M ≤ L n ω
      · exact Or.inl ⟨hω, h⟩
      · exact Or.inr (not_le.mp h)
    have hle : (P n) (A n)
        ≤ (P n) (A n ∩ {ω | -M ≤ L n ω}) + (P n) {ω | L n ω < -M} :=
      le_trans (measure_mono hsub) (measure_union_le _ _)
    have hle_real : ((P n) (A n)).toReal
        ≤ ((P n) (A n ∩ {ω | -M ≤ L n ω})).toReal
          + ((P n) {ω | L n ω < -M}).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      exact ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle
    have hAS : MeasurableSet (A n ∩ {ω | -M ≤ L n ω}) := (hA_meas n).inter hSmeas
    have hkey : ((P n) (A n ∩ {ω | -M ≤ L n ω})).toReal
        ≤ Real.exp M * ∫ ω in A n, Real.exp (L n ω) ∂(P n) := by
      have h1 : ((P n) (A n ∩ {ω | -M ≤ L n ω})).toReal
          = ∫ _ω in (A n ∩ {ω | -M ≤ L n ω}), (1 : ℝ) ∂(P n) := by
        rw [MeasureTheory.setIntegral_const]; simp [measureReal_def]
      have h2 : ∫ _ω in (A n ∩ {ω | -M ≤ L n ω}), (1 : ℝ) ∂(P n)
          ≤ ∫ ω in (A n ∩ {ω | -M ≤ L n ω}), Real.exp M * Real.exp (L n ω) ∂(P n) := by
        refine MeasureTheory.setIntegral_mono_on (integrable_const (1 : ℝ)).restrict
          (((h_exp_int n).const_mul (Real.exp M)).restrict) hAS (fun ω hω => ?_)
        have hmem : -M ≤ L n ω := hω.2
        calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp (M + L n ω) := Real.exp_le_exp.mpr (by linarith)
          _ = Real.exp M * Real.exp (L n ω) := Real.exp_add _ _
      have h3 : ∫ ω in (A n ∩ {ω | -M ≤ L n ω}), Real.exp M * Real.exp (L n ω) ∂(P n)
          = Real.exp M * ∫ ω in (A n ∩ {ω | -M ≤ L n ω}), Real.exp (L n ω) ∂(P n) :=
        MeasureTheory.integral_const_mul _ _
      have h4 : ∫ ω in (A n ∩ {ω | -M ≤ L n ω}), Real.exp (L n ω) ∂(P n)
          ≤ ∫ ω in A n, Real.exp (L n ω) ∂(P n) :=
        MeasureTheory.setIntegral_mono_set (h_exp_int n).restrict
          (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))
          (Filter.Eventually.of_forall (fun ω hω => hω.1))
      have h5 := mul_le_mul_of_nonneg_left h4 (Real.exp_pos M).le
      linarith
    have h6 : Real.exp M * ∫ ω in A n, Real.exp (L n ω) ∂(P n)
        ≤ Real.exp M * (((Q n) (A n)).toReal + ρ n) :=
      mul_le_mul_of_nonneg_left (h_bound' A hA_meas n) (Real.exp_pos M).le
    have h7 : ((P n) {ω | L n ω < -M}).toReal ≤ ε / 2 := hN₁ n hn₁
    have h8 : Real.exp M * (((Q n) (A n)).toReal + ρ n) < ε / 2 := hN₂ n hn₂
    linarith

end Contiguity
end AsymptoticStatistics
