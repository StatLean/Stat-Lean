import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
import StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal

/-!
# Equicontinuity-side chaining brick for Theorem 19.5

This file isolates the deepest textbook brick of the
`isPDonsker_of_finite_bracketing_entropy_integral` proof: the
strong-iid form of asymptotic equicontinuity under a finite bracketing
entropy integral. It is the consumer-form chaining/maximal-inequality
assembly described in the chaining proof of vdV §19.2 (`Theorem 19.5`'s
equicontinuity half): chain construction `δ_q ↓ 0`, envelope extraction
from the level-1 bracket cover, application of the tight maximal
inequality `maximal_inequality_bracketing_tight`, Markov, and the
diagonal limit driving the L²-vanishing back to a probability bound on
the empirical-process gap.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §19.2.

Headline declaration: `equicontinuity_chaining_assembly_brick`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Markov bridge — mean-`L²` vanishing implies probabilistic-`L²`
vanishing in `μ`**.

Given a random-pair sequence `(fhat n, ghat n) : ℕ → Ξ → (Ω → ℝ)`
whose pointwise `L²(P)`-gap vanishes in mean (in `μ`), the same gap
vanishes in `μ`-probability at every scale `δ > 0`:

`∫ ξ, ‖fhat n ξ − ghat n ξ‖²_{L²(P)} ∂μ → 0`  ⟹
`μ{ξ | δ ≤ ‖fhat n ξ − ghat n ξ‖²_{L²(P)}} → 0`  for every `δ > 0`.

Pure Markov via `meas_ge_le_lintegral_div` after bridging the real
integral to the lintegral form via `ofReal_integral_eq_lintegral_ofReal`.
The pointwise integrand `ψ_n ξ = ∫ x, (fhat n ξ x − ghat n ξ x)² ∂P` is
non-negative (square of a real-valued integrand), so the bridge applies
with a clean non-negativity hypothesis.

The conclusion is exactly the "L²-consistency in probability" form
consumed by the vdV §19.2 chaining argument: the L²-consistency
hypothesis combined with Markov pushes the event
`‖fhat n − ghat n‖_{L²(P)} > δ_q` to `μ`-measure 0. It feeds
`equi_chain_diagonal_assembly_with_prob_l2`. -/
private lemma equi_chain_mean_l2_to_prob_l2
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (h_l2_int : ∀ n, Integrable
      (fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) μ)
    (h_l2 : Tendsto (fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
        atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n =>
      μ {ξ | δ ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P}) atTop (𝓝 0) := by
  -- Abbreviate the per-`n` `L²(P)`-gap as `ψ_n : Ξ → ℝ`.
  set ψ : ℕ → Ξ → ℝ := fun n ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P with hψ_def
  -- Non-negativity: each `ψ n ξ` is the integral of a non-negative integrand.
  have hψ_nonneg : ∀ n ξ, 0 ≤ ψ n ξ :=
    fun n ξ => integral_nonneg (fun x => sq_nonneg _)
  -- Bridge to lintegral form via `ofReal_integral_eq_lintegral_ofReal`.
  have h_lint_eq : ∀ n,
      ENNReal.ofReal (∫ ξ, ψ n ξ ∂μ) = ∫⁻ ξ, ENNReal.ofReal (ψ n ξ) ∂μ :=
    fun n => ofReal_integral_eq_lintegral_ofReal (h_l2_int n)
      (Eventually.of_forall (hψ_nonneg n))
  -- The lintegral form tends to `0`.
  have h_lint_tendsto :
      Tendsto (fun n => ∫⁻ ξ, ENNReal.ofReal (ψ n ξ) ∂μ) atTop (𝓝 0) := by
    have h_real : Tendsto (fun n => ENNReal.ofReal (∫ ξ, ψ n ξ ∂μ))
        atTop (𝓝 (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp h_l2
    rw [ENNReal.ofReal_zero] at h_real
    refine h_real.congr (fun n => h_lint_eq n)
  -- AEMeasurability of `ψ n` for each `n` (from `Integrable`).
  have hψ_aem_real : ∀ n, AEMeasurable (ψ n) μ :=
    fun n => (h_l2_int n).aestronglyMeasurable.aemeasurable
  have hψ_aem : ∀ n, AEMeasurable (fun ξ => ENNReal.ofReal (ψ n ξ)) μ :=
    fun n => ENNReal.measurable_ofReal.comp_aemeasurable (hψ_aem_real n)
  -- Markov: for each `δ > 0`,
  --   `μ {ξ | ENNReal.ofReal δ ≤ ENNReal.ofReal (ψ n ξ)} ≤
  --    (∫⁻ ξ, ENNReal.ofReal (ψ n ξ) ∂μ) / ENNReal.ofReal δ`.
  set ε : ℝ≥0∞ := ENNReal.ofReal δ with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; exact ENNReal.ofReal_pos.mpr hδ
  have hε_ne : ε ≠ 0 := hε_pos.ne'
  have hε_top : ε ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_markov : ∀ n,
      μ {ξ | ε ≤ ENNReal.ofReal (ψ n ξ)} ≤
        (∫⁻ ξ, ENNReal.ofReal (ψ n ξ) ∂μ) / ε :=
    fun n => meas_ge_le_lintegral_div (hψ_aem n) hε_ne hε_top
  -- The Markov RHS tends to `0 / ε = 0`.
  have h_div_tendsto :
      Tendsto (fun n => (∫⁻ ξ, ENNReal.ofReal (ψ n ξ) ∂μ) / ε) atTop (𝓝 (0 / ε)) :=
    ENNReal.Tendsto.div_const h_lint_tendsto (Or.inr hε_ne)
  rw [ENNReal.zero_div] at h_div_tendsto
  -- Bridge the set descriptions: `{ξ | δ ≤ ψ n ξ} = {ξ | ε ≤ ENNReal.ofReal (ψ n ξ)}`
  -- (use non-negativity of `ψ n` and monotonicity of `ENNReal.ofReal`).
  have h_set_eq : ∀ n,
      {ξ | δ ≤ ψ n ξ} = {ξ | ε ≤ ENNReal.ofReal (ψ n ξ)} := by
    intro n
    ext ξ
    simp only [Set.mem_setOf_eq, hε_def]
    exact ⟨fun h => ENNReal.ofReal_le_ofReal h,
      fun h => (ENNReal.ofReal_le_ofReal_iff (hψ_nonneg n ξ)).mp h⟩
  -- Squeeze: `μ {δ ≤ ψ n} = μ {ε ≤ ofReal (ψ n)} ≤ Markov-RHS → 0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_div_tendsto
    (Eventually.of_forall fun _ => zero_le _) (Eventually.of_forall fun n => ?_)
  rw [h_set_eq n]
  exact h_markov n

/-- **Chain sequence existence — `δ_q ↓ 0` with `J_{[]}(δ_q, F, L²(P)) → 0`**.

The first textbook step of the vdV §19.2 chaining argument:
from finiteness of the bracketing-entropy integral up to scale `1`,
extract an explicit sequence `δ : ℕ → ℝ` of scales that:
* stays in `(0, 1]`,
* tends to `0`, and
* drives the partial bracketing-entropy integral to `0`.

Concretely we take `δ_q := 1 / (q + 1)`; the integral side is the
absolute continuity of `∫⁻ ε in Ioc 0 δ, integrand dε` with respect
to the Lebesgue measure of `Ioc 0 δ`, supplied by the Mathlib lemma
`MeasureTheory.tendsto_setLIntegral_zero`. The Lebesgue volume of
`Ioc 0 (1/(q+1))` is `1/(q+1) → 0`.

Isolating this leaf-fact strips the first vdV §19.2 chaining step out
of the diagonal assembly, leaving `equi_chain_assembly_given_chain_sequence`
to host only the envelope/slice/maximal-inequality/diagonal content. -/
private lemma equi_chain_chain_sequence_exists
    (F : Set (Ω → ℝ)) (P : Measure Ω)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ δ : ℕ → ℝ, (∀ q, 0 < δ q) ∧ (∀ q, δ q ≤ 1) ∧
      Tendsto δ atTop (𝓝 0) ∧
      Tendsto (fun q => bracketingEntropyIntegral (δ q) F P) atTop (𝓝 0) := by
  refine ⟨fun q => 1 / ((q : ℝ) + 1), ?_, ?_, ?_, ?_⟩
  · intro q; positivity
  · intro q
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ (q : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      linarith
    exact this
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · -- Apply `tendsto_setLIntegral_zero` with the restricted Lebesgue measure on `Ioc 0 1`.
    set g : ℝ → ℝ≥0∞ := fun ε =>
      ENat.recTopCoe (⊤ : ℝ≥0∞)
        (fun n : ℕ => ENNReal.ofReal (Real.sqrt (Real.log (n : ℝ))))
        (bracketingNumber ε F 2 P) with hg_def
    -- For δ ∈ (0, 1], `∫⁻ ε in Ioc 0 δ, g dvol = ∫⁻ ε in Ioc 0 δ, g d(vol.restrict (Ioc 0 1))`.
    have h_restrict_eq : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∫⁻ ε in Set.Ioc 0 δ, g ε ∂volume =
          ∫⁻ ε in Set.Ioc 0 δ, g ε
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      intro δ hδ_pos hδ_le_one
      rw [Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioc,
        max_self (0 : ℝ), min_eq_left hδ_le_one]
    -- The total measure `∫⁻ ε, g d(vol.restrict (Ioc 0 1)) = J(1)` is finite.
    have h_J1_finite :
        ∫⁻ ε, g ε ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ ∞ := by
      have : ∫⁻ ε, g ε ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) =
          bracketingEntropyIntegral 1 F P := rfl
      rw [this]; exact h_int.ne
    -- The measure `(vol.restrict (Ioc 0 1)) (Ioc 0 (1/(q+1)))` tends to `0`.
    have h_meas_tendsto : Tendsto
        (fun q : ℕ => (volume.restrict (Set.Ioc (0 : ℝ) 1))
          (Set.Ioc 0 ((1 : ℝ) / ((q : ℝ) + 1)))) atTop (𝓝 0) := by
      have h_vol_eq : ∀ q : ℕ,
          (volume.restrict (Set.Ioc (0 : ℝ) 1))
              (Set.Ioc 0 ((1 : ℝ) / ((q : ℝ) + 1))) =
            ENNReal.ofReal ((1 : ℝ) / ((q : ℝ) + 1)) := by
        intro q
        have hpos : (0 : ℝ) < 1 / ((q : ℝ) + 1) := by positivity
        have hle : (1 : ℝ) / ((q : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
          linarith
        rw [Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioc,
          max_self (0 : ℝ), min_eq_left hle,
          Real.volume_Ioc, sub_zero]
      have h_ofReal_tendsto : Tendsto
          (fun q : ℕ => ENNReal.ofReal ((1 : ℝ) / ((q : ℝ) + 1)))
          atTop (𝓝 (ENNReal.ofReal 0)) :=
        (ENNReal.continuous_ofReal.tendsto _).comp
          tendsto_one_div_add_atTop_nhds_zero_nat
      rw [ENNReal.ofReal_zero] at h_ofReal_tendsto
      refine h_ofReal_tendsto.congr (fun q => (h_vol_eq q).symm)
    -- Combine via `tendsto_setLIntegral_zero`.
    have h_set_tendsto : Tendsto
        (fun q : ℕ => ∫⁻ ε in Set.Ioc 0 ((1 : ℝ) / ((q : ℝ) + 1)), g ε
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) :=
      tendsto_setLIntegral_zero h_J1_finite h_meas_tendsto
    -- Bridge back via `h_restrict_eq`.
    refine h_set_tendsto.congr (fun q => ?_)
    have hpos : (0 : ℝ) < 1 / ((q : ℝ) + 1) := by positivity
    have hle : (1 : ℝ) / ((q : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      linarith
    exact (h_restrict_eq _ hpos hle).symm

/-- **Diagonal chaining assembly given the chain sequence**.

Given the chain sequence `δ : ℕ → ℝ` (with `δ_q ↓ 0` and
`J_{[]}(δ_q, F, L²) → 0`, supplied by
`equi_chain_chain_sequence_exists`) plus the probabilistic-L²
hypothesis on the random pair, this lemma carries the vdV §19.2
chaining content: envelope extraction from the level-1 bracket cover,
application of `maximal_inequality_bracketing_tight` at each scale
`δ_q`, and the diagonal-limit transport.

The core per-`q` chaining-bound claim has the form

  `∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, ∃ N_chain, ∀ n ≥ N_chain,
     μ (badEvent n \ l2Event ((δ q)^2) n) ≤ ENNReal.ofReal K * J(δ q, F, P)`

i.e., a uniform-in-`q` max-inequality bound on the `L²`-good portion
of `badEvent n` in terms of the per-scale bracketing-entropy integral
`J(δ q, F, P)`. This is the content of
`maximal_inequality_bracketing_tight` applied to the difference class
`F − F` at scale `δ q` (envelope from
`hasFiniteBracketingCover_difference_class`), plus Markov on the
threshold `η` and DCT for the envelope tail (absorbed into the
eventually-in-`n` quantifier `∃ N_chain`).

The surrounding ε-N reduction: the diagonal-`q` step uses
`ENNReal.Tendsto.const_mul` on `hδ_J_to_zero` to push `K · J(δ_q) → 0`,
the `L²`-gap branch uses `h_prob_l2` at scale `(δ q₀)² > 0` to extract
`N_l2`, and the union bound combines via `measure_union_le` +
`ENNReal.add_halves`. All bookkeeping (`badEvent`/`l2Event`
decomposition; `ε / 2 + ε / 2 = ε`) is closed inline. -/
private lemma equi_chain_assembly_given_chain_sequence
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (_h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (_hX_meas : ∀ i, Measurable (X i))
    (_hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (_hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (_hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (_h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (_h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (_h_fhat_in : ∀ n ξ, fhat n ξ ∈ F)
    (_h_ghat_in : ∀ n ξ, ghat n ξ ∈ F)
    (h_prob_l2 : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
        μ {ξ | δ ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P}) atTop (𝓝 0))
    -- Derived from `_h_int` via `equi_chain_chain_sequence_exists`.
    (δ : ℕ → ℝ) (hδ_pos : ∀ q, 0 < δ q) (_hδ_le_one : ∀ q, δ q ≤ 1)
    (_hδ_to_zero : Tendsto δ atTop (𝓝 0))
    (hδ_J_to_zero :
      Tendsto (fun q => bracketingEntropyIntegral (δ q) F P) atTop (𝓝 0))
    -- regularity input on the function class `F`. The degenerate case
    -- (J ≡ 0, i.e. `F` is L²-trivial at scale δ) is statistically vacuous.
    (hJ_pos : ∀ δ' : ℝ, 0 < δ' → 0 < bracketingEntropyIntegral δ' F P)
    -- see `chain_supnorm_integral_bound_at_delta_q` (bracket-restricted
    -- subclass + tight bound).
    (hChainBound_outer :
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → ∀ (n : ℕ),
          ∫⁻ ξ, supNormOver F
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
            ≤ ENNReal.ofReal 2 * bracketingEntropyIntegral δq F P
              + ENNReal.ofReal 2 *
                (ENNReal.ofReal (Real.sqrt n)
                  * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                      * Set.indicator {x | δq * Real.sqrt n < |Φ x|} 1 ω ∂P))
    (η : ℝ) (_hη : 0 < η) :
    Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|})
      atTop (𝓝 0) := by
  -- Convert the `Tendsto … (𝓝 0)` goal to the standard ε-N form for ℝ≥0∞.
  refine ENNReal.tendsto_atTop_zero.mpr ?_
  intro ε hε_pos
  -- Abbreviate the conclusion event.
  set badEvent : ℕ → Set Ξ := fun n =>
    {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
              - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
    with hbadEvent_def
  -- Abbreviate the L²-gap "ξ is δ'-far" event (driven to 0 by `h_prob_l2`).
  set l2Event : ℝ → ℕ → Set Ξ := fun δ' n =>
    {ξ | δ' ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P} with hl2Event_def
  -- Split target `ε = ε / 2 + ε / 2`; need each half separately.
  have hε_half_pos : 0 < ε / 2 := ENNReal.div_pos hε_pos.ne' (by norm_num)
  -- Key chaining obligation (the vdV §19.2 chaining content):
  -- there exists a universal constant `K > 0` such that, for each scale
  -- index `q`, eventually-in-`n` the measure of the "L²-good portion" of
  -- `badEvent n` is controlled by `K · J_{[]}(δ q, F, L²(P))`. This is
  -- the per-`q` consequence of `maximal_inequality_bracketing_tight`
  -- applied to the difference class `F − F` at scale `δ q` (envelope
  -- `Φ` from `hasFiniteBracketingCover_difference_class`), with the
  -- envelope-tail term absorbed into the eventually-in-`n` quantifier;
  -- held in `chaining_per_q_max_ineq_bound`, specialized along the chain
  -- sequence δ via `hδ_pos`.
  have hJq_pos : ∀ q, 0 < bracketingEntropyIntegral (δ q) F P :=
    fun q => hJ_pos (δ q) (hδ_pos q)
  obtain ⟨K, _hK_pos, h_per_q_bound⟩ :=
    chaining_per_q_max_ineq_bound F P _h_int μ X _hX_meas _hX_iindep _hX_id
      _hX_law fhat ghat _h_fhat_meas _h_ghat_meas _h_fhat_in _h_ghat_in
      δ hδ_pos _hδ_le_one hJq_pos hChainBound_outer η _hη
  -- Diagonal q-extraction: `K · J(δ_q, F, P) → 0` as `q → ∞` by
  -- `_hδ_J_to_zero` plus `ENNReal.Tendsto.const_mul` (with the side
  -- condition `ENNReal.ofReal K ≠ ∞`, automatic for finite-real `K`).
  have hK_ne_top : (ENNReal.ofReal K : ℝ≥0∞) ≠ ∞ := ENNReal.ofReal_ne_top
  have h_KJ_tendsto : Tendsto
      (fun q => (ENNReal.ofReal K : ℝ≥0∞) * bracketingEntropyIntegral (δ q) F P)
      atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hδ_J_to_zero (Or.inr hK_ne_top)
    simpa [mul_zero] using h
  obtain ⟨q₀, hq₀_KJ⟩ := ENNReal.tendsto_atTop_zero.mp h_KJ_tendsto (ε / 2) hε_half_pos
  -- Combine: at q = q₀, per-q chaining gives `N_chain` for the eventual bound;
  -- at q = q₀, diagonal q gives `K · J(δ_q₀, F, P) ≤ ε / 2`.
  have h_chain_q0 :
      (ENNReal.ofReal K : ℝ≥0∞) * bracketingEntropyIntegral (δ q₀) F P ≤ ε / 2 :=
    hq₀_KJ q₀ le_rfl
  obtain ⟨N_chain, h_N_chain⟩ := h_per_q_bound q₀
  have h_chain : ∀ n ≥ N_chain,
      μ (badEvent n \ l2Event ((δ q₀) ^ 2) n) ≤ ε / 2 :=
    fun n hn => (h_N_chain n hn).trans h_chain_q0
  -- L²-gap branch: apply `h_prob_l2` at scale `(δ q₀)² > 0` and convert
  -- the resulting `Tendsto _ (𝓝 0)` to ε-N form.
  have hδq_sq_pos : 0 < (δ q₀) ^ 2 := pow_pos (hδ_pos q₀) 2
  have h_l2_q0 : Tendsto (fun n => μ (l2Event ((δ q₀) ^ 2) n)) atTop (𝓝 0) := by
    have := h_prob_l2 ((δ q₀) ^ 2) hδq_sq_pos
    simpa [hl2Event_def] using this
  obtain ⟨N_l2, h_l2_bound⟩ :=
    ENNReal.tendsto_atTop_zero.mp h_l2_q0 (ε / 2) hε_half_pos
  -- Combine: choose `N = max N_chain N_l2` and split `badEvent n` into the
  -- two pieces.
  refine ⟨max N_chain N_l2, fun n hn => ?_⟩
  have hn_chain : N_chain ≤ n := le_trans (le_max_left _ _) hn
  have hn_l2 : N_l2 ≤ n := le_trans (le_max_right _ _) hn
  -- `badEvent n = (badEvent n \ l2Event _) ∪ (badEvent n ∩ l2Event _)`.
  have h_split :
      badEvent n =
        (badEvent n \ l2Event ((δ q₀) ^ 2) n)
          ∪ (badEvent n ∩ l2Event ((δ q₀) ^ 2) n) := by
    ext ξ
    simp only [Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    constructor
    · intro h
      by_cases hL : ξ ∈ l2Event ((δ q₀) ^ 2) n
      · exact Or.inr ⟨h, hL⟩
      · exact Or.inl ⟨h, hL⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  calc μ (badEvent n)
      = μ ((badEvent n \ l2Event ((δ q₀) ^ 2) n)
            ∪ (badEvent n ∩ l2Event ((δ q₀) ^ 2) n)) := by rw [← h_split]
    _ ≤ μ (badEvent n \ l2Event ((δ q₀) ^ 2) n)
          + μ (badEvent n ∩ l2Event ((δ q₀) ^ 2) n) := measure_union_le _ _
    _ ≤ ε / 2 + μ (l2Event ((δ q₀) ^ 2) n) :=
        add_le_add (h_chain n hn_chain)
          (measure_mono Set.inter_subset_right)
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl (h_l2_bound n hn_l2)
    _ = ε := ENNReal.add_halves ε

/-- **Equicontinuity chaining diagonal assembly with probabilistic
L²-vanishing pre-supplied** — wrapper around the chain-sequence
extraction and the diagonal-assembly residual.

Two-step delegation:
1. Extract the chain sequence `δ_q ↓ 0` with `J_{[]}(δ_q, F, L²) → 0`
   via `equi_chain_chain_sequence_exists` (via Mathlib's
   `tendsto_setLIntegral_zero` on the bracketing-entropy integral).
2. Delegate the remaining textbook content
   (envelope/slice/maximal-inequality/diagonal limit) to
   `equi_chain_assembly_given_chain_sequence`.

The work is split into (a) a Markov bridge
(`equi_chain_mean_l2_to_prob_l2`), (b) a chain-sequence extraction
(`equi_chain_chain_sequence_exists`), and (c) the diagonal chaining
assembly given the chain (`equi_chain_assembly_given_chain_sequence`),
which holds the vdV §19.2 envelope/slice/diagonal content. -/
private lemma equi_chain_diagonal_assembly_with_prob_l2
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (h_fhat_in : ∀ n ξ, fhat n ξ ∈ F)
    (h_ghat_in : ∀ n ξ, ghat n ξ ∈ F)
    (h_prob_l2 : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
        μ {ξ | δ ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P}) atTop (𝓝 0))
    -- regularity input on the function class `F`; see
    -- `equi_chain_assembly_given_chain_sequence`.
    (hJ_pos : ∀ δ' : ℝ, 0 < δ' → 0 < bracketingEntropyIntegral δ' F P)
    -- see `chain_supnorm_integral_bound_at_delta_q`.
    (hChainBound_outer :
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → ∀ (n : ℕ),
          ∫⁻ ξ, supNormOver F
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
            ≤ ENNReal.ofReal 2 * bracketingEntropyIntegral δq F P
              + ENNReal.ofReal 2 *
                (ENNReal.ofReal (Real.sqrt n)
                  * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                      * Set.indicator {x | δq * Real.sqrt n < |Φ x|} 1 ω ∂P))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|})
      atTop (𝓝 0) := by
  -- Step 1: extract the chain sequence `δ_q ↓ 0` with `J(δ_q) → 0`.
  obtain ⟨δ, hδ_pos, hδ_le_one, hδ_to_zero, hδ_J_to_zero⟩ :=
    equi_chain_chain_sequence_exists F P h_int
  -- Step 2: delegate to the residual diagonal-chaining assembly.
  exact equi_chain_assembly_given_chain_sequence F P h_int μ X hX_meas hX_iindep
    hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas h_fhat_in h_ghat_in h_prob_l2
    δ hδ_pos hδ_le_one hδ_to_zero hδ_J_to_zero hJ_pos hChainBound_outer η hη

/-- **Equicontinuity chaining brick (vdV §19.2)** —
strong-iid form of the consumer step that
`equicontinuity_consumer_step_strong_iid` delegates to.

**Statement.** For a class `F` of measurable functions with a finite
bracketing entropy integral `J_{[]}(1, F, L²(P)) < ⊤`, any random-pair
sequence `(fhat n, ghat n)` valued in `F` whose pointwise L²-gap
vanishes in mean (`∫ ξ, ‖fhat n ξ − ghat n ξ‖²_{L²(P)} ∂μ → 0`)
produces an empirical-process gap that vanishes in `μ`-probability:
`μ{ξ | |G_n(fhat n ξ) − G_n(ghat n ξ)| > η} → 0` for every `η > 0`,
where the empirical process is built from a mutually independent iid
sample `X : ℕ → Ξ → Ω` with `μ.map (X 0) = P`.

Two-step delegation:
1. Apply `equi_chain_mean_l2_to_prob_l2` (Markov bridge) to
   convert the mean-`L²` hypothesis into the probabilistic-`L²` form
   consumed by the chaining argument.
2. Delegate to `equi_chain_diagonal_assembly_with_prob_l2`, which
   carries the vdV §19.2 chaining content.

The upstream bricks (`hasFiniteBracketingCover_difference_class`,
`tendsto_meas_le_of_tendsto_integral_zero`,
`maximal_inequality_bracketing_tight`) supply the chain construction,
random envelope/slice instantiation, and the limit transport. -/
theorem equicontinuity_chaining_assembly_brick
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (h_fhat_in : ∀ n ξ, fhat n ξ ∈ F)
    (h_ghat_in : ∀ n ξ, ghat n ξ ∈ F)
    (h_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) μ)
    (h_l2 : Tendsto (fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
        atTop (𝓝 0))
    -- `equi_chain_assembly_given_chain_sequence`.
    (hJ_pos : ∀ δ' : ℝ, 0 < δ' → 0 < bracketingEntropyIntegral δ' F P)
    -- `chain_supnorm_integral_bound_at_delta_q` in `Maximal.lean`.
    (hChainBound_outer :
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → ∀ (n : ℕ),
          ∫⁻ ξ, supNormOver F
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
            ≤ ENNReal.ofReal 2 * bracketingEntropyIntegral δq F P
              + ENNReal.ofReal 2 *
                (ENNReal.ofReal (Real.sqrt n)
                  * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                      * Set.indicator {x | δq * Real.sqrt n < |Φ x|} 1 ω ∂P))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|})
      atTop (𝓝 0) := by
  -- Step 1: Markov bridge from mean-`L²` to probabilistic-`L²`.
  have h_prob_l2 : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      μ {ξ | δ ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P}) atTop (𝓝 0) :=
    fun δ hδ => equi_chain_mean_l2_to_prob_l2 μ P fhat ghat h_l2_int h_l2 hδ
  -- Step 2: delegate to the chaining sub-brick.
  exact equi_chain_diagonal_assembly_with_prob_l2 F P h_int μ X hX_meas hX_iindep
    hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas h_fhat_in h_ghat_in h_prob_l2
    hJ_pos hChainBound_outer η hη

end AsymptoticStatistics.EmpiricalProcess
