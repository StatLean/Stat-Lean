import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
import StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal
import StatLean.AsymptoticStatistics.EmpiricalProcess.EquicontinuityChaining
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Theorem 19.5: Donsker via bracketing entropy integral

Every class `F` of measurable functions with `J_{[]}(1, F, L_2(P)) < ∞` is
`P`-Donsker. The proof splits `IsPDonsker = IsMarginalCLT ∧
IsAsymptoticallyEquicontinuous`: the marginal-CLT half is provable from
Mathlib's iid CLT; the equicontinuity half black-boxes Lemma 19.34
(`maximal_inequality_bracketing`).

vdV §19.2 Theorem 19.5.

Headline declaration: `isPDonsker_of_finite_bracketing_entropy_integral`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Bracket-extraction step for the marginal-CLT half of Theorem 19.5**.

If the bracketing entropy integral `J_{[]}(1, F, L²(P))` is finite, then
there exists at least one scale `ε ∈ (0, 1]` at which the bracketing
number is finite (and hence `F` admits a finite ε-bracketing cover at
that scale).

**Proof.** Contrapositive: if `bracketingNumber ε F 2 P = ⊤` for every
`ε ∈ (0, 1]`, then the integrand of `bracketingEntropyIntegral` is
identically `⊤` on `(0, 1]`, so the lintegral equals `⊤ · volume((0,1])
= ⊤ · 1 = ⊤`, contradicting the finiteness hypothesis. -/
private lemma exists_finite_bracketingNumber_of_integral_lt_top
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) 1 ∧ bracketingNumber ε F 2 P < ⊤ := by
  by_contra h_no
  push Not at h_no
  have h_int_top : bracketingEntropyIntegral 1 F P = ⊤ := by
    unfold bracketingEntropyIntegral
    rw [setLIntegral_congr_fun (μ := volume) (s := Set.Ioc (0:ℝ) 1)
        (g := fun _ => (⊤ : ℝ≥0∞)) measurableSet_Ioc (by
          intro ε hε
          have h_top : bracketingNumber ε F 2 P = ⊤ := top_unique (h_no ε hε)
          simp [h_top])]
    rw [setLIntegral_const, Real.volume_Ioc]
    simp
  rw [h_int_top] at h_int
  exact (lt_irrefl _ h_int).elim

/-- **Auxiliary closed: marginal-CLT half of Theorem 19.5**.

From the finiteness of `J_{[]}(1, F, L²(P))` we extract a finite
ε-bracketing cover at some scale `ε ∈ (0, 1]`, find a bracket
`[l, u]` containing each `f ∈ F`, and bound `|f x| ≤ |l x| + |u x|`
pointwise to deduce `MemLp f 2 P` from `MemLp (l) 2 P` and
`MemLp (u) 2 P` via `MemLp.of_le_mul`. -/
private lemma marginalCLT_of_finite_bracketing_entropy_integral_aux
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_meas : ∀ f ∈ F, AEMeasurable f P)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    IsMarginalCLT F P := by
  intro f hf
  obtain ⟨ε, _hε, hN⟩ := exists_finite_bracketingNumber_of_integral_lt_top h_int
  obtain ⟨k, l, u, hbr, hcov⟩ := bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mp hN
  obtain ⟨i, hi⟩ := hcov f hf
  have hl_mem : MemLp (l i) 2 P := (hbr i).memLp_lower
  have hu_mem : MemLp (u i) 2 P := (hbr i).memLp_upper
  have h_f_strong : AEStronglyMeasurable f P := (h_meas f hf).aestronglyMeasurable
  refine MemLp.of_le_mul (c := 1) (hl_mem.abs.add hu_mem.abs) h_f_strong ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have h_nn : 0 ≤ |l i x| + |u i x| := by positivity
  change ‖f x‖ ≤ 1 * ‖|l i x| + |u i x|‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_nn, one_mul]
  obtain ⟨h1, h2⟩ := hi x
  rcases le_or_gt 0 (f x) with hf_pos | hf_neg
  · calc |f x|
        = f x := abs_of_nonneg hf_pos
      _ ≤ u i x := h2
      _ ≤ |u i x| := le_abs_self _
      _ ≤ |l i x| + |u i x| := by linarith [abs_nonneg (l i x)]
  · calc |f x|
        = -f x := abs_of_neg hf_neg
      _ ≤ -l i x := by linarith
      _ ≤ |l i x| := neg_le_abs _
      _ ≤ |l i x| + |u i x| := by linarith [abs_nonneg (u i x)]

/-- **vdV Lemma 19.31: bracketing of the difference class**.

If `F` has a finite `(η/2)`-bracketing cover in `L²(P)`, then the
**difference class** `F - F := {f - g : f, g ∈ F}` has a finite
`η`-bracketing cover in `L²(P)`.

The textbook construction (vdV §19.5): for each pair `(i, j)`
of brackets `[l_i, u_i]`, `[l_j, u_j]` from the `(η/2)`-cover of `F`,
the pair `[l_i - u_j, u_i - l_j]` brackets `f - g` whenever `f ∈ [l_i,
u_i]` and `g ∈ [l_j, u_j]`. Its L² size is
`‖(u_i - l_j) - (l_i - u_j)‖_2 = ‖(u_i - l_i) + (u_j - l_j)‖_2 ≤
η/2 + η/2 = η`. -/
private lemma hasFiniteBracketingCover_difference_class
    {F : Set (Ω → ℝ)} {P : Measure Ω}
    {η : ℝ} (hη : 0 < η)
    (hF : HasFiniteBracketingCover F (η / 2) 2 P) :
    HasFiniteBracketingCover
      {h : Ω → ℝ | ∃ f g, f ∈ F ∧ g ∈ F ∧ h = fun x => f x - g x} η 2 P := by
  -- vdV Lemma 19.31. Pair the `(η/2)`-brackets of `F` into `η`-brackets of
  -- `F - F` via `[l_i - u_j, u_i - l_j]`, indexed by `Fin (k * k)` through
  -- `finProdFinEquiv`. Algebra: `(u_i - l_j) - (l_i - u_j) =
  -- (u_i - l_i) + (u_j - l_j)`; triangle in L² gives the η bound.
  obtain ⟨k, l, u, hbr, hcov⟩ := hF
  have hη2 : (0 : ℝ) ≤ η / 2 := by linarith
  refine ⟨k * k,
    fun ij x => l (finProdFinEquiv.symm ij).1 x - u (finProdFinEquiv.symm ij).2 x,
    fun ij x => u (finProdFinEquiv.symm ij).1 x - l (finProdFinEquiv.symm ij).2 x,
    ?_, ?_⟩
  · -- each pair `[l i - u j, u i - l j]` is an η-bracket in L²(P)
    intro ij
    set p := finProdFinEquiv.symm ij
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      have h1 := (hbr p.1).isBracket x
      have h2 := (hbr p.2).isBracket x
      linarith
    · exact (hbr p.1).measurable_lower.sub (hbr p.2).measurable_upper
    · exact (hbr p.1).measurable_upper.sub (hbr p.2).measurable_lower
    · exact (hbr p.1).memLp_lower.sub (hbr p.2).memLp_upper
    · exact (hbr p.1).memLp_upper.sub (hbr p.2).memLp_lower
    · -- size bound: triangle + the two (η/2)-bracket bounds
      have hexpand :
          (fun x => (u p.1 x - l p.2 x) - (l p.1 x - u p.2 x)) =
          (fun x => (u p.1 x - l p.1 x) + (u p.2 x - l p.2 x)) := by
        funext x; ring
      rw [hexpand]
      have hmeas1 : AEStronglyMeasurable (fun x => u p.1 x - l p.1 x) P :=
        ((hbr p.1).memLp_upper.sub (hbr p.1).memLp_lower).aestronglyMeasurable
      have hmeas2 : AEStronglyMeasurable (fun x => u p.2 x - l p.2 x) P :=
        ((hbr p.2).memLp_upper.sub (hbr p.2).memLp_lower).aestronglyMeasurable
      have htri : eLpNorm (fun x => (u p.1 x - l p.1 x) + (u p.2 x - l p.2 x)) 2 P ≤
          eLpNorm (fun x => u p.1 x - l p.1 x) 2 P +
            eLpNorm (fun x => u p.2 x - l p.2 x) 2 P :=
        eLpNorm_add_le hmeas1 hmeas2 one_le_two
      have hi : eLpNorm (fun x => u p.1 x - l p.1 x) 2 P < ENNReal.ofReal (η / 2) :=
        (hbr p.1).size_lt
      have hj : eLpNorm (fun x => u p.2 x - l p.2 x) 2 P < ENNReal.ofReal (η / 2) :=
        (hbr p.2).size_lt
      have hsum :
          ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add hη2 hη2]
        congr 1; ring
      calc eLpNorm (fun x => (u p.1 x - l p.1 x) + (u p.2 x - l p.2 x)) 2 P
          ≤ eLpNorm (fun x => u p.1 x - l p.1 x) 2 P +
              eLpNorm (fun x => u p.2 x - l p.2 x) 2 P := htri
        _ < ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := ENNReal.add_lt_add hi hj
        _ = ENNReal.ofReal η := hsum
  · -- cover: every `h = f - g` lies in some bracket `[l i - u j, u i - l j]`
    rintro h ⟨f, g, hf, hg, h_eq⟩
    obtain ⟨i, hfi⟩ := hcov f hf
    obtain ⟨j, hgj⟩ := hcov g hg
    refine ⟨finProdFinEquiv (i, j), fun x => ?_⟩
    simp only [Equiv.symm_apply_apply, h_eq]
    refine ⟨?_, ?_⟩
    · have h1 := (hfi x).1
      have h2 := (hgj x).2
      linarith
    · have h1 := (hfi x).2
      have h2 := (hgj x).1
      linarith

/-- **Markov: L¹-integral convergence implies probability concentration**.

Given a sequence `ψ n : Ξ → ℝ≥0∞` of nonnegative measurable functions
with `∫⁻ ψ n dμ → 0`, then for every `ε > 0`,
`μ {ξ | ε ≤ ψ n ξ} → 0`.

This is the **random-pair bridge step** in the equicontinuity proof:
the consumer-form L²-vanishing hypothesis `∫ ξ, ‖fhat n ξ − ghat n
ξ‖²_{L²(P)} ∂μ → 0` is converted, by this lemma applied to
`ψ n ξ = ENNReal.ofReal (‖fhat n ξ − ghat n ξ‖²_{L²(P)})`, into the
probability bound `μ{ξ | δ² ≤ ‖fhat − ghat‖²_{L²(P)}} → 0`: exactly
the "L²-consistency in probability" form that controls the bad-set
of the random pair.

The proof goes via `meas_ge_le_lintegral_div` (Markov in ENNReal form)
and the squeeze `0 ≤ μ{·} ≤ ε⁻¹ · ∫⁻ ψ → 0`. -/
private lemma tendsto_meas_le_of_tendsto_integral_zero
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (ψ : ℕ → Ξ → ℝ≥0∞) (hψ_meas : ∀ n, Measurable (ψ n))
    (h_int : Tendsto (fun n => ∫⁻ ξ, ψ n ξ ∂μ) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) (hε_top : ε < ⊤) :
    Tendsto (fun n => μ {ξ | ε ≤ ψ n ξ}) atTop (𝓝 0) := by
  -- Markov in ENNReal form: `μ{ξ | ε ≤ ψ n ξ} ≤ (∫⁻ ψ n dμ) / ε`.
  -- The upper bound tends to `0 / ε = 0`; squeeze.
  have hε_ne : ε ≠ 0 := hε.ne'
  have hε_top_ne : ε ≠ ⊤ := hε_top.ne
  have h_markov : ∀ n, μ {ξ | ε ≤ ψ n ξ} ≤ (∫⁻ ξ, ψ n ξ ∂μ) / ε :=
    fun n => meas_ge_le_lintegral_div (hψ_meas n).aemeasurable hε_ne hε_top_ne
  have h_div : Tendsto (fun n => (∫⁻ ξ, ψ n ξ ∂μ) / ε) atTop (𝓝 (0 / ε)) :=
    ENNReal.Tendsto.div_const h_int (Or.inr hε_ne)
  rw [ENNReal.zero_div] at h_div
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_div
    (Eventually.of_forall fun _ => zero_le _) (Eventually.of_forall h_markov)

/-- **Strong-iid form of the consumer step under finite
bracketing entropy**.

Same conclusion as
`equicontinuity_consumer_step_finite_entropy` (vdV §19.2 chaining),
but with **mutual** independence (`iIndepFun X μ`) replacing
the pairwise hypothesis exposed by the predicate
`IsAsymptoticallyEquicontinuous`. The textbook chaining argument
genuinely consumes mutual independence (for the per-level
`finite_sup_bound` invocation inside `maximal_inequality_bracketing_tight`,
which factorises the empirical-process variance into a sum of
per-summand variances), so this is the form into which the body of
`equicontinuity_consumer_step_finite_entropy` lifts.

**Proof structure (vdV §19.2).**
1. Pick `δ ↓ 0` along a sequence `δ_q ↓ 0` with
   `J_{[]}(δ_q, F − F, L²) → 0`.
2. By `hasFiniteBracketingCover_difference_class`, the
   difference class `F − F` inherits finite bracketing-entropy at every
   scale; choose envelope `Φ` from the level-1 bracket cover (concretely
   `Φ = max_i (|l i| + |u i|)` from a finite cover at scale 1).
3. Apply `maximal_inequality_bracketing_tight` to the
   difference slice `F_δ := {f − g ∈ F − F : ‖f − g‖_{L²} ≤ δ_q}`,
   giving universal `K`:
     `∫⁻ supNormOver F_δ (G_n) ∂μ ≤ K · (J_{[]}(δ_q, F − F, L²) +
       √n · envelope_tail)`.
4. Markov (`tendsto_meas_le_of_tendsto_integral_zero`) converts the
   lintegral bound to a probability bound on
   `μ{ξ | η < supNormOver F_δ (G_n)(ω(ξ))}`.
5. The L²-consistency hypothesis combined with Markov pushes the event
   `‖fhat n − ghat n‖_{L²(P)} > δ_q` to μ-measure 0; on its complement
   `(fhat n ξ − ghat n ξ) ∈ F_{δ_q}`, so the deviation is controlled by
   step 4.
6. Diagonal `δ_q ↓ 0` drives the maximal-inequality bound to 0.

The full vdV §19.2 chaining assembly (chain construction, envelope
extraction from the level-1 bracket cover, Markov + diagonal-sequence
limit) is held by `equicontinuity_chaining_assembly_brick` in
`AsymptoticStatistics.EmpiricalProcess.EquicontinuityChaining`, which
this body delegates to via `exact`. -/
private lemma equicontinuity_consumer_step_strong_iid
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
    -- `EquicontinuityChaining.equi_chain_assembly_given_chain_sequence`.
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
      atTop (𝓝 0) :=
  equicontinuity_chaining_assembly_brick F P h_int μ X hX_meas hX_iindep hX_id
    hX_law fhat ghat h_fhat_meas h_ghat_meas h_fhat_in h_ghat_in h_l2_int h_l2
    hJ_pos hChainBound_outer η hη

/-- **Consumer-form Tendsto assembly under finite bracketing entropy**.

The full vdV §19.2 chaining argument, in the consumer
form that `IsAsymptoticallyEquicontinuous` directly exposes. With the
predicate exposing `iIndepFun X μ` directly, it `exact`s into
`equicontinuity_consumer_step_strong_iid`, which carries the genuine
vdV chaining content.

`IsAsymptoticallyEquicontinuous` (`Donsker.lean`) takes `iIndepFun`
directly, which standard iid call sites (e.g. via `Measure.infinitePi`
+ `iIndepFun_infinitePi`) supply natively. -/
private lemma equicontinuity_consumer_step_finite_entropy
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
    -- `EquicontinuityChaining.equi_chain_assembly_given_chain_sequence`.
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
      atTop (𝓝 0) :=
  equicontinuity_consumer_step_strong_iid F P h_int μ X hX_meas hX_iindep
    hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas h_fhat_in h_ghat_in
    h_l2_int h_l2 hJ_pos hChainBound_outer η hη

/-- **Equicontinuity half of Theorem 19.5**.

Unfolds the consumer-form universal quantifiers of
`IsAsymptoticallyEquicontinuous` and `exact`-delegates to
`equicontinuity_consumer_step_finite_entropy`, which forwards to
`equicontinuity_consumer_step_strong_iid` (vdV §19.2 chaining under
mutual independence). Two further upstream textbook bricks are named
above (`hasFiniteBracketingCover_difference_class` = vdV Lemma 19.31;
`tendsto_meas_le_of_tendsto_integral_zero` = Markov bridge from
L²-vanishing to probability concentration). -/
private lemma asymptoticallyEquicontinuous_of_finite_bracketing_entropy_integral_aux
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    -- `EquicontinuityChaining.equi_chain_assembly_given_chain_sequence`.
    (hJ_pos : ∀ δ' : ℝ, 0 < δ' → 0 < bracketingEntropyIntegral δ' F P)
    -- universal over the sample space Ξ since `IsAsymptoticallyEquicontinuous`
    -- itself quantifies over Ξ, μ, X.
    (hChainBound_outer :
      ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (X : ℕ → Ξ → Ω),
        ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
          ∀ {δq : ℝ}, 0 < δq → ∀ (n : ℕ),
            ∫⁻ ξ, supNormOver F
                  (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
              ≤ ENNReal.ofReal 2 * bracketingEntropyIntegral δq F P
                + ENNReal.ofReal 2 *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | δq * Real.sqrt n < |Φ x|} 1 ω ∂P)) :
    IsAsymptoticallyEquicontinuous F P := by
  intro Ξ _inst μ _inst2 X hX_meas hX_iindep hX_id hX_law
        fhat ghat h_fhat_meas h_ghat_meas h_fhat_in h_ghat_in h_l2_int h_l2 η hη
  exact equicontinuity_consumer_step_finite_entropy F P h_int μ X
    hX_meas hX_iindep hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas
    h_fhat_in h_ghat_in h_l2_int h_l2 hJ_pos (hChainBound_outer μ X) η hη

/-- **Auxiliary for Theorem 19.5**: combines the marginal-CLT
half (`marginalCLT_of_finite_bracketing_entropy_integral_aux`) with the
equicontinuity half
(`asymptoticallyEquicontinuous_of_finite_bracketing_entropy_integral_aux`)
into the `IsPDonsker` conjunction. The marginal-CLT conjunct is closed
via bracket extraction + `MemLp.of_le_mul`; the equicontinuity conjunct
delegates via `exact` to a sub-lemma carrying the textbook chaining
content. -/
private lemma isPDonsker_of_finite_bracketing_entropy_integral_aux
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_meas : ∀ f ∈ F, AEMeasurable f P)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    -- `EquicontinuityChaining.equi_chain_assembly_given_chain_sequence`.
    (hJ_pos : ∀ δ' : ℝ, 0 < δ' → 0 < bracketingEntropyIntegral δ' F P)
    -- `chain_supnorm_integral_bound_at_delta_q` in `Maximal.lean`.
    (hChainBound_outer :
      ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (X : ℕ → Ξ → Ω),
        ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
          ∀ {δq : ℝ}, 0 < δq → ∀ (n : ℕ),
            ∫⁻ ξ, supNormOver F
                  (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
              ≤ ENNReal.ofReal 2 * bracketingEntropyIntegral δq F P
                + ENNReal.ofReal 2 *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | δq * Real.sqrt n < |Φ x|} 1 ω ∂P)) :
    IsPDonsker F P :=
  ⟨marginalCLT_of_finite_bracketing_entropy_integral_aux F P h_meas h_int,
   asymptoticallyEquicontinuous_of_finite_bracketing_entropy_integral_aux F P h_int hJ_pos
     hChainBound_outer⟩

/-- **Theorem 19.5 (Donsker via bracketing entropy integral)**.

Every class `F` of measurable functions with `J_{[]}(1, F, L_2(P)) < ⊤`
is `P`-Donsker.

vdV §19.2 Theorem 19.5.

**Proof outline** (vdV §19.2):
1. Split `IsPDonsker = IsMarginalCLT ∧ IsAsymptoticallyEquicontinuous`.
2. **Marginal CLT half**: extract any single ε-bracket from the finite
   cover at a scale where `bracketingNumber < ⊤` (available because
   `J_{[]}(1, F, L²(P)) < ⊤`); for `f ∈ F` find a containing bracket
   `[l, u]` with `|f| ≤ |l| + (u − l)`; apply
   `IsEpsBracket.memLp_lower`/`memLp_upper` to conclude `MemLp f 2 P`.
3. **Equicontinuity half**: invokes `maximal_inequality_bracketing`.
   For each `δ`, the Lemma 19.34 bound gives
   `∫⁻ μ supNormOver F (G_n) ≤ K · (1 + J + envelope_tail)`. Take
   `n → ∞` (envelope tail vanishes after truncating at threshold
   `δ √n`; absorb `K = 2nδ + 2` cushion once `n, δ` are fixed).
   Markov converts the lintegral bound to a probability bound on
   `μ {ξ | η < |G_n(fhat) - G_n(ghat)|}`.

The marginal-CLT half is closed
(`marginalCLT_of_finite_bracketing_entropy_integral_aux`) via bracket
extraction (`exists_finite_bracketingNumber_of_integral_lt_top`) and
`MemLp.of_le_mul`. The asymptotic-equicontinuity half
(`asymptoticallyEquicontinuous_of_finite_bracketing_entropy_integral_aux`
→ `equicontinuity_consumer_step_finite_entropy` →
`equicontinuity_consumer_step_strong_iid`) delegates the genuine vdV
§19.2 chaining content to `equicontinuity_chaining_assembly_brick` in
`EquicontinuityChaining.lean`. -/
theorem isPDonsker_of_finite_bracketing_entropy_integral
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_meas : ∀ f ∈ F, AEMeasurable f P)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    -- Positivity of the bracketing-entropy integral at every scale `δ' > 0`
    -- on the class. The degenerate case (`F` is L²-trivial at scale δ) is
    -- statistically vacuous; a downstream J = 0-branch short-circuit will
    -- absorb it without requiring this regularity.
    (hJ_pos : ∀ δ' : ℝ, 0 < δ' → 0 < bracketingEntropyIntegral δ' F P)
    -- `chain_supnorm_integral_bound_at_delta_q` in `Maximal.lean`.
    (hChainBound_outer :
      ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
        (X : ℕ → Ξ → Ω),
        ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
          ∀ {δq : ℝ}, 0 < δq → ∀ (n : ℕ),
            ∫⁻ ξ, supNormOver F
                  (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
              ≤ ENNReal.ofReal 2 * bracketingEntropyIntegral δq F P
                + ENNReal.ofReal 2 *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | δq * Real.sqrt n < |Φ x|} 1 ω ∂P)) :
    IsPDonsker F P :=
  isPDonsker_of_finite_bracketing_entropy_integral_aux F P h_meas h_int hJ_pos
    hChainBound_outer

end AsymptoticStatistics.EmpiricalProcess
