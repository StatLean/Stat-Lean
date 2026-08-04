import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
import StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal
import StatLean.AsymptoticStatistics.EmpiricalProcess.EquicontinuityChaining
import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedClass
import StatLean.AsymptoticStatistics.EmpiricalProcess.ChainingAssembly
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Donsker theorem via bracketing entropy integral

Let $\mathcal{F}$ be a class of measurable functions $f : \Omega \to \mathbb{R}$ on a
probability space $(\Omega, P)$. Define the $L_2(P)$-bracketing entropy integral
$$
J_{[\,]}(1, \mathcal{F}, L_2(P))
  = \int_0^1 \sqrt{\log N_{[\,]}\!\big(\varepsilon, \mathcal{F}, L_2(P)\big)}\; d\varepsilon,
$$
where $N_{[\,]}(\varepsilon, \mathcal{F}, L_2(P))$ is the minimal number of
$\varepsilon$-brackets in $L_2(P)$ needed to cover $\mathcal{F}$. If
$J_{[\,]}(1, \mathcal{F}, L_2(P)) < \infty$, then $\mathcal{F}$ is $P$-Donsker: the
empirical process $\{\mathbb{G}_n f : f \in \mathcal{F}\}$, with
$\mathbb{G}_n f = \sqrt{n}\,(P_n - P)f$, converges in distribution in
$\ell^\infty(\mathcal{F})$ to a tight, mean-zero Gaussian process with the
$L_2(P)$ covariance of $\mathcal{F}$.

Being $P$-Donsker is decomposed here as the conjunction of two properties: the
**marginal central limit theorem** (every finite-dimensional projection converges,
which requires $f \in L_2(P)$ for each $f \in \mathcal{F}$) and **asymptotic
equicontinuity** of the empirical process with respect to the $L_2(P)$ seminorm.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 19 (Empirical Processes), §19.2 (Donsker Theorems), Theorem 19.5.

**Proof formalization notes.**
The headline declaration is `isPDonsker_of_finite_bracketing_entropy_integral`.
The proof splits `IsPDonsker = IsMarginalCLT ∧ IsAsymptoticallyEquicontinuous`:

* **Marginal-CLT half.** From $J_{[\,]}(1, \mathcal{F}, L_2(P)) < \infty$ extract a
  single $\varepsilon$-bracket from the finite cover at a scale where the bracketing
  number is finite (`exists_finite_bracketingNumber_of_integral_lt_top`); for each
  $f \in \mathcal{F}$ find a containing bracket $[l, u]$ and bound
  $|f| \le |l| + |u|$ pointwise to deduce $f \in L_2(P)$ via `MemLp.of_le_mul`
  from `IsEpsBracket.memLp_lower`/`memLp_upper`. This half is fully closed
  (`marginalCLT_of_finite_bracketing_entropy_integral_aux`).
* **Equicontinuity half.** The textbook chaining argument (vdV §19.2) controls
  $\int^* \sup_{f \in \mathcal{F}_\delta} \mathbb{G}_n f$ via the localized form of
  the bracketing maximal inequality (Lemma 19.34). The measurable-majorant theorem
  `localizedChainBound_measurableMajorant_of_finiteEntropy` in
  `ChainingAssembly.lean` bounds `localizedDifferenceClass F P δ` by
  $K\,(J_{[\,]}(\delta, \mathcal{F}, L_2) + \sqrt{n}\cdot
  \text{envelope tail})$, with one constant uniform in the localization scale and
  sample size. Its implementation assembles the per-level finite-class estimates,
  dyadic entropy comparison, and envelope-tail correction developed in
  `Maximal.lean`. A diagonal sequence $\delta_q \downarrow 0$ drives the entropy
  term to zero, while the envelope tail vanishes at its growing truncation
  threshold; the proof then applies the ENNReal Markov bound inline to obtain the
  outer-probability modulus. The difference class $\mathcal{F}-\mathcal{F}$ inherits
  finite bracketing entropy through the localized-class development (vdV Lemma
  19.31). Mutual independence (`iIndepFun X μ`) is exposed directly because the
  per-level variance factorisation genuinely consumes it.

Positivity of $J_{[\,]}(\delta', \mathcal{F}, L_2(P))$ at positive scales is
derived internally from `F.Nonempty`: the regularized entropy integrand uses
`log (1 + N)`, so no separate `hJ_pos` hypothesis is required.

**Bibliographic comments.**
The bracketing-entropy Donsker theorem originates with M. Ossiander, "A Central
Limit Theorem Under Metric Entropy with $L_2$ Bracketing," *The Annals of
Probability* **15** (1987), no. 3, 897–919. Ossiander proved an empirical-process
central limit theorem under exactly the integrability condition
$\int_0^1 \sqrt{\log N_{[\,]}(\varepsilon, \mathcal{F}, L_2(P))}\,d\varepsilon
< \infty$ on the $L_2$-bracketing metric entropy, generalizing earlier
uniform-entropy results of Dudley (1978, 1981) and Jain–Marcus (1975); the
tightness argument combined with Andersen–Dobrić (1987) yields the CLT. The form
stated here is van der Vaart's Theorem 19.5, a textbook synthesis of Ossiander's
result.
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

/-- **Marginal-CLT half of Theorem 19.5**.

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
  refine isMarginalCLT_of_memLp ?_
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

/-- **Envelope extraction from a finite bracketing-entropy integral** (file-local).

From `J_{[]}(1, F, L²(P)) < ⊤`, extract a finite bracketing cover at some scale
`ε ∈ (0,1]` and read off the measurable, `L²`-integrable envelope
`Φ := ∑_i (|l i| + |u i|)`, which dominates every `f ∈ F` pointwise. Mirrors the
private `chaining_envelope_from_bracket` in `Maximal.lean`, re-proved here so the
C2 producer (`asymptoticallyEquicontinuous_of_finite_bracketing_entropy_integral_aux`)
is self-contained inside its owned file. -/
private theorem chaining_envelope_from_bracket'
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ Φ : Ω → ℝ, Measurable Φ ∧ IsEnvelope F Φ ∧ MemLp Φ 2 P := by
  obtain ⟨ε, _hε, hN⟩ := exists_finite_bracketingNumber_of_integral_lt_top h_int
  obtain ⟨N, l, u, hbracket, hcover⟩ :=
    bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mp hN
  refine ⟨fun x => ∑ i : Fin N, (|l i x| + |u i x|), ?_, ?_, ?_⟩
  · refine Finset.measurable_sum _ ?_
    intro i _
    have hl : Measurable fun x => |l i x| :=
      continuous_abs.measurable.comp (hbracket i).measurable_lower
    have hu : Measurable fun x => |u i x| :=
      continuous_abs.measurable.comp (hbracket i).measurable_upper
    exact hl.add hu
  · intro f hf x
    obtain ⟨i, hbi⟩ := hcover f hf
    have hli : l i x ≤ f x := (hbi x).1
    have hui : f x ≤ u i x := (hbi x).2
    have h_abs_le : |f x| ≤ |l i x| + |u i x| := by
      rcases le_or_gt 0 (f x) with hfx | hfx
      · rw [abs_of_nonneg hfx]
        have h1 : f x ≤ |u i x| := hui.trans (le_abs_self _)
        linarith [abs_nonneg (l i x)]
      · rw [abs_of_neg hfx]
        have h3 : -(l i x) ≤ |l i x| := neg_le_abs _
        linarith [abs_nonneg (u i x)]
    refine h_abs_le.trans ?_
    have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin N)), 0 ≤ |l j x| + |u j x| :=
      fun j _ => by positivity
    exact Finset.single_le_sum (f := fun j => |l j x| + |u j x|)
      h_nonneg (Finset.mem_univ i)
  · refine memLp_finset_sum _ ?_
    intro i _
    exact (MemLp.abs (hbracket i).memLp_lower).add
      (MemLp.abs (hbracket i).memLp_upper)

/-- **Chain sequence extraction** (file-local).

From `J_{[]}(1, F, L²(P)) < ⊤`, build a localization scale sequence `δ_q ↓ 0` with
`δ_q ∈ (0, 1/4]` and `J_{[]}(δ_q, F, L²(P)) → 0`. The scale `δ_q := 1/(4(q+1))`;
`J(δ_q) → 0` because `J(1)` is finite and the lintegral over the shrinking window
`Ioc 0 δ_q` vanishes (`tendsto_setLIntegral_zero`). Mirrors the private
`equi_chain_chain_sequence_exists` in `EquicontinuityChaining.lean`, re-proved here
so the C2 producer is self-contained. -/
private lemma equi_chain_chain_sequence_exists'
    {F : Set (Ω → ℝ)} {P : Measure Ω}
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ δ : ℕ → ℝ, (∀ q, 0 < δ q) ∧ (∀ q, δ q ≤ 1 / 4) ∧
      Tendsto δ atTop (𝓝 0) ∧
      Tendsto (fun q => bracketingEntropyIntegral (δ q) F P) atTop (𝓝 0) := by
  refine ⟨fun q => 1 / (4 * ((q : ℝ) + 1)), ?_, ?_, ?_, ?_⟩
  · intro q; positivity
  · intro q
    have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    have h4 : (1 : ℝ) / 4 = 1 / (4 * (0 + 1)) := by norm_num
    rw [h4]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 4 : ℝ)
    simp only [mul_zero] at h
    refine h.congr (fun q => ?_)
    rw [one_div, one_div, ← mul_inv]; norm_num
  · set g : ℝ → ℝ≥0∞ := fun ε =>
      ENat.recTopCoe (⊤ : ℝ≥0∞)
        (fun n : ℕ => ENNReal.ofReal (Real.sqrt (Real.log (1 + (n : ℝ)))))
        (bracketingNumber ε F 2 P) with hg_def
    have h_restrict_eq : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∫⁻ ε in Set.Ioc 0 δ, g ε ∂volume =
          ∫⁻ ε in Set.Ioc 0 δ, g ε
            ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      intro δ hδ_pos hδ_le_one
      rw [Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioc,
        max_self (0 : ℝ), min_eq_left hδ_le_one]
    have h_J1_finite :
        ∫⁻ ε, g ε ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ ∞ := by
      have : ∫⁻ ε, g ε ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) =
          bracketingEntropyIntegral 1 F P := rfl
      rw [this]; exact h_int.ne
    have h_meas_tendsto : Tendsto
        (fun q : ℕ => (volume.restrict (Set.Ioc (0 : ℝ) 1))
          (Set.Ioc 0 ((1 : ℝ) / (4 * ((q : ℝ) + 1))))) atTop (𝓝 0) := by
      have h_vol_eq : ∀ q : ℕ,
          (volume.restrict (Set.Ioc (0 : ℝ) 1))
              (Set.Ioc 0 ((1 : ℝ) / (4 * ((q : ℝ) + 1)))) =
            ENNReal.ofReal ((1 : ℝ) / (4 * ((q : ℝ) + 1))) := by
        intro q
        have hpos : (0 : ℝ) < 1 / (4 * ((q : ℝ) + 1)) := by positivity
        have hle : (1 : ℝ) / (4 * ((q : ℝ) + 1)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
          nlinarith
        rw [Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioc,
          max_self (0 : ℝ), min_eq_left hle,
          Real.volume_Ioc, sub_zero]
      have h_ofReal_tendsto : Tendsto
          (fun q : ℕ => ENNReal.ofReal ((1 : ℝ) / (4 * ((q : ℝ) + 1))))
          atTop (𝓝 (ENNReal.ofReal 0)) := by
        refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 4 : ℝ)
        simp only [mul_zero] at h
        refine h.congr (fun q => ?_)
        rw [one_div, one_div, ← mul_inv]; norm_num
      rw [ENNReal.ofReal_zero] at h_ofReal_tendsto
      refine h_ofReal_tendsto.congr (fun q => (h_vol_eq q).symm)
    have h_set_tendsto : Tendsto
        (fun q : ℕ => ∫⁻ ε in Set.Ioc 0 ((1 : ℝ) / (4 * ((q : ℝ) + 1))), g ε
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) atTop (𝓝 0) :=
      tendsto_setLIntegral_zero h_J1_finite h_meas_tendsto
    refine h_set_tendsto.congr (fun q => ?_)
    have hpos : (0 : ℝ) < 1 / (4 * ((q : ℝ) + 1)) := by positivity
    have hle : (1 : ℝ) / (4 * ((q : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      nlinarith
    exact (h_restrict_eq _ hpos hle).symm

/-- **Strong-iid form of the consumer step under finite
bracketing entropy**.

This has the same conclusion as `equicontinuity_consumer_step_finite_entropy`
and assumes mutual independence through `iIndepFun X μ`, as required by the
finite-class bounds at each chaining level.

The hypothesis `hChainBound_outer` supplies a universal bound for the supremum
over `localizedDifferenceClass F P δq`, including the measurable majorant used
for Markov's inequality.  The lemma passes this estimate to
`equicontinuity_chaining_assembly_brick`, which combines it with the shrinking
entropy scale, the envelope-tail limit, and the `L²(P)` consistency of the
random pair. -/
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
    -- The localized chaining bound in the measurable-majorant form supplied by
    -- `localizedChainBound_measurableMajorant_of_finiteEntropy`.
    (hChainBound_outer :
      ∃ c : ℝ, 0 < c ∧
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
          ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ),
            ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
                  (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
              ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
                + ENNReal.ofReal c *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|})
      atTop (𝓝 0) :=
  equicontinuity_chaining_assembly_brick F P h_int μ X hX_meas hX_iindep hX_id
    hX_law fhat ghat h_fhat_meas h_ghat_meas h_fhat_in h_ghat_in h_l2_int h_l2
    hChainBound_outer η hη

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
    -- The localized chaining bound in the measurable-majorant form supplied by
    -- `localizedChainBound_measurableMajorant_of_finiteEntropy`.
    (hChainBound_outer :
      ∃ c : ℝ, 0 < c ∧
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
          ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ),
            ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
                  (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
              ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
                + ENNReal.ofReal c *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|})
      atTop (𝓝 0) :=
  equicontinuity_consumer_step_strong_iid F P h_int μ X hX_meas hX_iindep
    hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas h_fhat_in h_ghat_in
    h_l2_int h_l2 hChainBound_outer η hη

/-- **Equicontinuity half of Theorem 19.5**.

Unfolds the consumer-form universal quantifiers of
`IsAsymptoticallyEquicontinuous` and `exact`-delegates to
`equicontinuity_consumer_step_finite_entropy`, which forwards to
`equicontinuity_consumer_step_strong_iid` (vdV §19.2 chaining under
mutual independence). The private difference-class cover lift in
`LocalizedClass` (vdV Lemma 19.31) and the file-local
`tendsto_meas_le_of_tendsto_integral_zero` are standalone finite-cover and
expectation-to-probability facts. The proof below instead obtains a measurable
majorant from `localizedChainBound_measurableMajorant_of_finiteEntropy` and
applies the ENNReal Markov estimate `meas_ge_le_lintegral_div` inline. -/
private lemma asymptoticallyEquicontinuous_of_finite_bracketing_entropy_integral_aux
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    IsAsymptoticallyEquicontinuous F P := by
  classical
  -- Enter the modulus: fix the sample space, the iid sample, and `ε, η`.
  intro Ξ _ μ _ X hX_meas hX_iindep hX_id hX_law ε η hε hη
  -- Every `f ∈ F` is `L²(P)` (marginal-CLT half), used for integrability of pairs.
  have hmemLp : ∀ f ∈ F, MemLp f 2 P :=
    (marginalCLT_of_finite_bracketing_entropy_integral_aux F P
      (fun f hf => (hF_meas f hf).aemeasurable) h_int).memLp
  -- The class-`F` envelope `Φ`; upgrade to the difference-class envelope `Φ₂ := 2Φ`.
  obtain ⟨Φ, hΦ_meas, hΦ_env, hΦ_L2⟩ := chaining_envelope_from_bracket' h_int
  set Φ₂ : Ω → ℝ := fun x => 2 * Φ x with hΦ₂_def
  have hΦ₂_meas : Measurable Φ₂ := measurable_const.mul hΦ_meas
  have hΦ₂_env : IsEnvelope (differenceClass F) Φ₂ := isEnvelope_differenceClass_two hΦ_env
  have hΦ₂_L2 : MemLp Φ₂ 2 P := hΦ_L2.const_mul 2
  -- The chain sequence `δq → 0` with `J(δq, F, P) → 0` (entropy-integral finiteness).
  obtain ⟨δseq, hδ_pos, hδ_le_quarter, _hδ_to_zero, hδ_J_to_zero⟩ :=
    equi_chain_chain_sequence_exists' h_int
  -- The measurable-majorant chaining bound (universal `c`).
  obtain ⟨c, hc_pos, hMaj⟩ :=
    localizedChainBound_measurableMajorant_of_finiteEntropy hF_ne hF_meas
      h_int μ X hX_meas hX_iindep hX_id hX_law
  -- `ofReal ε` is a positive, finite ℝ≥0∞ — Markov divisor.
  have hεE_pos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hεE_ne : ENNReal.ofReal ε ≠ 0 := hεE_pos.ne'
  have hεE_ne_top : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Choose the localization scale `δq := δseq q` so the bracketing-entropy term
  -- `c·J(δq)` is below `(ofReal η)·(ofReal ε)`; then `c·J(δq)/ofReal ε ≤ ofReal η`.
  have hKJ_tendsto : Tendsto
      (fun q => (ENNReal.ofReal c) * bracketingEntropyIntegral (δseq q) F P)
      atTop (𝓝 0) := by
    have h : Tendsto
        (fun q => (ENNReal.ofReal c) * bracketingEntropyIntegral (δseq q) F P)
        atTop (𝓝 (ENNReal.ofReal c * 0)) :=
      ENNReal.Tendsto.const_mul hδ_J_to_zero
        (Or.inr (ENNReal.ofReal_ne_top (r := c)))
    rwa [mul_zero] at h
  obtain ⟨q₀, hq₀⟩ := (ENNReal.tendsto_atTop_zero.mp hKJ_tendsto)
    (ENNReal.ofReal η * ENNReal.ofReal ε)
    (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hη).ne' hεE_ne)
  have hJbound : (ENNReal.ofReal c) * bracketingEntropyIntegral (δseq q₀) F P
      ≤ ENNReal.ofReal η * ENNReal.ofReal ε := hq₀ q₀ le_rfl
  set δq : ℝ := δseq q₀ with hδq_def
  have hδq_pos : 0 < δq := hδ_pos q₀
  have hδq_le : δq ≤ 1 / 4 := hδ_le_quarter q₀
  -- Engine at scale `δq`: uniform clamp `M` + per-`n` measurable majorant `Maj n`.
  obtain ⟨M, hM_pos, hMajn⟩ := hMaj Φ₂ hΦ₂_meas hΦ₂_env hΦ₂_L2 hδq_pos hδq_le
  refine ⟨δq, hδq_pos, ?_⟩
  -- Abbreviate the localized class and the close-pair modulus event.
  set G := localizedDifferenceClass F P δq with hG_def
  set Bev : ℕ → Set Ξ := fun n =>
    {ξ | ∃ s t : ↥F, distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δq ∧
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|}
    with hBev_def
  -- The RHS bound at each `n`, as an ℝ≥0∞ sequence.
  set Tail : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.sqrt n)
      * ∫⁻ ω, ENNReal.ofReal (|Φ₂ ω|)
          * Set.indicator {x | Real.sqrt n * M < |Φ₂ x|} 1 ω ∂P with hTail_def
  set RHS : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal c * bracketingEntropyIntegral δq F P + ENNReal.ofReal c * Tail n
    with hRHS_def
  -- STEP 3+4: for each `n`, `μ* (Bev n) ≤ RHS n / ofReal ε`.
  have hkey : ∀ n, μ.outerMeasureStar (Bev n) ≤ RHS n / ENNReal.ofReal ε := by
    intro n
    obtain ⟨Maj, hMaj_meas, hMaj_dom, hMaj_int⟩ := hMajn n
    -- The close-pair event lands in the measurable superlevel set `{ofReal ε ≤ Maj}`.
    have hsub : Bev n ⊆ {ξ | ENNReal.ofReal ε ≤ Maj ξ} := by
      rintro ξ ⟨s, t, hclose, hosc⟩
      -- `s − t ∈ localizedDifferenceClass F P δq`.
      have hs_mem : MemLp (s : Ω → ℝ) 2 P := hmemLp s s.2
      have ht_mem : MemLp (t : Ω → ℝ) 2 P := hmemLp t t.2
      have hst_mem : MemLp (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P := hs_mem.sub ht_mem
      have hne_top : eLpNorm (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P ≠ ⊤ :=
        hst_mem.eLpNorm_lt_top.ne
      have hradius : eLpNorm (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P
          ≤ ENNReal.ofReal δq := by
        have htoReal_lt : (eLpNorm (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P).toReal
            < δq := hclose
        calc eLpNorm (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P
            = ENNReal.ofReal
                (eLpNorm (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) 2 P).toReal := by
              rw [ENNReal.ofReal_toReal hne_top]
          _ ≤ ENNReal.ofReal δq := ENNReal.ofReal_le_ofReal htoReal_lt.le
      have hst_in : (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x) ∈ G :=
        mem_localizedDifferenceClass s.2 t.2 hradius
      -- `ofReal ε ≤ ofReal |G_n(s−t)| ≤ supNormOver G (G_n) ≤ Maj ξ`.
      have hlin : empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x)
          = empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ) :=
        empiricalProcess_sub P n _ _ _ (hs_mem.integrable one_le_two)
          (ht_mem.integrable one_le_two)
      have hosc' : ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x)| := by rw [hlin]; exact hosc
      have hle_g : ENNReal.ofReal ε ≤ supNormOver G
          (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) := by
        calc ENNReal.ofReal ε
            ≤ ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x)| :=
              ENNReal.ofReal_le_ofReal hosc'.le
          _ ≤ supNormOver G
                (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) :=
              le_supNormOver hst_in
      exact le_trans hle_g (hMaj_dom ξ)
    -- Outer-measure monotone + measurable superlevel collapses to genuine measure.
    have hms : MeasurableSet {ξ | ENNReal.ofReal ε ≤ Maj ξ} :=
      measurableSet_le measurable_const hMaj_meas
    calc μ.outerMeasureStar (Bev n)
        ≤ μ.outerMeasureStar {ξ | ENNReal.ofReal ε ≤ Maj ξ} :=
          outerMeasureStar_mono μ hsub
      _ = μ {ξ | ENNReal.ofReal ε ≤ Maj ξ} := outerMeasureStar_eq_measure hms
      _ ≤ (∫⁻ ξ, Maj ξ ∂μ) / ENNReal.ofReal ε :=
          meas_ge_le_lintegral_div hMaj_meas.aemeasurable hεE_ne hεE_ne_top
      _ ≤ RHS n / ENNReal.ofReal ε := by
          apply ENNReal.div_le_div_right
          rw [hRHS_def, hTail_def]; exact hMaj_int
  -- STEP 5: `limsupₙ (μ* (Bev n)) ≤ limsupₙ (RHS n / ofReal ε) ≤ ofReal η`.
  have hRHS_div : (fun n => RHS n / ENNReal.ofReal ε)
      = fun n => (ENNReal.ofReal c * bracketingEntropyIntegral δq F P) / ENNReal.ofReal ε
          + (ENNReal.ofReal c * Tail n) / ENNReal.ofReal ε := by
    funext n; rw [hRHS_def, ENNReal.add_div]
  -- The constant term is `≤ ofReal η`.
  have hconst_le : (ENNReal.ofReal c * bracketingEntropyIntegral δq F P)
        / ENNReal.ofReal ε ≤ ENNReal.ofReal η := by
    rw [ENNReal.div_le_iff hεE_ne hεE_ne_top]
    exact hJbound
  -- The `√n·tail` term → 0 (DCT on the `L²` envelope).
  have hTail_tendsto : Tendsto Tail atTop (𝓝 0) := by
    have h_tendsto := tendsto_envelope_tail_const_threshold P hΦ₂_meas hΦ₂_L2 hM_pos
    have h_set_eq : ∀ n : ℕ,
        (fun ω => ENNReal.ofReal (|Φ₂ ω|)
            * Set.indicator {x | M * Real.sqrt n < |Φ₂ x|} 1 ω)
        = (fun ω => ENNReal.ofReal (|Φ₂ ω|)
            * Set.indicator {x | Real.sqrt n * M < |Φ₂ x|} 1 ω) := by
      intro n; simp_rw [mul_comm M (Real.sqrt n)]
    refine (h_tendsto.congr (fun n => ?_))
    rw [hTail_def]; rw [h_set_eq n]
  have hVf_tendsto : Tendsto (fun n => (ENNReal.ofReal c * Tail n) / ENNReal.ofReal ε)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ENNReal.ofReal c * Tail n) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul hTail_tendsto
        (Or.inr (ENNReal.ofReal_ne_top (r := c)))
      rwa [mul_zero] at h
    have h2 : Tendsto (fun n => (ENNReal.ofReal c * Tail n) / ENNReal.ofReal ε)
        atTop (𝓝 (0 / ENNReal.ofReal ε)) :=
      ENNReal.Tendsto.div_const h1 (Or.inr hεE_ne)
    rwa [ENNReal.zero_div] at h2
  -- Combine: `limsup (const + Vf) ≤ const` since `Vf → 0`.
  have hRHSdiv_limsup : limsup (fun n => RHS n / ENNReal.ofReal ε) atTop
      ≤ ENNReal.ofReal η := by
    rw [hRHS_div]
    refine le_trans (limsup_add_tendsto_zero_le
      (fun _ => (ENNReal.ofReal c * bracketingEntropyIntegral δq F P) / ENNReal.ofReal ε)
      (fun n => (ENNReal.ofReal c * Tail n) / ENNReal.ofReal ε) _ ?_ hVf_tendsto) hconst_le
    exact le_of_eq (limsup_const _)
  refine le_trans (limsup_le_limsup (Eventually.of_forall hkey)
    isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)) hRHSdiv_limsup

/-- **Auxiliary for Theorem 19.5**: combines the marginal-CLT
half (`marginalCLT_of_finite_bracketing_entropy_integral_aux`) with the
equicontinuity half
(`asymptoticallyEquicontinuous_of_finite_bracketing_entropy_integral_aux`)
into the `IsPDonsker` conjunction. The marginal-CLT conjunct follows
via bracket extraction + `MemLp.of_le_mul`; the equicontinuity conjunct
delegates via `exact` to a sub-lemma carrying the textbook chaining
content. -/
private lemma isPDonsker_of_finite_bracketing_entropy_integral_aux
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    IsPDonsker F P :=
  ⟨marginalCLT_of_finite_bracketing_entropy_integral_aux F P
     (fun f hf => (hF_meas f hf).aemeasurable) h_int,
   asymptoticallyEquicontinuous_of_finite_bracketing_entropy_integral_aux F P
     hF_ne hF_meas h_int⟩

/-- **Theorem 19.5 (Donsker via bracketing entropy integral)**.

Every class `F` of measurable functions with `J_{[]}(1, F, L_2(P)) < ⊤`
is `P`-Donsker.

vdV §19.2 Theorem 19.5.

The marginal-CLT half extracts a finite bracket cover at one positive scale and
uses its `L²(P)` endpoints to prove `MemLp f 2 P` for every `f ∈ F`.  For the
equicontinuity half, close pairs determine elements of
`localizedDifferenceClass F P δq`.  The measurable-majorant form of
`localizedChainBound_of_finiteEntropy` bounds the corresponding localized
supremum by the shrinking entropy integral and an envelope tail.
`equicontinuity_chaining_assembly_brick` then applies Markov's inequality and
the envelope-tail limit to obtain the outer-probability modulus.

On the `L²`-good event, the random difference lies in
`localizedDifferenceClass F P δq`, so the integrand is bounded by the localized
class supremum. The corresponding bound follows from
`localizedChainBound_of_finiteEntropy` (vdV Lemma 19.34).

The positivity `0 < J(δ')` is derived from `F.Nonempty`
because the entropy integrand is `√(log (1 + N_{[]}(ε, F, L²(P))))` — the `1 +`
regularizer makes a nonempty class (`N ≥ 1`) have integrand `≥ √(log 2) > 0`
pointwise, hence `J(δ') > 0` for every `δ' > 0`
(`bracketingEntropyIntegral_pos_of_nonempty`).  The localized chaining bound
derives `0 < J(δq)` internally from `hF_ne`, so no separate positivity
hypothesis is required.

Both halves (marginal CLT + asymptotic equicontinuity) are genuinely sound; the
headline carries vdV Theorem 19.5's assumptions: `hF_ne` (F nonempty — F = ∅ is
vacuously Donsker), `hF_meas` (measurability, vdV Thm 19.5 p.270), and `h_int`
(finite bracketing entropy integral `J_{[]}(1, F, L²(P)) < ⊤`). -/
theorem isPDonsker_of_finite_bracketing_entropy_integral
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    IsPDonsker F P :=
  isPDonsker_of_finite_bracketing_entropy_integral_aux F P
    hF_ne hF_meas h_int

end AsymptoticStatistics.EmpiricalProcess
