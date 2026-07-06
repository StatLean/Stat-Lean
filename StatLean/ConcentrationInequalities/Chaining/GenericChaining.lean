import StatLean.ConcentrationInequalities.Chaining.GammaTwo
import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
import StatLean.ConcentrationInequalities.Chaining.TailToExpectation
import StatLean.ConcentrationInequalities.Chaining.DyadicNets
import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Generic chaining (Talagrand's γ₂ bound)

For a mean-zero process $(X_t)_{t \in T}$ with sub-Gaussian increments
(Eq. 8.1) on a metric space $(T, d)$,
$$ \mathbb{E} \sup_{t \in T} X_t \;\le\; C K \,\gamma_2(T, d), $$
where $\gamma_2$ is the Talagrand functional over admissible sequences
(Definition 8.5.1, `Chaining/GammaTwo.lean`).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.5.2, Theorem 8.5.2 (proof Steps 1–3,
Eqs. (8.48)–(8.50)); Remark 8.5.3 for the mean-zero-free $|X_t - X_{t_0}|$
form.

**Proof formalization notes.** Finite-`T` core per the batch sup policy
(book WLOG, p. 247 Step 1). The high-probability form
(`generic_chaining_tail`) carries per-level thresholds
$2^{k/2}(\sqrt{2\log 2} + 1) + u$ over the admissible-sequence levels and a
union bound over $|T_k|\cdot|T_{k-1}| \le 2^{2^{k+1}}$ chain pairs; the
expectation forms integrate it via
`Chaining/TailToExpectation.lean`. **Frozen constants** (formula + numeral):
tail threshold factor `(12 + 4u)` (from $\sum_k 2^{k/2}\,2^{-k/2}$-style
geometric bookkeeping at the designed thresholds); expectation constant
`20` (book's absolute `C`; formula $6 + 2\sqrt{\pi} \le 10$). Per batch
reconciliation R4, the mean-zero assemblies carry the LEAN-ONLY hypothesis
`hint : ∀ t ∈ T, Integrable (X t) μ` ruling out Bochner-junk means (the
per-pair increment means are then genuine). Work-item single named-sorry
fallback: `generic_chaining_tail` (the per-level event bookkeeping); the
integration and `iInf` steps to Theorem 8.5.2 must close against it.

**Bibliographic comments.** Generic chaining and the majorizing-measure
theory are due to X. Fernique (1975) and M. Talagrand ("Regularity of
Gaussian processes," *Acta Math.* 159 (1987), 99–149; *Upper and Lower
Bounds for Stochastic Processes*, Springer 2014). The admissible-sequence
formulation follows Talagrand via HDP §8.5; the matching lower bound
(majorizing measure theorem, HDP Theorem 8.5.5) is out of Batch-10 scope.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- A.e.-measurability of a finite (hence countable) `biSup` of
a.e.-measurable functions. -/
private lemma aemeasurable_biSup_of_finite {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {E : Type*} {T : Set E} (hfin : T.Finite) {g : E → Ω → ℝ}
    (hg : ∀ t ∈ T, AEMeasurable (g t) μ) :
    AEMeasurable (fun ω => ⨆ t ∈ T, g t ω) μ :=
  AEMeasurable.biSup T hfin.countable hg

/-- A single value is dominated by the finite `biSup` (via `Finset.sup'`). -/
private lemma le_biSup_of_finite {E : Type*} {T : Set E} (hfin : T.Finite)
    (g : E → ℝ) {t : E} (ht : t ∈ T) : g t ≤ ⨆ s ∈ T, g s := by
  have hFne : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]; exact ⟨t, ht⟩
  have setToF : (⨆ s ∈ hfin.toFinset, g s) = ⨆ s ∈ T, g s :=
    iSup_congr fun s => by rw [hfin.mem_toFinset]
  rw [← setToF, biSup_finset_eq_sup' hFne]
  exact Finset.le_sup' g (hfin.mem_toFinset.mpr ht)

/-- A uniform bound on the values dominates the finite `biSup` (via
`Finset.sup'`). -/
private lemma biSup_le_of_finite {E : Type*} {T : Set E} (hfin : T.Finite)
    (hne : T.Nonempty) (g : E → ℝ) {c : ℝ} (h : ∀ s ∈ T, g s ≤ c) :
    ⨆ s ∈ T, g s ≤ c := by
  have hFne : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]; exact hne
  have setToF : (⨆ s ∈ hfin.toFinset, g s) = ⨆ s ∈ T, g s :=
    iSup_congr fun s => by rw [hfin.mem_toFinset]
  rw [← setToF, biSup_finset_eq_sup' hFne]
  exact Finset.sup'_le hFne g (fun s hs => h s (hfin.mem_toFinset.mp hs))

/-- **Generic chaining, high-probability form** (HDP §8.5.2, Theorem 8.5.2
proof Steps 2–3, Eqs. (8.48)–(8.50)): for any admissible sequence `A`, the
sup of increments exceeds `(12 + 4u)·K·γ(A)` with probability at most
`2 exp(−u²)`. This work item's single named-sorry fallback. -/
theorem generic_chaining_tail {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure; bridge-B1 tail machinery requires it
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (book WLOG p.247 Step 1; sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index so the sup is genuine
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the process; regularity
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point of the increment sup; Remark 8.5.3 device
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    -- LEAN-ONLY: finite functional (⊤ makes the event's threshold junk 0)
    (hA : gammaFunctional A ≠ ⊤)
    {u : ℝ}
    -- USER-INPUT: deviation parameter u ≥ 0; HDP Eq (8.50)
    (hu : 0 ≤ u) :
    μ {ω | (12 + 4 * u) * K * (gammaFunctional A).toReal <
        ⨆ t ∈ T, |X t ω - X t₀ ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by sorry

/-- Generic chaining, expectation form at a fixed admissible sequence (HDP
§8.5.2 + Remark 8.5.3 — no mean-zero for the `|X_t − X_{t₀}|` form).
Frozen constant `20` (formula `6 + 2√π ≤ 10`), integrating
`generic_chaining_tail` via `TailToExpectation`. -/
theorem generic_chaining_of_admissible {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T) :
    ENNReal.ofReal (∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ) ≤
      20 * K * gammaFunctional A := by
  -- Measurability and nonnegativity of the increment sup.
  have hZm : AEMeasurable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ :=
    aemeasurable_biSup_of_finite hfin (g := fun t ω => |X t ω - X t₀ ω|)
      (fun t ht => ((hmeas t ht).sub (hmeas t₀ ht₀)).abs)
  have hZ0 : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω| := by
    filter_upwards with ω
    exact Real.iSup_nonneg (fun t => Real.iSup_nonneg (fun _ => abs_nonneg _))
  by_cases hK0 : K = 0
  · -- K = 0: all increments vanish a.e., so the sup is a.e. 0.
    subst hK0
    have hz : ∀ᵐ ω ∂μ, ∀ t ∈ T, X t ω - X t₀ ω = 0 := by
      rw [ae_ball_iff hfin.countable]
      intro t ht
      have hnorm : subGaussianNorm (fun ω => X t ω - X t₀ ω) μ = 0 := by
        have h := hinc t₀ ht₀ t ht
        simp only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at h
        exact h
      exact ae_eq_zero_of_subGaussianNorm_eq_zero ((hmeas t ht).sub (hmeas t₀ ht₀)) hnorm
    have hZae : (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) =ᵐ[μ] 0 := by
      filter_upwards [hz] with ω hω
      have hup : (⨆ t ∈ T, |X t ω - X t₀ ω|) ≤ 0 :=
        biSup_le_of_finite hfin hne _ (fun s hs => by rw [hω s hs]; simp)
      have hlo : (0 : ℝ) ≤ ⨆ t ∈ T, |X t ω - X t₀ ω| :=
        Real.iSup_nonneg (fun t => Real.iSup_nonneg (fun _ => abs_nonneg _))
      simp only [Pi.zero_apply]
      linarith
    rw [integral_congr_ae hZae]
    simp
  · by_cases hγ : gammaFunctional A = ⊤
    · rw [hγ, ENNReal.mul_top (mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr hK0))]
      exact le_top
    · -- Main case: integrate the tail bound via `TailToExpectation`.
      have ha0 : (0 : ℝ) ≤ 6 * (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg (mul_nonneg (by norm_num) K.coe_nonneg) ENNReal.toReal_nonneg
      have hb0 : (0 : ℝ) ≤ 2 * (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg (mul_nonneg (by norm_num) K.coe_nonneg) ENNReal.toReal_nonneg
      have htail : ∀ u : ℝ, 0 ≤ u →
          μ {ω | 6 * (K : ℝ) * (gammaFunctional A).toReal
                + 2 * (K : ℝ) * (gammaFunctional A).toReal * u
              < ⨆ t ∈ T, |X t ω - X t₀ ω|}
            ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
        intro u hu
        have hval := generic_chaining_tail hfin hne hmeas hinc ht₀ A hγ hu
        have hthr : 6 * (K : ℝ) * (gammaFunctional A).toReal
              + 2 * (K : ℝ) * (gammaFunctional A).toReal * u
            = (12 + 4 * u) * (K : ℝ) * (gammaFunctional A).toReal := by ring
        have hset : {ω | 6 * (K : ℝ) * (gammaFunctional A).toReal
                + 2 * (K : ℝ) * (gammaFunctional A).toReal * u
              < ⨆ t ∈ T, |X t ω - X t₀ ω|}
            = {ω | (12 + 4 * u) * (K : ℝ) * (gammaFunctional A).toReal
              < ⨆ t ∈ T, |X t ω - X t₀ ω|} := by
          ext ω; simp only [Set.mem_setOf_eq, hthr]
        rw [hset]; exact hval
      have hInt : ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
          ≤ 6 * (K : ℝ) * (gammaFunctional A).toReal
            + Real.sqrt Real.pi * (2 * (K : ℝ) * (gammaFunctional A).toReal) :=
        integral_le_of_tail_le hZm hZ0 ha0 hb0 htail
      have hc : (0 : ℝ) ≤ (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg K.coe_nonneg ENNReal.toReal_nonneg
      have hsqrt : Real.sqrt Real.pi ≤ 2 := by
        nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_lt_d2]
      have hmid : 6 * (K : ℝ) * (gammaFunctional A).toReal
          + Real.sqrt Real.pi * (2 * (K : ℝ) * (gammaFunctional A).toReal)
          ≤ 20 * (K : ℝ) * (gammaFunctional A).toReal := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) hc, hc, hsqrt]
      have hfinal : ENNReal.ofReal (20 * (K : ℝ) * (gammaFunctional A).toReal)
          = 20 * ↑K * gammaFunctional A := by
        rw [show (10 : ℝ) * (K : ℝ) * (gammaFunctional A).toReal
              = 10 * ((K : ℝ) * (gammaFunctional A).toReal) from by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10),
            ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_toReal hγ, ENNReal.ofReal_ofNat]
        ring
      calc ENNReal.ofReal (∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ)
          ≤ ENNReal.ofReal (6 * (K : ℝ) * (gammaFunctional A).toReal
              + Real.sqrt Real.pi * (2 * (K : ℝ) * (gammaFunctional A).toReal)) :=
            ENNReal.ofReal_le_ofReal hInt
        _ ≤ ENNReal.ofReal (20 * (K : ℝ) * (gammaFunctional A).toReal) :=
            ENNReal.ofReal_le_ofReal hmid
        _ = 20 * ↑K * gammaFunctional A := hfinal

/-- **Theorem 8.5.2 (generic chaining bound)** (HDP §8.5.2; book's absolute
constant frozen `C = 10`): mean-zero process with sub-Gaussian increments
has `E sup X ≤ 10·K·γ₂(T,d)`, in `ofReal` form. -/
theorem generic_chaining {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (book WLOG; sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: integrability of the process, ruling out Bochner-junk
    -- means (batch reconciliation R4; the book's E X_t = 0 presupposes it)
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero process; HDP Thm 8.5.2
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ) :
    ENNReal.ofReal (∫ ω, ⨆ t ∈ T, X t ω ∂μ) ≤ 20 * K * gammaTwo T := by
  -- Anchor at a point of `T` (Remark 8.5.3 device).
  set t₀ := hne.some with ht₀def
  have ht₀ : t₀ ∈ T := hne.some_mem
  -- Measurability of the two increment sups.
  have hWm : AEMeasurable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ :=
    aemeasurable_biSup_of_finite hfin (g := fun t ω => |X t ω - X t₀ ω|)
      (fun t ht => ((hmeas t ht).sub (hmeas t₀ ht₀)).abs)
  have hSXm : AEMeasurable (fun ω => ⨆ t ∈ T, X t ω) μ :=
    aemeasurable_biSup_of_finite hfin (g := fun t ω => X t ω) (fun t ht => hmeas t ht)
  -- Integrability of the increment sup via domination by a finite sum.
  have hSumInt : Integrable (fun ω => ∑ t ∈ hfin.toFinset, |X t ω - X t₀ ω|) μ :=
    integrable_finset_sum _
      (fun t ht => ((hint t (hfin.mem_toFinset.mp ht)).sub (hint t₀ ht₀)).abs)
  have hWint : Integrable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ := by
    refine Integrable.mono' hSumInt hWm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.iSup_nonneg (fun t => Real.iSup_nonneg (fun _ => abs_nonneg _)))]
    exact biSup_le_of_finite hfin ⟨t₀, ht₀⟩ _
      (fun s hs => Finset.single_le_sum (f := fun t => |X t ω - X t₀ ω|)
        (fun i _ => abs_nonneg _) (hfin.mem_toFinset.mpr hs))
  -- Integrability of the process sup, sandwiched by `X t₀` and `X t₀ + sup |·|`.
  have hSXint : Integrable (fun ω => ⨆ t ∈ T, X t ω) μ := by
    refine Integrable.mono' ((hint t₀ ht₀).norm.add hWint) hSXm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    have hlo : X t₀ ω ≤ ⨆ t ∈ T, X t ω := le_biSup_of_finite hfin (fun t => X t ω) ht₀
    have hhi : ⨆ t ∈ T, X t ω ≤ X t₀ ω + ⨆ t ∈ T, |X t ω - X t₀ ω| := by
      refine biSup_le_of_finite hfin ⟨t₀, ht₀⟩ _ (fun s hs => ?_)
      have h1 : |X s ω - X t₀ ω| ≤ ⨆ t ∈ T, |X t ω - X t₀ ω| :=
        le_biSup_of_finite hfin (fun r => |X r ω - X t₀ ω|) hs
      have h2 := le_abs_self (X s ω - X t₀ ω)
      linarith
    have hW0 : (0 : ℝ) ≤ ⨆ t ∈ T, |X t ω - X t₀ ω| :=
      Real.iSup_nonneg (fun t => Real.iSup_nonneg (fun _ => abs_nonneg _))
    simp only [Real.norm_eq_abs, Pi.add_apply, abs_le]
    refine ⟨?_, ?_⟩
    · nlinarith [hlo, neg_abs_le (X t₀ ω), hW0]
    · nlinarith [hhi, le_abs_self (X t₀ ω), hW0]
  -- E sup X ≤ E sup |X − X t₀| (mean-zero anchor cancels).
  have hred : ∫ ω, ⨆ t ∈ T, X t ω ∂μ ≤ ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ := by
    have hbound : ∫ ω, ⨆ t ∈ T, X t ω ∂μ
        ≤ ∫ ω, (X t₀ ω + ⨆ t ∈ T, |X t ω - X t₀ ω|) ∂μ := by
      refine integral_mono hSXint ((hint t₀ ht₀).add hWint) (fun ω => ?_)
      refine biSup_le_of_finite hfin ⟨t₀, ht₀⟩ _ (fun s hs => ?_)
      have h1 : |X s ω - X t₀ ω| ≤ ⨆ t ∈ T, |X t ω - X t₀ ω| :=
        le_biSup_of_finite hfin (fun r => |X r ω - X t₀ ω|) hs
      have h2 := le_abs_self (X s ω - X t₀ ω)
      linarith
    rwa [integral_add (hint t₀ ht₀) hWint, hmean t₀ ht₀, zero_add] at hbound
  refine le_trans (ENNReal.ofReal_le_ofReal hred) ?_
  haveI : Nonempty (AdmissibleSequence T) := nonempty_admissibleSequence hne
  have ha_top : (10 : ℝ≥0∞) * ↑K ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  have hpush : (10 : ℝ≥0∞) * ↑K * gammaTwo T
      = ⨅ A : AdmissibleSequence T, 20 * ↑K * gammaFunctional A := by
    rw [show gammaTwo T = ⨅ A : AdmissibleSequence T, gammaFunctional A from rfl]
    exact ENNReal.mul_iInf (fun h => absurd h ha_top)
  rw [hpush]
  exact le_iInf (fun A => generic_chaining_of_admissible hfin hne hmeas hinc ht₀ A)

/-- Theorem 8.5.2, real display (LEAN-ONLY: via `gammaTwo_lt_top_of_finite`
the `ℝ≥0∞` bound descends to `ℝ`). -/
theorem generic_chaining_real {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: integrability (R4, as above)
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero process; HDP Thm 8.5.2
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ) :
    ∫ ω, ⨆ t ∈ T, X t ω ∂μ ≤ 20 * K * (gammaTwo T).toReal := by
  have h3 := generic_chaining hfin hne hmeas hint hmean hinc
  have htop : (10 : ℝ≥0∞) * ↑K * gammaTwo T ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
      (gammaTwo_lt_top_of_finite hfin hne).ne
  rw [ENNReal.ofReal_le_iff_le_toReal htop, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.coe_toReal] at h3
  exact h3

end StatLean.ConcentrationInequalities
