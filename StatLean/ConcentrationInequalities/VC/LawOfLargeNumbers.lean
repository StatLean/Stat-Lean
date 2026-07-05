import StatLean.ConcentrationInequalities.VC.CoveringByVC
import StatLean.ConcentrationInequalities.VC.EntropyIntegral
import StatLean.ConcentrationInequalities.Symmetrization.Rademacher
import StatLean.ConcentrationInequalities.Symmetrization.Empirical
import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
import StatLean.ConcentrationInequalities.Chaining.DudleyConsumers

/-!
# VC law of large numbers (Theorem 8.3.15) — finite-class core

For an i.i.d. sample $X_1, \dots, X_n \sim \mu$ and a finite class
$\mathcal{F}$ of measurable sets with $\mathrm{vc}(\mathcal{F}) \le d$
($d \ge 1$),
$$ \mathbb{E}\,\max_{S \in \mathcal{F}}
   \bigl|\mu_n(S) - \mu(S)\bigr|
   \;\le\; 5400\,\sqrt{\frac{d}{n}}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.6, Theorem 8.3.15 (the book's unnamed
absolute constant `C`).

**Proof formalization notes.** This is the ONLY VC file touching other
Batch-10 clusters; all contact is confined to the adapter lemmas here.
Pipeline: (1) `symmetrization_adapter` cites the symmetrization cluster's
Exercise 8.11 (`empirical_symmetrization`, instantiated at `ι := ↥F` via
`Set.indicator`, `Fin n ↔ ℕ` by precomposition, and
`∫ 𝟙_S dμ = μ.real S` via `integral_indicator_one_real`) — factor `2`.
(2) Per fixed sample `x`, the Rademacher linear process `Z_v(e) = ⟨e, v⟩`
on the symmetrized empirical projection
`T' := empProj x '' F ∪ (−(empProj x '' F)) ⊆ closedBall 0 1` has
sub-Gaussian increments with `K = √6` (`subGaussianIncrements_inner_signVec`:
coordinate Rademachers via `iIndepFun_eval_signVec`, each `e i · c` bounded
in `[−|c|, |c|]` so `HasSubgaussianMGF` with proxy `c²` via
`hasSubgaussianMGF_of_mem_Icc`, summed by
`HasSubgaussianMGF.sum_of_iIndepFun` to proxy `‖v − w‖²`, then bridged to
`subGaussianNorm ≤ √6 · dist` by the orlicz bridge B3
`subGaussianNorm_le_of_isSubGaussian`). (3) The chaining cluster's
`dudley_inequality_abs` (frozen constant `40`) with the SAMPLE-INDEPENDENT
entropy bound `N(T', ε) ≤ (4/ε)^{22d}` from `coveringNumber_empProj_le` —
valid pointwise in the sample because Theorem 8.3.13 holds for *every*
probability measure, in particular the random empirical measure; the
unconditioning is `integral_mono` against a constant plus Fubini
(`MeasureTheory.integral_integral_swap` / `Measure.prod`). (4) The entropy
integral `≤ 27√d` is `entropyIntegral_le` (`VC/EntropyIntegral.lean`).

**Constants (frozen numerals, recomputed from the batch's frozen
interfaces — DEVIATION from the design's provisional 500/1000).**
Conditional Rademacher step: `40 · √6 · 27 = 1080·√6 ≈ 2645.5 ≤ 2700`
(frozen `2700` in `rademacher_process_expectation_le`). Headline:
`2 × 2700 = 5400` (frozen `5400` in `vc_lln_finset`; formula
`2 (symmetrization, Ex 8.11) × 40 (dudley_inequality_abs) × √6 (B3 bridge)
× 27 (entropy integral) = 2160·√6 ≈ 5290.9 ≤ 5400`). Downstream consumers
scale linearly: `5400/√n` (Glivenko–Cantelli), `2·5400 = 10800`
(generalization). Named-sorry fallback of this work item:
`rademacher_process_expectation_le` (the conditional Dudley glue over the
three cross-cluster stubs); `symmetrization_adapter` and the Fubini
assembly must close.

**Bibliographic comments.** The uniform LLN over VC classes is the
Vapnik–Chervonenkis theorem (*Theory Probab. Appl.* 16 (1971), 264–280);
the `√(d/n)` rate through Dudley's entropy integral and Haussler-type
covering bounds follows R. M. Dudley (*Ann. Probab.* 6 (1978), 899–929)
and D. Haussler (*J. Combin. Theory Ser. A* 69 (1995), 217–232), as
presented in HDP §8.3.6 and its Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `∫ 𝟙_S dμ = μ.real S` in the `(fun _ => (1 : ℝ))` indicator form used by
`empFrac` (LEAN-ONLY adapter for instantiating Exercise 8.11 at indicator
classes; no book content). -/
lemma integral_indicator_one_real {μ : Measure Ω} {S : Set Ω}
    -- LEAN-ONLY: measurability so the indicator integral evaluates.
    (hS : MeasurableSet S) :
    ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real S := by
  sorry

/-- `Finset.sup'` equals the subtype-indexed `ciSup` (LEAN-ONLY adapter
between the sup policy's finite core and Exercise 8.11's `⨆ k : ι` shape;
no book content). -/
lemma finset_sup'_eq_iSup_subtype {α : Type*} {F : Finset α}
    (hFne : F.Nonempty) (f : α → ℝ) :
    F.sup' hFne f = ⨆ k : {S // S ∈ F}, f (k : α) := by
  sorry

/-- **The Rademacher linear process has sub-Gaussian increments** (R6 named
lemma; HDP §8.3.6, Theorem 8.3.15 proof step): on any index set
`T ⊆ ℝⁿ`, the process `Z_v(e) = ∑ᵢ eᵢ vᵢ` under the Rademacher sign vector
`signVec n` satisfies `‖Z_v − Z_w‖_{ψ₂} ≤ √6 · dist v w` — coordinate
independence (`iIndepFun_eval_signVec`) + bounded-increment MGF
(`hasSubgaussianMGF_of_mem_Icc`, `HasSubgaussianMGF.sum_of_iIndepFun`,
proxy `‖v − w‖²`) + the orlicz bridge B3
(`subGaussianNorm_le_of_isSubGaussian`, factor `√6`). -/
lemma subGaussianIncrements_inner_signVec {n : ℕ}
    (T : Set (EuclideanSpace ℝ (Fin n))) :
    SubGaussianIncrements
      (fun (v : EuclideanSpace ℝ (Fin n)) (e : Fin n → ℝ) => ∑ i, e i * v i)
      (NNReal.sqrt 6) T (signVec n) := by
  sorry

/-- **Conditional Rademacher complexity bound** (HDP §8.3.6, Theorem 8.3.15
conditional step): for a fixed sample `x`, the expected Rademacher supremum
over a finite class of VC dimension `≤ d` is at most `2700·√d/√n`.
Frozen numeral: `40 (dudley_inequality_abs) × √6 (B3) × 27 (entropy
integral) = 1080·√6 ≈ 2645.5 ≤ 2700` — DEVIATION from the design's
provisional `500`, recomputed from the batch's frozen constants. Applied
over `T' = empProj x '' F ∪ (−(empProj x '' F))` with the
sample-independent entropy bound `N(T', ε) ≤ (4/ε)^{22d}` from
`coveringNumber_empProj_le`. -/
lemma rademacher_process_expectation_le {n : ℕ} [NeZero n] (x : Fin n → Ω)
    (F : Finset (Set Ω)) (hFne : F.Nonempty)
    -- LEAN-ONLY: measurability of the class members; needed for the
    -- empirical-measure covering bound, no scope change.
    (hFmeas : ∀ S ∈ F, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.6, Theorem 8.3.15.
    (hd : vcDim (↑F : Set (Set Ω)) ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.6 (regime of Theorem 8.3.13).
    (hd1 : 1 ≤ d) :
    ∫ e, F.sup' hFne (fun S =>
        |(n : ℝ)⁻¹ * ∑ i : Fin n, e i * S.indicator (fun _ => (1 : ℝ)) (x i)|)
      ∂(signVec n)
      ≤ 2700 * Real.sqrt d / Real.sqrt n := by
  sorry

/-- **Symmetrization adapter** (HDP §8.3.6 via Exercise 8.11): the expected
uniform deviation is at most twice the expected Rademacher supremum, jointly
over sample and signs. Cites the symmetrization cluster's
`empirical_symmetrization` instantiated at `ι := ↥F` (indicators, bounded
by 1), `Fin n` by precomposition, and `integral_indicator_one_real`; this
adapter isolates any statement-shape mismatch. -/
lemma symmetrization_adapter {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; regularity, no scope
    -- change.
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent; HDP §8.3.6,
    -- Theorem 8.3.15.
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP §8.3.6 (map form;
    -- `ProbabilityTheory.HasLaw` not used per batch interface).
    (hlaw : ∀ i, P.map (X i) = μ)
    (F : Finset (Set Ω)) (hFne : F.Nonempty)
    -- LEAN-ONLY: measurability of the class members; Exercise 8.11 input.
    (hFmeas : ∀ S ∈ F, MeasurableSet S)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.3.6 (implicit).
    (hn : 1 ≤ n) :
    ∫ ξ, F.sup' hFne (fun S =>
        |empFrac (fun i : Fin n => X i ξ) S - μ.real S|) ∂P
      ≤ 2 * ∫ p, F.sup' hFne (fun S =>
          |(n : ℝ)⁻¹ * ∑ i : Fin n,
            p.2 i * S.indicator (fun _ => (1 : ℝ)) (X i p.1)|)
        ∂(P.prod (signVec n)) := by
  sorry

/-- **VC law of large numbers, finite core** (HDP §8.3.6, Theorem 8.3.15):
`E max_{S ∈ F} |μ_n(S) − μ(S)| ≤ 5400·√d/√n` for a finite class of VC
dimension `≤ d`. Frozen numeral: `2 (symmetrization) × 40
(dudley_inequality_abs) × √6 (B3) × 27 (entropy integral) = 2160·√6
≈ 5290.9 ≤ 5400` — DEVIATION from the design's provisional `1000`,
recomputed from the batch's frozen constants. Proof: symmetrize
(`symmetrization_adapter`) → Fubini → conditional Dudley with
sample-independent RHS (`rademacher_process_expectation_le`). -/
theorem vc_lln_finset {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; regularity, no scope
    -- change.
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent; HDP §8.3.6,
    -- Theorem 8.3.15.
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP §8.3.6 (map form).
    (hlaw : ∀ i, P.map (X i) = μ)
    (F : Finset (Set Ω)) (hFne : F.Nonempty)
    -- LEAN-ONLY: measurability of the class members (implicit in the book's
    -- Boolean functions on a probability space).
    (hFmeas : ∀ S ∈ F, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.6, Theorem 8.3.15.
    (hd : vcDim (↑F : Set (Set Ω)) ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.6.
    (hd1 : 1 ≤ d)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.3.6 (implicit).
    (hn : 1 ≤ n) :
    ∫ ξ, F.sup' hFne (fun S =>
        |empFrac (fun i : Fin n => X i ξ) S - μ.real S|) ∂P
      ≤ 5400 * Real.sqrt d / Real.sqrt n := by
  sorry

end StatLean.ConcentrationInequalities
