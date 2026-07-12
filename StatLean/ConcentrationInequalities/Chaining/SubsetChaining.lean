import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal
import StatLean.ConcentrationInequalities.Chaining.PsiTwoMaximal
import StatLean.ConcentrationInequalities.Chaining.DyadicNets

/-!
# Residual bounds for chaining a finite subset through nets of the carrier

The faithful infinite-`T` chaining statements (HDP Theorems 8.1.3/8.1.4/8.5.2
read through Remark 7.2.1: $\mathbb{E}\sup_{t \in T} X_t$ *is* the supremum
over finite subsets $F \subseteq T$ of $\mathbb{E}\max_{t \in F} X_t$) chain
each finite $F$ through $\varepsilon$-nets **of the full carrier $T$**. For
infinite $T$ the walk cannot stop at a finest net identifying with $T$ (the
finite-$T$ device `exists_fine_scale`); instead the chain is truncated at an
arbitrary level and the **residual** $\max_{t\in F}(X_t - X_{\pi t})$ — a
maximum of $|F|$ variables that are $\psi_2$-small of scale $K\varepsilon$ —
is bounded and sent to $0$ as $\varepsilon \to 0$ with $F$ fixed. This file
provides the three residual bounds (mean-zero expectation, absolute
expectation, tail), one per consuming assembly.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Remark 7.2.1 (the finite-subset reading of
E sup) and §8.1 (the chaining set-up whose truncation these residuals
close); the p. 227 footnote ("the general case typically follows by
approximation") is exactly this approximation.

**Proof formalization notes.** Each lemma is a direct application of the
Batch-10 finite maximal inequalities to the family
`fun t => X t ω − X (netProj N t) ω` indexed by the finite subset `F`: the
mean-zero form via the B2 bridge (`SubGaussianIncrements.isSubGaussian_sub`,
proxy `3(K·nndist)² ≤ 3(K·ε)²`) + `expectation_max_finset_le`
(bound `√3·Kε·√(2 log |F|)`); the absolute form via `expectation_abs_max_le`
(bound `2·Kε·√(log(2|F|))`); the tail via `tail_abs_max_le`
(bound `2|F|·exp(−δ²/(Kε)²)`). All three vanish as `ε → 0` for fixed finite
`F`, which is the only limit the faithful assemblies need. Named-sorry
fallback of this work item: `residual_tail_le` (the two expectation forms
land first).

**Bibliographic comments.** The truncation-and-limit reading of the chaining
argument for non-finite index sets is folklore, implicit in R. M. Dudley,
"The sizes of compact subsets of Hilbert space and continuity of Gaussian
processes," *J. Funct. Anal.* 1 (1967), 290–330, and standard in
M. Talagrand, *Upper and Lower Bounds for Stochastic Processes*, Springer,
2014, §2.2 (where processes are handled through their finite-dimensional
marginals throughout).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- Net projections of carrier points stay in the carrier. -/
lemma netProj_mem_of_subset {N : Finset E} {T : Set E}
    -- LEAN-ONLY: the net lives inside the carrier
    (hNsub : ↑N ⊆ T)
    -- LEAN-ONLY: nonemptiness so `netProj` picks a genuine net point
    (hNne : N.Nonempty) (t : E) :
    netProj N t ∈ T :=
  hNsub (Finset.mem_coe.mpr (netProj_mem hNne t))

/-- **Mean-zero chaining residual** (HDP §8.1 truncation; Remark 7.2.1
approximation): for a finite subset `F` of the carrier and an `ε`-net `N` of
the carrier, the expected maximum of the truncation residuals is at most
`√3 · Kε · √(2 log |F|)` — vanishing as `ε → 0` for fixed `F`. -/
theorem residual_expectation_le
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ] {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    {N : Finset E}
    -- LEAN-ONLY: the net lives inside the carrier (internal covering)
    (hNsub : ↑N ⊆ T)
    -- LEAN-ONLY: nonemptiness of the net
    (hNne : N.Nonempty)
    {ε : ℝ}
    -- LEAN-ONLY: nonnegative net radius
    (hε : 0 ≤ ε)
    -- LEAN-ONLY: `N` is an ε-net of the carrier
    (hprox : ∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε)
    {F : Finset E}
    -- LEAN-ONLY: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ∫ ω, F.sup' hFne (fun t => X t ω - X (netProj N t) ω) ∂μ
      ≤ Real.sqrt 3 * ((K : ℝ) * ε) * Real.sqrt (2 * Real.log (F.card : ℝ)) := by
  sorry

/-- **Absolute chaining residual** (HDP §8.1 truncation, no mean-zero): the
expected maximum of `|X_t − X_{π t}|` over a finite subset is at most
`2 · Kε · √(log(2|F|))`. -/
theorem residual_abs_expectation_le
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ] {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    {N : Finset E}
    -- LEAN-ONLY: the net lives inside the carrier
    (hNsub : ↑N ⊆ T)
    -- LEAN-ONLY: nonemptiness of the net
    (hNne : N.Nonempty)
    {ε : ℝ}
    -- LEAN-ONLY: positive net radius (the ψ₂ scale `Kε` must be positive
    -- for the maximal engine; the assemblies' dyadic radii are positive)
    (hε : 0 < ε)
    -- LEAN-ONLY: nondegenerate increment constant (K = 0 is handled by the
    -- degenerate branches of the assemblies)
    (hK : 0 < K)
    -- LEAN-ONLY: `N` is an ε-net of the carrier
    (hprox : ∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε)
    {F : Finset E}
    -- LEAN-ONLY: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ∫ ω, F.sup' hFne (fun t => |X t ω - X (netProj N t) ω|) ∂μ
      ≤ 2 * ((K : ℝ) * ε) * Real.sqrt (Real.log (2 * (F.card : ℝ))) := by
  sorry

/-- **Chaining residual, tail form** (HDP §8.1 / Remark 8.1.6 truncation):
the maximum truncation residual over a finite subset exceeds `δ ≥ 0` with
probability at most `2|F| · exp(−δ²/(Kε)²)` — vanishing as `ε → 0` for fixed
`F` and `δ > 0`, which is the δ-slack the faithful tail assembly sends to
zero by continuity from below. -/
theorem residual_tail_le
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ] {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    {N : Finset E}
    -- LEAN-ONLY: the net lives inside the carrier
    (hNsub : ↑N ⊆ T)
    -- LEAN-ONLY: nonemptiness of the net
    (hNne : N.Nonempty)
    {ε : ℝ}
    -- LEAN-ONLY: positive net radius (ψ₂ scale positivity)
    (hε : 0 < ε)
    -- LEAN-ONLY: nondegenerate increment constant
    (hK : 0 < K)
    -- LEAN-ONLY: `N` is an ε-net of the carrier
    (hprox : ∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε)
    {F : Finset E}
    -- LEAN-ONLY: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty)
    {δ : ℝ}
    -- LEAN-ONLY: nonnegative threshold
    (hδ : 0 ≤ δ) :
    μ {ω | δ < F.sup' hFne (fun t => |X t ω - X (netProj N t) ω|)}
      ≤ ENNReal.ofReal
          (2 * (F.card : ℝ) * Real.exp (-δ ^ 2 / ((K : ℝ) * ε) ^ 2)) := by
  sorry

end StatLean.ConcentrationInequalities
