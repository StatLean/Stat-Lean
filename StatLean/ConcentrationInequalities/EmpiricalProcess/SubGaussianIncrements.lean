import StatLean.ConcentrationInequalities.EmpiricalProcess.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Bounded
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.Orlicz.Defs
import StatLean.ConcentrationInequalities.Orlicz.TailToNorm
import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval

/-!
# Sub-Gaussian increments of the empirical process — Theorem 8.2.3, Step 1

For i.i.d. data $X_1, \dots, X_n \sim P$ and bounded $f, g$ with
$\|f - g\|_\infty \le \delta$, the empirical-process increment is mean-zero
and sub-Gaussian with variance proxy **exactly** $\delta^2 / n$:
$$ \mathbb{E}\, X_f = 0, \qquad
   \mathbb{E}\exp\bigl(\lambda (X_f - X_g)\bigr)
   \le \exp\Bigl(\frac{\lambda^2 \delta^2}{2n}\Bigr), $$
whence the $\psi_2$-norm increment bound
$\|X_f - X_g\|_{\psi_2} \le \sqrt{6}\,\|f - g\|_\infty / \sqrt{n}$, i.e. the
sub-Gaussian-increments hypothesis of Dudley's inequality (HDP Definition
8.1.1) over the index space $C([0,1], \mathbb{R})$ with the sup metric.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2, proof of Theorem 8.2.3, Step 1 (and §8.1,
Definition 8.1.1 for the increment condition).

**Proof formalization notes.** The MGF-level route is strictly better than
the book's Step 1 (Proposition 2.7.1 + centering Lemma 2.7.8, which lose
absolute constants): per summand, $(f-g)(X_i) \in [c - \delta, c + \delta]$
gives the Hoeffding proxy $((b-a)/2)^2 = \delta^2$
(`hasSubgaussianMGF_of_mem_Icc`), `HasSubgaussianMGF.sum_of_iIndepFun` gives
$n\delta^2$, and scaling by $n^{-1}$ (`isSubGaussian_const_mul`) gives
$\delta^2/n$ — **no constant loss**. The only constant enters at the
$\psi_2$-conversion: the Orlicz bridge `subGaussianNorm_le_of_isSubGaussian`
(B3) with its frozen carrier $\sqrt{6\sigma^2}$, giving explicit $\sqrt{6}$
factors (no alias constants). The common law is encoded by the map
hypothesis `μ.map (X i) = P` (`ProbabilityTheory.HasLaw` is absent at pin);
independence by the pin's `iIndepFun X μ`. Edge behavior: non-integrable `f`
never arises (all lemmas assume explicit sup bounds, hence integrability
under the probability `P` is derived in proofs, not exported). The
`SubGaussianIncrements` package is stated with `T = Set.univ` over all of
`C(unitInterval, ℝ)` and is restricted downstream via
`SubGaussianIncrements.mono_set`. Named-sorry fallback of the work item
`hdp-emp-increments`: `subGaussianNorm_empiricalProcess_sub_le_dist` (the
MGF-level core and the `δ`-form must close for real).

**Bibliographic comments.** The bounded-difference MGF bound is
W. Hoeffding, "Probability inequalities for sums of bounded random
variables," *J. Amer. Statist. Assoc.* 58 (1963), 13–30; the sub-Gaussian
increment condition for processes is R. M. Dudley, *J. Funct. Anal.* 1
(1967), 290–330; see HDP §8 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {μ : Measure Ω} {P : Measure Ω'} {n : ℕ} {X : Fin n → Ω → Ω'}

/-- Integrability transfers along a law identity (LEAN-ONLY change-of-variables;
`ProbabilityTheory.HasLaw` is absent at pin, so the law is the map equation). -/
theorem integrable_comp_of_map_eq {Y : Ω → Ω'} {f : Ω' → ℝ}
    -- LEAN-ONLY: a.e.-measurability of the data map; regularity, no book content
    (hY : AEMeasurable Y μ)
    -- USER-INPUT: Y has law P; HDP §8.2 ("points X_i drawn from P")
    (hlaw : μ.map Y = P)
    -- LEAN-ONLY: integrability under the population law; derived from boundedness at call sites
    (hf_int : Integrable f P) :
    Integrable (fun ω => f (Y ω)) μ := by
  sorry

/-- **The empirical process is mean-zero** (HDP §8.2, Definition 8.2.5):
`E[X_f] = n⁻¹ ∑ᵢ E f(Xᵢ) − ∫ f dP = 0` since each `Xᵢ` has law `P`. -/
theorem integral_empiricalProcess [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n] {f : Ω' → ℝ}
    -- LEAN-ONLY: integrability under P; derived from boundedness at call sites
    (hf_int : Integrable f P)
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    ∫ ω, empiricalProcess P n X f ω ∂μ = 0 := by
  sorry

/-- Sum-level Hoeffding bound (HDP §2.6 / §8.2 Step 1): the centered sum
`∑ᵢ (f(Xᵢ) − E_P f)` has sub-Gaussian MGF with proxy `n·δ²`
(per-summand `Icc(−δ, δ)`-membership proxy `δ²` + `sum_of_iIndepFun`). -/
theorem hasSubgaussianMGF_sum_centered_comp [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] {f : Ω' → ℝ} {δ : ℝ≥0}
    -- LEAN-ONLY: measurability of the class member; regularity, no book content
    (hf : Measurable f)
    -- USER-INPUT: uniform bound ‖f‖∞ ≤ δ; HDP §8.2 Step 1
    (hfδ : ∀ x, |f x| ≤ (δ : ℝ))
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    HasSubgaussianMGF (fun ω => ∑ i, (f (X i ω) - ∫ x, f x ∂P))
      ((n : ℝ≥0) * δ ^ 2) μ := by
  sorry

/-- **Step 1, MGF level** (HDP §8.2, proof of Theorem 8.2.3): the increment
`X_f − X_g` has sub-Gaussian MGF with proxy **exactly** `δ²/n` where
`‖f − g‖∞ ≤ δ` (scale the sum-level bound by `n⁻¹`; rewrite the centered
variable via `integral_empiricalProcess`). -/
theorem hasSubgaussianMGF_empiricalProcess_sub [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n] {f g : Ω' → ℝ} {δ : ℝ≥0}
    -- LEAN-ONLY: measurability of the class members; regularity, no book content
    (hf : Measurable f) (hg : Measurable g)
    -- USER-INPUT: sup-distance bound ‖f − g‖∞ ≤ δ; HDP §8.2 Step 1
    (hfg : ∀ x, |f x - g x| ≤ (δ : ℝ))
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    HasSubgaussianMGF
      (fun ω => empiricalProcess P n X f ω - empiricalProcess P n X g ω)
      (δ ^ 2 / n) μ := by
  sorry

/-- Single-function corollary (`g = 0`): `X_f` itself is sub-Gaussian with
proxy `B²/n` when `‖f‖∞ ≤ B` (HDP §8.2). -/
theorem hasSubgaussianMGF_empiricalProcess [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n] {f : Ω' → ℝ} {B : ℝ≥0}
    -- LEAN-ONLY: measurability of the class member; regularity, no book content
    (hf : Measurable f)
    -- USER-INPUT: uniform bound ‖f‖∞ ≤ B; HDP §8.2
    (hfB : ∀ x, |f x| ≤ (B : ℝ))
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    HasSubgaussianMGF (empiricalProcess P n X f) (B ^ 2 / n) μ := by
  sorry

/-- Repackaging into the project predicate `IsSubGaussian` — the exact input
shape of the Orlicz bridge B3 (`subGaussianNorm_le_of_isSubGaussian`). -/
theorem isSubGaussian_empiricalProcess_sub [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n] {f g : Ω' → ℝ} {δ : ℝ≥0}
    -- LEAN-ONLY: measurability of the class members; regularity, no book content
    (hf : Measurable f) (hg : Measurable g)
    -- USER-INPUT: sup-distance bound ‖f − g‖∞ ≤ δ; HDP §8.2 Step 1
    (hfg : ∀ x, |f x - g x| ≤ (δ : ℝ))
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    IsSubGaussian
      (fun ω => empiricalProcess P n X f ω - empiricalProcess P n X g ω)
      (δ ^ 2 / n) μ := by
  sorry

/-- **Step 1, ψ₂ level** (HDP §8.2 Step 1):
`‖X_f − X_g‖_{ψ₂} ≤ √(6·δ²/n) = √6·δ/√n` — the Orlicz bridge B3 applied at
`σ² = δ²/n`, carrier `√(6σ²)` verbatim (explicit `√6`, no alias constant). -/
theorem subGaussianNorm_empiricalProcess_sub_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n] {f g : Ω' → ℝ} {δ : ℝ≥0}
    -- LEAN-ONLY: measurability of the class members; regularity, no book content
    (hf : Measurable f) (hg : Measurable g)
    -- USER-INPUT: sup-distance bound ‖f − g‖∞ ≤ δ; HDP §8.2 Step 1
    (hfg : ∀ x, |f x - g x| ≤ (δ : ℝ))
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    subGaussianNorm
      (fun ω => empiricalProcess P n X f ω - empiricalProcess P n X g ω) μ
      ≤ (NNReal.sqrt (6 * (δ ^ 2 / n)) : ℝ≥0∞) := by
  sorry

/-- **Increment condition over `C([0,1], ℝ)`** (HDP §8.1, Definition 8.1.1):
`‖X_f − X_g‖_{ψ₂} ≤ (√6/√n) · dist f g` for *all* continuous `f, g` on the
sup-metric index space (`dist_apply_le_dist` supplies the pointwise bound).
Named-sorry fallback of `hdp-emp-increments`. -/
theorem subGaussianNorm_empiricalProcess_sub_le_dist [IsProbabilityMeasure μ]
    {P : Measure unitInterval} [IsProbabilityMeasure P] [NeZero n]
    {X : Fin n → Ω → unitInterval} {f g : C(unitInterval, ℝ)}
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data on [0,1]; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    subGaussianNorm
      (fun ω => empiricalProcess P n X ⇑f ω - empiricalProcess P n X ⇑g ω) μ
      ≤ ENNReal.ofReal (Real.sqrt 6 / Real.sqrt n * dist f g) := by
  sorry

/-- **Packaged increments** (HDP §8.1, Definition 8.1.1): the empirical
process indexed by `C(unitInterval, ℝ)` has `K`-sub-Gaussian increments with
`K = √6/√n`, stated on `T = Set.univ` (restrict downstream via
`SubGaussianIncrements.mono_set`). -/
theorem subGaussianIncrements_empiricalProcess [IsProbabilityMeasure μ]
    {P : Measure unitInterval} [IsProbabilityMeasure P] [NeZero n]
    {X : Fin n → Ω → unitInterval}
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data on [0,1]; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    SubGaussianIncrements (fun (f : C(unitInterval, ℝ)) => empiricalProcess P n X ⇑f)
      (Real.toNNReal (Real.sqrt 6 / Real.sqrt n)) Set.univ μ := by
  sorry

end StatLean.ConcentrationInequalities
