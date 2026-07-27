import StatLean.Bayesian.BernsteinVonMises.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.Bounded

/-!
# Boosting consistent tests to exponential power (far range of Lemma 10.3)

The second half of vdV Lemma 10.3: given *any* uniformly consistent test sequence for
`H₀ : θ = θ₀` against `H₁ : ‖θ − θ₀‖ ≥ ε` (condition (10.2)), one can construct tests whose
type-II error decays **exponentially** in `n`, uniformly over the far alternatives. The
construction blocks the sample into groups of a fixed size `kb`, applies the given level-`kb`
test to each block, and rejects when the average of the block tests exceeds `1/2`; Hoeffding's
inequality for `[0,1]`-valued iid block statistics gives the exponential bound.

* `bvmBlockAvg` — the average of a one-block statistic over the `⌊n/kb⌋` disjoint blocks;
* `blockAvg_typeII_tail` — the Hoeffding bound
  `P^n_θ(blockAvg < 1/2) ≤ exp(−⌊n/kb⌋/8)` when the one-block mean is `≥ 3/4`;
* `exists_boosted_tests` — the headline: exponentially consistent tests on
  `‖θ − θ₀‖ ≥ ε`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Lemma 10.3, p. 144 (second test sequence; blocks `Y_{n,1}, …, Y_{n,m}`).

**Proof formalization notes.** Under `productMeasure M μ θ n` the block statistics are iid
`[0,1]`-valued with mean `∫ φ_kb dP^{kb}_θ`; independence of the blocks follows from
`ProbabilityTheory.iIndepFun_pi` composed with the disjoint block-coordinate projections.
Hoeffding is `StatLean.ConcentrationInequalities.hoeffding` (with
`isSubGaussian_of_mem_Icc`). The auxiliary size-`kb` level and the threshold `1/2` follow
vdV's choice `P^{kb}_{θ₀} φ_{kb} < 1/4 < 3/4 ≤ P^{kb}_θ φ_{kb}`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open AsymptoticStatistics (ParametricFamily IsPDFOf)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)}

/-- Within-block index arithmetic: the `i`-th coordinate of the `j`-th length-`kb` block is a
valid sample index. -/
lemma bvmBlockIndex_lt {n kb : ℕ} (j : Fin (n / kb)) (i : Fin kb) :
    j.val * kb + i.val < n := by
  have h1 : j.val + 1 ≤ n / kb := j.isLt
  have h2 : (j.val + 1) * kb ≤ (n / kb) * kb := Nat.mul_le_mul_right kb h1
  have h3 : (n / kb) * kb ≤ n := Nat.div_mul_le_self n kb
  have h4 : j.val * kb + i.val < (j.val + 1) * kb := by
    rw [Nat.add_one_mul]; exact Nat.add_lt_add_left i.isLt _
  omega

/-- **Block average of a one-block statistic**: split `ω : Fin n → 𝓧` into `⌊n/kb⌋` disjoint
consecutive blocks of length `kb` and average `g` over the blocks. Junk behavior: for
`kb = 0` or `n < kb` the block count is `0` and the average is the empty-sum `0` scaled by
`(0 : ℝ)⁻¹ = 0`. -/
noncomputable def bvmBlockAvg (kb : ℕ) (g : (Fin kb → 𝓧) → ℝ) (n : ℕ)
    (ω : Fin n → 𝓧) : ℝ :=
  ((n / kb : ℕ) : ℝ)⁻¹ *
    ∑ j : Fin (n / kb), g fun i : Fin kb =>
      ω ⟨j.val * kb + i.val, bvmBlockIndex_lt j i⟩

/-- **Hoeffding bound for the block average** (vdV p. 144): if the one-block statistic `g`
takes values in `[0,1]` and has `P^{kb}_θ`-mean at least `3/4`, then
`P^n_θ(bvmBlockAvg < 1/2) ≤ exp(−⌊n/kb⌋/8)`. -/
theorem blockAvg_typeII_tail
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ) {kb : ℕ}
    -- LEAN-ONLY: nonempty blocks
    (hkb : 1 ≤ kb) {g : (Fin kb → 𝓧) → ℝ}
    -- LEAN-ONLY: measurable one-block statistic (regularity)
    (hg_meas : Measurable g)
    -- LEAN-ONLY: `[0,1]`-valued one-block statistic (a test)
    (hg01 : ∀ ζ, g ζ ∈ Set.Icc (0 : ℝ) 1)
    (θ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: one-block power `≥ 3/4` at `θ`; vdV p. 144
    (hpow : 3 / 4 ≤ ∫ ζ, g ζ ∂(productMeasure M μ θ kb)) {n : ℕ}
    -- LEAN-ONLY: at least one full block
    (hn : kb ≤ n) :
    (productMeasure M μ θ n).real {ω | bvmBlockAvg kb g n ω < 1 / 2}
      ≤ Real.exp (-(↑(n / kb) : ℝ) / 8) := by
  sorry

/-- **Exponentially consistent tests on the far range** (vdV Lemma 10.3, second test
sequence): under the tests condition (10.2), for every `ε > 0` there are measurable
`[0,1]`-tests with vanishing size at `θ₀` and type-II error `≤ exp(−c n)` uniformly over
`‖θ − θ₀‖ ≥ ε`, for `n` large. -/
theorem exists_boosted_tests
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the tests condition (10.2); vdV Thm 10.1
    (hTests : UniformlyConsistentTests M μ θ₀) {ε : ℝ}
    -- LEAN-ONLY: nontrivial separation radius
    (hε : 0 < ε) :
    ∃ (φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ) (c : ℝ), 0 < c ∧
      (∀ n, Measurable (φ n)) ∧ (∀ n ω, φ n ω ∈ Set.Icc (0 : ℝ) 1) ∧
      Tendsto (fun n => ∫ ω, φ n ω ∂(productMeasure M μ θ₀ n)) atTop (𝓝 0) ∧
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ θ, ε ≤ ‖θ - θ₀‖ →
        ∫ ω, (1 - φ n ω) ∂(productMeasure M μ θ n) ≤ Real.exp (-c * n) := by
  sorry

end StatLean.Bayesian
