import Mathlib.GroupTheory.Perm.Basic
import StatLean.ExperimentalDesign.SurveySampling.InclusionProbability
import StatLean.ExperimentalDesign.SurveySampling.HorvitzThompson

/-!
# Simple random sampling without replacement

**Simple random sampling without replacement** (SRSWOR) of size `n` from the finite
population `U` draws a subset uniformly from the `n`-element subsets:
$$D_{n} = \operatorname{Uniform}\{S \subseteq U : |S| = n\}.$$
This file constructs the design and proves the classical exact results:
$$\pi_i = \frac nN, \qquad \pi_{ij} = \frac{n(n-1)}{N(N-1)} \ (i \ne j), \qquad
  \mathbb E[\bar y_S] = \bar y, \qquad
  \operatorname{Var}(\bar y_S) = \Bigl(1 - \frac nN\Bigr)\frac{S_y^2}{n},$$
the last displaying the **finite-population correction** `1 − n/N`.  Under SRS the
Horvitz–Thompson estimator collapses to the scaled sample total `(N/n) ∑_{i∈S} yᵢ`.

## Main results

* `samplesOfCard_nonempty`, `simpleRandomSampling` — the design.
* `mem_support_simpleRandomSampling` — the support is the `n`-subsets.
* `simpleRandomSampling_map_image` — permutation invariance.
* `srs_inclusionProb`, `srs_pairInclusionProb` — inclusion probabilities.
* `srs_sampleMean_unbiased`, `srs_sampleMean_variance` — the sample-mean moments.
* `srs_horvitzThompson_eq` — Horvitz–Thompson as the scaled sample total.

**Reference.** Mead treats drawing `n` of `N` units uniformly as the elementary
randomisation device (R. Mead, *The Design of Experiments*, CUP, 1988, §9.2–§9.3;
Example 9.3 draws 4 mice of 20 uniformly over the `binom(20,4)` subsets); the
inclusion-probability and finite-population-correction formulas are survey-sampling
classics (Horvitz–Thompson 1952; W.G. Cochran, *Sampling Techniques*, 3rd ed., Wiley,
1977, ch. 2).  (`Mead §9.3`, `HT52`.)

**Proof formalization notes.**
* The same moments over the population `Fin n` are fully proved in
  `StatLean.HypothesisTesting.ForMathlib.HypergeometricMoments` (as moments of
  two-sample splits); the counting arguments there — subsets of prescribed size
  containing a given unit or pair — port verbatim to a general `Fintype` population.
  Either adapt those proofs or transfer along an equivalence `U ≃ Fin N`.
* `srs_sampleMean_variance` is exact, with `S²` the `N−1`-normalised
  `populationVariance`; degenerate cases (`n = N`, `N = 1`) hold because both sides
  vanish.
* `srs_horvitzThompson_eq` is a pointwise identity for every subset (not only those
  in the support): both sides scale the sample total by constants that agree by
  `srs_inclusionProb`, degenerating correctly at `n = 0` by the division convention.
-/

open scoped ENNReal

namespace StatLean.ExperimentalDesign

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The `n`-element subsets of a population of size at least `n` form a nonempty
family. -/
theorem samplesOfCard_nonempty {n : ℕ}
    -- USER-INPUT: the sample size does not exceed the population size; Mead §9.3
    (hn : n ≤ Fintype.card U) :
    (Finset.powersetCard n (Finset.univ : Finset U)).Nonempty := by
  sorry

/-- **Simple random sampling without replacement** of size `n`: the uniform
distribution on the `n`-element subsets of the population (`Mead §9.3`). -/
noncomputable def simpleRandomSampling (n : ℕ) (hn : n ≤ Fintype.card U) :
    SamplingDesign U :=
  PMF.uniformOfFinset (Finset.powersetCard n Finset.univ) (samplesOfCard_nonempty hn)

theorem mem_support_simpleRandomSampling {n : ℕ} {hn : n ≤ Fintype.card U}
    {s : Finset U} :
    s ∈ (simpleRandomSampling n hn).support ↔ s.card = n := by
  sorry

/-- **Sampling symmetry**: SRSWOR is invariant under relabelling the units by any
permutation. -/
theorem simpleRandomSampling_map_image (n : ℕ) (hn : n ≤ Fintype.card U)
    (σ : Equiv.Perm U) :
    (simpleRandomSampling n hn).map (fun s => s.image (σ : U → U))
      = simpleRandomSampling n hn := by
  sorry

/-- **First-order inclusion probability under SRS**: `πᵢ = n/N`. -/
theorem srs_inclusionProb (n : ℕ) (hn : n ≤ Fintype.card U) (i : U) :
    inclusionProb (simpleRandomSampling n hn) i
      = (n : ℝ) / (Fintype.card U : ℝ) := by
  sorry

/-- **Second-order inclusion probability under SRS**:
`π_{ij} = n(n−1)/(N(N−1))` for distinct units. -/
theorem srs_pairInclusionProb (n : ℕ) (hn : n ≤ Fintype.card U) {i j : U}
    -- LEAN-ONLY: distinct units; the diagonal is `pairInclusionProb_self`
    (hij : i ≠ j) :
    pairInclusionProb (simpleRandomSampling n hn) i j
      = (n : ℝ) * ((n : ℝ) - 1)
          / ((Fintype.card U : ℝ) * ((Fintype.card U : ℝ) - 1)) := by
  sorry

/-- **Unbiasedness of the SRS sample mean**: `E[ȳ_S] = ȳ` for a positive sample
size. -/
theorem srs_sampleMean_unbiased (n : ℕ) (hn : n ≤ Fintype.card U)
    -- USER-INPUT: positive sample size, so the sample mean is well defined; Mead §9.3
    (hn0 : n ≠ 0) (y : U → ℝ) :
    pmfExpect (simpleRandomSampling n hn) (sampleMean y) = populationMean y := by
  sorry

/-- **Exact variance of the SRS sample mean with finite-population correction**:
`Var(ȳ_S) = (1 − n/N) S²_y / n` (`HT52`; Cochran ch. 2, Theorem 2.2). -/
theorem srs_sampleMean_variance (n : ℕ) (hn : n ≤ Fintype.card U)
    -- USER-INPUT: positive sample size, so the sample mean is well defined; Mead §9.3
    (hn0 : n ≠ 0) (y : U → ℝ) :
    pmfVar (simpleRandomSampling n hn) (sampleMean y)
      = (1 - (n : ℝ) / (Fintype.card U : ℝ)) * populationVariance y / (n : ℝ) := by
  sorry

/-- Under SRS the Horvitz–Thompson estimator is the scaled sample total
`(N/n) ∑_{i ∈ s} yᵢ` — pointwise in the subset `s`, by the constancy of the
inclusion probabilities. -/
theorem srs_horvitzThompson_eq (n : ℕ) (hn : n ≤ Fintype.card U) (y : U → ℝ)
    (s : Finset U) :
    horvitzThompson (simpleRandomSampling n hn) y s
      = (Fintype.card U : ℝ) / (n : ℝ) * ∑ i ∈ s, y i := by
  sorry

end StatLean.ExperimentalDesign
