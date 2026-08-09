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
    (Finset.powersetCard n (Finset.univ : Finset U)).Nonempty :=
  Finset.powersetCard_nonempty.2 (by simpa using hn)

/-- **Simple random sampling without replacement** of size `n`: the uniform
distribution on the `n`-element subsets of the population (`Mead §9.3`). -/
noncomputable def simpleRandomSampling (n : ℕ) (hn : n ≤ Fintype.card U) :
    SamplingDesign U :=
  PMF.uniformOfFinset (Finset.powersetCard n Finset.univ) (samplesOfCard_nonempty hn)

theorem mem_support_simpleRandomSampling {n : ℕ} {hn : n ≤ Fintype.card U}
    {s : Finset U} :
    s ∈ (simpleRandomSampling n hn).support ↔ s.card = n := by
  rw [simpleRandomSampling, PMF.mem_support_uniformOfFinset_iff, Finset.mem_powersetCard]
  exact and_iff_right (Finset.subset_univ s)

/-- **Sampling symmetry**: SRSWOR is invariant under relabelling the units by any
permutation. -/
theorem simpleRandomSampling_map_image (n : ℕ) (hn : n ≤ Fintype.card U)
    (σ : Equiv.Perm U) :
    (simpleRandomSampling n hn).map (fun s => s.image (σ : U → U))
      = simpleRandomSampling n hn := by
  ext u
  rw [PMF.map_apply]
  have himg : ∀ t : Finset U, (t.image (σ.symm : U → U)).image (σ : U → U) = t := by
    intro t; rw [Finset.image_image]; simp
  refine (tsum_eq_single (u.image (σ.symm : U → U)) ?_).trans ?_
  · intro t ht
    refine if_neg fun h => ht ?_
    rw [h, Finset.image_image]
    simp
  · rw [himg u, if_pos rfl]
    simp only [simpleRandomSampling, PMF.uniformOfFinset_apply, Finset.mem_powersetCard,
      Finset.subset_univ, true_and, Finset.card_image_of_injective _ σ.symm.injective]

omit [Fintype U] in
/-- Membership in a permuted sample: `a ∈ σ(s) ↔ σ⁻¹(a) ∈ s`. -/
private lemma mem_image_perm {σ : Equiv.Perm U} {s : Finset U} {a : U} :
    a ∈ s.image (σ : U → U) ↔ σ.symm a ∈ s := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨σ.symm a, h, by simp⟩

omit [Fintype U] in
private lemma inclusionIndicator_image_perm (σ : Equiv.Perm U) (a : U) (s : Finset U) :
    inclusionIndicator a (s.image (σ : U → U)) = inclusionIndicator (σ.symm a) s := by
  simp only [inclusionIndicator, mem_image_perm]

/-- Relabelling invariance of SRS expectations: the design expectation of `f` equals
that of `f ∘ σ`, for any permutation `σ` of the population. -/
private lemma srs_expect_perm (n : ℕ) (hn : n ≤ Fintype.card U) (σ : Equiv.Perm U)
    (f : Finset U → ℝ) :
    pmfExpect (simpleRandomSampling n hn) f
      = pmfExpect (simpleRandomSampling n hn) (fun s => f (s.image (σ : U → U))) := by
  conv_lhs => rw [← simpleRandomSampling_map_image n hn σ]
  rw [pmfExpect_map]

/-- Two statistics agreeing on the `n`-subsets have the same SRS expectation. -/
private lemma srs_expect_congr (n : ℕ) (hn : n ≤ Fintype.card U) {f g : Finset U → ℝ}
    (h : ∀ s : Finset U, s.card = n → f s = g s) :
    pmfExpect (simpleRandomSampling n hn) f = pmfExpect (simpleRandomSampling n hn) g := by
  rw [simpleRandomSampling, pmfExpect_uniformOfFinset, pmfExpect_uniformOfFinset]
  congr 1
  exact Finset.sum_congr rfl fun s hs => h s (Finset.mem_powersetCard.1 hs).2

/-- Two statistics agreeing on the `n`-subsets have the same SRS variance. -/
private lemma srs_var_congr (n : ℕ) (hn : n ≤ Fintype.card U) {f g : Finset U → ℝ}
    (h : ∀ s : Finset U, s.card = n → f s = g s) :
    pmfVar (simpleRandomSampling n hn) f = pmfVar (simpleRandomSampling n hn) g := by
  unfold pmfVar
  rw [srs_expect_congr n hn h]
  exact srs_expect_congr n hn fun s hs => by rw [h s hs]

/-- The SRS sample size is deterministically `n`. -/
private lemma srs_expect_card (n : ℕ) (hn : n ≤ Fintype.card U) :
    pmfExpect (simpleRandomSampling n hn) (fun s => (s.card : ℝ)) = (n : ℝ) := by
  rw [srs_expect_congr n hn (g := fun _ => (n : ℝ)) fun s hs => by rw [hs]]
  exact pmfExpect_const _ _

/-- Inclusion probabilities are constant across units, by relabelling symmetry. -/
private lemma srs_inclusionProb_eq (n : ℕ) (hn : n ≤ Fintype.card U) (i j : U) :
    inclusionProb (simpleRandomSampling n hn) i
      = inclusionProb (simpleRandomSampling n hn) j := by
  unfold inclusionProb
  rw [srs_expect_perm n hn (Equiv.swap i j) (inclusionIndicator i)]
  congr 1
  funext s
  rw [inclusionIndicator_image_perm, Equiv.symm_swap, Equiv.swap_apply_left]

/-- **First-order inclusion probability under SRS**: `πᵢ = n/N`. -/
theorem srs_inclusionProb (n : ℕ) (hn : n ≤ Fintype.card U) (i : U) :
    inclusionProb (simpleRandomSampling n hn) i
      = (n : ℝ) / (Fintype.card U : ℝ) := by
  have hcard : 0 < Fintype.card U := Fintype.card_pos_iff.2 ⟨i⟩
  have hN : (Fintype.card U : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hcard.ne'
  have hsum : ∑ k, inclusionProb (simpleRandomSampling n hn) k = (n : ℝ) := by
    rw [← expect_sampleCard]; exact srs_expect_card n hn
  have hconst : ∑ k, inclusionProb (simpleRandomSampling n hn) k
      = (Fintype.card U : ℝ) * inclusionProb (simpleRandomSampling n hn) i := by
    rw [Finset.sum_congr rfl fun k _ => srs_inclusionProb_eq n hn k i, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  rw [hconst] at hsum
  rw [eq_div_iff hN]
  linear_combination hsum

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
