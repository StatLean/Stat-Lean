import StatLean.HypothesisTesting.ForMathlib.PermutationMarginals
import StatLean.HypothesisTesting.ForMathlib.SteinMethod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF

/-!
# The combinatorial central limit theorem

Let `d : Fin N → ℝ` be a deterministic coefficient vector and let `a : Fin m → Fin N` pick out
`m` distinct positions. A uniform random permutation `σ` of `Fin N` relabels the positions,
and the **block sum**
$$ B_\sigma \;=\; \sum_{i < m} d\bigl(\sigma(a_i)\bigr) $$
is the sum of a *simple random sample of size `m` without replacement* from the finite
population `{d(1), …, d(N)}`. Every linear permutation statistic — in particular the
two-sample permutation statistic of `Randomization/TwoSamplePermutation` — is an affine
function of such a block sum.

The first two moments are elementary and are proved here from the one- and two-coordinate
marginals of `ForMathlib/PermutationMarginals`: for a **centred** population (`∑ d = 0`),
$$ \mathbb E\, B_\sigma = 0, \qquad
   \mathbb E\, B_\sigma^2 = \frac{m(N-m)}{N(N-1)} \sum_l d(l)^2 . $$
The **combinatorial central limit theorem** of Wald–Wolfowitz, Noether, Hoeffding, Erdős–Rényi
and Hájek says that the standardized block sum is asymptotically standard normal as soon as
both `m` and `N - m` tend to infinity and the population satisfies a Lindeberg-type condition;
that is `tendsto_perm_cdf_blockSum` below.

## Main results

* `sum_perm_inv` — a group average is unchanged by inverting the permutation. (The
  randomization action of `Randomization/TwoSamplePermutation` is `(σ • x) i = x (σ⁻¹ i)`,
  whereas the marginal bricks are written with `σ`; this is the bridge.)
* `avg_perm_blockSum` — the exact first moment of a block sum.
* `avg_perm_blockSum_sq` — the exact second moment of a **centred** block sum, i.e. the
  finite-population variance `m(N-m)/(N(N-1)) · ∑ d²`.
* `perm_avg_indicator_blockAvg_sub_mean_le` and its inverse-convention twin
  `perm_avg_indicator_blockAvg_inv_sub_mean_le` — the Chebyshev step for a block average of
  **uncentred** coefficients against the population mean.
* `avg_measureReal_eq_integral_avg_indicator` — Fubini for a finite group: the group average
  of deviation *probabilities* is the integral of the group average of the *indicators*.
* `blockSumScale` — the asymptotic standard deviation `√(m(N-m)/N)` used to standardize.
* `blockSet`, `SwapIndex`, `stdBlockSum`, `stdBlockSumSwap` — the **exchangeable pair** of
  Stein's method: swap one sampled position with one unsampled position.
* `sum_blockSet_mul_swap` and `stdBlockSumSwap_sub` — the increment of the pair.
* `sum_swap_exchangeable` — the pair is exchangeable.
* `sum_swapIndex_increment` and `sum_swapIndex_increment'` — the linearity condition, exactly,
  with `λ = N/(m(N-m))`.
* `tendsto_perm_avg_lipschitz` — the combinatorial CLT tested against bounded Lipschitz
  functions (the core brick; open, see the status note at the statement).
* `tendsto_perm_cdf_blockSum` — **the combinatorial central limit theorem**, derived from the
  previous one by the elementary ramp de-smoothing.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 12 (Extensions of the
CLT to Sums of Dependent Random Variables), §12.2 (Random Sampling Without Replacement from a
Finite Population), and Chapter 17 (Permutation and Randomization Tests), §17.3, where the
theorem is applied to the two-sample statistic. (`TSH4 §12.2`, `TSH4 §17.3`.)

**Proof formalization notes.**
* *Which model.* Sampling without replacement has two equivalent carriers in this
  repository: the **subset** model of `ForMathlib/HypergeometricMoments` (uniform on
  `SubsetsOfCard N m`, average written `expect`) and the **permutation** model of
  `ForMathlib/PermutationMarginals` (uniform on `Equiv.Perm (Fin N)`, average written as an
  explicit normalized sum). This file uses the permutation model, because `randDist` and
  `randPairLaw` are *defined* as averages over the acting group, so no transfer lemma is
  needed at the point of use. The two moment computations below are the permutation-model
  twins of `HypergeometricMoments.expect_weight` and `HypergeometricMoments.var_linear`.
* *No factorial.* As in `PermutationMarginals`, the cardinality of the symmetric group is
  never computed; it cancels against itself through `avg_perm_apply` and
  `avg_perm_apply_pair`.
* *Standardization.* `blockSumScale N m = √(m(N-m)/N)` is the asymptotic standard deviation
  of a block sum whose population is normalized to `N⁻¹ ∑ d² → 1`; the exact standard
  deviation carries the extra finite-population factor `N/(N-1) · (N⁻¹ ∑ d²)`, which tends
  to `1` under the hypotheses of `tendsto_perm_cdf_blockSum` and would only clutter the
  statement. Both `m` and `N - m` are required to tend to infinity, which is necessary: for
  `m` bounded the block sum is a sum of boundedly many terms and has no normal limit, and the
  problem is symmetric under `m ↦ N - m` because `∑ d = 0` makes the two blocks negatives of
  each other.
* *Which Lindeberg condition.* The threshold is `ε √(min m (N-m))`, i.e. Hájek's condition,
  not `ε √N`. The two agree when `m/N` stays bounded away from `0` and `1` — which is the
  two-sample regime `m/n → λ ∈ (0, ∞)` — but Hájek's is the one that is also *necessary*, so
  it is the honest hypothesis to record.

**Bibliographic comments.** The theorem originates with A. Wald and J. Wolfowitz,
"Statistical tests based on permutations of the observations," *Ann. Math. Statist.* **15**
(1944), 358–372, who assumed all moments; G. E. Noether, "On a theorem of Pitman," *Ann.
Math. Statist.* **20** (1949), 455–458, and W. Hoeffding, "A combinatorial central limit
theorem," *Ann. Math. Statist.* **22** (1951), 558–566, reduced the hypotheses to conditions
on the fourth and second moments respectively. The definitive form — a Lindeberg condition
that is both necessary and sufficient for simple random sampling from a finite population —
is due to P. Erdős and A. Rényi, "On the central limit theorem for samples from a finite
population," *Publ. Math. Inst. Hungar. Acad. Sci.* **4** (1959), 49–61, and J. Hájek,
"Limiting distributions in simple random sampling from a finite population," *Publ. Math.
Inst. Hungar. Acad. Sci.* **5** (1960), 361–374. Modern proofs go through Stein's method for
exchangeable pairs (C. Stein, *Approximate Computation of Expectations*, IMS, 1986) or
through a coupling with the conditioned Bernoulli representation.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

/-! ### Inverting the permutation inside a group average -/

/-- A sum over a finite group is unchanged by inversion. The randomization action used by
`Randomization/TwoSamplePermutation` is `(σ • x) i = x (σ⁻¹ i)`, while the marginal bricks of
`ForMathlib/PermutationMarginals` are stated with `σ`; this lemma is the bridge, and it costs
nothing because inversion is a bijection of the group. -/
theorem sum_perm_inv {G : Type*} [Group G] [Fintype G] {M : Type*} [AddCommMonoid M]
    (f : G → M) : ∑ g : G, f g⁻¹ = ∑ g : G, f g :=
  Equiv.sum_comp (Equiv.inv G) f

/-! ### The first two moments of a block sum -/

/-- **First moment of a block sum.** Under a uniform random permutation each of the `m`
sampled positions is uniform on the `N` items, so the block sum has mean `m · N⁻¹ ∑ d`. No
injectivity of the block is needed: the first moment is additive. -/
theorem avg_perm_blockSum {N m : ℕ} (a : Fin m → Fin N) (d : Fin N → ℝ) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), ∑ i, d (σ (a i))
      = (m : ℝ) * ((N : ℝ)⁻¹ * ∑ l, d l) := by
  classical
  rw [Finset.sum_comm, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
    avg_perm_apply (a i) d]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Fintype.card_fin]

/-- **Second moment of a centred block sum** — the finite-population variance
$$ \frac1{|\mathbf S_N|}\sum_\sigma \Bigl(\sum_{i<m} d(\sigma(a_i))\Bigr)^2
   \;=\; \frac{m(N-m)}{N(N-1)} \sum_l d(l)^2 . $$
The `m` diagonal terms contribute `N⁻¹ ∑ d²` each and the `m(m-1)` off-diagonal ones
contribute `-(N(N-1))⁻¹ ∑ d²` each, by the one- and two-coordinate marginals; the negative
sign is the negative correlation forced by sampling without replacement. Both degenerate
blocks `m = 0` and `m = N` give variance `0`, as they must. -/
theorem avg_perm_blockSum_sq {N m : ℕ}
    -- USER-INPUT: at least two items (the factor `N - 1` is a denominator)
    (hN : 2 ≤ N)
    -- USER-INPUT: the block is a set of `m` distinct positions
    (a : Fin m → Fin N) (ha : Function.Injective a)
    -- USER-INPUT: centred coefficients
    (d : Fin N → ℝ) (hd : ∑ l, d l = 0) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N), (∑ i, d (σ (a i))) ^ 2
      = (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) * ((N : ℝ) - 1)) * ∑ l, d l ^ 2 := by
  classical
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  set S₂ : ℝ := ∑ l, d l ^ 2 with hS₂
  -- expand the square into a double sum over block positions
  have hexpand : ∀ σ : Equiv.Perm (Fin N), (∑ i, d (σ (a i))) ^ 2
      = ∑ i : Fin m, ∑ j : Fin m, d (σ (a i)) * d (σ (a j)) := by
    intro σ
    rw [sq (∑ i, d (σ (a i))), Finset.sum_mul_sum]
  -- the average of each cross term is a one- or two-coordinate marginal
  have hdiag : ∀ i : Fin m, (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), d (σ (a i)) * d (σ (a i)) = (N : ℝ)⁻¹ * S₂ := by
    intro i
    have h := avg_perm_apply (a i) (fun l => d l * d l)
    rw [Fintype.card_fin] at h
    rw [h, hS₂]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [sq]
  have hoff : ∀ i j : Fin m, i ≠ j → (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), d (σ (a i)) * d (σ (a j))
      = -(((N : ℝ) * ((N : ℝ) - 1))⁻¹ * S₂) := by
    intro i j hij
    have hne : a i ≠ a j := fun hcon => hij (ha hcon)
    have h := avg_perm_apply_pair hne (fun l l' => d l * d l')
    rw [Fintype.card_fin] at h
    rw [h]
    have hdiagsum : ∑ l : Fin N, d l * d l = S₂ := by
      rw [hS₂]; exact Finset.sum_congr rfl fun l _ => by rw [sq]
    have hprod : ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)),
        d p.1 * d p.2 = ∑ l, ∑ l', d l * d l' := Finset.sum_product _ _ _
    have hfull : ∑ l : Fin N, ∑ l', d l * d l' = (∑ l, d l) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
    have hdecomp : ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)))
        = (Finset.univ : Finset (Fin N)).diag ∪ (Finset.univ : Finset (Fin N)).offDiag :=
      (Finset.diag_union_offDiag _).symm
    have hdisj : Disjoint ((Finset.univ : Finset (Fin N)).diag)
        ((Finset.univ : Finset (Fin N)).offDiag) := Finset.disjoint_diag_offDiag _
    rw [hdecomp, Finset.sum_union hdisj, Finset.sum_diag, hdiagsum, hfull, hd] at hprod
    have hsplit : ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, d p.1 * d p.2 = -S₂ := by
      rw [show (0 : ℝ) ^ 2 = 0 from by ring] at hprod
      linarith
    rw [hsplit]
    ring
  -- assemble: `m` diagonal terms and `m(m−1)` off-diagonal ones
  have hswap : ∑ σ : Equiv.Perm (Fin N), (∑ i, d (σ (a i))) ^ 2
      = ∑ σ : Equiv.Perm (Fin N), ∑ i : Fin m, ∑ j : Fin m, d (σ (a i)) * d (σ (a j)) :=
    Finset.sum_congr rfl fun σ _ => hexpand σ
  have hexch : (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      (∑ σ : Equiv.Perm (Fin N), ∑ i : Fin m, ∑ j : Fin m, d (σ (a i)) * d (σ (a j)))
      = ∑ i : Fin m, ∑ j : Fin m,
          (if i = j then (N : ℝ)⁻¹ * S₂ else -(((N : ℝ) * ((N : ℝ) - 1))⁻¹ * S₂)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]; exact hdiag i
    · rw [if_neg hij]; exact hoff i j hij
  rw [hswap, hexch]
  -- the closed form of the double sum
  set A : ℝ := (N : ℝ)⁻¹ * S₂ with hA
  set B : ℝ := -(((N : ℝ) * ((N : ℝ) - 1))⁻¹ * S₂) with hB
  have hrow : ∀ i : Fin m, (∑ j : Fin m, (if i = j then A else B))
      = (m : ℝ) * B + (A - B) := by
    intro i
    have hterm : ∀ j : Fin m, (if i = j then A else B) = B + (if i = j then A - B else 0) := by
      intro j; by_cases h : i = j <;> simp [h]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_eq Finset.univ i (fun _ => A - B), if_pos (Finset.mem_univ i)]
  have hcount : (∑ i : Fin m, ∑ j : Fin m, (if i = j then A else B))
      = (m : ℝ) * A + ((m : ℝ) * (m : ℝ) - (m : ℝ)) * B := by
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hcount, hA, hB]
  field_simp
  ring

/-! ### Chebyshev for a block average, with uncentred coefficients

`PermutationMarginals.perm_avg_indicator_blockAvg_le` is stated for an already-centred
coefficient vector, which is the form in which the variance identity is cleanest. Consumers,
however, arrive with a raw vector `c` — the pooled data, or a function of it — and want to
compare its block average against its *population* average `c̄ = N⁻¹ ∑ c`. Recentring is a
one-line shift, recorded here once so that the studentized-scale arguments do not each
repeat it. -/

/-- **Chebyshev for a block average against the population mean.** Under a uniform random
permutation, the fraction of permutations whose block average of `c` deviates from
`c̄ = N⁻¹ ∑ c` by `ε` is at most `ε⁻² (1/m) (N⁻¹ ∑ (c - c̄)²)` — the population dispersion
divided by the block size, exactly as for sampling with replacement, the finite-population
correction having been discarded. -/
theorem perm_avg_indicator_blockAvg_sub_mean_le {N m : ℕ}
    -- USER-INPUT: a nonempty block (the average divides by `m`)
    (hm : 0 < m)
    -- USER-INPUT: at least two items (the factor `N - 1` is a denominator upstream)
    (hN : 2 ≤ N)
    -- USER-INPUT: the block is a set of `m` distinct positions
    (a : Fin m → Fin N) (ha : Function.Injective a) (c : Fin N → ℝ) {ε : ℝ}
    -- USER-INPUT: a positive deviation
    (hε : 0 < ε) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          (if ε ≤ |(m : ℝ)⁻¹ * (∑ i, c (σ (a i))) - (N : ℝ)⁻¹ * ∑ l, c l|
            then (1 : ℝ) else 0)
      ≤ ε⁻¹ ^ 2 * ((m : ℝ)⁻¹ *
          ((N : ℝ)⁻¹ * ∑ l, (c l - (N : ℝ)⁻¹ * ∑ l', c l') ^ 2)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  have hd : ∑ l, (c l - (N : ℝ)⁻¹ * ∑ l', c l') = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul, sub_self]
  have hshift : ∀ σ : Equiv.Perm (Fin N),
      (m : ℝ)⁻¹ * ∑ i, (c (σ (a i)) - (N : ℝ)⁻¹ * ∑ l', c l')
        = (m : ℝ)⁻¹ * (∑ i, c (σ (a i))) - (N : ℝ)⁻¹ * ∑ l, c l := by
    intro σ
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hmR.ne', one_mul]
  have h := perm_avg_indicator_blockAvg_le hm hN a ha
    (fun l => c l - (N : ℝ)⁻¹ * ∑ l', c l') hd hε
  simp only [hshift] at h
  exact h

/-- The same bound for the *inverse* convention `x ∘ σ⁻¹`, which is how the randomization
action of `Randomization/TwoSamplePermutation` relabels coordinates. -/
theorem perm_avg_indicator_blockAvg_inv_sub_mean_le {N m : ℕ} (hm : 0 < m) (hN : 2 ≤ N)
    (a : Fin m → Fin N) (ha : Function.Injective a) (c : Fin N → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin N),
          (if ε ≤ |(m : ℝ)⁻¹ * (∑ i, c (σ⁻¹ (a i))) - (N : ℝ)⁻¹ * ∑ l, c l|
            then (1 : ℝ) else 0)
      ≤ ε⁻¹ ^ 2 * ((m : ℝ)⁻¹ *
          ((N : ℝ)⁻¹ * ∑ l, (c l - (N : ℝ)⁻¹ * ∑ l', c l') ^ 2)) := by
  rw [sum_perm_inv (G := Equiv.Perm (Fin N))
    (f := fun σ : Equiv.Perm (Fin N) =>
      if ε ≤ |(m : ℝ)⁻¹ * (∑ i, c (σ (a i))) - (N : ℝ)⁻¹ * ∑ l, c l| then (1 : ℝ) else 0)]
  exact perm_avg_indicator_blockAvg_sub_mean_le hm hN a ha c hε

/-! ### From permutation averages to randomization probabilities

The bounds above are pointwise in the data: they control the group average of an *indicator*
at a fixed data vector. The hypotheses consumed by the randomization theory
(`TendstoInProbRandomized`, and the `hrem` hypotheses of the Slutsky transfers) are group
averages of *probabilities*. The two are exchanged by Fubini for a finite group, which is
the following identity — the only step needed to turn `perm_avg_indicator_blockAvg_..._le`
into a statement about the data law. -/

/-- **Fubini for a finite group average of deviation probabilities.** The group average of
`P{ε ≤ A g}` is the `P`-integral of the group average of the indicators. Only measurability
of each `A g` is required; the group being finite, the sum is a finite one and no product
measure is involved. -/
theorem avg_measureReal_eq_integral_avg_indicator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (P : Measure 𝓨) [IsProbabilityMeasure P] {G : Type*} [Fintype G]
    (A : G → 𝓨 → ℝ) (hA : ∀ g, Measurable (A g)) (ε : ℝ) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, P.real {x | ε ≤ A g x}
      = ∫ x, (Fintype.card G : ℝ)⁻¹ * ∑ g : G, (if ε ≤ A g x then (1 : ℝ) else 0) ∂P := by
  classical
  have hset : ∀ g : G, MeasurableSet {x : 𝓨 | ε ≤ A g x} :=
    fun g => measurableSet_le measurable_const (hA g)
  have hind : ∀ g : G, (fun x => if ε ≤ A g x then (1 : ℝ) else 0)
      = Set.indicator {x | ε ≤ A g x} 1 := by
    intro g; funext x; simp [Set.indicator_apply]
  have hint : ∀ g : G, Integrable (fun x => if ε ≤ A g x then (1 : ℝ) else 0) P := by
    intro g
    rw [hind g]
    exact (integrable_const (1 : ℝ)).indicator (hset g)
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun g _ => hint g)]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hind g, integral_indicator_one (hset g)]

/-! ### The exchangeable pair of Stein's method

The modern proof of the combinatorial CLT builds an **exchangeable pair** out of a single
elementary move: pick one sampled position and one unsampled position uniformly at random and
interchange them. The three facts that Stein's method consumes — the increment formula, the
exchangeability, and the exact linearity of the conditional drift — are proved here; they are
all purely combinatorial, and together they instantiate the abstract engine
`ForMathlib/SteinMethod.abs_avg_sub_le` at `Ω = Equiv.Perm (Fin N)` and
`K = SwapIndex a`. -/

section SwapPair

variable {N m : ℕ}

/-- The set of **sampled positions** of a block `a`. -/
def blockSet (a : Fin m → Fin N) : Finset (Fin N) := Finset.image a Finset.univ

/-- A sum over the sampled *set* is a sum over the block *index*, the block being injective. -/
theorem sum_blockSet (a : Fin m → Fin N) (ha : Function.Injective a) (g : Fin N → ℝ) :
    ∑ p ∈ blockSet a, g p = ∑ i, g (a i) := by
  classical
  rw [blockSet, Finset.sum_image fun i _ j _ hij => ha hij]

/-- The sampled set has exactly `m` elements. -/
theorem card_blockSet (a : Fin m → Fin N) (ha : Function.Injective a) :
    (blockSet a).card = m := by
  classical
  rw [blockSet, Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]

/-- The **swap index**: an ordered pair consisting of one sampled and one unsampled position.
Interchanging the two is the elementary move that generates the exchangeable pair. There are
exactly `m (N - m)` of them. -/
abbrev SwapIndex (a : Fin m → Fin N) : Type :=
  {p : Fin N // p ∈ blockSet a} × {q : Fin N // q ∈ (blockSet a)ᶜ}

/-- The number of elementary swaps is `m (N - m)`. -/
theorem card_swapIndex (a : Fin m → Fin N) (ha : Function.Injective a) :
    Fintype.card (SwapIndex a) = m * (N - m) := by
  classical
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, Finset.card_compl,
    card_blockSet a ha, Fintype.card_fin]

/-- The **standardized block sum**, as a function on the acting group: `u` is the reciprocal
of the standardizing scale. -/
noncomputable def stdBlockSum (a : Fin m → Fin N) (d : Fin N → ℝ) (u : ℝ)
    (σ : Equiv.Perm (Fin N)) : ℝ := u * ∑ r ∈ blockSet a, d (σ r)

/-- The second coordinate of the exchangeable pair: the standardized block sum after the
elementary swap `k` has been applied to the positions. -/
noncomputable def stdBlockSumSwap (a : Fin m → Fin N) (d : Fin N → ℝ) (u : ℝ)
    (σ : Equiv.Perm (Fin N)) (k : SwapIndex a) : ℝ :=
  stdBlockSum a d u (σ * Equiv.swap k.1.1 k.2.1)

/-- **The elementary swap moves exactly one summand.** Interchanging a sampled position `p`
with an unsampled position `q` removes `d(σ p)` from the block sum and inserts `d(σ q)`. -/
theorem sum_blockSet_mul_swap (a : Fin m → Fin N) (d : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    {p q : Fin N} (hp : p ∈ blockSet a) (hq : q ∈ (blockSet a)ᶜ) :
    ∑ r ∈ blockSet a, d ((σ * Equiv.swap p q) r)
      = (∑ r ∈ blockSet a, d (σ r)) - d (σ p) + d (σ q) := by
  classical
  rw [Finset.mem_compl] at hq
  rw [← Finset.add_sum_erase _ (fun r => d ((σ * Equiv.swap p q) r)) hp,
    ← Finset.add_sum_erase _ (fun r => d (σ r)) hp]
  have h1 : d ((σ * Equiv.swap p q) p) = d (σ q) := by
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have h2 : ∀ r ∈ (blockSet a).erase p, d ((σ * Equiv.swap p q) r) = d (σ r) := by
    intro r hr
    have hrp : r ≠ p := (Finset.mem_erase.1 hr).1
    have hrq : r ≠ q := fun hcon => hq (hcon ▸ (Finset.mem_erase.1 hr).2)
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hrp hrq]
  rw [h1, Finset.sum_congr rfl h2]
  ring

/-- **The increment of the exchangeable pair.** -/
theorem stdBlockSumSwap_sub (a : Fin m → Fin N) (d : Fin N → ℝ) (u : ℝ)
    (σ : Equiv.Perm (Fin N)) (k : SwapIndex a) :
    stdBlockSumSwap a d u σ k - stdBlockSum a d u σ = u * (d (σ k.2.1) - d (σ k.1.1)) := by
  rw [stdBlockSumSwap, stdBlockSum, stdBlockSum, sum_blockSet_mul_swap a d σ k.1.2 k.2.2]
  ring

/-- **Exchangeability of the swap pair.** For every test function `F` of two variables the
total sum over the group and the swap index is unchanged when the two coordinates of the pair
are interchanged. The proof is a reindexing of the group by right multiplication with the
transposition, which is an involution: `(σ s) s = σ`. -/
theorem sum_swap_exchangeable (a : Fin m → Fin N) (d : Fin N → ℝ) (u : ℝ) (F : ℝ → ℝ → ℝ) :
    ∑ σ : Equiv.Perm (Fin N), ∑ k : SwapIndex a,
        F (stdBlockSum a d u σ) (stdBlockSumSwap a d u σ k)
      = ∑ σ : Equiv.Perm (Fin N), ∑ k : SwapIndex a,
        F (stdBlockSumSwap a d u σ k) (stdBlockSum a d u σ) := by
  classical
  have main : ∀ k : SwapIndex a,
      ∑ σ : Equiv.Perm (Fin N), F (stdBlockSum a d u σ) (stdBlockSumSwap a d u σ k)
        = ∑ σ : Equiv.Perm (Fin N), F (stdBlockSumSwap a d u σ k) (stdBlockSum a d u σ) := by
    intro k
    set s : Equiv.Perm (Fin N) := Equiv.swap k.1.1 k.2.1 with hs
    have hss : s * s = 1 := Equiv.swap_mul_self _ _
    have key := Equiv.sum_comp (Equiv.mulRight s)
      (fun σ : Equiv.Perm (Fin N) =>
        F (stdBlockSum a d u σ) (stdBlockSum a d u (σ * s)))
    simp only [Equiv.coe_mulRight, mul_assoc, hss, mul_one] at key
    exact key.symm
  calc ∑ σ : Equiv.Perm (Fin N), ∑ k : SwapIndex a,
          F (stdBlockSum a d u σ) (stdBlockSumSwap a d u σ k)
      = ∑ k : SwapIndex a, ∑ σ : Equiv.Perm (Fin N),
          F (stdBlockSum a d u σ) (stdBlockSumSwap a d u σ k) := Finset.sum_comm
    _ = ∑ k : SwapIndex a, ∑ σ : Equiv.Perm (Fin N),
          F (stdBlockSumSwap a d u σ k) (stdBlockSum a d u σ) :=
        Finset.sum_congr rfl fun k _ => main k
    _ = _ := Finset.sum_comm

/-- **The linearity condition, exactly.** For a *centred* population the conditional drift of
the swap pair is proportional to the current value:
`∑ₖ (W' σ k − W σ) = -N · W σ`, i.e. `𝔼[W' − W ∣ σ] = -λ W σ` with

`λ = N / (m (N − m))`,

since there are `m (N − m)` elementary swaps. (The wave-6 status note of
`tendsto_perm_cdf_blockSum` recorded `λ = 1/(m(N-m))`; the correct value carries the extra
factor `N`, as the computation below shows.) -/
theorem sum_swapIndex_increment (a : Fin m → Fin N) (ha : Function.Injective a)
    (d : Fin N → ℝ) (hd : ∑ l, d l = 0) (u : ℝ) (σ : Equiv.Perm (Fin N)) :
    ∑ k : SwapIndex a, (stdBlockSumSwap a d u σ k - stdBlockSum a d u σ)
      = -(N : ℝ) * stdBlockSum a d u σ := by
  classical
  have hmN : m ≤ N := by
    have := card_blockSet a ha ▸ Finset.card_le_univ (blockSet a)
    simpa using this
  have htot : ∑ r : Fin N, d (σ r) = 0 := by rw [Equiv.sum_comp σ d]; exact hd
  have hsplit := Finset.sum_add_sum_compl (blockSet a) (fun r => d (σ r))
  have hcompl : ∑ r ∈ (blockSet a)ᶜ, d (σ r) = -∑ r ∈ blockSet a, d (σ r) := by
    rw [htot] at hsplit; linarith
  have hcardc : ((blockSet a)ᶜ.card : ℝ) = (N : ℝ) - m := by
    rw [Finset.card_compl, card_blockSet a ha, Fintype.card_fin,
      Nat.cast_sub hmN]
  rw [Finset.sum_congr rfl fun k _ => stdBlockSumSwap_sub a d u σ k, Fintype.sum_prod_type]
  have hinner : ∀ p : {p : Fin N // p ∈ blockSet a},
      ∑ q : {q : Fin N // q ∈ (blockSet a)ᶜ}, u * (d (σ q.1) - d (σ p.1))
        = u * (-∑ r ∈ blockSet a, d (σ r)) - ((N : ℝ) - m) * (u * d (σ p.1)) := by
    intro p
    have hdist : ∀ q : {q : Fin N // q ∈ (blockSet a)ᶜ},
        u * (d (σ q.1) - d (σ p.1)) = u * d (σ q.1) - u * d (σ p.1) := fun q => by ring
    rw [Finset.sum_congr rfl fun q _ => hdist q, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, hcardc, ← Finset.mul_sum,
      Finset.sum_coe_sort (blockSet a)ᶜ (fun r => d (σ r)), hcompl]
  rw [Finset.sum_congr rfl fun p _ => hinner p, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, card_blockSet a ha, nsmul_eq_mul]
  have hlast : ∑ p : {p : Fin N // p ∈ blockSet a}, ((N : ℝ) - m) * (u * d (σ p.1))
      = ((N : ℝ) - m) * (u * ∑ r ∈ blockSet a, d (σ r)) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_coe_sort (blockSet a) (fun r => d (σ r))]
  rw [hlast, stdBlockSum]
  ring

/-- The linearity condition in the exact shape consumed by
`ForMathlib/SteinMethod.abs_avg_sub_le`, with `λ = N / (m (N − m))`. -/
theorem sum_swapIndex_increment' (a : Fin m → Fin N) (ha : Function.Injective a)
    (hm : 0 < m) (hmN : m < N) (d : Fin N → ℝ) (hd : ∑ l, d l = 0) (u : ℝ)
    (σ : Equiv.Perm (Fin N)) :
    ∑ k : SwapIndex a, (stdBlockSumSwap a d u σ k - stdBlockSum a d u σ)
      = -((N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) * (Fintype.card (SwapIndex a) : ℝ)
          * stdBlockSum a d u σ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNmR : (0 : ℝ) < (N : ℝ) - m := by
    have : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmN
    linarith
  rw [sum_swapIndex_increment a ha d hd u σ, card_swapIndex a ha,
    Nat.cast_mul, Nat.cast_sub hmN.le]
  field_simp

end SwapPair

/-! ### Standardization and the central limit theorem -/

/-- The asymptotic standard deviation `√(m(N-m)/N)` of a block sum drawn from a population
normalized by `N⁻¹ ∑ d² = 1`. The exact standard deviation of `avg_perm_blockSum_sq` differs
by the factor `√(N/(N-1) · N⁻¹ ∑ d²)`, which tends to `1` in the regime of
`tendsto_perm_cdf_blockSum`. -/
noncomputable def blockSumScale (N m : ℕ) : ℝ := Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / (N : ℝ))

/-- **The combinatorial central limit theorem, tested against Lipschitz functions** — the
core analytic brick. Under the hypotheses of `tendsto_perm_cdf_blockSum`, the group average
of `h` evaluated at the standardized block sum converges to the standard normal expectation
of `h`, for every bounded Lipschitz `h`.

STATUS (wave 7): OPEN, but no longer a bare statement — the whole apparatus it needs now
exists in the repository and the *combinatorial* half of the proof is proved. Route (Stein's
method for exchangeable pairs, `ForMathlib/SteinMethod`):

* the engine `SteinMethod.abs_avg_sub_le` bounds `|avg h(W) − 𝔼h(Z)|` by
  `B₁ · avg|1 − V/(2λ)| + B₂/(4λ) · avg|W' − W|³` for any exchangeable pair with
  `𝔼[W' − W ∣ σ] = -λ W`, where `B₁` bounds `f_h'` and `B₂` is a Lipschitz constant for
  `f_h'`; it is PROVED;
* the pair itself is the swap pair of the section above: `Ω = Equiv.Perm (Fin (N k))`,
  `K = SwapIndex (a k)`, `W = stdBlockSum`, `W' = stdBlockSumSwap`. Exchangeability
  (`sum_swap_exchangeable`) and the linearity condition with `λ = N/(m(N−m))`
  (`sum_swapIndex_increment'`) are PROVED;
* what is left is (i) the three classical bounds on the Stein solution
  (`SteinMethod.abs_steinSolution_le`, `abs_deriv_steinSolution_le`,
  `lipschitz_deriv_steinSolution`, all sorried there), and (ii) the two moment estimates for
  this particular pair, namely that both error terms vanish.

WARNING on (ii). The third-moment term is **not** controlled by `hvar` and `hlind` alone:
`λ⁻¹ 𝔼|W' − W|³ ≍ N⁻¹∑|d|³ / √(m(N−m)/N)`, and a Lindeberg condition does not bound
`N⁻¹∑|d|³`. The classical proof therefore **truncates** the population at the Lindeberg
scale `ε√(min (m k) (N k − m k))` first: on the truncated part `N⁻¹∑|d|³ ≤
ε√(min(m,N−m))·N⁻¹∑d²`, which is `O(ε)` after dividing by the scale, and the discarded part
is `o(1)` in probability by `hlind` together with the Chebyshev brick
`perm_avg_indicator_blockAvg_le`. Any future attempt that states an untruncated
third-moment brick will be stating something FALSE; this is recorded here so that the trap
is not walked into twice. The variance-regression term `avg|1 − V/(2λ)|` is a genuine
fourth-moment computation: with `A₂ σ = ∑_{p ∈ blockSet a} d(σ p)²` one has, exactly,
`∑ₖ (W' σ k − W σ)² = u² (m ∑ d² + (N − 2m) A₂ σ + 2 (u⁻¹ W σ)²)`, so the term is small as
soon as `A₂` concentrates at its mean `(m/N)∑d²` — again after truncation. -/
theorem tendsto_perm_avg_lipschitz {N m : ℕ → ℕ}
    -- USER-INPUT: at each stage the block is a set of `m k` distinct positions
    (a : ∀ k, Fin (m k) → Fin (N k)) (ha : ∀ k, Function.Injective (a k))
    -- USER-INPUT: the finite populations, centred
    (d : ∀ k, Fin (N k) → ℝ) (hcent : ∀ k, ∑ l, d k l = 0)
    -- USER-INPUT: both the block and its complement grow
    (hm : Tendsto (fun k => (m k : ℝ)) atTop atTop)
    (hNm : Tendsto (fun k => (N k : ℝ) - m k) atTop atTop)
    -- USER-INPUT: the populations are normalized in the second moment
    (hvar : Tendsto (fun k => (N k : ℝ)⁻¹ * ∑ l, d k l ^ 2) atTop (𝓝 1))
    -- USER-INPUT: Hájek's Lindeberg condition at scale `√(min (m k) (N k - m k))`
    (hlind : ∀ ε > (0 : ℝ), Tendsto (fun k => (N k : ℝ)⁻¹ *
        ∑ l, (if ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k)) ≤ |d k l|
              then d k l ^ 2 else 0)) atTop (𝓝 0))
    -- USER-INPUT: a bounded Lipschitz test function
    (h : ℝ → ℝ) {L C : ℝ} (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|)
    (hbdd : ∀ x, |h x| ≤ C) :
    Tendsto (fun k => (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (N k)),
          h ((blockSumScale (N k) (m k))⁻¹ * ∑ i, d k (σ (a k i))))
      atTop (𝓝 (stdGaussianExpect h)) := by
  sorry

/-- **The combinatorial central limit theorem** (Wald–Wolfowitz, Noether, Hoeffding,
Erdős–Rényi, Hájek). Let `d k` be a centred population on `Fin (N k)` with normalized second
moment tending to `1`, and let `a k` sample `m k` distinct positions. If both block sizes
`m k` and `N k - m k` tend to infinity and the populations satisfy Hájek's Lindeberg
condition at scale `√(min (m k) (N k - m k))`, then the block sum standardized by
`blockSumScale` is asymptotically standard normal — stated here in the group-average
c.d.f. form in which randomization distributions are defined.

STATUS (wave 7): DISCHARGED to the single core brick `tendsto_perm_avg_lipschitz` below —
the same theorem tested against *Lipschitz* functions instead of a half-line indicator. The
de-smoothing step performed here is the elementary one: the indicator of `Iic t` is squeezed
between two ramps of width `ε` (`ForMathlib/EsseenSmoothing.ramp`), the ramps are `ε⁻¹`-
Lipschitz and bounded by `1`, their Gaussian expectations bracket `Φ(t ∓ ε)`, and `Φ` is
1-Lipschitz (`ForMathlib/SteinMethod.lipschitzWith_cdf_gaussianReal`), hence continuous, so
letting `ε → 0` costs nothing. -/
theorem tendsto_perm_cdf_blockSum {N m : ℕ → ℕ}
    -- USER-INPUT: at each stage the block is a set of `m k` distinct positions
    (a : ∀ k, Fin (m k) → Fin (N k)) (ha : ∀ k, Function.Injective (a k))
    -- USER-INPUT: the finite populations
    (d : ∀ k, Fin (N k) → ℝ)
    -- USER-INPUT: each population is centred
    (hcent : ∀ k, ∑ l, d k l = 0)
    -- USER-INPUT: both the block and its complement grow
    (hm : Tendsto (fun k => (m k : ℝ)) atTop atTop)
    (hNm : Tendsto (fun k => (N k : ℝ) - m k) atTop atTop)
    -- USER-INPUT: the populations are normalized in the second moment
    (hvar : Tendsto (fun k => (N k : ℝ)⁻¹ * ∑ l, d k l ^ 2) atTop (𝓝 1))
    -- USER-INPUT: Hájek's Lindeberg condition at scale `√(min (m k) (N k - m k))`
    (hlind : ∀ ε > (0 : ℝ), Tendsto (fun k => (N k : ℝ)⁻¹ *
        ∑ l, (if ε * Real.sqrt (min (m k : ℝ) ((N k : ℝ) - m k)) ≤ |d k l|
              then d k l ^ 2 else 0)) atTop (𝓝 0))
    (t : ℝ) :
    Tendsto (fun k => (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm (Fin (N k)),
          (if ∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k) then (1 : ℝ) else 0))
      atTop (𝓝 (cdf (gaussianReal 0 1) t)) := by
  classical
  have hcont : ContinuousAt (fun s : ℝ => cdf (gaussianReal 0 1) s) t :=
    lipschitzWith_cdf_gaussianReal.continuous.continuousAt
  refine tendsto_of_squeeze_continuousAt hcont ?_
  intro ε hε
  -- the two ramp test functions: `ε⁻¹`-Lipschitz and bounded by `1`
  have hrbdd : ∀ (u : ℝ) (x : ℝ), |ramp u ε x| ≤ 1 := fun u x => by
    rw [abs_of_nonneg (ramp_nonneg u ε x)]; exact ramp_le_one u ε x
  have hU := tendsto_perm_avg_lipschitz a ha d hcent hm hNm hvar hlind (ramp t ε)
    (fun x y => abs_ramp_sub_ramp_le hε x y) (hrbdd t)
  have hL := tendsto_perm_avg_lipschitz a ha d hcent hm hNm hvar hlind (ramp (t - ε) ε)
    (fun x y => abs_ramp_sub_ramp_le hε x y) (hrbdd (t - ε))
  -- the Gaussian expectations of the two ramps bracket the limit c.d.f.
  have hUb : stdGaussianExpect (ramp t ε) ≤ cdf (gaussianReal 0 1) (t + ε) := by
    have hb := integral_ramp_le_measure_Iic (gaussianReal 0 1) hε t
    rw [stdGaussianExpect, cdf_eq_real, measureReal_def]
    exact hb
  have hLb : cdf (gaussianReal 0 1) (t - ε) ≤ stdGaussianExpect (ramp (t - ε) ε) := by
    have hb := measure_Iic_le_integral_ramp (gaussianReal 0 1) hε (t - ε)
    rw [stdGaussianExpect, cdf_eq_real, measureReal_def]
    exact hb
  -- the standardizing scale is eventually positive, and then the indicator is squeezed
  have hscale : ∀ᶠ k in atTop, 0 < blockSumScale (N k) (m k) := by
    filter_upwards [hm.eventually_gt_atTop 0, hNm.eventually_gt_atTop 0] with k h1 h2
    have hN : (0 : ℝ) < (N k : ℝ) := by linarith
    rw [blockSumScale, Real.sqrt_pos]
    exact div_pos (mul_pos h1 h2) hN
  have hsq : ∀ᶠ k in atTop,
      ((Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (N k)),
          ramp (t - ε) ε ((blockSumScale (N k) (m k))⁻¹ * ∑ i, d k (σ (a k i)))
        ≤ (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (N k)),
            (if ∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k) then (1 : ℝ) else 0))
      ∧ ((Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (N k)),
            (if ∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k) then (1 : ℝ) else 0)
          ≤ (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin (N k)),
              ramp t ε ((blockSumScale (N k) (m k))⁻¹ * ∑ i, d k (σ (a k i)))) := by
    filter_upwards [hscale] with k hk
    have hiff : ∀ σ : Equiv.Perm (Fin (N k)),
        (∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k))
          ↔ (blockSumScale (N k) (m k))⁻¹ * (∑ i, d k (σ (a k i))) ≤ t := by
      intro σ
      rw [inv_mul_le_iff₀ hk, mul_comm]
    have hcinv : (0 : ℝ) ≤ (Fintype.card (Equiv.Perm (Fin (N k))) : ℝ)⁻¹ :=
      inv_nonneg.2 (Nat.cast_nonneg _)
    constructor
    · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) hcinv
      by_cases hσ : ∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k)
      · rw [if_pos hσ]; exact ramp_le_one _ _ _
      · rw [if_neg hσ]
        refine le_of_eq (ramp_eq_zero_of_le hε ?_)
        have hnot : ¬ ((blockSumScale (N k) (m k))⁻¹ * (∑ i, d k (σ (a k i))) ≤ t) :=
          fun hcon => hσ ((hiff σ).2 hcon)
        rw [not_le] at hnot
        linarith
    · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) hcinv
      by_cases hσ : ∑ i, d k (σ (a k i)) ≤ t * blockSumScale (N k) (m k)
      · rw [if_pos hσ, ramp_eq_one_of_le hε ((hiff σ).1 hσ)]
      · rw [if_neg hσ]; exact ramp_nonneg _ _ _
  -- close the squeeze
  filter_upwards [hsq, Metric.tendsto_nhds.1 hU ε hε, Metric.tendsto_nhds.1 hL ε hε]
    with k hk hUk hLk
  rw [Real.dist_eq, abs_lt] at hUk hLk
  exact ⟨by linarith [hk.1, hLk.1], by linarith [hk.2, hUk.2]⟩

end StatLean.HypothesisTesting
