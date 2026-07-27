import StatLean.HypothesisTesting.ForMathlib.PermutationMarginals
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
* `tendsto_perm_cdf_blockSum` — **the combinatorial central limit theorem** (open; see the
  status note at the statement).

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

/-! ### Standardization and the central limit theorem -/

/-- The asymptotic standard deviation `√(m(N-m)/N)` of a block sum drawn from a population
normalized by `N⁻¹ ∑ d² = 1`. The exact standard deviation of `avg_perm_blockSum_sq` differs
by the factor `√(N/(N-1) · N⁻¹ ∑ d²)`, which tends to `1` in the regime of
`tendsto_perm_cdf_blockSum`. -/
noncomputable def blockSumScale (N m : ℕ) : ℝ := Real.sqrt ((m : ℝ) * ((N : ℝ) - m) / (N : ℝ))

/-- **The combinatorial central limit theorem** (Wald–Wolfowitz, Noether, Hoeffding,
Erdős–Rényi, Hájek). Let `d k` be a centred population on `Fin (N k)` with normalized second
moment tending to `1`, and let `a k` sample `m k` distinct positions. If both block sizes
`m k` and `N k - m k` tend to infinity and the populations satisfy Hájek's Lindeberg
condition at scale `√(min (m k) (N k - m k))`, then the block sum standardized by
`blockSumScale` is asymptotically standard normal — stated here in the group-average
c.d.f. form in which randomization distributions are defined.

STATUS (wave 6): OPEN. This is the last deep analytic input of the two-sample permutation
chain; everything else in `Randomization/TwoSamplePermutation` and
`Randomization/Studentized` is reduced to it. Re-checked against Mathlib v4.29.1: there is no
combinatorial CLT, no Stein's-method/exchangeable-pairs machinery, and no finite-population
sampling limit theorem; `Mathlib.Probability.Distributions.Hypergeometric` does not exist.
The repository stops at the first two moments — the two theorems above and the sibling brick
`ForMathlib/HypergeometricMoments` — which is exactly the input the theorem *consumes*, not
the theorem.

The two routes, both genuinely long:
1. *Lindeberg swap on the conditional characteristic function.* The weights are indicators of
   sampling **without** replacement, hence dependent, so the average of `exp(i t Bσ)` is not
   an `N`-th power and the factorization that makes the sign-change engine
   (`Randomization/PairCLT.charFun_randPairLaw_signSum`) exact at every finite `N` is
   unavailable. What replaces it is Hájek's coupling: `(W₁, …, W_N)` conditioned on
   `∑ Wᵢ = m` has the law of i.i.d. `Bernoulli(m/N)` conditioned on the same event, so the
   conditional characteristic function is a *ratio* of two independent-sum characteristic
   functions, and a local limit theorem for the lattice variable `∑ Bᵢ` converts the
   conditioning into a Gaussian factor. The varying-exponent bricks
   `tendsto_one_add_pow_of_tendsto_nat_mul` and `tendsto_charFun_pow` of
   `Randomization/TwoSamplePermutation` are exactly the shape the independent-sum half needs;
   the missing half is the local limit theorem, which Mathlib does not have either.
2. *Stein's method for exchangeable pairs.* Swap one sampled index with one unsampled index
   to build the exchangeable pair; the linearity condition holds exactly with
   `λ = 1/(m(N-m))`. This is the standard modern proof and gives a Berry–Esseen rate, but it
   needs the whole Stein apparatus (solution of the Stein equation and its derivative bounds)
   which is likewise absent.

Neither route is blocked by a *false* statement or by a missing Mathlib API that cannot be
built; both are simply large. The statement is recorded here, with its exact hypotheses, so
that the consumers can be written against it. -/
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
  sorry

end StatLean.HypothesisTesting
