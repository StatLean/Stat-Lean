import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators

/-!
# Moments of sampling without replacement

A two-sample split assigns `m` of `n` labelled items to the first group, all
`binom(n, m)` splits being equally likely. Writing `Wᵢ = 1{i is in the first group}`, the
weights are exchangeable Bernoulli`(m/n)` variables that are *negatively correlated* — the
constraint `∑ᵢ Wᵢ = m` makes them dependent — and every linear statistic of a two-sample
permutation test is of the form `∑ᵢ cᵢ Wᵢ` for a deterministic vector `c` built from the
pooled data. Its first two moments are therefore the arithmetic backbone of permutation
inference, and this file records them:
$$\mathbb E W_i = \frac{m}{n}, \qquad
  \mathbb E W_i W_j = \frac{m(m-1)}{n(n-1)}\ (i \ne j), \qquad
  \operatorname{Cov}(W_i, W_j) = -\frac{m(n-m)}{n^2 (n-1)} ,$$
$$\operatorname{Var}\Bigl(\sum_i c_i W_i\Bigr)
  = \frac{m(n-m)}{n(n-1)} \sum_i (c_i - \bar c)^2 ,$$
from which the group average `m⁻¹ ∑ᵢ cᵢ Wᵢ` has variance of order `1/m` times the
population dispersion of `c` — the estimate that drives the permutation central limit
theorem.

## Main results

* `SubsetsOfCard`, `weight`, `expect` — the sampling space and the uniform average.
* `expect_eq_sum_uniform` — `expect` is the expectation under the uniform law on splits.
* `expect_weight`, `expect_weight_pair`, `cov_weight` — the first and second moments.
* `var_linear` — the exact variance of a linear statistic.
* `var_mean_linear_le` — the `O(1/m)` bound on the variance of the group average.

**Reference.** Classical sampling theory; original sources in the bibliographic comments
below.

**Proof formalization notes.**
* Randomness is carried by the **finite-set** model: the sample space is the subtype
  `SubsetsOfCard n m = {s : Finset (Fin n) // s.card = m}` of `m`-element subsets, uniformly
  weighted. This is the form in which the moments are cleanest — every identity is a
  counting statement about how many `m`-subsets contain a given index or pair of indices —
  and it avoids the bookkeeping of the equivalent "random permutation of `Fin n`, take the
  first `m`" model.
* The uniform law is available both as a probability mass function
  (`sampleUnif = PMF.uniformOfFintype`, the least-friction Mathlib carrier: it needs no
  σ-algebra on the subtype, unlike `Measure.count` normalisation) and, for computations, as
  the normalised counting average `expect`. `expect_eq_sum_uniform` is the bridge; all
  moment statements are phrased with `expect`, so that no `Nonempty` instance argument
  pollutes them.
* Edge behaviour of `expect`: when `m > n` the sample space is empty, `Fintype.card = 0`,
  and `expect f = 0` for every `f` (Lean's `(0 : ℝ)⁻¹ = 0`). Statements that would be false
  there carry `m ≤ n`.
* Subtraction is performed in `ℝ`, never in `ℕ`: `(m : ℝ) - 1` and `(n : ℝ) - m` are the
  intended quantities, and truncated natural subtraction would silently change the
  identities at `m = 0`.
* Side conditions are kept minimal: `0 < n` is *not* assumed in `expect_weight` (an
  argument `i : Fin n` already provides it), and `2 ≤ n` is not assumed in
  `expect_weight_pair` (two distinct indices in `Fin n` already provide it). It is assumed
  in `var_linear`, where nothing else rules out the vacuous `n ≤ 1` case in which the factor
  `(n - 1)` in the denominator vanishes.
* `var_mean_linear_le` states the bound with the explicit constant `2`, obtained from the
  exact identity by `(n - m)/(n - 1) ≤ 2` for `n ≥ 2`; no attempt is made to keep the sharp
  finite-population correction factor, since consumers only need the `O(1/m)` rate.

**Bibliographic comments.** The permutation/randomization model in which these moments are
computed goes back to R. A. Fisher, *The Design of Experiments*, Oliver & Boyd, 1935, and
E. J. G. Pitman, "Significance tests which may be applied to samples from any populations,"
*Suppl. J. Roy. Statist. Soc.* **4** (1937), 119–130. The moment calculations and the
combinatorial central limit theorem they support are due to A. Wald and J. Wolfowitz,
"Statistical tests based on permutations of the observations," *Ann. Math. Statist.* **15**
(1944), 358–372, and W. Hoeffding, "A combinatorial central limit theorem," *Ann. Math.
Statist.* **22** (1951), 558–566, and "The large-sample power of tests based on permutations
of observations," *Ann. Math. Statist.* **23** (1952), 169–192.
-/

open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

/-- The sample space of a two-sample split: the `m`-element subsets of `Fin n`, i.e. the
possible first groups. Empty when `m > n`. -/
abbrev SubsetsOfCard (n m : ℕ) := {s : Finset (Fin n) // s.card = m}

/-- The **inclusion weight** of item `i` in the split `s`: `1` if `i` lands in the first
group, `0` otherwise. -/
def weight {n m : ℕ} (i : Fin n) (s : SubsetsOfCard n m) : ℝ :=
  if i ∈ s.val then 1 else 0

/-- The **uniform average** over all `m`-element splits — the expectation under the uniform
law on `SubsetsOfCard n m`.

Edge behaviour: when the sample space is empty (`m > n`) the cardinality is `0` and the
value is `0`. -/
noncomputable def expect {n m : ℕ} (f : SubsetsOfCard n m → ℝ) : ℝ :=
  (Fintype.card (SubsetsOfCard n m) : ℝ)⁻¹ * ∑ s, f s

/-- The **uniform law on splits** as a probability mass function; the probabilistic carrier
behind `expect`. Requires the split to exist (`m ≤ n`), which is what the `Nonempty`
instance argument records. -/
noncomputable def sampleUnif (n m : ℕ) [Nonempty (SubsetsOfCard n m)] :
    PMF (SubsetsOfCard n m) :=
  PMF.uniformOfFintype (SubsetsOfCard n m)

/-- `expect` is the expectation under the uniform law on splits: each of the
`binom(n, m)` splits carries mass `binom(n, m)⁻¹`. -/
lemma expect_eq_sum_uniform {n m : ℕ} [Nonempty (SubsetsOfCard n m)]
    (f : SubsetsOfCard n m → ℝ) :
    expect f = ∑ s, (sampleUnif n m s).toReal * f s := by
  sorry

/-- **First moment**: `E Wᵢ = m/n`. Counting: the `m`-subsets containing a fixed index are
`binom(n-1, m-1)` out of `binom(n, m)`. -/
theorem expect_weight {n m : ℕ}
    -- USER-INPUT: the split exists (for `m > n` the sample space is empty).
    (hm : m ≤ n) (i : Fin n) :
    expect (fun s : SubsetsOfCard n m => weight i s) = (m : ℝ) / n := by
  sorry

/-- **Second cross moment**: for `i ≠ j`, `E WᵢWⱼ = m(m-1)/(n(n-1))`. Counting: the
`m`-subsets containing two fixed indices are `binom(n-2, m-2)` out of `binom(n, m)`. -/
theorem expect_weight_pair {n m : ℕ}
    -- USER-INPUT: the split exists.
    (hm : m ≤ n) {i j : Fin n}
    -- USER-INPUT: two distinct items (this already forces `2 ≤ n`).
    (hij : i ≠ j) :
    expect (fun s : SubsetsOfCard n m => weight i s * weight j s)
      = ((m : ℝ) * ((m : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
  sorry

/-- **Negative correlation**: for `i ≠ j`,
`Cov(Wᵢ, Wⱼ) = −m(n−m)/(n²(n−1))`.
Immediate from `expect_weight` and `expect_weight_pair`; the sign reflects the constraint
`∑ᵢ Wᵢ = m`. -/
theorem cov_weight {n m : ℕ}
    -- USER-INPUT: the split exists.
    (hm : m ≤ n) {i j : Fin n}
    -- USER-INPUT: two distinct items.
    (hij : i ≠ j) :
    expect (fun s : SubsetsOfCard n m => weight i s * weight j s)
        - expect (fun s : SubsetsOfCard n m => weight i s)
          * expect (fun s : SubsetsOfCard n m => weight j s)
      = -((m : ℝ) * ((n : ℝ) - m)) / ((n : ℝ) ^ 2 * ((n : ℝ) - 1)) := by
  sorry

/-- **Exact variance of a linear statistic.** For deterministic coefficients `c` with mean
`c̄ = n⁻¹ ∑ᵢ cᵢ`,
$$\operatorname{Var}\Bigl(\sum_i c_i W_i\Bigr)
  = \frac{m(n-m)}{n(n-1)} \sum_i (c_i - \bar c)^2 .$$
Expanding the square and substituting the variance `p(1-p)` on the diagonal and
`cov_weight` off it; the cross terms reassemble into the centred sum of squares. Both
degenerate splits `m = 0` and `m = n` give variance `0`, as they must. -/
theorem var_linear {n m : ℕ}
    -- USER-INPUT: the split exists.
    (hm : m ≤ n)
    -- USER-INPUT: at least two items (the factor `n - 1` is a denominator).
    (hn : 2 ≤ n) (c : Fin n → ℝ) :
    expect (fun s : SubsetsOfCard n m =>
        ((∑ i, c i * weight i s)
          - expect (fun s' : SubsetsOfCard n m => ∑ i, c i * weight i s')) ^ 2)
      = ((m : ℝ) * ((n : ℝ) - m)) / ((n : ℝ) * ((n : ℝ) - 1))
          * ∑ i, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2 := by
  sorry

/-- **`O(1/m)` variance bound for the group average.** With `s²_n = n⁻¹ ∑ᵢ (cᵢ - c̄)²` the
population dispersion of the coefficients,
$$\operatorname{Var}\Bigl(\frac 1m \sum_i c_i W_i\Bigr) \;\le\; \frac{2}{m}\, s^2_n .$$
From `var_linear`, since the finite-population factor `(n-m)/(n-1)` is at most `2` once
`n ≥ 2`. This is the form consumed by the permutation central limit theorem, where `s²_n`
stays bounded and the bound drives the negligibility of individual summands. -/
theorem var_mean_linear_le {n m : ℕ}
    -- USER-INPUT: a nonempty first group (the average divides by `m`).
    (hm0 : 0 < m)
    -- USER-INPUT: the split exists.
    (hm : m ≤ n)
    -- USER-INPUT: at least two items.
    (hn : 2 ≤ n) (c : Fin n → ℝ) :
    expect (fun s : SubsetsOfCard n m =>
        ((m : ℝ)⁻¹ * ((∑ i, c i * weight i s)
          - expect (fun s' : SubsetsOfCard n m => ∑ i, c i * weight i s'))) ^ 2)
      ≤ (2 / m) * ((n : ℝ)⁻¹ * ∑ i, (c i - (n : ℝ)⁻¹ * ∑ j, c j) ^ 2) := by
  sorry

end StatLean.HypothesisTesting
