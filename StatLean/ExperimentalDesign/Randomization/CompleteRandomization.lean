import Mathlib.GroupTheory.Perm.Basic
import StatLean.ExperimentalDesign.Core.Design
import StatLean.ExperimentalDesign.ForMathlib.PMFExpectation

/-!
# The completely randomised design

Fix a replication pattern `r : T → ℕ` with `∑ₜ r t = N = |U|`.  The **completely
randomised design** draws an allocation uniformly at random from the allocations whose
arm sizes are exactly `r`:
$$\mathcal A_r = \{a : U → T \mid |\{i : a(i) = t\}| = r_t \ \forall t\}, \qquad
  D_r = \operatorname{Uniform}(\mathcal A_r).$$
This file constructs `D_r` and proves the exact first- and second-order assignment
probabilities of randomisation theory:
$$P(A_i = t) = \frac{r_t}{N}, \qquad
  P(A_i = t, A_j = t) = \frac{r_t (r_t - 1)}{N (N-1)}, \qquad
  P(A_i = t, A_j = s) = \frac{r_t\, r_s}{N (N-1)} \quad (s \ne t),$$
for distinct units `i ≠ j`, together with the indicator variance
`r_t (N − r_t) / N²` and the negative indicator covariance
`− r_t (N − r_t) / (N² (N−1))`.  These are the atomic ingredients of every exact
randomisation-based moment (arm means, randomization tests, Neyman-style causal
variance formulas).

## Main results

* `validAllocations`, `validAllocations_nonempty`, `completeRandomization` — the
  design.
* `mem_support_completeRandomization`, `card_arm_of_mem_validAllocations` — support.
* `completeRandomization_map_precomp` — permutation invariance (the randomisation
  symmetry).
* `expect_armIndicator` — first-order assignment probability `r_t / N`.
* `expect_armIndicator_pair_same`, `expect_armIndicator_pair_distinct` — second-order
  assignment probabilities.
* `var_armIndicator`, `cov_armIndicator_of_ne` — indicator variance and covariance.

**Reference.** R. Mead, *The Design of Experiments*, Cambridge University Press,
1988: the completely randomised design with replications `n₁, …, n_t`, §6.2; the
requirement that each unit be equally likely to receive each treatment and the
allocation probabilities `n_A/∑n, …, n_T/∑n`, §9.2 and §9.6; the indicator moment
calculus (`E δ`, `E δδ'` patterns), §9.4.  (`Mead §6.2`, `Mead §9.2`, `Mead §9.4`,
`Mead §9.6`.)

**Proof formalization notes.**
* Intended proof route for the moments — *symmetry, not counting*.  No cardinality of
  `𝒜_r` is ever computed:
  1. `completeRandomization_map_precomp`: precomposition with a permutation `σ` of the
     units is a bijection of `𝒜_r` (arms pull back along `σ`, preserving their sizes),
     and the pushforward of a uniform law under a bijection preserving its support
     finset is itself.
  2. Marginals: by (1) with a transposition, `E[χ_{t,i}]` is the same for all units
     `i`; summing `card_arm_eq_sum_indicator` over the support gives
     `∑_i E[χ_{t,i}] = r_t`, hence each equals `r_t / N`.
  3. Pairs: for fixed `i`, transpositions fixing `i` show `E[χ_{t,i} χ_{t,j}]` is the
     same for all `j ≠ i`; then
     `(N−1) E[χ_{t,i} χ_{t,j}] = E[χ_{t,i} (∑_{j ≠ i} χ_{t,j})]
        = E[χ_{t,i} (r_t − χ_{t,i})] = (r_t − 1) r_t / N`
     using idempotency of indicators on the support.  The distinct-treatment case is
     the same computation with `E[χ_{t,i} χ_{s,i}] = 0` (exclusivity).
* Degenerate denominators are vacuous: a hypothesis `i ≠ j` forces `N ≥ 2`, and a
  unit argument `i : U` forces `N ≥ 1`, so the real-division formulas never actually
  divide by zero.
* The variance/covariance forms follow from the pair probabilities by pure algebra
  via `pmfVar_eq_expect_sq_sub_sq` / `pmfCov_eq_expect_mul_sub_mul`.
-/

open scoped ENNReal

namespace StatLean.ExperimentalDesign

variable {U T : Type*} [Fintype U] [DecidableEq U] [Fintype T] [DecidableEq T]

/-- The **valid allocations** of the replication pattern `r`: allocations whose arm
sizes are exactly `r` (`Mead §6.2`). -/
def validAllocations (r : T → ℕ) : Finset (Allocation U T) :=
  Finset.univ.filter fun a => ∀ t, (arm t a).card = r t

theorem mem_validAllocations {r : T → ℕ} {a : Allocation U T} :
    a ∈ validAllocations (U := U) r ↔ ∀ t, (arm t a).card = r t := by
  sorry

/-- A replication pattern summing to the population size admits a valid allocation. -/
theorem validAllocations_nonempty (r : T → ℕ)
    -- USER-INPUT: the replications exhaust the units; Mead §6.2
    (hr : ∑ t, r t = Fintype.card U) :
    (validAllocations (U := U) r).Nonempty := by
  sorry

/-- The **completely randomised design** with replication pattern `r`: the uniform
distribution on the valid allocations (`Mead §6.2`, `Mead §9.2`). -/
noncomputable def completeRandomization (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) : RandomizationDesign U T :=
  PMF.uniformOfFinset (validAllocations r) (validAllocations_nonempty r hr)

theorem mem_support_completeRandomization {r : T → ℕ}
    {hr : ∑ t, r t = Fintype.card U} {a : Allocation U T} :
    a ∈ (completeRandomization r hr).support ↔ ∀ t, (arm t a).card = r t := by
  sorry

/-- On the support of the design, arm sizes are the prescribed replications. -/
theorem card_arm_of_mem_validAllocations {r : T → ℕ} {a : Allocation U T}
    (ha : a ∈ validAllocations (U := U) r) (t : T) :
    (arm t a).card = r t := by
  sorry

/-- Every replication is at most the population size. -/
theorem replication_le_card (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) (t : T) :
    r t ≤ Fintype.card U := by
  sorry

/-- **Randomisation symmetry**: the completely randomised design is invariant under
relabelling the units by any permutation (`Mead §9.2`: every unit is treated
symmetrically by the random allocation). -/
theorem completeRandomization_map_precomp (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) (σ : Equiv.Perm U) :
    (completeRandomization r hr).map (fun a => fun i => a (σ i))
      = completeRandomization r hr := by
  sorry

/-- **First-order assignment probability**: each unit receives treatment `t` with
probability `r_t / N` (`Mead §9.6`, allocation probabilities `n_A/∑n`). -/
theorem expect_armIndicator (r : T → ℕ) (hr : ∑ t, r t = Fintype.card U)
    (i : U) (t : T) :
    pmfExpect (completeRandomization r hr) (armIndicator t i)
      = (r t : ℝ) / (Fintype.card U : ℝ) := by
  sorry

/-- **Second-order assignment probability, same treatment**: distinct units both
receive `t` with probability `r_t (r_t − 1) / (N (N−1))` (`Mead §9.4`, the
`E[δ δ']` pattern). -/
theorem expect_armIndicator_pair_same (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) {i j : U}
    -- LEAN-ONLY: distinct units; the same-unit case is the idempotency identity
    (hij : i ≠ j) (t : T) :
    pmfExpect (completeRandomization r hr)
        (fun a => armIndicator t i a * armIndicator t j a)
      = (r t : ℝ) * ((r t : ℝ) - 1)
          / ((Fintype.card U : ℝ) * ((Fintype.card U : ℝ) - 1)) := by
  sorry

/-- **Second-order assignment probability, distinct treatments**: distinct units
receive `t` and `s ≠ t` with probability `r_t r_s / (N (N−1))` (`Mead §9.4`). -/
theorem expect_armIndicator_pair_distinct (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) {i j : U}
    -- LEAN-ONLY: distinct units; same-unit exclusivity gives probability zero
    (hij : i ≠ j) {t s : T}
    -- LEAN-ONLY: distinct treatments; the same-treatment case is the lemma above
    (hts : t ≠ s) :
    pmfExpect (completeRandomization r hr)
        (fun a => armIndicator t i a * armIndicator s j a)
      = (r t : ℝ) * (r s : ℝ)
          / ((Fintype.card U : ℝ) * ((Fintype.card U : ℝ) - 1)) := by
  sorry

/-- **Indicator variance**: `Var(χ_{t,i}) = r_t (N − r_t) / N²` — the Bernoulli
variance of the assignment (`Mead §9.4`). -/
theorem var_armIndicator (r : T → ℕ) (hr : ∑ t, r t = Fintype.card U)
    (i : U) (t : T) :
    pmfVar (completeRandomization r hr) (armIndicator t i)
      = (r t : ℝ) * ((Fintype.card U : ℝ) - (r t : ℝ)) / (Fintype.card U : ℝ) ^ 2 := by
  sorry

/-- **Negative indicator covariance across units**:
`Cov(χ_{t,i}, χ_{t,j}) = − r_t (N − r_t) / (N² (N−1))` for `i ≠ j` — the fixed arm
sizes make assignments negatively dependent (`Mead §9.4`). -/
theorem cov_armIndicator_of_ne (r : T → ℕ) (hr : ∑ t, r t = Fintype.card U)
    {i j : U}
    -- LEAN-ONLY: distinct units; the same-unit case is `var_armIndicator`
    (hij : i ≠ j) (t : T) :
    pmfCov (completeRandomization r hr) (armIndicator t i) (armIndicator t j)
      = -((r t : ℝ) * ((Fintype.card U : ℝ) - (r t : ℝ)))
          / ((Fintype.card U : ℝ) ^ 2 * ((Fintype.card U : ℝ) - 1)) := by
  sorry

end StatLean.ExperimentalDesign
