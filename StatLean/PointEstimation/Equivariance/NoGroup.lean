import StatLean.PointEstimation.Equivariance.Defs
import Mathlib.MeasureTheory.Measure.Count

/-!
# A family with no nontrivial invariance

The equivariance principle is only available when the model admits symmetries. This file
exhibits a family for which it is not: the **power series family** on `ℕ`,

`P_θ{X = k} = c_k θ^k h(θ)`,   `k = 0, 1, 2, …`,  `θ > 0`,

with all coefficients `c_k` strictly positive. For such a family the *only* bijection of
the sample space leaving the family invariant is the identity, so the invariance group is
trivial and the equivariance principle has no content.

* `powerSeriesFamily` — the family, as a density with respect to the counting measure on
  `ℕ`, normalized by the total sum;
* `powerSeriesFamily_invariant_affine` — the structural step: an invariance-preserving
  bijection has constant successive increments;
* `powerSeriesFamily_invariant_perm_eq_one` — the conclusion: such a bijection is the
  identity;
* `powerSeriesFamily_invariantPerms_eq_singleton` — the same statement packaged as "the
  set of invariance-preserving permutations is `{1}`".

**Reference.** Classical equivariance theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* The classical conclusion really is the general "the transformation is the identity"
  claim (not a two-point comparison), so it is transcribed as such, with the bijection
  modelled as `Equiv.Perm ℕ`.
* The argument runs as follows. Write `a_k = g(k)`. Matching point masses gives
  `c_k θ^k h(θ) = c_{a_k} μ^{a_k} h(μ)` for the transported parameter `μ`; taking ratios
  of consecutive `k` twice shows `μ^{a_{k+2} − a_{k+1}}` is proportional to
  `μ^{a_{k+1} − a_k}` *throughout an interval of `μ`*, whence the exponents agree and
  `a_k = a_0 + kΔ`. Being a permutation of `ℕ` forces `Δ = 1` and `a_0 = 0`.
* Because the exponent-matching step needs `μ` to range over an interval, the parameter
  set is taken to be an interval `Ioo 0 R` on which the series converges, rather than the
  informal "`0 < θ < ∞`". The increments are recorded in `ℤ`, since `ℕ`-subtraction would
  truncate and the increments are not known to be nonnegative before the final step.
* The strict positivity of every coefficient is essential and not cosmetic: when
  `c_k = 0` for all `k` beyond some threshold the conclusion fails — the binomial family
  is invariant under `k ↦ n − k`, whose induced parameter map is `p ↦ 1 − p`.
* Edge behaviour of `powerSeriesFamily`: the normalizer is the total sum
  `∑' j, c_j θ^j`, so the definition returns the zero measure where the series diverges
  and the junk `∞`-valued density where it vanishes. Theorems carry the convergence
  hypothesis.

**Bibliographic comments.** The group-theoretic framework in which "the model admits no
nontrivial symmetries" is the relevant negative statement is due to G. A. Hunt and
C. Stein (unpublished manuscript, 1946), first reported in print by M. A. Girshick and
L. J. Savage, "Bayes and minimax estimates for quadratic loss functions," *Proc. Second
Berkeley Symp. Math. Statist. Probab.*, Univ. California Press, 1951, 53–73.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

/-- The **power series family** on `ℕ` with coefficients `a`: the law with density
`k ↦ a k · θ^k / ∑' j, a j · θ^j` with respect to the counting measure.

The normalizer is the total sum, so this is a probability measure exactly where that sum
is finite and nonzero; elsewhere the definition takes the junk value coming from
`ℝ≥0∞`-division (zero measure when the sum is infinite, `∞`-valued density when it
vanishes). Theorems carry the corresponding convergence hypotheses. -/
noncomputable def powerSeriesFamily (a : ℕ → ℝ≥0∞) (θ : ℝ) : Measure ℕ :=
  Measure.count.withDensity fun k =>
    (a k * (ENNReal.ofReal θ) ^ k) / (∑' j, a j * (ENNReal.ofReal θ) ^ j)

/-- Analytic core of `powerSeriesFamily_invariant_affine`: density matching plus the
coefficient-ratio / exponent arithmetic-progression argument. Isolated as the single
lifted debt of this file. -/
private theorem powerSeriesFamily_invariant_affine_core {a : ℕ → ℝ≥0∞}
    (ha₀ : ∀ k, a k ≠ 0) (ha : ∀ k, a k ≠ ∞) {R : ℝ} (hR : 0 < R)
    (hconv : ∀ θ ∈ Set.Ioo (0 : ℝ) R, (∑' j, a j * (ENNReal.ofReal θ) ^ j) ≠ ∞)
    (g : Equiv.Perm ℕ)
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) R, ∃ θ' ∈ Set.Ioo (0 : ℝ) R,
      (powerSeriesFamily a θ).map (g : ℕ → ℕ) = powerSeriesFamily a θ') :
    ∃ d : ℤ, ∀ k : ℕ, (g (k + 1) : ℤ) - (g k : ℤ) = d := by
  -- TODO: prove the analytic core. From `(P θ).map g = P θ'` and `g`-invariance of the
  -- counting measure, matching point masses gives `a k θ^k / Z(θ) = a (g k) θ'^(g k) / Z(θ')`
  -- for all `k`; taking ratios of consecutive `k` twice forces `μ^{a_{k+2}-a_{k+1}}` to be
  -- proportional to `μ^{a_{k+1}-a_k}` throughout an interval of the transported parameter,
  -- whence the exponents agree and `g (k+1) - g k` is constant.
  sorry

/-- **Structural step towards triviality of the invariance group.** A bijection of the
sample space that maps every member of a power series family to another member has
constant successive increments, `g(k+1) − g(k) = Δ` for all `k`. -/
theorem powerSeriesFamily_invariant_affine {a : ℕ → ℝ≥0∞}
    -- USER-INPUT: every coefficient is strictly positive (the family has full support)
    (ha₀ : ∀ k, a k ≠ 0)
    -- LEAN-ONLY: coefficients are finite, so the densities are genuine real numbers
    (ha : ∀ k, a k ≠ ∞)
    {R : ℝ}
    -- USER-INPUT: the parameter ranges over an interval, on which the series converges
    (hR : 0 < R)
    (hconv : ∀ θ ∈ Set.Ioo (0 : ℝ) R, (∑' j, a j * (ENNReal.ofReal θ) ^ j) ≠ ∞)
    (g : Equiv.Perm ℕ)
    -- USER-INPUT: `g` leaves the family invariant — it maps each member to a member
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) R, ∃ θ' ∈ Set.Ioo (0 : ℝ) R,
      (powerSeriesFamily a θ).map (g : ℕ → ℕ) = powerSeriesFamily a θ') :
    ∃ d : ℤ, ∀ k : ℕ, (g (k + 1) : ℤ) - (g k : ℤ) = d :=
  powerSeriesFamily_invariant_affine_core ha₀ ha hR hconv g hg

/-- **A power series family with strictly positive coefficients admits no nontrivial
symmetry of the sample space.** Any bijection of `ℕ` mapping every member of the family
to a member of the family is the identity.

Since the equivariance principle only has content relative to a group of transformations
leaving the model invariant, it is vacuous for such families. -/
theorem powerSeriesFamily_invariant_perm_eq_one {a : ℕ → ℝ≥0∞}
    -- USER-INPUT: every coefficient is strictly positive; the conclusion is false
    -- without this, as the binomial family shows
    (ha₀ : ∀ k, a k ≠ 0)
    -- LEAN-ONLY: coefficients are finite
    (ha : ∀ k, a k ≠ ∞)
    {R : ℝ}
    -- USER-INPUT: the parameter ranges over an interval, on which the series converges
    (hR : 0 < R)
    (hconv : ∀ θ ∈ Set.Ioo (0 : ℝ) R, (∑' j, a j * (ENNReal.ofReal θ) ^ j) ≠ ∞)
    (g : Equiv.Perm ℕ)
    -- USER-INPUT: `g` leaves the family invariant
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) R, ∃ θ' ∈ Set.Ioo (0 : ℝ) R,
      (powerSeriesFamily a θ).map (g : ℕ → ℕ) = powerSeriesFamily a θ') :
    g = 1 := by
  obtain ⟨d, hd⟩ := powerSeriesFamily_invariant_affine ha₀ ha hR hconv g hg
  -- closed form of the (integer) values along the arithmetic progression
  have hform : ∀ k : ℕ, (g k : ℤ) = (g 0 : ℤ) + k * d := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have hstep : (g (n + 1) : ℤ) = (g n : ℤ) + d := by linarith [hd n]
      rw [hstep, ih]; push_cast; ring
  have hnn : ∀ k : ℕ, (0 : ℤ) ≤ (g k : ℤ) := fun k => Int.natCast_nonneg _
  -- `d ≠ 0` (else `g` is not injective)
  have hd_ne : d ≠ 0 := by
    intro h0
    have h1 : (g 1 : ℤ) = (g 0 : ℤ) := by rw [hform 1, h0]; simp
    exact one_ne_zero (g.injective (by exact_mod_cast h1))
  -- `d > 0` (else the values eventually go negative)
  have hd_pos : 0 < d := by
    rcases lt_or_gt_of_ne hd_ne with hneg | hpos
    · exfalso
      have hk := hform (g 0 + 1)
      have hge := hnn (g 0 + 1)
      rw [hk] at hge
      push_cast at hge
      nlinarith [hnn 0, hge, hneg]
    · exact hpos
  -- `g 0 = 0` (surjectivity hits `0`)
  have hg0 : (g 0 : ℤ) = 0 := by
    obtain ⟨k, hk⟩ := g.surjective 0
    have := hform k
    rw [hk] at this
    push_cast at this
    nlinarith [hnn 0, mul_nonneg (Int.natCast_nonneg k) hd_pos.le, this]
  -- `d = 1` (surjectivity hits `1`)
  have hd1 : d = 1 := by
    obtain ⟨k, hk⟩ := g.surjective 1
    have hval := hform k
    rw [hk, hg0] at hval
    push_cast at hval
    -- `1 = k * d`, with `d > 0`, forces `d = 1`
    have hdvd : d ∣ 1 := ⟨(k : ℤ), by linarith [hval]⟩
    exact Int.eq_one_of_dvd_one hd_pos.le hdvd
  -- conclude `g = id`
  ext k
  have := hform k
  rw [hg0, hd1] at this
  simp only [Equiv.Perm.coe_one, id_eq]
  have hgk : (g k : ℤ) = (k : ℤ) := by rw [this]; ring
  exact_mod_cast hgk

/-- The invariance group of a power series family with strictly positive coefficients is
trivial: the set of permutations of the sample space leaving the family invariant is the
one-element set containing the identity. -/
theorem powerSeriesFamily_invariantPerms_eq_singleton {a : ℕ → ℝ≥0∞}
    -- USER-INPUT: every coefficient is strictly positive
    (ha₀ : ∀ k, a k ≠ 0)
    -- LEAN-ONLY: coefficients are finite
    (ha : ∀ k, a k ≠ ∞)
    {R : ℝ}
    -- USER-INPUT: the parameter ranges over an interval, on which the series converges
    (hR : 0 < R)
    (hconv : ∀ θ ∈ Set.Ioo (0 : ℝ) R, (∑' j, a j * (ENNReal.ofReal θ) ^ j) ≠ ∞) :
    {g : Equiv.Perm ℕ | ∀ θ ∈ Set.Ioo (0 : ℝ) R, ∃ θ' ∈ Set.Ioo (0 : ℝ) R,
      (powerSeriesFamily a θ).map (g : ℕ → ℕ) = powerSeriesFamily a θ'} = {1} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨fun θ hθ => ⟨θ, hθ, ?_⟩, ?_⟩
  · rw [Equiv.Perm.coe_one, Measure.map_id]
  · intro g hg
    exact powerSeriesFamily_invariant_perm_eq_one ha₀ ha hR hconv g hg

end StatLean.PointEstimation
