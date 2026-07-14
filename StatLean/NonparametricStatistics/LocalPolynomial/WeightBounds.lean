import StatLean.NonparametricStatistics.LocalPolynomial.Quadratic

/-!
# Bounds on local polynomial weights

Under the standing assumptions (eigenvalue lower bound, design density bound, boxed kernel)
and `h ≥ 1/(2n)`, the LP(`ℓ`) weights satisfy, uniformly over `t ∈ [0,1]`:

* `|W*ᵢ(t)| ≤ C*/(n·h)`;
* `∑ i, |W*ᵢ(t)| ≤ C*`;
* `W*ᵢ(t) = 0` whenever `|xdat i − t| > h`,

with the explicit constant `C* = lpWeightConst Kmax lam0 a₀ = max{2K_max/λ₀, 4K_max·a₀/λ₀}`.

**Proof formalization notes.** (iii) is immediate from the kernel's support. For (i):
`|W*ᵢ| ≤ (nh)⁻¹·‖B⁻¹U(zᵢ)K(zᵢ)‖ ≤ (nh)⁻¹·K_max·‖U(zᵢ)‖/λ₀` by the inverse bound
(`lpMatrix_inv_mulVec_sq_le`); on `|z| ≤ 1`, `‖U(z)‖² = ∑ (z^k/k!)² ≤ ∑ 1/k! ≤ e ≤ 4`
(`lpBasis_normSq_le`), so `‖U(zᵢ)‖ ≤ 2`. For (ii), sum (i) over the at most
`n·a₀·max(2h, 1/n) = 2a₀·n·h` indices with `|xᵢ − t| ≤ h` (design density bound, using
`h ≥ 1/(2n)` to resolve the max).

**Bibliographic comments.** These weight bounds are the standard technical core of local
polynomial risk analysis; cf. C. J. Stone, *Ann. Statist.* **8** (1980), 1348–1360, and
J. Fan and I. Gijbels, *Local Polynomial Modelling and Its Applications* (1996).
-/

namespace StatLean.NonparametricStatistics

variable {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {h lam0 a₀ Kmax : ℝ} {ℓ : ℕ}

/-- On `|z| ≤ 1` the rescaled monomial basis vector has squared norm at most `e` (hence norm
at most `2`): `∑ k, (z^k/k!)² ≤ e`. -/
theorem lpBasis_normSq_le (ℓ : ℕ) {z : ℝ} (hz : |z| ≤ 1) :
    ∑ k, (lpBasis ℓ z k) ^ 2 ≤ Real.exp 1 := by
  sorry

/-- **Weight vanishing outside the bandwidth window**: `W*ᵢ(t) = 0` when `|xdat i − t| > h`
(boxed kernel, positive bandwidth). -/
theorem lp_weight_eq_zero_of_far
    -- LEAN-ONLY: positive bandwidth; standard side condition
    (hh : 0 < h)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    {t : ℝ} {i : Fin n} (hfar : h < |xdat i - t|) :
    lpWeight xdat K h ℓ t i = 0 := by
  sorry

/-- **Sup-norm weight bound**: `|W*ᵢ(t)| ≤ C*/(n·h)` uniformly over `t ∈ [0,1]` and `i`. -/
theorem lp_weight_abs_le
    -- LEAN-ONLY: nonempty sample and positive bandwidth; standard side conditions
    (hn : 0 < n) (hh : 0 < h)
    -- USER-INPUT: positive eigenvalue floor; standing design assumption
    (hlam : 0 < lam0)
    -- USER-INPUT: nonnegative density constant; standing design assumption
    (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: eigenvalue lower bound on the local design matrix; standing assumption
    (heig : DesignEigenvalueLB xdat K h ℓ lam0)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    |lpWeight xdat K h ℓ t i| ≤ lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) := by
  sorry

/-- **ℓ¹ weight bound**: `∑ i, |W*ᵢ(t)| ≤ C*` uniformly over `t ∈ [0,1]`, provided
`h ≥ 1/(2n)`. -/
theorem lp_weight_sum_abs_le
    -- LEAN-ONLY: nonempty sample; standard side condition
    (hn : 0 < n)
    -- USER-INPUT: bandwidth at least `1/(2n)`; classical range of the weight bounds
    (hhl : 1 / (2 * (n : ℝ)) ≤ h)
    -- USER-INPUT: positive eigenvalue floor and nonnegative density constant; standing
    -- design assumptions
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: eigenvalue lower bound on the local design matrix; standing assumption
    (heig : DesignEigenvalueLB xdat K h ℓ lam0)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: design density bound; standing design assumption
    (hdens : DesignDensityBound xdat a₀)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i, |lpWeight xdat K h ℓ t i| ≤ lpWeightConst Kmax lam0 a₀ := by
  sorry

end StatLean.NonparametricStatistics
