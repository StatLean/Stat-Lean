import StatLean.NonparametricStatistics.LocalPolynomial.WeightBounds

/-!
# Lipschitz control of local polynomial weights in the evaluation point

For a Lipschitz boxed kernel, the total variation of the weight vector between two evaluation
points is controlled:
$$ \sum_i \bigl|W^*_i(t) - W^*_i(t')\bigr| \;\le\; C_L\,\frac{|t - t'|}{h^3},
   \qquad t, t' \in [0,1], $$
with `C_L = C_L(ℓ, K_max, λ₀, a₀, L_K)`. This is the grid-to-continuum step of the sup-norm
analysis: on a grid of mesh `n^{-4}` the increment is `O(n^{-4}/h³) = O(n^{-1})`.

**Proof formalization notes.** Write the weight difference through the resolvent identity
`B_t⁻¹ − B_{t'}⁻¹ = B_t⁻¹(B_{t'} − B_t)B_{t'}⁻¹`. Each ingredient is Lipschitz in `t` with
constants polynomial in `1/h`: `‖U(zᵢ)K(zᵢ) − U(z'ᵢ)K(z'ᵢ)‖ ≤ C·|t−t'|/h` (Lipschitz kernel,
bounded basis on the support), `‖B_t − B_{t'}‖ ≤ C·|t−t'|/h` (design density bound controls
the number of active summands), and `‖B⁻¹‖ ≤ 1/λ₀`. Both `t, t'` count on the union of the
two bandwidth windows, of cardinality `≤ 4a₀nh`. The generous `h⁻³` absorbs all bookkeeping
(only upper bounds are needed; `h ≤ 1`).

**Bibliographic comments.** Standard chaining/discretization bookkeeping; folklore.
-/

namespace StatLean.NonparametricStatistics

/-- **ℓ¹-Lipschitz bound of the weight vector in the evaluation point**: there is
`C_L = C_L(ℓ, K_max, λ₀, a₀, L_K)` with
`∑ i, |W*ᵢ(t) − W*ᵢ(t')| ≤ C_L·|t − t'|/h³` for all `t, t' ∈ [0,1]` under the standing
assumptions. -/
theorem lp_weight_lipschitz_sum {ℓ : ℕ} {K : ℝ → ℝ} {Kmax lam0 a₀ LK : ℝ}
    -- USER-INPUT: positive eigenvalue floor and nonnegative density constant; standing
    -- design assumptions
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: Lipschitz kernel; the sup-norm analysis input
    (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|) :
    ∃ CL : ℝ, 0 < CL ∧
      ∀ {n : ℕ}, 0 < n → ∀ {h : ℝ}, 1 / (2 * (n : ℝ)) ≤ h → h ≤ 1 →
      ∀ {xdat : Fin n → ℝ}, (∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1) →
        DesignEigenvalueLB xdat K h ℓ lam0 → DesignDensityBound xdat a₀ →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        ∑ i, |lpWeight xdat K h ℓ t i - lpWeight xdat K h ℓ t' i|
          ≤ CL * |t - t'| / h ^ 3 := by
  sorry

end StatLean.NonparametricStatistics
