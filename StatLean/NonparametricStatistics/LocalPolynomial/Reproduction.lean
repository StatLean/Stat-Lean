import StatLean.NonparametricStatistics.LocalPolynomial.Quadratic

/-!
# Polynomial reproduction by local polynomial weights

Under `B_t ≻ 0`, the LP(`ℓ`) weights reproduce every polynomial of degree at most `ℓ`
*exactly*, for any data configuration:
`∑ i, Q(xdat i)·W*ᵢ(t) = Q(t)`. Stated in the centered monomial basis `(x − t)^k` — every
polynomial of degree `≤ ℓ` is a combination `∑_k c_k (x − t)^k`, so this is equivalent to the
classical statement. In particular the weights sum to one, and their centered moments of
orders `1, …, ℓ` vanish — the cancellation mechanism of the bias analysis.

**Proof formalization notes.** For responses `Y i = (xdat i − t)^k`, the coefficient vector
`q` with `q_j = δ_{jk}·k!·h^k` satisfies `q ⬝ U((xᵢ−t)/h) = (xᵢ−t)^k`, so the objective at
`q` is zero-residual and minimal; uniqueness of the minimiser (`isLPSolution_unique`) forces
`θ̂ = q`, and `lpEstimator = θ̂ 0 = q 0` (`lpEstimator_eq_isLPSolution`). By linearity of the
weights, the general centered-polynomial identity follows by summation. Needs `h ≠ 0` (so
the basis change `z = (x−t)/h` is invertible).

**Bibliographic comments.** The reproduction property is the defining feature of local
polynomial smoothers; cf. J. Fan and I. Gijbels, *Local Polynomial Modelling and Its
Applications*, Chapman & Hall, 1996, §3.1, and C. J. Stone, *Ann. Statist.* **5** (1977),
595–620.
-/

namespace StatLean.NonparametricStatistics

variable {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ} {h : ℝ} {ℓ : ℕ} {t : ℝ}

/-- **Centered monomial reproduction**: under `B_t ≻ 0` and `h ≠ 0`, for `k ≤ ℓ`,
`∑ i, (xdat i − t)^k·W*ᵢ(t) = δ_{k,0}` — i.e. the weights sum to `1` and their centered
moments of orders `1, …, ℓ` vanish. -/
theorem lp_weight_reproduce_monomial (hpd : (lpMatrix xdat K h ℓ t).PosDef)
    -- LEAN-ONLY: nonzero bandwidth so the centered basis change is invertible
    (hh : h ≠ 0)
    {k : ℕ} (hk : k ≤ ℓ) :
    ∑ i, (xdat i - t) ^ k * lpWeight xdat K h ℓ t i = if k = 0 then 1 else 0 := by
  sorry

/-- The LP(`ℓ`) weights sum to one (the `k = 0` case of monomial reproduction). -/
theorem lp_weight_sum_one (hpd : (lpMatrix xdat K h ℓ t).PosDef) (hh : h ≠ 0) :
    ∑ i, lpWeight xdat K h ℓ t i = 1 := by
  sorry

/-- **Polynomial reproduction** in the centered basis: under `B_t ≻ 0` and `h ≠ 0`, for any
coefficients `c : Fin (ℓ+1) → ℝ`,
`∑ i, (∑ k, c k·(xdat i − t)^k)·W*ᵢ(t) = c 0` — that is, `∑ᵢ Q(xdat i)·W*ᵢ(t) = Q(t)` for
every polynomial `Q` of degree at most `ℓ`. -/
theorem lp_weight_reproduce_poly (hpd : (lpMatrix xdat K h ℓ t).PosDef) (hh : h ≠ 0)
    (c : Fin (ℓ + 1) → ℝ) :
    ∑ i, (∑ k : Fin (ℓ + 1), c k * (xdat i - t) ^ (k : ℕ)) * lpWeight xdat K h ℓ t i
      = c 0 := by
  sorry

end StatLean.NonparametricStatistics
