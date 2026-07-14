import StatLean.NonparametricStatistics.Projection.Defs
import StatLean.NonparametricStatistics.ForMathlib.TrigDiscreteSums

/-!
# Discrete orthonormality of the trigonometric system at the regular design

The exact discrete analogue of `L²[0,1]`-orthonormality: at the regular design
`x_s = s/n`, `s = 1, …, n`,
$$ \frac1n \sum_{s=1}^{n} \varphi_j(s/n)\,\varphi_k(s/n) \;=\; \delta_{jk},
   \qquad 1 \le j, k \le n-1. $$
This is the reason coefficient estimates at the regular design behave *exactly* like Fourier
coefficients: the empirical Gram matrix of the first `n − 1` basis functions is the identity.

**Proof formalization notes.** Product-to-sum turns each product into discrete cosine/sine
sums at frequencies `j/2 ± k/2` (ℕ-division bookkeeping); by `ForMathlib/TrigDiscreteSums`
these vanish unless the frequency is a multiple of `n`, and for `1 ≤ j, k ≤ n − 1` the
frequencies `j/2 ± k/2` lie in `(−n, n)`, so only the zero frequency survives — precisely at
same-parity equal indices, where the normalization `(√2)²·(1/2) = 1` (and `φ₁ ≡ 1`) gives the
diagonal. The frequency-range arithmetic is the delicate step; state each parity case as a
private lemma if useful.

**Bibliographic comments.** Classical discrete Fourier analysis; its use for regular-design
regression estimates appears in J. Rice, *Ann. Statist.* **12** (1984), 1215–1230, and
B. T. Polyak and A. B. Tsybakov, "Asymptotic optimality of the `C_p`-test for the orthogonal
series estimation of regression," *Theory Probab. Appl.* **35** (1990), 293–306.
-/

namespace StatLean.NonparametricStatistics

/-- **Discrete orthonormality at the regular design**: for `1 ≤ j, k ≤ n − 1`,
`n⁻¹ ∑_{s=1}^n φⱼ(s/n)·φ_k(s/n) = δ_{jk}`. -/
theorem trigBasis_discrete_orthonormal {n j k : ℕ}
    (hj : 1 ≤ j) (hj' : j ≤ n - 1) (hk : 1 ≤ k) (hk' : k ≤ n - 1) :
    (n : ℝ)⁻¹ * ∑ i : Fin n, trigBasis j (regularDesign n i) * trigBasis k (regularDesign n i)
      = if j = k then 1 else 0 := by
  sorry

end StatLean.NonparametricStatistics
