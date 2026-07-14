import StatLean.NonparametricStatistics.Projection.DiscreteOrthogonality
import StatLean.NonparametricStatistics.ForMathlib.TailSumRpow

/-!
# Aliasing bounds for Riemann-sum residuals over Sobolev ellipsoids

The Riemann-sum residual `αⱼ` of the coefficient estimate is pure *aliasing*: at the regular
design, the frequencies `1 ≤ m ≤ n − 1` reproduce exactly, so only the coefficient tail
`m ≥ n` leaks:
$$ \max_{1\le j\le n-1} |\alpha_j| \;\le\; 2\!\!\sum_{m \ge n}\!|\theta_m|
   \;\le\; C_{\beta,Q}\, n^{\frac12-\beta} \quad \text{over } \Theta(\beta, Q),\ \beta > 1/2. $$
Also here: membership in an ellipsoid with `β > 1/2` forces absolute summability of the
coefficients — so the summability assumption of the risk decomposition is *derived* on the
ellipsoid, never assumed there.

**Proof formalization notes.** Substituting the (uniformly convergent) series into the design
sum and using discrete orthonormality for `m ≤ n − 1` leaves
`αⱼ = ∑_{m≥n} θ_m·(n⁻¹∑ₛφ_m(s/n)φⱼ(s/n))`, and each averaged product is bounded by `2`
(`|φ| ≤ √2`). Cauchy–Schwarz against the ellipsoid weights plus the p-series tail bound
(`tsum_nat_add_rpow_neg_le`, with `a_m ≥ (m−1)^β`, i.e. `s = 2β`) gives the rate; the
explicit constant is
`residualConst β Q = 2·√Q·√(2β/(2β−1))·3^{β−1/2}` (the `3^{β−1/2}` absorbs the shift
`(n−2) ≥ n/3`, valid for `n ≥ 3`). The ellipsoid-to-`ℓ¹` lemma is Cauchy–Schwarz with the
convergent weight series `∑ a_m^{-2}`.

**Bibliographic comments.** J. Rice, *Ann. Statist.* **12** (1984), 1215–1230; the extension
of discrete orthogonality beyond `n − 1` frequencies is studied in B. T. Polyak and
A. B. Tsybakov, *Theory Probab. Appl.* **35** (1990), 293–306.
-/

open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- The explicit aliasing constant `C_{β,Q} = 2·√Q·√(2β/(2β−1))·3^{β−1/2}` of the residual
bound over the ellipsoid `Θ(β, Q)`. -/
noncomputable def residualConst (β Q : ℝ) : ℝ :=
  2 * Real.sqrt Q * Real.sqrt (2 * β / (2 * β - 1)) * 3 ^ (β - 1 / 2)

/-- **Ellipsoid membership implies absolutely summable coefficients** (for `β > 1/2`):
the summability input of the risk decomposition is derived on the ellipsoid. -/
theorem MemEllipsoid.summable_abs {β Q : ℝ} {θ : ℕ → ℝ}
    -- USER-INPUT: smoothness above one half and nonnegative radius; classical range in
    -- which the ellipsoid embeds into `ℓ¹`
    (hβ : 1 / 2 < β) (hQ : 0 ≤ Q)
    (hθ : MemEllipsoid β Q θ) :
    Summable fun j => |θ j| := by
  sorry

/-- **Aliasing bound via the coefficient tail**: for `1 ≤ j ≤ n − 1` and absolutely summable
coefficients, `|αⱼ| ≤ 2·∑_{m≥n}|θ_m|` (re-indexed as a `tsum` over `m ↦ n + m`). -/
theorem riemannResidual_abs_le_tail {θ : ℕ → ℝ} {n j : ℕ}
    (hj : 1 ≤ j) (hj' : j ≤ n - 1)
    -- USER-INPUT: absolutely summable coefficients; the classical summability assumption
    (hθ1 : Summable fun j => |θ j|) :
    |riemannResidual θ n j| ≤ 2 * ∑' m : ℕ, |θ (n + m)| := by
  sorry

/-- **Aliasing rate over the Sobolev ellipsoid**: for `θ ∈ Θ(β, Q)` with `β > 1/2`, `n ≥ 3`,
and `1 ≤ j ≤ n − 1`, `|αⱼ| ≤ residualConst β Q · n^{1/2−β}`. -/
theorem riemannResidual_abs_le {β Q : ℝ} {θ : ℕ → ℝ} {n j : ℕ}
    -- USER-INPUT: smoothness above one half and nonnegative radius; classical parameters
    (hβ : 1 / 2 < β) (hQ : 0 ≤ Q)
    -- LEAN-ONLY: `n ≥ 3` so the tail estimate's shifted power is controlled
    (hn : 3 ≤ n)
    (hj : 1 ≤ j) (hj' : j ≤ n - 1)
    (hθ : MemEllipsoid β Q θ) :
    |riemannResidual θ n j| ≤ residualConst β Q * (n : ℝ) ^ ((1 : ℝ) / 2 - β) := by
  sorry

end StatLean.NonparametricStatistics
