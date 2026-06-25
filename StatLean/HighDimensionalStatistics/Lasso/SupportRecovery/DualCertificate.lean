import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Defs
import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Subgradient

/-!
# Primal–dual witness construction and strict dual feasibility (Wainwright §7.5.2)

The deterministic heart of Theorem 7.21: construct the primal–dual witness `(θ̂, ẑ)` and
prove **strict dual feasibility** plus the **ℓ∞ error bound**.

`pdw_witness_exists` bundles, under conditions (A3),(A4) and the regularization condition
(7.44), the witness consumed by `Subgradient.lean`'s Lemma 7.23:
* `θ̂` supported on `S` (PDW steps 1–2: zero off `S`, oracle solve on `S`);
* `ẑ ∈ ∂‖θ̂‖₁` with the KKT condition (7.48);
* **strict dual feasibility** `|ẑ_j| < 1` for `j ∉ S` (= `½(1+α) < 1`), from the block
  decomposition `ẑ_{Sᶜ} = μ + V_{Sᶜ}` (7.53), `‖μ‖_∞ ≤ α` (incoherence + Hölder) and
  `‖V_{Sᶜ}‖_∞ ≤ ½(1−α)` (choice of λ);
* the **ℓ∞ bound** `‖θ̂_S − θ*_S‖_∞ ≤ B(λ;X)` (7.54 / 7.45).

Internal proof roadmap (named `private` lemmas, see cluster prompt): `theta_diff_eq` (7.52),
`zSc_eq` (7.53), `incoherence_bound`, `noise_bound`, `strict_dual_feasibility`,
`linf_error_bound`. Uses the Gram/inverse/projection bounds from `GramMatrix.lean`.
-/

open Matrix
open scoped InnerProductSpace

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Primal–dual witness existence + strict feasibility + ℓ∞ bound** (Wainwright §7.5.2).
Under the lower-eigenvalue condition (A3), mutual incoherence (A4) with `α ∈ [0,1)`, and the
regularization condition (7.44) `λ ≥ (2/(1−α))·‖Xₛᶜᵀ Π_{S⊥}(X) w/n‖_∞`, the Lagrangian Lasso
with response `Y = X θ* + w` admits a primal–dual witness `(θ̂, ẑ)` that is supported on `S`,
KKT-optimal, **strictly** dual feasible off `S`, and whose support error obeys the bound
`B(λ;X)`. -/
theorem pdw_witness_exists (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin n)) (lam α cmin : ℝ)
    -- USER-INPUT: 0 < n; Wainwright §7.5
    (hn : 0 < n)
    -- USER-INPUT: θ* supported on S; Wainwright §7.5 (S-sparse model)
    (hsupp : ∀ j ∉ S, θstar.ofLp j = 0)
    -- USER-INPUT: lower-eigenvalue condition (A3); Wainwright §7.5.1 (7.43a)
    (hA3 : LowerEigenvalue X S cmin)
    -- USER-INPUT: 0 < cmin; Wainwright §7.5.1 (7.43a)
    (hcmin : 0 < cmin)
    -- USER-INPUT: mutual incoherence (A4); Wainwright §7.5.1 (7.43b)
    (hA4 : MutualIncoherence X S α)
    -- USER-INPUT: 0 ≤ α; Wainwright §7.5.1 (incoherence parameter α ∈ [0,1))
    (hα0 : 0 ≤ α)
    -- USER-INPUT: α < 1; Wainwright §7.5.1 (incoherence parameter α ∈ [0,1))
    (hα1 : α < 1)
    -- USER-INPUT: 0 < λ; Wainwright §7.5
    (hlampos : 0 < lam)
    -- USER-INPUT: regularization condition λ ≥ (2/(1−α))·‖Xₛᶜᵀ Π_{S⊥} w/n‖_∞; Wainwright (7.44)
    (hlam : lam ≥ (2 / (1 - α)) * projNoiseLinf X S w) :
    ∃ θhat zhat : EuclideanSpace ℝ (Fin d),
      (∀ j ∉ S, θhat.ofLp j = 0) ∧
      IsL1Subgradient zhat θhat ∧
      IsKKT X (designMap X θstar + w) lam θhat zhat ∧
      (∀ j ∉ S, |zhat.ofLp j| < 1) ∧
      linfNorm (restrict S (θhat - θstar)) ≤ supportRecoveryBound X S w lam := by
  sorry

end StatLean.HighDimensionalStatistics
