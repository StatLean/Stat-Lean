import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Subgradient
import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.DualCertificate

/-!
# Theorem 7.21 — Lasso variable-selection consistency (Wainwright §7.5)

The deterministic primal–dual-witness guarantee for the Lagrangian Lasso, assembled from the
witness construction (`DualCertificate.lean`) and the uniqueness lemma 7.23
(`Subgradient.lean`). Parts (a)–(d) of the boxed Theorem 7.21:

* (a) `lasso_support_recovery_unique` — a **unique** optimal solution.
* (b) `lasso_support_recovery_no_false_inclusion` — `supp(θ̂) ⊆ S`.
* (c) `lasso_support_recovery_linf` — `‖θ̂_S − θ*_S‖_∞ ≤ B(λ;X)` (7.45).
* (d) `lasso_support_recovery_no_false_exclusion` — every large coordinate is recovered.

Parts (b)–(d) are stated in the strong ∀-form (over *every* Lasso minimizer); combined with
(a) this is exactly the book's statement about "the" solution. Standing hypotheses are the
S-sparse model with conditions (A3),(A4), `α ∈ [0,1)`, and the regularization condition (7.44).
-/

open Matrix
open scoped InnerProductSpace

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Theorem 7.21 (a) — uniqueness** (Wainwright §7.5). Under (A3),(A4), `α ∈ [0,1)` and the
regularization condition (7.44), the Lagrangian Lasso for `Y = X θ* + w` has a unique optimum. -/
theorem lasso_support_recovery_unique (X : Matrix (Fin n) (Fin d) ℝ)
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
    -- USER-INPUT: 0 ≤ α; Wainwright §7.5.1
    (hα0 : 0 ≤ α)
    -- USER-INPUT: α < 1; Wainwright §7.5.1
    (hα1 : α < 1)
    -- USER-INPUT: 0 < λ; Wainwright §7.5
    (hlampos : 0 < lam)
    -- USER-INPUT: regularization condition (7.44); Wainwright §7.5
    (hlam : lam ≥ (2 / (1 - α)) * projNoiseLinf X S w) :
    ∃! βhat, IsLassoEstimator X (designMap X θstar + w) lam βhat := by
  sorry

/-- **Theorem 7.21 (b) — no false inclusion** (Wainwright §7.5): every Lasso minimizer has
its support contained in `S`. -/
theorem lasso_support_recovery_no_false_inclusion (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin n)) (lam α cmin : ℝ)
    (hn : 0 < n) (hsupp : ∀ j ∉ S, θstar.ofLp j = 0)
    (hA3 : LowerEigenvalue X S cmin) (hcmin : 0 < cmin)
    (hA4 : MutualIncoherence X S α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlampos : 0 < lam) (hlam : lam ≥ (2 / (1 - α)) * projNoiseLinf X S w)
    (βhat : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: β̂ is a Lasso minimizer; Wainwright §7.5
    (hopt : IsLassoEstimator X (designMap X θstar + w) lam βhat) :
    ∀ j ∉ S, βhat.ofLp j = 0 := by
  sorry

/-- **Theorem 7.21 (c) — ℓ∞ error bound** (Wainwright 7.45): every Lasso minimizer satisfies
`‖β̂_S − θ*_S‖_∞ ≤ B(λ;X)`. -/
theorem lasso_support_recovery_linf (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin n)) (lam α cmin : ℝ)
    (hn : 0 < n) (hsupp : ∀ j ∉ S, θstar.ofLp j = 0)
    (hA3 : LowerEigenvalue X S cmin) (hcmin : 0 < cmin)
    (hA4 : MutualIncoherence X S α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlampos : 0 < lam) (hlam : lam ≥ (2 / (1 - α)) * projNoiseLinf X S w)
    (βhat : EuclideanSpace ℝ (Fin d))
    (hopt : IsLassoEstimator X (designMap X θstar + w) lam βhat) :
    linfNorm (restrict S (βhat - θstar)) ≤ supportRecoveryBound X S w lam := by
  sorry

/-- **Theorem 7.21 (d) — no false exclusion** (Wainwright §7.5): the Lasso recovers every
support coordinate whose magnitude exceeds the bound; hence variable-selection consistency
when `min_{i∈S}|θ*_i| > B(λ;X)`. -/
theorem lasso_support_recovery_no_false_exclusion (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d)) (θstar : EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin n)) (lam α cmin : ℝ)
    (hn : 0 < n) (hsupp : ∀ j ∉ S, θstar.ofLp j = 0)
    (hA3 : LowerEigenvalue X S cmin) (hcmin : 0 < cmin)
    (hA4 : MutualIncoherence X S α) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlampos : 0 < lam) (hlam : lam ≥ (2 / (1 - α)) * projNoiseLinf X S w)
    (βhat : EuclideanSpace ℝ (Fin d))
    (hopt : IsLassoEstimator X (designMap X θstar + w) lam βhat)
    (i : Fin d) (hiS : i ∈ S)
    -- USER-INPUT: the coordinate exceeds the bound, |θ*_i| > B(λ;X); Wainwright §7.5 (d)
    (hbig : supportRecoveryBound X S w lam < |θstar.ofLp i|) :
    βhat.ofLp i ≠ 0 := by
  sorry

end StatLean.HighDimensionalStatistics
