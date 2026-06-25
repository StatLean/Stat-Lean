import StatLean.HighDimensionalStatistics.Lasso.SupportRecovery.Defs

/-!
# ℓ¹ subdifferential, convexity, and the PDW uniqueness lemma (Wainwright §7.5.2)

The convex-analytic core of the primal–dual-witness proof of Theorem 7.21:

* `l1_subgradient_iff` — `z ∈ ∂‖θ‖₁ ↔ (⟪z,θ⟫ = ‖θ‖₁ ∧ ‖z‖_∞ ≤ 1)` (dual pairing form).
* `loss_convex_gradient` — the gradient inequality of the quadratic loss `(1/2n)‖Y−Xθ‖²`.
* `lasso_minimizer_exists` — existence of a Lasso minimizer (coercive extreme-value theorem).
* `kkt_of_isLassoEstimator` — a Lasso minimizer admits a KKT subgradient certificate (7.48).
* `pdw_every_minimizer_supported` — **Lemma 7.23 (b)**: strict dual feasibility ⇒ *every*
  Lasso minimizer is supported on `S`.
* `pdw_unique` — **Lemma 7.23 (a)**: with (A3), the Lasso minimizer is unique.

Matrix-free except `pdw_unique`, whose strict-convexity step uses the (A3) `LowerEigenvalue`
quadratic-form bound on support-difference vectors. Reuses the Hölder bound
`abs_inner_le_l1Norm_mul_linfNorm` (`ForMathlib/VecNorms.lean`).
-/

open Matrix
open scoped InnerProductSpace

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- `⟪z,θ⟫ ≤ ‖θ‖₁` whenever `‖z‖_∞ ≤ 1` (Hölder ℓ¹–ℓ∞). -/
theorem inner_le_l1Norm_of_linfNorm_le_one (z θ : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: ‖z‖_∞ ≤ 1 (dual-feasible certificate); Wainwright §7.5.2
    (hz : linfNorm z ≤ 1) :
    ⟪z, θ⟫_ℝ ≤ l1Norm θ := by
  sorry

/-- **Dual-pairing characterization of `∂‖·‖₁`** (Wainwright §7.5.2):
`z ∈ ∂‖θ‖₁ ↔ ⟪z,θ⟫ = ‖θ‖₁ ∧ ‖z‖_∞ ≤ 1`. -/
theorem l1_subgradient_iff (z θ : EuclideanSpace ℝ (Fin d)) :
    IsL1Subgradient z θ ↔ (⟪z, θ⟫_ℝ = l1Norm θ ∧ linfNorm z ≤ 1) := by
  sorry

/-- **Gradient inequality of the quadratic loss** `F(θ) = (1/2n)‖Y − Xθ‖²` (convexity):
`F(θ') ≥ F(θ) + ⟪∇F(θ), θ' − θ⟫` with `∇F(θ) = (1/n) Xᵀ(Xθ − Y)`. -/
theorem loss_convex_gradient (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (θ θ' : EuclideanSpace ℝ (Fin d)) :
    (1 / (2 * (n : ℝ))) * ‖Y - designMap X θ‖ ^ 2
        + ⟪(1 / (n : ℝ)) • designMap Xᵀ (designMap X θ - Y), θ' - θ⟫_ℝ
      ≤ (1 / (2 * (n : ℝ))) * ‖Y - designMap X θ'‖ ^ 2 := by
  sorry

/-- **Existence of a Lasso minimizer** (coercive extreme-value theorem,
`Continuous.exists_forall_le'`): for `λ > 0` the Lasso objective attains its minimum. -/
theorem lasso_minimizer_exists (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ)
    -- USER-INPUT: λ > 0 (coercivity of the ℓ¹ penalty); Wainwright §7.5.2
    (hlam : 0 < lam) :
    ∃ βhat, IsLassoEstimator X Y lam βhat := by
  sorry

/-- **KKT certificate of a Lasso minimizer** (Wainwright 7.48): an optimal `θ̂` admits a
subgradient `z ∈ ∂‖θ̂‖₁` with `(1/n) Xᵀ(X θ̂ − Y) + λ z = 0`. -/
theorem kkt_of_isLassoEstimator (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (θhat : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: 0 < n; Wainwright §7.5.2
    (hn : 0 < n)
    -- USER-INPUT: θ̂ minimises the Lasso objective; Wainwright §7.5.2
    (hopt : IsLassoEstimator X Y lam θhat) :
    ∃ z, IsL1Subgradient z θhat ∧ IsKKT X Y lam θhat z := by
  sorry

/-- **Lemma 7.23 (b)** (Wainwright §7.5.2): if the primal–dual witness `(θ̂, ẑ)` satisfies
the KKT condition with `θ̂` supported on `S` and *strict* dual feasibility off `S`
(`|ẑ_j| < 1` for `j ∉ S`), then **every** Lasso minimizer `θ̃` is supported on `S`. -/
theorem pdw_every_minimizer_supported (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin d)) (lam : ℝ)
    (θhat zhat θtil : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: 0 < n; Wainwright §7.5.2
    (hn : 0 < n)
    -- USER-INPUT: witness θ̂ supported on S; Wainwright §7.5.2 (PDW step 1)
    (hsupp : ∀ j ∉ S, θhat.ofLp j = 0)
    -- USER-INPUT: ẑ ∈ ∂‖θ̂‖₁; Wainwright §7.5.2
    (hsub : IsL1Subgradient zhat θhat)
    -- USER-INPUT: KKT (7.48) holds for (θ̂, ẑ); Wainwright §7.5.2
    (hkkt : IsKKT X Y lam θhat zhat)
    -- USER-INPUT: strict dual feasibility |ẑ_j| < 1 for j ∉ S; Wainwright §7.5.2 (PDW step 3)
    (hstrict : ∀ j ∉ S, |zhat.ofLp j| < 1)
    -- USER-INPUT: θ̃ is any Lasso minimizer; Wainwright §7.5.2 (Lemma 7.23)
    (hopt : IsLassoEstimator X Y lam θtil) :
    ∀ j ∉ S, θtil.ofLp j = 0 := by
  sorry

/-- **Lemma 7.23 (a)** (Wainwright §7.5.2): under the lower-eigenvalue condition (A3), a
successful primal–dual witness implies the Lasso has a **unique** optimal solution. -/
theorem pdw_unique (X : Matrix (Fin n) (Fin d) ℝ)
    (Y : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin d)) (lam cmin : ℝ)
    (θhat zhat : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: 0 < n; Wainwright §7.5.2
    (hn : 0 < n)
    -- USER-INPUT: witness θ̂ supported on S; Wainwright §7.5.2
    (hsupp : ∀ j ∉ S, θhat.ofLp j = 0)
    -- USER-INPUT: ẑ ∈ ∂‖θ̂‖₁; Wainwright §7.5.2
    (hsub : IsL1Subgradient zhat θhat)
    -- USER-INPUT: KKT (7.48) holds; Wainwright §7.5.2
    (hkkt : IsKKT X Y lam θhat zhat)
    -- USER-INPUT: strict dual feasibility; Wainwright §7.5.2
    (hstrict : ∀ j ∉ S, |zhat.ofLp j| < 1)
    -- USER-INPUT: lower-eigenvalue condition (A3); Wainwright §7.5.1 (7.43a)
    (hA3 : LowerEigenvalue X S cmin)
    -- USER-INPUT: 0 < cmin; Wainwright §7.5.1 (7.43a)
    (hcmin : 0 < cmin) :
    ∃! βhat, IsLassoEstimator X Y lam βhat := by
  sorry

end StatLean.HighDimensionalStatistics
