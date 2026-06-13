import Mathlib.Analysis.InnerProductSpace.Adjoint
import StatLean.HighDimensionalStatistics.Lasso.Defs

/-!
# Deterministic ℓ² rate of the Lasso estimator (Lu §8, thm:re)

This file proves the **deterministic** (noise-free) ℓ² rate bound

  `‖β̂ − β*‖ ≤ (3/κ) · √s · λ`

for a Lasso estimator `β̂` satisfying `IsLassoEstimator X Y λ β̂` under the
restricted eigenvalue condition `RE(κ, 3)` and the tuning condition
`λ ≥ (2/n) · ‖Xᵀε‖∞`.  All hypotheses are deterministic; no probability
appears.  The proof follows the standard basic-inequality argument from
Lu, *Big Data Analysis* §8 (theorem tag `thm:re`).

**Proof sketch.**
1. From `IsLassoEstimator` at `β = β*` derive the *basic inequality*
   `(1/2n)‖XΔ‖² ≤ (1/n)⟨ε, XΔ⟩ + λ(‖β*‖₁ − ‖β̂‖₁)` where `Δ = β̂ − β*`.
2. Bound the noise term via the adjoint identity `⟨ε, XΔ⟩ = ⟨Xᵀε, Δ⟩` and
   Hölder `|⟨·,·⟩| ≤ ‖·‖₁·‖·‖∞` to get `(1/n)⟨ε, XΔ⟩ ≤ (λ/2)‖Δ‖₁`.
3. Use the support decomposition `‖β*‖₁ − ‖β̂‖₁ ≤ ‖Δ_S‖₁ − ‖Δ_{Sᶜ}‖₁`
   to show `Δ ∈ reCone S 3`.
4. Apply `RestrictedEigenvalue` and Cauchy–Schwarz `‖·_S‖₁ ≤ √s·‖·‖₂` to
   close `κ‖Δ‖² ≤ 3λ√s·‖Δ‖ ⟹ ‖Δ‖ ≤ (3/κ)√s·λ`.
-/

open Matrix

namespace StatLean.HighDimensionalStatistics

open scoped InnerProductSpace

variable {n d : ℕ}

/-! ## Helper lemmas -/

/-- **Adjoint identity**: `⟨ε, XΔ⟩ = ⟨Xᵀε, Δ⟩`.
Uses `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` from Mathlib. -/
private lemma inner_designMap_transpose (X : Matrix (Fin n) (Fin d) ℝ)
    (ε : EuclideanSpace ℝ (Fin n)) (Δ : EuclideanSpace ℝ (Fin d)) :
    ⟪ε, designMap X Δ⟫_ℝ = ⟪designMap Xᵀ ε, Δ⟫_ℝ := by
  unfold designMap
  -- For real matrices conjTranspose = transpose; the adjoint identity then gives the result.
  have h : Xᵀ.toEuclideanLin = X.toEuclideanLin.adjoint := by
    have := Matrix.toEuclideanLin_conjTranspose_eq_adjoint X
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  rw [h]
  -- LinearMap.adjoint_inner_left (A : E →ₗ[𝕜] F) (x : E) (y : F) :
  --   ⟪adjoint A y, x⟫ = ⟪y, A x⟫
  exact (LinearMap.adjoint_inner_left (𝕜 := ℝ) _ Δ ε).symm

/-- The ℓ¹ norm splits as the sum over `S` and `Sᶜ`. -/
private lemma l1Norm_eq_restrict_add_compl (S : Finset (Fin d)) (β : EuclideanSpace ℝ (Fin d)) :
    l1Norm β = l1Norm (restrict S β) + l1Norm (restrict Sᶜ β) := by
  simp only [l1Norm_restrict_eq_sum]
  unfold l1Norm
  linarith [Finset.sum_add_sum_compl S (fun i => |β.ofLp i|)]

/-- When `βstar` is supported on `S`, `l1Norm βstar = l1Norm (restrict S βstar)`. -/
private lemma l1Norm_of_support (S : Finset (Fin d)) (βstar : EuclideanSpace ℝ (Fin d))
    (hS : ∀ j ∉ S, βstar.ofLp j = 0) :
    l1Norm βstar = l1Norm (restrict S βstar) := by
  rw [l1Norm_eq_restrict_add_compl S βstar]
  have hzero : l1Norm (restrict Sᶜ βstar) = 0 := by
    rw [l1Norm_restrict_eq_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simp [hS i (Finset.mem_compl.mp hi)]
  linarith [l1Norm_nonneg (restrict Sᶜ βstar)]

/-- When `βstar` is zero on `Sᶜ`, the complement-restriction of `βhat − βstar`
equals that of `βhat`. -/
private lemma l1Norm_restrict_compl_sub (S : Finset (Fin d))
    (βhat βstar : EuclideanSpace ℝ (Fin d))
    (hS : ∀ j ∉ S, βstar.ofLp j = 0) :
    l1Norm (restrict Sᶜ (βhat - βstar)) = l1Norm (restrict Sᶜ βhat) := by
  simp only [l1Norm_restrict_eq_sum, WithLp.ofLp_sub,
             Pi.sub_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hiS : i ∉ S := Finset.mem_compl.mp hi
  simp [hS i hiS]

/-- **Support decomposition**: when `βstar` is supported on `S` and `Δ = βhat − β*`,
`l1Norm β* − l1Norm β̂ ≤ ‖Δ_S‖₁ − ‖Δ_{Sᶜ}‖₁`. -/
private lemma l1Norm_support_decomp (S : Finset (Fin d))
    (βhat βstar : EuclideanSpace ℝ (Fin d))
    (hS : ∀ j ∉ S, βstar.ofLp j = 0) :
    l1Norm βstar - l1Norm βhat ≤
      l1Norm (restrict S (βhat - βstar)) - l1Norm (restrict Sᶜ (βhat - βstar)) := by
  have hβs : l1Norm βstar = l1Norm (restrict S βstar) :=
    l1Norm_of_support S βstar hS
  have hβh : l1Norm βhat = l1Norm (restrict S βhat) + l1Norm (restrict Sᶜ βhat) :=
    l1Norm_eq_restrict_add_compl S βhat
  have hSc : l1Norm (restrict Sᶜ (βhat - βstar)) = l1Norm (restrict Sᶜ βhat) :=
    l1Norm_restrict_compl_sub S βhat βstar hS
  -- Triangle: ‖βstar_S‖₁ ≤ ‖βhat_S‖₁ + ‖(βhat − βstar)_S‖₁
  have htri : l1Norm (restrict S βstar) ≤
      l1Norm (restrict S βhat) + l1Norm (restrict S (βhat - βstar)) := by
    simp only [l1Norm_restrict_eq_sum, WithLp.ofLp_sub, Pi.sub_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc |βstar.ofLp i|
        = |βhat.ofLp i + (βstar.ofLp i - βhat.ofLp i)| := by ring_nf
      _ ≤ |βhat.ofLp i| + |βstar.ofLp i - βhat.ofLp i| := abs_add_le _ _
      _ = |βhat.ofLp i| + |βhat.ofLp i - βstar.ofLp i| := by rw [abs_sub_comm]
  linarith

/-! ## Main theorem -/

/-- **Deterministic ℓ² rate of the Lasso** (Lu, *Big Data Analysis* §8, `thm:re`).

Given the fixed-design linear model `Y = Xβ* + ε`, a Lasso estimator `β̂`, the
restricted eigenvalue condition `RE(κ, 3)`, and the tuning condition
`λ ≥ (2/n)·‖Xᵀε‖∞`, the error `‖β̂ − β*‖₂ ≤ (3/κ)·√s·λ`
where `s = |S|` is the sparsity of `β*`. -/
theorem lasso_l2_rate
    (X : Matrix (Fin n) (Fin d) ℝ)
    (βstar : EuclideanSpace ℝ (Fin d))
    (S : Finset (Fin d))
    (ε : EuclideanSpace ℝ (Fin n))
    (Y : EuclideanSpace ℝ (Fin n))
    (lam κ : ℝ)
    (βhat : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: n > 0; Lu-BDA §8 (thm:re)
    (hn : 0 < n)
    -- USER-INPUT: κ > 0; Lu-BDA §8 (thm:re)
    (hkappa : 0 < κ)
    -- USER-INPUT: λ > 0; Lu-BDA §8 (thm:re)
    (hlam_pos : 0 < lam)
    -- USER-INPUT: restricted eigenvalue RE(κ, 3) holds; Lu-BDA §8 (thm:re)
    (hre : RestrictedEigenvalue X S κ 3)
    -- USER-INPUT: β̂ minimises the Lasso objective; Lu-BDA §8 (thm:re)
    (hLasso : IsLassoEstimator X Y lam βhat)
    -- USER-INPUT: linear model Y = Xβ* + ε; Lu-BDA §8 (thm:re)
    (hY : Y = designMap X βstar + ε)
    -- USER-INPUT: β* supported on S (β*_j = 0 for j ∉ S); Lu-BDA §8 (thm:re)
    (hS : ∀ j ∉ S, βstar.ofLp j = 0)
    -- USER-INPUT: tuning condition λ ≥ (2/n)·‖Xᵀε‖∞; Lu-BDA §8 (thm:re)
    (hlam : lam ≥ (2 / (n : ℝ)) * linfNorm (designMap Xᵀ ε)) :
    ‖βhat - βstar‖ ≤ (3 / κ) * Real.sqrt (S.card : ℝ) * lam := by
  -- Abbreviations
  set Δ := βhat - βstar with hΔ_def
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlam_nn : (0 : ℝ) ≤ lam := le_of_lt hlam_pos
  -- ── Step 1: Simplify the residual vectors ──────────────────────────────────
  -- Y − Xβ̂ = ε − XΔ,  Y − Xβ* = ε
  have hYd : Y - designMap X βhat = ε - designMap X Δ := by
    simp only [hY, hΔ_def, map_sub]; abel
  have hYs : Y - designMap X βstar = ε := by
    simp only [hY]; abel
  -- ── Step 2: Basic inequality (from IsLassoEstimator at β = β*) ─────────────
  -- (1/2n)‖Y−Xβ̂‖² + λ‖β̂‖₁ ≤ (1/2n)‖Y−Xβ*‖² + λ‖β*‖₁
  have hbasic_raw :
      (1 / (2 * (n : ℝ))) * ‖Y - designMap X βhat‖ ^ 2 + lam * l1Norm βhat ≤
      (1 / (2 * (n : ℝ))) * ‖Y - designMap X βstar‖ ^ 2 + lam * l1Norm βstar := by
    have h := hLasso βstar
    simp only [lassoObjective] at h
    exact h
  -- Substitute and expand ‖ε − XΔ‖² = ‖ε‖² − 2⟨ε, XΔ⟩ + ‖XΔ‖²
  rw [hYd, hYs, norm_sub_sq_real] at hbasic_raw
  -- Rearrange: (1/2n)‖XΔ‖² ≤ (1/n)⟨ε, XΔ⟩ + λ(‖β*‖₁ − ‖β̂‖₁)
  have hbasic :
      (1 / (2 * (n : ℝ))) * ‖designMap X Δ‖ ^ 2 ≤
      (1 / (n : ℝ)) * ⟪ε, designMap X Δ⟫_ℝ + lam * (l1Norm βstar - l1Norm βhat) := by
    nlinarith [hbasic_raw, l1Norm_nonneg βhat, l1Norm_nonneg βstar,
               sq_nonneg ‖designMap X Δ‖,
               show (1 / (2 * (n : ℝ))) *
                    (‖ε‖ ^ 2 - 2 * ⟪ε, designMap X Δ⟫_ℝ + ‖designMap X Δ‖ ^ 2) =
                    (1 / (2 * (n : ℝ))) * ‖ε‖ ^ 2 -
                    (1 / (n : ℝ)) * ⟪ε, designMap X Δ⟫_ℝ +
                    (1 / (2 * (n : ℝ))) * ‖designMap X Δ‖ ^ 2 from by ring]
  -- ── Step 3: Noise bound ────────────────────────────────────────────────────
  -- (1/n)⟨ε, XΔ⟩ = (1/n)⟨Xᵀε, Δ⟩ ≤ (1/n)‖Xᵀε‖∞·‖Δ‖₁ ≤ (λ/2)‖Δ‖₁
  have hnoise : (1 / (n : ℝ)) * ⟪ε, designMap X Δ⟫_ℝ ≤ (lam / 2) * l1Norm Δ := by
    rw [inner_designMap_transpose, real_inner_comm]
    -- tuning: (1/n)·linfNorm(Xᵀε) ≤ λ/2
    have hlinf : (1 / (n : ℝ)) * linfNorm (designMap Xᵀ ε) ≤ lam / 2 := by
      nlinarith [linfNorm_nonneg (designMap Xᵀ ε),
                 show (1 / (n : ℝ)) * linfNorm (designMap Xᵀ ε) * 2 =
                      (2 / (n : ℝ)) * linfNorm (designMap Xᵀ ε) from by ring]
    have hh := abs_inner_le_l1Norm_mul_linfNorm Δ (designMap Xᵀ ε)
    calc (1 / (n : ℝ)) * ⟪Δ, designMap Xᵀ ε⟫_ℝ
        ≤ (1 / (n : ℝ)) * |⟪Δ, designMap Xᵀ ε⟫_ℝ| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ (1 / (n : ℝ)) * (l1Norm Δ * linfNorm (designMap Xᵀ ε)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
      _ = l1Norm Δ * ((1 / (n : ℝ)) * linfNorm (designMap Xᵀ ε)) := by ring
      _ ≤ l1Norm Δ * (lam / 2) :=
            mul_le_mul_of_nonneg_left hlinf (l1Norm_nonneg _)
      _ = (lam / 2) * l1Norm Δ := by ring
  -- ── Step 4: Support decomposition ─────────────────────────────────────────
  -- λ(‖β*‖₁ − ‖β̂‖₁) ≤ λ(‖Δ_S‖₁ − ‖Δ_{Sᶜ}‖₁)
  have hdecomp : lam * (l1Norm βstar - l1Norm βhat) ≤
      lam * (l1Norm (restrict S Δ) - l1Norm (restrict Sᶜ Δ)) :=
    mul_le_mul_of_nonneg_left (l1Norm_support_decomp S βhat βstar hS) hlam_nn
  -- l1Norm Δ = ‖Δ_S‖₁ + ‖Δ_{Sᶜ}‖₁
  have hl1_split : l1Norm Δ = l1Norm (restrict S Δ) + l1Norm (restrict Sᶜ Δ) :=
    l1Norm_eq_restrict_add_compl S Δ
  -- Set u := ‖Δ_S‖₁, v := ‖Δ_{Sᶜ}‖₁ for readability
  set u := l1Norm (restrict S Δ) with hu_def
  set v := l1Norm (restrict Sᶜ Δ) with hv_def
  have hu : 0 ≤ u := l1Norm_nonneg _
  have hv : 0 ≤ v := l1Norm_nonneg _
  -- ── Step 5: Combine → (1/2n)‖XΔ‖² + (λ/2)v ≤ (3λ/2)u ──────────────────
  have hXD_sq_bound :
      (1 / (2 * (n : ℝ))) * ‖designMap X Δ‖ ^ 2 ≤ (3 * lam / 2) * u - (lam / 2) * v := by
    calc (1 / (2 * (n : ℝ))) * ‖designMap X Δ‖ ^ 2
        ≤ (1 / (n : ℝ)) * ⟪ε, designMap X Δ⟫_ℝ + lam * (l1Norm βstar - l1Norm βhat) := hbasic
      _ ≤ (lam / 2) * l1Norm Δ + lam * (u - v) := by linarith [hnoise, hdecomp]
      _ = (lam / 2) * (u + v) + lam * (u - v) := by rw [hl1_split]
      _ = (3 * lam / 2) * u - (lam / 2) * v := by ring
  -- ── Step 6: Cone condition Δ ∈ reCone S 3 ─────────────────────────────────
  -- From (lam/2)v ≤ (3lam/2)u and lam > 0, divide to get v ≤ 3u.
  have hcone : Δ ∈ reCone S 3 := by
    unfold reCone; simp only [Set.mem_setOf_eq]
    -- v ≤ 3 * u
    have hlam2 : (0 : ℝ) < lam / 2 := by linarith
    have hkey : (lam / 2) * v ≤ (lam / 2) * (3 * u) := by
      have hnn : (0 : ℝ) ≤ (1 / (2 * (n : ℝ))) * ‖designMap X Δ‖ ^ 2 := by positivity
      nlinarith [hXD_sq_bound]
    exact le_of_mul_le_mul_left hkey hlam2
  -- ── Step 7: Apply RestrictedEigenvalue ────────────────────────────────────
  -- κ·‖Δ‖² ≤ (1/n)·‖XΔ‖²
  have hre_bound : κ * ‖Δ‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designMap X Δ‖ ^ 2 :=
    hre Δ hcone
  -- ── Step 8: Upper bound on (1/n)·‖XΔ‖² ──────────────────────────────────
  -- (1/n)·‖XΔ‖² = 2·(1/2n)·‖XΔ‖² ≤ 2·(3λ/2)·u = 3λ·u
  have hXD_upper : (1 / (n : ℝ)) * ‖designMap X Δ‖ ^ 2 ≤ 3 * lam * u := by
    nlinarith [hXD_sq_bound, mul_nonneg hlam_nn hv,
               show (1 / (n : ℝ)) * ‖designMap X Δ‖ ^ 2 =
                    2 * ((1 / (2 * (n : ℝ))) * ‖designMap X Δ‖ ^ 2) from by ring,
               show (3 : ℝ) * lam * u = 2 * ((3 * lam / 2) * u) from by ring]
  -- ── Step 9: Cauchy–Schwarz + chain ────────────────────────────────────────
  -- ‖Δ_S‖₁ ≤ √s · ‖Δ‖ (from VecNorms)
  have hCS : u ≤ Real.sqrt (S.card : ℝ) * ‖Δ‖ :=
    l1Norm_restrict_le_sqrt_card_mul_norm S Δ
  -- κ·‖Δ‖² ≤ 3·λ·√s·‖Δ‖
  have hchain : κ * ‖Δ‖ ^ 2 ≤ 3 * lam * Real.sqrt (S.card : ℝ) * ‖Δ‖ := by
    calc κ * ‖Δ‖ ^ 2
        ≤ (1 / (n : ℝ)) * ‖designMap X Δ‖ ^ 2 := hre_bound
      _ ≤ 3 * lam * u := hXD_upper
      _ ≤ 3 * lam * (Real.sqrt (S.card : ℝ) * ‖Δ‖) := by
            apply mul_le_mul_of_nonneg_left hCS; positivity
      _ = 3 * lam * Real.sqrt (S.card : ℝ) * ‖Δ‖ := by ring
  -- ── Step 10: Conclude ‖Δ‖ ≤ (3/κ)·√s·λ ──────────────────────────────────
  have hΔ_nn : 0 ≤ ‖Δ‖ := norm_nonneg _
  rcases eq_or_lt_of_le hΔ_nn with h | h
  · -- ‖Δ‖ = 0: trivially ‖Δ‖ ≤ (3/κ)·√s·λ since RHS ≥ 0
    rw [← h]
    positivity
  · -- ‖Δ‖ > 0: divide κ·‖Δ‖² ≤ 3·λ·√s·‖Δ‖ by ‖Δ‖
    -- to get κ·‖Δ‖ ≤ 3·λ·√s, then divide by κ.
    have hDiv : κ * ‖Δ‖ ≤ 3 * lam * Real.sqrt (S.card : ℝ) := by
      have hchain' : κ * ‖Δ‖ * ‖Δ‖ ≤ 3 * lam * Real.sqrt (S.card : ℝ) * ‖Δ‖ := by
        nlinarith [hchain, sq ‖Δ‖]
      exact le_of_mul_le_mul_right hchain' h
    calc ‖Δ‖
        = (1 / κ) * (κ * ‖Δ‖) := by field_simp
      _ ≤ (1 / κ) * (3 * lam * Real.sqrt (S.card : ℝ)) := by
            apply mul_le_mul_of_nonneg_left hDiv; positivity
      _ = (3 / κ) * Real.sqrt (S.card : ℝ) * lam := by ring

end StatLean.HighDimensionalStatistics
