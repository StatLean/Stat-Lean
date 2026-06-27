import StatLean.Minimaxity.Defs
import StatLean.Minimaxity.ForMathlib.KLDivergence

/-!
# Mutual information for M-ary testing (Wainwright §15.3.1)

For the M-ary testing problem (index `J` uniform on `[M]`, observation `Z ∼ P_{θᴶ}`), the mutual
information `I(Z; J)` measures how much the observation reveals about the index. Wainwright defines
it as the KL divergence between the joint law and the product of marginals (Eq. (15.29)),
`I(Z, J) = D(ℚ_{Z,J} ‖ ℚ_Z ℚ_J)`, which (Eq. (15.30)) equals the average KL divergence between each
component and the mixture:
```
I(Z; J) = (1/M) Σⱼ D(P_{θʲ} ‖ Q̄),     Q̄ = (1/M) Σⱼ P_{θʲ}.
```
We take Eq. (15.30) as the definition (it is the form used in the bounds) and prove the convexity
upper bound (Eq. (15.34))
```
I(Z; J) ≤ (1/M²) Σⱼ Σₖ D(P_{θʲ} ‖ P_{θᵏ}),
```
which controls the mutual information by the pairwise KL divergences for local-packing arguments.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.1.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]

/-- **Mutual information** of the M-ary testing problem (Wainwright Eq. (15.30)):
`I(Z; J) = (1/M) Σⱼ D(P_{θʲ} ‖ Q̄)`, the average KL divergence between each component `Q j = P_{θʲ}`
and the uniform mixture `Q̄`. Equivalent to the KL divergence between the joint and product laws
(Eq. (15.29)).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.1, Eq. (15.30). -/
noncomputable def mutualInformation {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) : ℝ≥0∞ :=
  (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) (mixture Q)

/-- The uniform mixture written as an explicit scaled finite sum:
`Q̄ = Q ∘ₘ Unif[M] = (1/M) Σₖ Q k`. This unfolds the kernel/prior composition `mixture` into the
sum form used by the convexity estimates. -/
lemma mixture_eq_inv_smul_sum {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) :
    mixture Q = (M : ℝ≥0∞)⁻¹ • ∑ k, Q k := by
  rw [mixture, Measure.comp_eq_sum_of_countable, Measure.sum_fintype]
  have hpt : ∀ k : Fin M, (uniformPrior M) {k} = (M : ℝ≥0∞)⁻¹ := by
    intro k
    rw [uniformPrior, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k),
      PMF.uniformOfFintype_apply, Fintype.card_fin]
  simp_rw [hpt]
  rw [← Finset.smul_sum]

open Real in
/-- **Pointwise convexity of `klFun` along the perspective direction.** For `A ≥ 0`, weights
`B k ≥ 0` summing to `M`, and any `D k` with `D k · B k = A` (so `D k = A / B k` where `B k > 0`),
the value `klFun A` is bounded by the `B`-average of `klFun (D k)`:
`klFun A ≤ (1/M) Σₖ B k · klFun (D k)`. This is the real-analytic heart of the second-argument
convexity of `klDiv` (the perspective `(p, q) ↦ q · klFun(p/q)` is jointly convex); the proof
reduces, after expanding `klFun x = x log x + 1 - x`, to concavity of `log`
(`Real.strictConcaveOn_log_Ioi`), which forces `(1/M) Σₖ log (B k) ≤ log 1 = 0`. -/
private lemma klFun_le_avg_real {M : ℕ} (hM : 0 < M) {A : ℝ} (hA : 0 ≤ A)
    {B D : Fin M → ℝ} (hB : ∀ k, 0 ≤ B k) (hBD : ∀ k, D k * B k = A)
    (hsumB : ∑ k, B k = (M : ℝ)) :
    klFun A ≤ (M : ℝ)⁻¹ * ∑ k, B k * klFun (D k) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rcases hA.lt_or_eq with hApos | hA0
  · -- `0 < A`: every weight is positive and `D k = A / B k`.
    have hBpos : ∀ k, 0 < B k := by
      intro k
      rcases (hB k).lt_or_eq with h | h
      · exact h
      · exfalso; have hk := hBD k; rw [← h, mul_zero] at hk; exact hApos.ne' hk.symm
    have hD : ∀ k, D k = A / B k := fun k => by
      rw [eq_div_iff (hBpos k).ne']; exact hBD k
    have hterm : ∀ k, B k * klFun (D k) = A * log A - A * log (B k) + B k - A := by
      intro k
      rw [hD k, klFun_apply, Real.log_div hApos.ne' (hBpos k).ne']
      field_simp [(hBpos k).ne']
    have key : ∑ k, B k * klFun (D k)
        = (M : ℝ) * (A * log A + 1 - A) - A * ∑ k, log (B k) := by
      rw [Finset.sum_congr rfl (fun k _ => hterm k)]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hsumB]
      ring
    have hjensen : (M : ℝ)⁻¹ * ∑ k, log (B k) ≤ 0 := by
      have hconc := (strictConcaveOn_log_Ioi).concaveOn
      have hw : ∀ k ∈ (Finset.univ : Finset (Fin M)), (0 : ℝ) ≤ (M : ℝ)⁻¹ :=
        fun k _ => by positivity
      have hw1 : ∑ _k : Fin M, (M : ℝ)⁻¹ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_inv_cancel₀ hMr.ne']
      have hmem : ∀ k ∈ (Finset.univ : Finset (Fin M)), B k ∈ Set.Ioi (0 : ℝ) :=
        fun k _ => hBpos k
      have hjs := hconc.le_map_sum hw hw1 hmem
      simp only [smul_eq_mul, ← Finset.mul_sum, hsumB] at hjs
      rwa [inv_mul_cancel₀ hMr.ne', Real.log_one] at hjs
    have hAjensen : A * ((M : ℝ)⁻¹ * ∑ k, log (B k)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hApos.le hjensen
    rw [klFun_apply]
    have hrhs : (M : ℝ)⁻¹ * ∑ k, B k * klFun (D k)
        = (A * log A + 1 - A) - A * ((M : ℝ)⁻¹ * ∑ k, log (B k)) := by
      rw [key, mul_sub, ← mul_assoc, inv_mul_cancel₀ hMr.ne', one_mul]; ring
    rw [hrhs]; linarith
  · -- `A = 0`: each term equals `B k`, so the average is `1 = klFun 0`.
    have hterm0 : ∀ k, B k * klFun (D k) = B k := by
      intro k
      rcases (hB k).lt_or_eq with h | h
      · have hDk : D k = 0 := by
          have hk := hBD k
          rw [← hA0, mul_eq_zero] at hk
          rcases hk with h1 | h2
          · exact h1
          · exact absurd h2 h.ne'
        rw [hDk, klFun_zero, mul_one]
      · rw [← h, zero_mul]
    have hL : klFun A = 1 := by rw [← hA0]; exact klFun_zero
    have hR : (M : ℝ)⁻¹ * ∑ k, B k * klFun (D k) = 1 := by
      rw [Finset.sum_congr rfl (fun k _ => hterm0 k), hsumB, inv_mul_cancel₀ hMr.ne']
    exact le_of_eq (hL.trans hR.symm)

/-- **Convexity of the KL divergence in its second argument** (Jensen): the divergence from a
fixed component `Q j` to the uniform mixture `Q̄ = (1/M) Σₖ Q k` is at most the average of the
divergences to the components, `D(Q j ‖ Q̄) ≤ (1/M) Σₖ D(Q j ‖ Q k)`. This is the analytic core of
Wainwright Eq. (15.34); it follows from the joint convexity of `(p, q) ↦ q · klFun(p/q)` (the
perspective of the strictly convex `klFun`), which Mathlib does not yet package for `klDiv`.

The non-absolutely-continuous case is discharged here (the right-hand side is `∞`); the remaining
absolutely-continuous case reduces, via `klDiv_eq_lintegral_klFun_of_ac` against the reference
`mixture Q` and the Radon–Nikodym chain rule `Measure.rnDeriv_mul_rnDeriv`, to the pointwise bound
`klFun_le_avg_real` integrated over `mixture Q`. -/
private lemma klDiv_le_avg {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    (j : Fin M) :
    klDiv (Q j) (mixture Q) ≤ (M : ℝ≥0∞)⁻¹ * ∑ k, klDiv (Q j) (Q k) := by
  by_cases hAC : ∀ k, Q j ≪ Q k
  · -- TODO(mmx): absolutely-continuous case — lift `klFun_le_avg_real` to the lintegral form via
    -- `klDiv_eq_lintegral_klFun_of_ac` (reference `mixture Q`) + `Measure.rnDeriv_mul_rnDeriv`
    -- + `mixture_eq_inv_smul_sum`; Wainwright Eq. (15.34).
    sorry
  · rw [not_forall] at hAC
    obtain ⟨k₀, hk₀⟩ := hAC
    have htop : klDiv (Q j) (Q k₀) = ⊤ := klDiv_of_not_ac hk₀
    have hle : klDiv (Q j) (Q k₀) ≤ ∑ k, klDiv (Q j) (Q k) :=
      Finset.single_le_sum (f := fun k => klDiv (Q j) (Q k)) (fun i _ => zero_le _)
        (Finset.mem_univ k₀)
    have hsum : ∑ k, klDiv (Q j) (Q k) = ⊤ := top_le_iff.mp (htop ▸ hle)
    rw [hsum, ENNReal.mul_top (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M))]
    exact le_top

/-- **Convexity bound on the mutual information** (Wainwright Eq. (15.34)):
`I(Z; J) ≤ (1/M²) Σⱼ Σₖ D(P_{θʲ} ‖ P_{θᵏ})`. Obtained from the convexity of the KL divergence in its
second argument (the mixture minimizes the average divergence).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.2, Eq. (15.34). -/
theorem mutualInformation_le_avg_pairwise_kl {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧)
    [IsMarkovKernel Q] :
    mutualInformation Q ≤ ((M : ℝ≥0∞) ^ 2)⁻¹ * ∑ j, ∑ k, klDiv (Q j) (Q k) := by
  unfold mutualInformation
  calc (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) (mixture Q)
      ≤ (M : ℝ≥0∞)⁻¹ * ∑ j, ((M : ℝ≥0∞)⁻¹ * ∑ k, klDiv (Q j) (Q k)) := by
        gcongr with j
        exact klDiv_le_avg Q j
    _ = (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞)⁻¹ * ∑ j, ∑ k, klDiv (Q j) (Q k)) := by
        rw [← Finset.mul_sum]
    _ = ((M : ℝ≥0∞) ^ 2)⁻¹ * ∑ j, ∑ k, klDiv (Q j) (Q k) := by
        rw [← mul_assoc, sq,
          ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top M))
            (Or.inl (ENNReal.natCast_ne_top M))]

end StatLean.Minimaxity
