import StatLean.ConcentrationInequalities.Orlicz.SubGaussianMGF
import StatLean.ConcentrationInequalities.Orlicz.TailToNorm

/-!
# ψ₂-norm of independent sums

For independent, mean-zero $X_1, \dots, X_n$ with $\|X_i\|_{\psi_2} \le K_i$
and weights $v \in \mathbb{R}^n$,
$$ \Bigl\|\sum_{i=1}^{n} v_i X_i\Bigr\|_{\psi_2}^2
   \;\le\; 18 \sum_{i=1}^{n} v_i^2 K_i^2. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §2.7, Proposition 2.7.1 (weighted form; the
unweighted display is the $v \equiv 1$ instance).

**Proof formalization notes.** Constant frozen: `C = 18 = 6 · 3` — the
composite of bridge B2 (`hasSubgaussianMGF_of_subGaussianNorm_le`, proxy
`3K²`, R1 freeze) routed through Mathlib's
`HasSubgaussianMGF.sum_of_iIndepFun` (proxies add) and back through bridge
B3 (`subGaussianNorm_le_of_isSubGaussian`, factor `√6`). The book's absolute
constant `C` is thus explicit; the deviation from any sharper constant is
documented here per the batch's formula+numeral rule. `hK : ∀ i, 0 < K i` is
a mild LEAN-ONLY strengthening (zero bound forces `Xᵢ = 0` a.e.). Consumed by
`Orlicz/VectorNorm.lean` (Lemma 3.4.2 upper bound, `∑ vᵢ² = ‖v‖² = 1`).
Work-item fallback: this file belongs to `hdp-orlicz-vector`, whose single
named-sorry fallback is `subGaussianVecNorm_le_of_indep` in
`Orlicz/VectorNorm.lean` — everything here must close.

**Bibliographic comments.** The rotation-invariance-style additivity of
sub-Gaussian norms under independent sums is classical (Hoeffding/Kahane);
the ψ₂-norm packaging follows HDP §2.7 and Buldygin–Kozachenko (AMS 2000,
Ch. 1).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Weighted independent sums keep sub-Gaussian MGF with additive proxies
(LEAN-ONLY composite of B2 + `mgf` scaling + `sum_of_iIndepFun`; HDP §2.7
machinery). Proxy: `∑ vᵢ² · (3 Kᵢ²)` with the R1-frozen B2 factor `3`. -/
theorem hasSubgaussianMGF_weighted_sum
    -- LEAN-ONLY: probability measure; MGF machinery
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : Fin n → ℝ≥0}
    (v : Fin n → ℝ)
    -- LEAN-ONLY: measurability of each coordinate
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence; HDP Prop 2.7.1
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero coordinates; HDP Prop 2.7.1
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive norm bounds (mild strengthening, see module notes)
    (hK : ∀ i, 0 < K i)
    -- USER-INPUT: ‖Xᵢ‖_{ψ₂} ≤ Kᵢ; HDP Prop 2.7.1
    (hnorm : ∀ i, subGaussianNorm (X i) μ ≤ K i) :
    ProbabilityTheory.HasSubgaussianMGF (fun ω => ∑ i, v i * X i ω)
      (∑ i, ⟨(v i) ^ 2, sq_nonneg _⟩ * (3 * (K i) ^ 2)) μ := by sorry

/-- **ψ₂-norm of a weighted independent sum** (HDP Proposition 2.7.1,
weighted; frozen constant `C = 18 = 6·3` from B3 ∘ B2). -/
theorem subGaussianNorm_weighted_sum_le
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : Fin n → ℝ≥0}
    (v : Fin n → ℝ)
    -- LEAN-ONLY: measurability of each coordinate
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence; HDP Prop 2.7.1
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero coordinates; HDP Prop 2.7.1
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive norm bounds (mild strengthening)
    (hK : ∀ i, 0 < K i)
    -- USER-INPUT: ‖Xᵢ‖_{ψ₂} ≤ Kᵢ; HDP Prop 2.7.1
    (hnorm : ∀ i, subGaussianNorm (X i) μ ≤ K i) :
    subGaussianNorm (fun ω => ∑ i, v i * X i ω) μ ≤
      (NNReal.sqrt (18 * ∑ i, ⟨(v i) ^ 2, sq_nonneg _⟩ * (K i) ^ 2) :
        ℝ≥0∞) := by sorry

/-- **ψ₂-norm of an independent sum** (HDP Proposition 2.7.1, the `v ≡ 1`
instance): `‖∑ Xᵢ‖_{ψ₂} ≤ √(18 ∑ Kᵢ²)`. -/
theorem subGaussianNorm_sum_le
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : Fin n → ℝ≥0}
    -- LEAN-ONLY: measurability of each coordinate
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence; HDP Prop 2.7.1
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero coordinates; HDP Prop 2.7.1
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive norm bounds (mild strengthening)
    (hK : ∀ i, 0 < K i)
    -- USER-INPUT: ‖Xᵢ‖_{ψ₂} ≤ Kᵢ; HDP Prop 2.7.1
    (hnorm : ∀ i, subGaussianNorm (X i) μ ≤ K i) :
    subGaussianNorm (fun ω => ∑ i, X i ω) μ ≤
      (NNReal.sqrt (18 * ∑ i, (K i) ^ 2) : ℝ≥0∞) := by sorry

end StatLean.ConcentrationInequalities
