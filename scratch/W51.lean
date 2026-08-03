import StatLean.HypothesisTesting.Bootstrap.NonparametricMean

open MeasureTheory

namespace W51

/-- stub of `integral_pi_sum_moments` -/
lemma integral_pi_sum_moments (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hV0 : ∫ x, V x ∂F = 0) (n : ℕ) :
    (∫ y : Fin n → ℝ, (∑ i, V (y i)) ∂(Measure.pi fun _ : Fin n => F)) = 0 ∧
      (∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 2 ∂(Measure.pi fun _ : Fin n => F))
        = n * ∫ x, V x ^ 2 ∂F ∧
      (∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 4 ∂(Measure.pi fun _ : Fin n => F))
        ≤ n * (∫ x, V x ^ 4 ∂F) + 3 * n ^ 2 * (∫ x, V x ^ 2 ∂F) ^ 2 := sorry

lemma integral_pi_sum_pow_succ (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (n p : ℕ) :
    ∫ y : Fin (n + 1) → ℝ, (∑ i, V (y i)) ^ p ∂(Measure.pi fun _ : Fin (n + 1) => F)
      = ∑ k ∈ Finset.range (p + 1), (p.choose k : ℝ) * (∫ x, V x ^ k ∂F)
          * ∫ z : Fin n → ℝ, (∑ i, V (z i)) ^ (p - k) ∂(Measure.pi fun _ : Fin n => F) := sorry

lemma integral_pi_sum_pow_three (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hV0 : ∫ x, V x ∂F = 0) (n : ℕ) :
    ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 3 ∂(Measure.pi fun _ : Fin n => F)
      = (n : ℝ) * ∫ x, V x ^ 3 ∂F := sorry

lemma integral_pi_sum_pow_six_le (F : Measure ℝ) [IsProbabilityMeasure F] {V : ℝ → ℝ}
    (hV : Measurable V) {B : ℝ} (hB : ∀ x, |V x| ≤ B) (hV0 : ∫ x, V x ∂F = 0) (n : ℕ) :
    ∫ y : Fin n → ℝ, (∑ i, V (y i)) ^ 6 ∂(Measure.pi fun _ : Fin n => F)
      ≤ (n : ℝ) * (∫ x, V x ^ 6 ∂F)
        + 15 * (n : ℝ) ^ 2 * (∫ x, V x ^ 2 ∂F) * (∫ x, V x ^ 4 ∂F)
        + 10 * (n : ℝ) ^ 2 * (∫ x, V x ^ 3 ∂F) ^ 2
        + 15 * (n : ℝ) ^ 3 * (∫ x, V x ^ 2 ∂F) ^ 3 := sorry

end W51
