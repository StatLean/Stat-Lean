import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Empirical measure of a finite sample

The empirical measure `P_n = (1/n) · Σᵢ δ_{X i}` of a sample `X : Fin n → Ω`:
the natural unbiased estimator of an underlying distribution `P`. All
higher-level empirical-process objects (the centred empirical process `G_n`,
the Glivenko–Cantelli predicate, the Donsker predicate) are stated in terms
of integrals against this measure or, equivalently, against the
empirical-average shorthand `empiricalAvg`.

Main declarations: `empiricalMeasure`, `empiricalAvg`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §19.1.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **empirical measure** of a sample `X : Fin n → Ω`:

`empiricalMeasure n X = (1/n) · Σᵢ Measure.dirac (X i)`.

Edge: for `n = 0`, the indexing `Fin 0` is empty and the sum is the
zero measure; the scaling `(0 : ℝ≥0∞)⁻¹ = ∞` collapses against `0`
to leave the zero measure. The `IsProbabilityMeasure` instance is
therefore stated under `[NeZero n]`.

vdV §19.1: the natural unbiased estimator of an
underlying distribution `P`. -/
noncomputable def empiricalMeasure (n : ℕ) (X : Fin n → Ω) : Measure Ω :=
  ((n : ℝ≥0∞))⁻¹ • ∑ i, Measure.dirac (X i)

@[simp] lemma empiricalMeasure_zero (X : Fin 0 → Ω) :
    empiricalMeasure 0 X = 0 := by
  unfold empiricalMeasure
  simp

/-- The empirical measure is a probability measure for `n ≥ 1`. -/
instance instIsProbabilityMeasure_empiricalMeasure
    (n : ℕ) [NeZero n] (X : Fin n → Ω) : IsProbabilityMeasure (empiricalMeasure n X) := by
  refine ⟨?_⟩
  unfold empiricalMeasure
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
  have hsum : (∑ i : Fin n, (Measure.dirac (X i) : Measure Ω) Set.univ)
      = (n : ℝ≥0∞) := by
    have hi : ∀ i : Fin n, (Measure.dirac (X i) : Measure Ω) Set.univ = 1 :=
      fun i => Measure.dirac_apply_of_mem (Set.mem_univ _)
    simp [hi]
  rw [hsum, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (NeZero.ne n)) (natCast_ne_top n)

/-- The **empirical average** of `f` on the sample `X`:
`empiricalAvg f n X = (1/n) · Σᵢ f (X i)`.

Edge: for `n = 0`, the sum is empty and the prefactor `(0 : ℝ)⁻¹ = 0`
in Lean's convention, so the whole expression is `0`.

This is the real-valued shorthand for `∫ f d(empiricalMeasure n X)`,
the form used in the proof of vdV Theorem 19.4. -/
noncomputable def empiricalAvg (f : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (X i)

omit [MeasurableSpace Ω] in
@[simp] lemma empiricalAvg_zero (f : Ω → ℝ) (X : Fin 0 → Ω) :
    empiricalAvg f 0 X = 0 := by
  simp [empiricalAvg]

omit [MeasurableSpace Ω] in
@[simp] lemma empiricalAvg_const_zero (n : ℕ) (X : Fin n → Ω) :
    empiricalAvg (fun _ => (0 : ℝ)) n X = 0 := by
  simp [empiricalAvg]

omit [MeasurableSpace Ω] in
lemma empiricalAvg_add (f g : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) :
    empiricalAvg (fun x => f x + g x) n X = empiricalAvg f n X + empiricalAvg g n X := by
  unfold empiricalAvg
  rw [Finset.sum_add_distrib, mul_add]

omit [MeasurableSpace Ω] in
lemma empiricalAvg_smul (c : ℝ) (f : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) :
    empiricalAvg (fun x => c * f x) n X = c * empiricalAvg f n X := by
  unfold empiricalAvg
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (n : ℝ)⁻¹ c, mul_assoc]

end AsymptoticStatistics.EmpiricalProcess
