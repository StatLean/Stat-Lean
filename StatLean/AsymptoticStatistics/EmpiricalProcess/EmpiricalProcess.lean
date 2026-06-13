import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Empirical process `G_n f = √n · (P_n f − P f)`

The centred, scaled empirical measure indexed by a real-valued function
`f : Ω → ℝ`. This is the central object of vdV §19.1: convergence of
`G_n` (uniformly in `f` over a class `F`) is what Glivenko–Cantelli and
Donsker theorems characterise.

Main definition: `empiricalProcess`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The **empirical process** `G_n f = √n · (P_n f − P f)`, where `P_n`
is the empirical measure of a sample `X : Fin n → Ω` and `P` is the
underlying distribution.

Operationally we use the empirical-average shorthand `empiricalAvg`
in place of `∫ f dP_n`; the two agree on measurable functions.

Edge: for `n = 0`, `empiricalAvg f 0 X = 0` and `Real.sqrt 0 = 0`, so
`empiricalProcess P 0 X f = -0 * ∫ f dP = 0`. Stated explicitly via
`empiricalProcess_zero`.

vdV §19.1: the centred, `√n`-scaled empirical measure indexed by `f`. -/
noncomputable def empiricalProcess
    (P : Measure Ω) (n : ℕ) (X : Fin n → Ω) (f : Ω → ℝ) : ℝ :=
  Real.sqrt n * (empiricalAvg f n X - ∫ x, f x ∂P)

@[simp] lemma empiricalProcess_zero (P : Measure Ω) (X : Fin 0 → Ω) (f : Ω → ℝ) :
    empiricalProcess P 0 X f = 0 := by
  simp [empiricalProcess]

lemma empiricalProcess_add (P : Measure Ω) (n : ℕ) (X : Fin n → Ω)
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P) :
    empiricalProcess P n X (fun x => f x + g x) =
      empiricalProcess P n X f + empiricalProcess P n X g := by
  unfold empiricalProcess
  rw [empiricalAvg_add, integral_add hf hg]
  ring

lemma empiricalProcess_smul (P : Measure Ω) (n : ℕ) (X : Fin n → Ω)
    (c : ℝ) (f : Ω → ℝ) :
    empiricalProcess P n X (fun x => c * f x) = c * empiricalProcess P n X f := by
  unfold empiricalProcess
  rw [empiricalAvg_smul, integral_const_mul]
  ring

end AsymptoticStatistics.EmpiricalProcess
