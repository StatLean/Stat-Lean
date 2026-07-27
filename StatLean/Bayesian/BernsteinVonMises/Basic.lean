import StatLean.Bayesian.BernsteinVonMises.Defs

/-!
# Bernstein–von Mises: basic properties of the local model

Elementary lemmas about the data model of `Defs.lean`: the local rescaling and its inverse,
and measurability of the centering sequence.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, p. 139.

**Proof formalization notes.** Pure wiring: `smul_smul` and `inv_mul_cancel₀` for the scale
inverses (`√n ≠ 0` for `n ≥ 1`), continuous-linear-map composition for the measurability of
the centering sequence.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open AsymptoticStatistics.AsymptoticRepresentation (scoreSum)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]

lemma bvmLocalUnscale_bvmLocalScale (θ₀ : EuclideanSpace ℝ (Fin k)) {n : ℕ}
    -- LEAN-ONLY: `√n ≠ 0` needs `1 ≤ n`; the `n = 0` case is junk
    (hn : 1 ≤ n) (θ : EuclideanSpace ℝ (Fin k)) :
    bvmLocalUnscale θ₀ n (bvmLocalScale θ₀ n θ) = θ := by
  sorry

lemma bvmLocalScale_bvmLocalUnscale (θ₀ : EuclideanSpace ℝ (Fin k)) {n : ℕ}
    -- LEAN-ONLY: `√n ≠ 0` needs `1 ≤ n`; the `n = 0` case is junk
    (hn : 1 ≤ n) (h : EuclideanSpace ℝ (Fin k)) :
    bvmLocalScale θ₀ n (bvmLocalUnscale θ₀ n h) = h := by
  sorry

lemma measurable_bvmEffScore (J : Matrix (Fin k) (Fin k) ℝ)
    {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc) (n : ℕ) :
    Measurable (bvmEffScore J sc n) := by
  sorry

end StatLean.Bayesian
