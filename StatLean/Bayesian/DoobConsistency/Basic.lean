import StatLean.Bayesian.DoobConsistency.Defs

/-!
# Doob consistency: basic properties of the joint experiment

Elementary lemmas about the data model of `Defs.lean`: measurability of the
first-`n`-observations statistic and the filtration properties of the observation
σ-algebras.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.4, p. 149.

**Proof formalization notes.** Pure wiring: coordinate-projection measurability and
monotonicity of `MeasurableSpace.comap` along restriction maps.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

lemma measurable_doobData (n : ℕ) : Measurable (doobData (Θ := Θ) (𝓧 := 𝓧) n) := by
  sorry

lemma doobSigma_mono {m n : ℕ} (hmn : m ≤ n) :
    doobSigma (Θ := Θ) (𝓧 := 𝓧) m ≤ doobSigma n := by
  sorry

lemma doobSigma_le (n : ℕ) :
    doobSigma (Θ := Θ) (𝓧 := 𝓧) n ≤ (inferInstance : MeasurableSpace ((ℕ → 𝓧) × Θ)) := by
  sorry

end StatLean.Bayesian
