import StatLean.Bayesian.DoobConsistency.Defs
import StatLean.Bayesian.DoobConsistency.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Kernel.CondDistrib

/-!
# The posterior martingale and Lévy's upward theorem

The martingale half of the proof of vdV Theorem 10.10: on the joint space
`Ω = (ℕ → 𝓧) × Θ`, the posterior probabilities `Π(A | X₁..Xₙ)` form a bounded martingale
for the observation filtration, and converge almost surely to the indicator `1_A(Θ̄)` once
the parameter is (a.e.) a measurable function of the data sequence.

* `iSup_comap_data_eq_pi` — the observation σ-algebras generate the product σ-algebra of
  the data sequence: `⨆ n, comap (restrict to first n) = pi`;
* `iSup_doobSigma_eq_comap_fst` — on the joint space, `⨆ n, doobSigma n = comap fst`;
* `doobJoint_map_data_param` — the joint law of `(X₁..Xₙ, Θ̄)` is the swapped
  `π ⊗ₘ iidKernel K n`;
* `condDistrib_doobData_eq_posterior` — the regular conditional distribution of `Θ̄` given
  `X₁..Xₙ` **is** the posterior kernel `(iidKernel K n)†π` (equality of kernels: both are
  `condKernel` of the same measure);
* `posterior_ae_tendsto_indicator` — Lévy's upward convergence of the posterior masses to
  `1_A(Θ̄)`, given a measurable a.e.-retraction of the parameter from the data (display
  (10.11), supplied by `Accessible.lean`).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.4, proof of
Theorem 10.10, pp. 149–150 (the martingale display and (10.11)).

**Proof formalization notes.** Lévy upward is `MeasureTheory.Integrable.tendsto_ae_condExp`
(real-valued, ℕ-filtration); the bridge from the kernel posterior to the conditional
expectation is `ProbabilityTheory.condDistrib_ae_eq_condExp` plus
`condDistrib_doobData_eq_posterior`. The `Filtration` structure over `doobSigma` is
assembled at the point of use from `doobSigma_mono` / `doobSigma_le`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- **The observation σ-algebras generate the sequence σ-algebra**:
`⨆ n, comap (ω ↦ (ω ∘ Fin.val : Fin n → 𝓧)) = MeasurableSpace.pi` on `ℕ → 𝓧`. -/
theorem iSup_comap_data_eq_pi :
    ⨆ n : ℕ, MeasurableSpace.comap
        (fun (ω : ℕ → 𝓧) => (fun i : Fin n => ω i.val)) inferInstance
      = (inferInstance : MeasurableSpace (ℕ → 𝓧)) := by
  sorry

/-- On the joint space, the observation filtration generates exactly the data σ-algebra:
`⨆ n, doobSigma n = comap Prod.fst`. -/
theorem iSup_doobSigma_eq_comap_fst :
    ⨆ n : ℕ, doobSigma (Θ := Θ) (𝓧 := 𝓧) n
      = MeasurableSpace.comap (Prod.fst : (ℕ → 𝓧) × Θ → ℕ → 𝓧) inferInstance := by
  sorry

/-- **The joint law of `(X₁..Xₙ, Θ̄)`** under `doobJoint` is the swapped finite joint
`(π ⊗ₘ iidKernel K n).map Prod.swap`. -/
theorem doobJoint_map_data_param (K : Kernel Θ 𝓧) [IsMarkovKernel K] (π : Measure Θ)
    [IsFiniteMeasure π] (n : ℕ) :
    (doobJoint K π).map (fun ω => (doobData n ω, ω.2))
      = (π ⊗ₘ iidKernel K n).map Prod.swap := by
  sorry

/-- **The conditional distribution of the parameter given the first `n` observations is the
posterior kernel** — an equality of kernels (both sides are `Measure.condKernel` of the
same measure, by `doobJoint_map_data_param`). -/
theorem condDistrib_doobData_eq_posterior [StandardBorelSpace Θ] [Nonempty Θ]
    (K : Kernel Θ 𝓧) [IsMarkovKernel K] (π : Measure Θ) [IsProbabilityMeasure π] (n : ℕ) :
    condDistrib (Prod.snd : (ℕ → 𝓧) × Θ → Θ) (doobData n) (doobJoint K π)
      = (iidKernel K n)†π := by
  sorry

/-- **Lévy upward convergence of the posterior masses** (vdV p. 149, the martingale
display): given a measurable a.e.-retraction of the parameter from the data sequence
(display (10.11)), for every measurable `A ⊆ Θ` the posterior masses converge
`doobJoint`-a.s. to the indicator `1_A(Θ̄)`. -/
theorem posterior_ae_tendsto_indicator [StandardBorelSpace Θ] [Nonempty Θ]
    (K : Kernel Θ 𝓧) [IsMarkovKernel K] (π : Measure Θ) [IsProbabilityMeasure π]
    -- LEAN-ONLY: display (10.11) — the parameter is a.e. a measurable function of the
    -- data; supplied by `exists_measurable_retraction` (vdV p. 149)
    (hrec : ∃ g : (ℕ → 𝓧) → Θ, Measurable g ∧
      ∀ᵐ ω ∂(doobJoint K π), g ω.1 = ω.2)
    {A : Set Θ}
    -- LEAN-ONLY: measurable parameter set (regularity)
    (hA : MeasurableSet A) :
    ∀ᵐ ω ∂(doobJoint K π),
      Tendsto (fun n => (((iidKernel K n)†π) (doobData n ω) A).toReal) atTop
        (𝓝 (A.indicator (fun _ => (1 : ℝ)) ω.2)) := by
  sorry

end StatLean.Bayesian
