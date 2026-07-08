import StatLean.Bayesian.ForMathlib.IIDKernel
import Mathlib.Probability.Kernel.Posterior

/-!
# Exchangeability and conditional independence

The easy, useful direction of de Finetti: a **conditionally i.i.d.** sample — drawn i.i.d. from
`f(·|θ)` with `θ` itself random — has an **exchangeable** marginal law, and its posterior depends on
the data only through their (permutation-invariant) empirical content. The full de Finetti
representation theorem is postponed (recorded in `roadmap.md`, Batch 4).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.5 and §3.8.2 (exchangeability and de Finetti's theorem);
§10.2 (the conditional-independence structure of hierarchical models).

**Proof formalization notes.** `IsExchangeable` is invariance of the law under coordinate
permutations. `iidKernel_map_perm` is permutation invariance of `Measure.pi` of identical factors
(`Measure.pi` is symmetric under `MeasurableEquiv.piCongrLeft`/coordinate relabelling);
`conditionallyIID_implies_exchangeable` pushes it through the mixing `∘ₘ π` (map commutes with
bind); `posterior_exchangeable_of_exchangeable_hierarchy` transports it to the posterior via the
posterior's uniqueness under the permuted joint.

**Bibliographic comments.** Exchangeability and the representation of an exchangeable sequence as a
mixture of i.i.d. sequences are due to B. de Finetti ("Funzione caratteristica di un fenomeno
aleatorio," *Atti Accad. Naz. Lincei* 4 (1931), 251–299; "La prévision," *Ann. Inst. H. Poincaré*
7 (1937), 1–68); the general (Polish-space) form is E. Hewitt and L. J. Savage (*Trans. Amer. Math.
Soc.* 80 (1955), 470–501). The conditionally-i.i.d. direction formalized here is the "if" half and
the foundation of the Bayesian reading of hierarchical models (Robert §3.8.2).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- A law on `Fin n → α` is **exchangeable** if it is invariant under permuting the coordinates
(Robert §3.8.2). -/
def IsExchangeable {n : ℕ} {α : Type*} [MeasurableSpace α] (μ : Measure (Fin n → α)) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), μ.map (fun x i => x (σ i)) = μ

/-- **Conditional group joint is permutation-invariant** (3B.1): the i.i.d. product law is
symmetric under coordinate permutations. -/
theorem iidKernel_map_perm (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (n : ℕ) (θ : Θ)
    (σ : Equiv.Perm (Fin n)) :
    (iidKernel κ n θ).map (fun x i => x (σ i)) = iidKernel κ n θ := by
  sorry

/-- **Conditionally i.i.d. ⇒ exchangeable** (3B.2): mixing an i.i.d. product over a prior gives an
exchangeable marginal (de Finetti, the easy direction). -/
theorem conditionallyIID_implies_exchangeable (κ : Kernel Θ 𝓧) [IsMarkovKernel κ] (n : ℕ)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    IsExchangeable (iidKernel κ n ∘ₘ π) := by
  sorry

/-- **Posterior is exchangeable** (3B.3): under the conditionally-i.i.d. hierarchy the posterior at
a permuted sample agrees with the posterior at the original sample, for marginal-a.e. data. -/
theorem posterior_exchangeable_of_exchangeable_hierarchy (κ : Kernel Θ 𝓧) [IsMarkovKernel κ]
    (n : ℕ) (π : Measure Θ) [IsProbabilityMeasure π] [StandardBorelSpace Θ] [Nonempty Θ]
    (σ : Equiv.Perm (Fin n)) :
    ∀ᵐ x ∂(iidKernel κ n ∘ₘ π),
      ((iidKernel κ n) † π) (fun i => x (σ i)) = ((iidKernel κ n) † π) x := by
  sorry

end StatLean.Bayesian
