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

/-- **Convexity bound on the mutual information** (Wainwright Eq. (15.34)):
`I(Z; J) ≤ (1/M²) Σⱼ Σₖ D(P_{θʲ} ‖ P_{θᵏ})`. Obtained from the convexity of the KL divergence in its
second argument (the mixture minimizes the average divergence).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.2, Eq. (15.34). -/
theorem mutualInformation_le_avg_pairwise_kl {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧)
    [IsMarkovKernel Q] :
    mutualInformation Q ≤ ((M : ℝ≥0∞) ^ 2)⁻¹ * ∑ j, ∑ k, klDiv (Q j) (Q k) := by
  sorry

end StatLean.Minimaxity
