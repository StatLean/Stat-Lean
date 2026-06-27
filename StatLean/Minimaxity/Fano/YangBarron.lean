import StatLean.Minimaxity.Fano.MutualInformation

/-!
# Yang–Barron mutual-information bound (Wainwright §15.3.5)

The Yang–Barron refinement bounds the mutual information directly by the global metric entropy of
the family in the square-root KL divergence, with no need to construct a local packing:
```
I(Z; J) ≤ inf_{ε>0} { ε² + log N_KL(ε; 𝒫) }          (Lemma 15.21, Eq. (15.51)),
```
where `N_KL(ε; 𝒫)` is the `ε`-covering number of `𝒫` in the square-root KL pseudo-distance.

We state the per-cover form: given a finite set `{γₖ}` of size `N` that `ε`-covers the family in
`√KL` (i.e. `D(P_{θʲ} ‖ γₖ) ≤ ε²` for some `k`, for each `j`), the mutual information is at most
`ε² + log N`. The infimum form (Eq. (15.51)) follows by optimizing over covers.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.5, Lemma 15.21.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]

/-- **Yang–Barron mutual-information bound** (Wainwright Lemma 15.21, Eq. (15.51), per-cover form):
if `{γ k}_{k<N}` is an `ε`-cover of the family `{Q j}` in the square-root KL divergence — meaning for
each `j` there is `k` with `D(Q j ‖ γ k) ≤ ε²` — then `I(Z; J) ≤ ε² + log N`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.5, Lemma 15.21. -/
theorem yang_barron {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    {N : ℕ} (γ : Fin N → Measure 𝓧) (ε : ℝ≥0∞)
    -- USER-INPUT: `{γ k}` is an `ε`-cover of `{Q j}` in √KL; Wainwright §15.3.5.
    (hcover : ∀ j, ∃ k, klDiv (Q j) (γ k) ≤ ε ^ 2) :
    mutualInformation Q ≤ ε ^ 2 + ENNReal.ofReal (Real.log (N : ℝ)) := by
  sorry

end StatLean.Minimaxity
