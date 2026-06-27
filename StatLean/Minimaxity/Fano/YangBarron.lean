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

/-- **Yang–Barron cover bound crux** (Wainwright Lemma 15.21, Eq. (15.52)): the unnormalized sum of
the divergences to the uniform mixture `Q̄ = mixture Q` is controlled by `M·(ε² + log N)` against an
`ε`-cover `{γ k}` in √KL. Combining the two book steps:

* mixture minimization — `Σⱼ D(Qⱼ ‖ Q̄) ≤ Σⱼ D(Qⱼ ‖ G)` for the cover mixture `G = (1/N) Σₖ γ k`
  (`sum_klDiv_mixture_le` / `klDiv_mixture_minimizes`, Exercise 15.11), and
* drop-the-other-terms — `D(Qⱼ ‖ G) ≤ D(Qⱼ ‖ γ_{k(j)}) + log N` since `G ≥ (1/N) γ_{k(j)}`
  forces `dQⱼ/dG ≤ N·dQⱼ/dγ_{k(j)}`, so `∫ log(dQⱼ/dG) dQⱼ ≤ ∫ log(dQⱼ/dγ_{k(j)}) dQⱼ + log N`,

then bounding each `D(Qⱼ ‖ γ_{k(j)}) ≤ ε²` by the cover hypothesis. The `ε`-cover components `γ k`
are general measures, so the mixture-minimization step (which Mathlib only exposes for a
probability-measure reference) plus the drop-the-other-terms `log N` lemma require new
information-theoretic infrastructure in `ForMathlib/`. The `ℝ≥0∞` normalization
`(1/M)·(M·X) = X` is discharged in `yang_barron` below. -/
private lemma yang_barron_sum_le {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    {N : ℕ} (γ : Fin N → Measure 𝓧) (ε : ℝ≥0∞)
    (hcover : ∀ j, ∃ k, klDiv (Q j) (γ k) ≤ ε ^ 2) :
    ∑ j, klDiv (Q j) (mixture Q)
      ≤ (M : ℝ≥0∞) * (ε ^ 2 + ENNReal.ofReal (Real.log (N : ℝ))) := by
  -- TODO(mmx): the load-bearing step `klDiv P (mixture) ≤ klDiv P (component) + log N` plus the
  -- mixture-minimization `Σⱼ D(Qⱼ‖Q̄) ≤ Σⱼ D(Qⱼ‖G)` for the cover mixture `G = (1/N) Σₖ γ k`
  -- (general `γ k`, so Mathlib's probability-reference `sum_klDiv_mixture_le` does not directly
  -- apply); Wainwright Eq. (15.52). Named debt.
  sorry

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
  -- `I = (1/M) Σⱼ D(Qⱼ ‖ Q̄)`; the crux bounds the sum by `M·(ε² + log N)`, then `(1/M)·M = 1`.
  rw [mutualInformation]
  calc (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) (mixture Q)
      ≤ (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) * (ε ^ 2 + ENNReal.ofReal (Real.log (N : ℝ)))) := by
        gcongr
        exact yang_barron_sum_le Q γ ε hcover
    _ = ε ^ 2 + ENNReal.ofReal (Real.log (N : ℝ)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (NeZero.ne M))
          (ENNReal.natCast_ne_top M), one_mul]

end StatLean.Minimaxity
