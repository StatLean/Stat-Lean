# Close the 3 reduced Wave-1 residuals (small tractable cores)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds. 0 sorries.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/KLDivergence.lean`     (close the `sorry` in `klDiv_mixture_minimizes`)
- `StatLean/Minimaxity/Fano/MutualInformation.lean`      (close the `sorry` in `klDiv_le_avg`)
- `StatLean/Minimaxity/ForMathlib/HellingerDivergence.lean` (close the `sorry` in `sqHellinger_pi_le_nsmul_aux`)
Each file already has the proof STRUCTURE in place with one remaining `sorry` at a named private lemma —
close exactly that. Keep all signatures/docstrings UNCHANGED.

## The three residual cores
1. `klDiv_mixture_minimizes` (KLDivergence): the remaining step is the **Gibbs identity**
   `∑ⱼ D(Pⱼ‖Q) − ∑ⱼ D(Pⱼ‖Q̄) = M · D(Q̄‖Q) ≥ 0` (Q̄ = (1/M)Σ Pₖ). Expand each `klDiv` on the a.c. case via
   `klDiv_eq_integral_llr`/`llr`: `D(Pⱼ‖Q) − D(Pⱼ‖Q̄) = ∫ log(dQ̄/dQ) dPⱼ`; summing over j and using
   `∑ⱼ Pⱼ = M·Q̄` gives `M ∫ log(dQ̄/dQ) dQ̄ = M·D(Q̄‖Q) ≥ 0` (`klDiv_nonneg`). Handle the non-a.c. branch
   (if `Pⱼ ⋘ Q` for some j then RHS `= ∞`). Mathlib: `klDiv_eq_integral_llr`, `Measure.rnDeriv`, `llr_add`/
   `llr` chain, `integral` linearity, `klDiv_nonneg`/`0 ≤ klDiv` (ℝ≥0∞).
2. `klDiv_le_avg` (MutualInformation): lift the real `klFun` convexity (`convexOn_klFun`, Jensen on the
   `M` components) to the `lintegral`/`klDiv` form on the absolutely-continuous case. Use
   `klDiv_eq_lintegral_klFun_of_ac` and `ConvexOn.le_map_sum` / `inner_le_nnorm` for the per-point bound,
   then `lintegral_mono`. Non-a.c. branch: RHS `= ∞`.
3. `sqHellinger_pi_le_nsmul_aux` (HellingerDivergence): finish the eLpNorm bridge — establish
   `sqHellinger μ ν = ((eLpNorm (fun x => √(μ.rnDeriv (μ+ν) x).toReal − √(ν.rnDeriv (μ+ν) x).toReal) 2 (μ+ν))).toReal ^ 2`
   (L²-norm-squared = the integral of the square; `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm` with `p=2`,
   `ENNReal.toReal`, `Real.sq_sqrt`), then apply `HellingerProduct.hellinger_product_eLpNorm_le_sqrt_n_per_sample`
   squared. Pick dominating `ξ = μ+ν` for the StatLean lemma's `hμ : μ ≪ ξ`, `hν : ν ≪ ξ`.

GOAL: all three to 0-sorry. If one genuinely resists, leave ITS single named sorry and close the other two.
## DONE: build the 3 modules green, 0 sorry; `git add` only the 3 files; commit `mmx(batch9): close Wave-1 residuals`.
