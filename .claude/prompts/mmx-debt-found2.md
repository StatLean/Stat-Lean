# Close the unblocked foundation residuals: Pinsker cores, Hellinger eLpNorm, Yang-Barron log-N

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds. Goal 0 sorry.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/PinskerInequality.lean` (close `bernoulli_pinsker_scalar` + `klDiv_ge_two_mul_tvDist_sq`)
- `StatLean/Minimaxity/ForMathlib/HellingerDivergence.lean` (close `sqHellinger_pi_le_nsmul_aux`)
- `StatLean/Minimaxity/Fano/YangBarron.lean` (close the `klDiv P (mixture) ≤ klDiv P (component) + log N` step)
Keep public signatures/docstrings UNCHANGED. Helpers `private`. These all have proof STRUCTURE with small residual sorries.

## The residuals (all now tractable)
1. `bernoulli_pinsker_scalar` (Pinsker): the scalar inequality `2(a−b)² ≤ a log(a/b)+(1−a)log((1−a)/(1−b))`
   for `a,b ∈ (0,1)` — 1-variable calculus. Fix `b`, let `g(a)=RHS−LHS`; `g(b)=0`, `g'(a)=log(a/b)−log((1−a)/(1−b))−4(a−b)`,
   `g'(b)=0`, `g''(a)=1/(a(1−a))−4 ≥ 0` (AM-GM `a(1−a)≤1/4`). So `g` convex, min 0 at `a=b`. Use `mul_log`,
   `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` no; `nlinarith`/`Real.log` derivative bounds, or
   `inner_le_nnorm`. Elementary — close it.
2. `klDiv_ge_two_mul_tvDist_sq` (Pinsker): KL data-processing under the 2-cell partition `{p≥q}`. The map
   `x ↦ 𝟙[p(x)≥q(x)]` pushes μ,ν to Bernoulli(δ_p),(δ_q); `klDiv ν μ ≥ klDiv (Bernoulli δ_q)(Bernoulli δ_p)`
   by DPI (`klDiv_comp_le`/`klDiv_map_le` — search Mathlib for the KL data-processing/`klDiv_map`), `= kl_Bern`,
   then `bernoulli_pinsker_scalar` gives `≥ 2(δ_p−δ_q)² = 2·tvDist²`. Search `klDiv_map`, `klDiv_comp`.
3. `sqHellinger_pi_le_nsmul_aux` (Hellinger): finish the eLpNorm bridge —
   `sqHellinger μ ν = ((eLpNorm (√(dμ/dξ)−√(dν/dξ)) 2 ξ)).toReal²` for ξ=μ+ν
   (`eLpNorm_eq_lintegral_rpow_enorm` p=2 → `∫⁻ ‖·‖₊²`, `ENNReal.toReal`, `Real.sq_sqrt`), then square
   `HellingerProduct.hellinger_product_eLpNorm_le_sqrt_n_per_sample`. The dominating measure for the product
   side is `Measure.pi (fun _ => μ+ν)` — confirm it equals/dominates `Measure.pi μ + Measure.pi ν` appropriately.
4. YangBarron: `klDiv (Q j) ((1/N)Σ γ_k) ≤ klDiv (Q j) γ_{k(j)} + log N`. Since `(1/N)Σγ ≥ (1/N)γ_{k(j)}`,
   `rnDeriv (Q j) ((1/N)Σγ) ≤ N · rnDeriv (Q j) γ_{k(j)}`, so `∫ log(rnDeriv) dQj ≤ ∫ log(N·rnDeriv γ) dQj
   = log N + klDiv(Qj‖γ)`. Use `Measure.rnDeriv_le_of_le`/monotonicity of rnDeriv in the 2nd measure,
   `Real.log_mul`, `klDiv_eq_integral_llr`. (`klDiv_mixture_minimizes` is already CLOSED — use it.)

## DONE: build the 3 modules green 0 sorry; `git add` only the 3 files; commit `mmx(batch9): close foundation residuals`.
Report which closed.
