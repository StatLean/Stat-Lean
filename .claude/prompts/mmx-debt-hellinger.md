# Close the Hellinger tensorization bridge (HellingerDivergence.lean)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun.
FOREGROUND builds only. 0 sorries.

## Touch-set (edit ONLY) — `StatLean/Minimaxity/ForMathlib/HellingerDivergence.lean`
Close `sqHellinger_pi_le_nsmul_aux`: `sqHellinger (Measure.pi μ) (Measure.pi ν) ≤ n • sqHellinger μ ν`.
Keep public signature/docstring UNCHANGED. Helpers `private`.

## Strategy — bridge our `sqHellinger` to the StatLean eLpNorm Hellinger product
REUSE (cross-area, already imported): `StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct` —
`hellinger_product_eLpNorm_le_sqrt_n_per_sample` (eLpNorm form of Eq 15.12b),
`one_sub_pow_le_nsmul_one_sub`, `hellinger_affinity_pi_eq_pow`, `prod_sqrt_eq_sqrt_prod_toReal`.
Our `sqHellinger μ ν = ∫⁻ x, ofReal((√p−√q)²) ∂(μ+ν)` where `p=μ.rnDeriv(μ+ν)`. The StatLean lemma is in
`eLpNorm (√(dμ/dξ) − √(dν/dξ)) 2 ξ` form with dominating `ξ`; note `(eLpNorm f 2 ξ)².toReal = ∫⁻ ofReal(f²)`
for the L² norm. KEY identity: `sqHellinger μ ν = ((eLpNorm (fun x => √(μ.rnDeriv (μ+ν) x).toReal −
√(ν.rnDeriv (μ+ν) x).toReal) 2 (μ+ν))).toReal²` (or its ℝ≥0∞ form). Establish the bridge lemma
(`sqHellinger = eLpNorm²`) — possibly needing `μ+ν` as the dominating measure for both the n-fold product
and single (`Measure.pi (μ+ν)` vs `Measure.pi μ + Measure.pi ν` — check which `ξ` the StatLean lemma uses
and align; it takes `hμ : μ ≪ ξ`, `hν : ν ≪ ξ`, so pick `ξ = μ+ν`), then square the eLpNorm √n inequality.
Coercion-heavy (`ENNReal.toReal`, `Real.sq_sqrt`, `eLpNorm` two = `(∫⁻ ‖·‖^2)^(1/2)`). Time-box.

Lift a genuinely-stuck coercion sub-step to a SMALLER named `private` sorry + `-- TODO(mmx)`.

## DONE
`lake build StatLean.Minimaxity.ForMathlib.HellingerDivergence` green; commit `git add` ONLY that file.
Report closed/residual + the bridge lemma used.
