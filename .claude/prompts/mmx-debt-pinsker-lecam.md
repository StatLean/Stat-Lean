# Close Pinsker (Ex 15.6) + Le Cam (Ex 15.5) half-lintegral cruxes

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds only.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/PinskerInequality.lean`  (`pinsker_half_lintegral_le`)
- `StatLean/Minimaxity/ForMathlib/LeCamInequality.lean`    (`lecam_half_lintegral_le`)
Keep public signatures/docstrings UNCHANGED. Helpers `private`. (The public theorems already reduce to these
cruxes via `tvDist_eq_half_lintegral` — which is being closed in parallel; you may assume it as a black box.)

## Pinsker `pinsker_half_lintegral_le`: `½∫|p−q|dξ ≤ √(½ klDiv ν μ)`  (densities vs ξ=μ+ν)
Wainwright Ex 15.6 route: reduce to Bernoulli. For the partition `A={p≥q}`, `δ_p=μ A`, `δ_q=ν A`:
the data-processing inequality for KL under the 2-cell partition gives `klDiv ν μ ≥ kl_Bernoulli(δ_q‖δ_p)`,
and the scalar Pinsker `2(δ_p−δ_q)² ≤ kl_Bernoulli` (prove via `2(a−b)² ≤ a log(a/b)+(1−a)log((1−a)/(1−b))`,
a 1-var calculus/`nlinarith` fact). Since `½∫|p−q|dξ = |δ_p − δ_q|` … actually `½∫|p−q| = tvDist = δ_p−δ_q`
on the optimal set. Combine: `(½∫|p−q|)² = (δ_p−δ_q)² ≤ ½ kl_Bernoulli ≤ ½ klDiv ν μ`, then `√`. Mathlib:
`Real.add_pow_le_pow_mul_pow_of_sq_le_sq` no; use `Real.inner_mul_le_norm_mul_norm`/`Real.log` bounds,
`klDiv` data-processing (`klDiv_comp`/`klDiv_map`/`klDiv_le_…` — search), `ENNReal.rpow_natCast`/`rpow_le_rpow`.
Isolate the scalar-Bernoulli-Pinsker as ONE named `private` lemma if helpful (prove it — it's elementary calculus).

## Le Cam `lecam_half_lintegral_le`: `½∫|p−q|dξ ≤ √(H²)·√(1−H²/4)`
Cauchy–Schwarz: `∫|p−q| = ∫|√p−√q|·(√p+√q) ≤ √(∫(√p−√q)²)·√(∫(√p+√q)²)` (Mathlib
`MeasureTheory.lintegral_mul_le_…` / `inner_mul_le_norm_mul_norm` / `ENNReal.lintegral_mul_le_Lp_mul_Lq`
Hölder with p=q=2). `∫(√p−√q)² = H²` (= `sqHellinger`), `∫(√p+√q)² = ∫(p+q) + 2∫√(pq) = 2 + (2−H²) = 4−H²`
(since `∫√(pq) = 1 − H²/2`). So `(½∫|p−q|)² ≤ ¼·H²·(4−H²) = H²(1−H²/4)`. Then `√`. Build the `∫√(pq)=1−H²/2`
identity from `(√p−√q)² = p+q−2√(pq)`.

GOAL: close both; reduce any residual to a SMALLER named `private` sorry + precise `-- TODO(mmx)`.
## DONE: build both modules green; `git add` ONLY the two files; commit. Report closed/residual + lemmas.
