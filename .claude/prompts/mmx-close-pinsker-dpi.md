# Close #7: klDiv data-processing (KLDataProcessing.lean) + Pinsker (PinskerInequality.lean)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds only. Goal 0 sorry.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/KLDataProcessing.lean` (prove `klDiv_map_le`)
- `StatLean/Minimaxity/ForMathlib/PinskerInequality.lean` (prove `klDiv_ge_two_mul_tvDist_sq`; ADD
  `import StatLean.Minimaxity.ForMathlib.KLDataProcessing` at the top)
Keep public signatures/docstrings UNCHANGED. Helpers `private`.

## 1. `klDiv_map_le (hf : Measurable f) (μ ν) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν`
Data-processing inequality. Two routes — try (a), fall back to a Bool-specialized lemma if needed:
(a) **Jensen per fibre.** `klDiv μ ν = ∫ klFun (μ.rnDeriv ν) dν` (Mathlib `klDiv_eq_integral_klFun`/`_of_ac`).
   `klFun` is convex (`InformationTheory.convexOn_klFun`). The push-forward densities satisfy
   `(μ.map f).rnDeriv (ν.map f) (f x) = E_ν[ μ.rnDeriv ν | f ]`, so by Jensen (`ConvexOn.map_integral_le` /
   conditional-Jensen) `klFun(E[r|f]) ≤ E[klFun(r)|f]`; integrate. Search `klDiv_map`, `klDiv_comp`,
   `Measure.rnDeriv_map`, `condExp` Jensen.
(b) **Chain rule.** Disintegrate `μ = (μ.map f) ⊗ₘ κ` (Mathlib `condDistrib`/`compProd_map_condDistrib`);
   `klDiv_compProd_eq_add` gives `klDiv μ ν = klDiv (μ.map f)(ν.map f) + (≥0 conditional term)`.
FALLBACK: the Pinsker use only needs `f : α → Bool`. For a 2-cell `f`, `klDiv (·.map f)` on `Bool` is the
finite sum `∑_{b} klFun(...)`, and DPI is per-cell Jensen `μ(A)·klFun(ν(A)/μ(A)) ≤ ∫_A klFun(dν/dμ) dμ`
(`convexOn_klFun` + `ConvexOn.smul_le_integral`/`MeasureTheory.lintegral`-Jensen). If (a)/(b) resist, prove a
`private klDiv_map_le_bool` for `f : α → Bool` and use THAT in Pinsker; leave `klDiv_map_le` general with one
named sorry ONLY as a last resort.

## 2. `klDiv_ge_two_mul_tvDist_sq : ENNReal.ofReal (2*(tvDist μ ν).toReal^2) ≤ klDiv ν μ`
`A = {x | (ν.rnDeriv (μ+ν) x) ≤ (μ.rnDeriv (μ+ν) x)}` is measurable (`measurableSet_le` + `Measure.measurable_rnDeriv`).
`tvDist μ ν = (μ A − ν A)` via `tvDist_eq_half_lintegral` + the optimal-set identity (already in the file's
docstring/TODO). Let `f = A.indicator` (to `Bool`). `klDiv (ν.map f) (μ.map f) = bernoulli KL = (ν A) terms`;
apply `klDiv_map_le` (`klDiv (ν.map f)(μ.map f) ≤ klDiv ν μ`) then `bernoulli_pinsker_scalar` (already proven,
with `a = (ν A).toReal`, `b = (μ A).toReal`) gives `2(ν A − μ A)² ≤ klDiv ν μ`. ENNReal/toReal coercions.

## DONE: `lake build StatLean.Minimaxity.ForMathlib.KLDataProcessing StatLean.Minimaxity.ForMathlib.PinskerInequality`
green, 0 sorry. `git add` ONLY the two files; commit. Report routes used.
