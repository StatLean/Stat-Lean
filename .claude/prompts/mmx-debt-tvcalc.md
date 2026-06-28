# Close the TV density-form + variational debts (TotalVariation.lean)

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun.
FOREGROUND builds only. 0 sorries.

## Touch-set (edit ONLY) — `StatLean/Minimaxity/ForMathlib/TotalVariation.lean`
Close `tvDist_eq_half_lintegral_aux` (Eq 15.6) and `one_sub_tvDist_eq_iInf_aux` (Ex 15.1).
Keep public signatures/docstrings UNCHANGED. Helpers `private`.

## Strategy — densities `p = μ.rnDeriv (μ+ν)`, `q = ν.rnDeriv (μ+ν)`, `ξ = μ+ν`
Mathlib: `Measure.rnDeriv`, `Measure.withDensity_rnDeriv_eq`, `Measure.rnDeriv_add`,
`Measure.lintegral_rnDeriv`, `MeasureTheory.setLIntegral_…`, `Measure.haveLebesgueDecomposition_add`.
Note `μ A = ∫_A p dξ`, `ν A = ∫_A q dξ` (since `μ = ξ.withDensity p`).
- `tvDist_eq_half_lintegral_aux`: `tvDist μ ν = ½∫|p−q|dξ`. The `⨆_s (μ s − ν s)` is attained at
  `A = {x | q x ≤ p x}` (measurable, `measurableSet_le`): there `μ A − ν A = ∫_A (p−q) dξ = ∫_A |p−q| dξ`,
  and since `∫(p−q)dξ = μ univ − ν univ = 0`, `∫_A|p−q| = ∫_{Aᶜ}|p−q| = ½∫|p−q|`. Show `≤` (any `s`:
  `μ s − ν s = ∫_s(p−q) ≤ ∫_{p≥q}(p−q)`) and `≥` (take `s = A`). Use `ENNReal`/`lintegral` monotonicity,
  `lintegral_add_compl`, `ENNReal.ofReal` for the real `|p−q|` integrand.
- `one_sub_tvDist_eq_iInf_aux`: `1 − tvDist = ⨅_{f₀+f₁≥1} (∫f₀dμ + ∫f₁dν)`. `≥`: for feasible `f₀,f₁`,
  `∫f₀dμ+∫f₁dν ≥ ∫min over the partition = 1 − tvDist`. `≤`: the indicator optimum `f₀ = 𝟙_{q>p}`,
  `f₁ = 𝟙_{p≥q}` gives `∫f₀dμ+∫f₁dν = μ{q>p}+ν{p≥q} = 1 − (μ{p≥q}−ν{p≥q}) = 1 − tvDist`. May reuse the
  density form above. Hard direction is the `≥` (every feasible pair) — `le_iInf`/`iInf_le`.

Lift any genuinely-stuck sub-step to a SMALLER named `private` sorry + `-- TODO(mmx)`.

## DONE
`lake build StatLean.Minimaxity.ForMathlib.TotalVariation` green; commit `git add` ONLY that file.
Report closed/residual + Mathlib lemmas.
