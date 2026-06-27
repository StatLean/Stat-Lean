# Close the KL-convexity debts: klDiv_mixture_minimizes + klDiv_le_avg

Lean 4 / Mathlib engineer on **StatLean** (read CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, inside srun.
Run `lake build` SYNCHRONOUSLY in the FOREGROUND (never background; never end turn mid-build). 0 sorries.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/ForMathlib/KLDivergence.lean`   (close `klDiv_mixture_minimizes`)
- `StatLean/Minimaxity/Fano/MutualInformation.lean`    (close `klDiv_le_avg`)
Keep ALL public signatures/tags/citation docstrings UNCHANGED. No axiom/admit. New helpers `private`.

## Strategy (both are second-argument convexity of `klDiv`)
Mathlib KEY: `InformationTheory.convexOn_klFun` / `strictConvexOn_klFun` (`klFun` convex on `Ici 0`),
`klDiv_eq_integral_klFun` / `klDiv_eq_lintegral_klFun_of_ac` (`klDiv μ ν = ∫ klFun (μ.rnDeriv ν) ∂ν`).
KL is **jointly convex** in `(μ,ν)` (perspective of `klFun`): `(p,q) ↦ q·klFun(p/q)` is jointly convex.
- `klDiv_le_avg` (MutualInformation): `klDiv (Q j) ((1/M)Σ Q k) ≤ (1/M) Σ klDiv (Q j) (Q k)`. This is
  convexity of `R ↦ klDiv (Q j) R` at the average `R̄ = (1/M)Σ Q k`. Search Mathlib for a ready
  `klDiv` convexity/`ConvexOn` lemma (`klDiv_…convex…`, `ConvexOn … klDiv`); if absent, derive from the
  integral form + `ConvexOn.perspective`/`ConvexOn.smul`/Jensen `inner_le_weight_mul_Lp`. The mixture is
  `mixture Q = Q ∘ₘ uniformPrior` — relate `∑ Q k` to the mixture via the bind/sum form.
- `klDiv_mixture_minimizes` (KLDivergence): `Σⱼ klDiv (Pⱼ) ((1/M)Σ Pₖ) ≤ Σⱼ klDiv (Pⱼ) Q` for any `Q`.
  This is the Gibbs/variational fact that the mixture `Q̄` minimizes `Q ↦ Σⱼ D(Pⱼ‖Q)`; equivalently
  `Σⱼ D(Pⱼ‖Q) − Σⱼ D(Pⱼ‖Q̄) = M·D(Q̄‖Q) ≥ 0`. Prove the identity (expand `klDiv` via `llr`/`klFun`,
  the `log(Pⱼ/Q) = log(Pⱼ/Q̄) + log(Q̄/Q)` split) then `klDiv_nonneg`. (Ref Wainwright Ex 15.11.)

If a sub-step genuinely resists after honest effort, lift it to a SMALLER named `private` lemma with one
`sorry` + `-- TODO(mmx): <precise residual>` and close everything around it. Goal: shrink/eliminate debt.

## DONE
`lake build StatLean.Minimaxity.ForMathlib.KLDivergence StatLean.Minimaxity.Fano.MutualInformation`
green; `grep -c sorry` per file = 0 (or a smaller named residual). `git add` ONLY the two files, commit
`mmx(batch9): close KL-convexity debts`. Report exactly what closed + Mathlib lemmas used.
