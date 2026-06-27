# Close the divergence sorries: KLDivergence, TotalVariation, HellingerDivergence (Wainwright §15.1.3)

Lean 4 / Mathlib proof engineer on **StatLean** (read repo `CLAUDE.md` first: §2, §6, §7). Pin `v4.29.1`.
You are ON the cluster inside an `srun` allocation — iterate with plain `lake build <module>` until
**0 errors, 0 sorries**. Never `lake update`.

## Touch-set (edit ONLY these three files)
- `StatLean/Minimaxity/ForMathlib/KLDivergence.lean`
- `StatLean/Minimaxity/ForMathlib/TotalVariation.lean`
- `StatLean/Minimaxity/ForMathlib/HellingerDivergence.lean`

Do NOT touch `Defs.lean`, the umbrella, or any other file. Keep every theorem **signature**,
`-- USER-INPUT`/`-- LEAN-ONLY` tag, and the `**Reference.** Wainwright …` citation docstring UNCHANGED.
No `axiom`/`admit`/`sorry` in the final state; no new hypotheses on public signatures. Split-out helper
lemmas must be `private`. Build each file: `lake build StatLean.Minimaxity.ForMathlib.KLDivergence` etc.

## KLDivergence.lean — reuse Mathlib `InformationTheory.klDiv`
Wainwright `D(ℚ‖ℙ)` = Mathlib `klDiv ℚ ℙ` (arg order matches; integrate against the first measure).
1. `klDiv_prod_eq_add` — write the product as a composition-product with a constant kernel:
   `μ₁.prod μ₂ = μ₁ ⊗ₘ Kernel.const _ μ₂` (search: `Measure.compProd_const`, `Measure.prod_eq_comp…`),
   then apply `InformationTheory.klDiv_compProd_eq_add`; the residual term
   `klDiv (μ₁ ⊗ₘ const μ₂) (μ₁ ⊗ₘ const ν₂)` collapses to `klDiv μ₂ ν₂` for a probability `μ₁`
   (constant conditional kernel; see `klDiv_compProd_left` and the conditional-KL lemmas in
   `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`).
2. `klDiv_pi_eq_nsmul` — induct on `n`. Base: `Measure.pi` over `Fin 0` is a Dirac, `klDiv = 0`. Step:
   `Fin (n+1)`-product `≅ μ ×ₘ (Fin n)-product` via `MeasurableEquiv.piFinSucc` / `Measure.pi_succ`
   (search `Measure.pi_succ`, `Measure.map_piFinSucc`); combine with `klDiv_prod_eq_add` and the IH;
   `(n+1) • x = x + n • x`.
3. `sum_klDiv_mixture_le` — the uniform mixture `Q̄` minimizes `Q ↦ Σⱼ D(ℙⱼ‖Q)`. Use convexity of KL in
   the second argument / the variational form. If this resists after honest effort, lift the crux to a
   `private` lemma named `klDiv_mixture_minimizes` with one `sorry` + `-- TODO(mmx): Ex 15.11` and
   report it — do NOT block the other two files.

## TotalVariation.lean — `tvDist μ ν = ⨆ s, ⨆ (_ : MeasurableSet s), μ s - ν s` (ℝ≥0∞ sub)
1. `tvDist_comm` — for measurable `s`, `μ s - ν s` and `ν sᶜ - μ sᶜ` relate via `measure_compl` /
   `prob_compl_eq` (probabilities); the `⨆` over `s` and over `sᶜ` coincide. Reindex the sup by complement.
2. `tvDist_le_one` — each term `μ s - ν s ≤ μ s ≤ μ univ = 1`; `iSup_le`.
3. `tvDist_eq_half_lintegral` — with `ξ = μ + ν`, `p = dμ/dξ`, `q = dν/dξ`: the sup is attained on
   `A = {p ≥ q}`, and `μ s - ν s = ∫_s (p − q) dξ`. Show `tvDist = ∫_{p≥q}(p−q)dξ = ½∫|p−q|dξ`
   (since `∫(p−q)dξ = 0`). Use `Measure.rnDeriv_add`, `MeasureTheory.setLIntegral`, `lintegral`
   monotonicity. Hard — if it resists, lift to a `private` named `sorry` + report.
4. `one_sub_tvDist_eq_iInf` (Ex 15.1) — `≤`: any `f₀,f₁≥0` with `f₀+f₁≥1` give
   `∫f₀dμ+∫f₁dν ≥ 1 − tvDist`. `≥`: take `f₀ = 𝟙_{q>p}`, `f₁ = 𝟙_{p≥q}` (indicator optimum). Hard —
   lift to a named `sorry` + report if needed.

## HellingerDivergence.lean — `sqHellinger μ ν = ∫⁻ x, ofReal((√p − √q)²) ∂(μ+ν)`
1. `sqHellinger_comm` — swap `μ,ν`: `μ+ν = ν+μ` (`add_comm`) and `(√p−√q)² = (√q−√p)²` (`neg_sub`,
   `sq`). `simp`/`congr` + `lintegral_congr`.
2. `sqHellinger_le_two` — pointwise `(√p−√q)² ≤ p + q`; `∫⁻(p+q)d(μ+ν)`. With `p=d μ/d(μ+ν)`,
   `q=dν/d(μ+ν)`, `(μ+ν).withDensity (p) = μ`, so `∫⁻ p d(μ+ν) = μ univ = 1` (and similarly `ν`),
   giving `≤ 2`. Use `Measure.withDensity_rnDeriv_eq`, `Measure.rnDeriv_add`, `lintegral_rnDeriv_…`.
3. `sqHellinger_pi_le_nsmul` — bridge to the StatLean eLpNorm form and reuse
   `StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct.hellinger_product_eLpNorm_le_sqrt_n_per_sample`
   together with `one_sub_pow_le_nsmul_one_sub`. `sqHellinger μ ν = (eLpNorm (√p−√q) 2 (μ+ν)).toReal²`
   (the `L²`-norm squared equals the integral). Square the eLpNorm inequality and convert. Non-trivial
   coercion work; if it resists, lift the bridge to a `private` named `sorry` + report.

## DONE
For each file: `lake build StatLean.Minimaxity.ForMathlib.<File> 2>&1 | grep -c sorry` is 0 (or only the
explicitly-reported `private` TODO debts). Run `#print axioms pinsker_tv_le_kl` is NOT needed here.
Report per file: which sorries closed, which lifted to named debts (with the exact lemma name + why),
and the key Mathlib lemmas used.
