# mt-chisquared-dist — χ²ₖ := Gamma(k/2,½) + sum-of-squares law (Candès L2 §2.3)

You are a Lean 4 proof subagent on branch `mt/chisquared-dist` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with
plain `lake build`, ITERATE. Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/ForMathlib/ChiSquared.lean`

Do **not** change the `def chiSquared` signature (downstream depends on it) or any public theorem
signature. You MAY add `private` helpers. Do not touch other files (the merged
`ForMathlib/GammaMoments.lean` is imported, read-only — reuse its `mgf_gammaMeasure`,
`integral_id_gammaMeasure`, `variance_gammaMeasure`).

## Goal
Close the 5 `sorry`s. **The 4 distributional lemmas (isProbabilityMeasure, mgf, mean, variance) are
direct GAMMA reuse and MUST land 0-sorry.** The 5th, `map_sum_sq_eq_chiSquared` (the exact law), is
HARD (see below) — attempt it fully; if it resists after real effort, leave it as the SINGLE named
`sorry` with a one-line reason. `lake build StatLean.MultipleTesting.ForMathlib.ChiSquared` green.

## Easy lemmas (reuse — `chiSquared k = gammaMeasure (k/2) (1/2)`, so `unfold chiSquared`)
- `isProbabilityMeasure_chiSquared`: `isProbabilityMeasure_gammaMeasure` with `k/2 > 0`
  (`NeZero k` ⇒ `k ≥ 1`) and `1/2 > 0`.
- `mgf_chiSquared`: `mgf_gammaMeasure (a:=k/2) (r:=1/2)` (needs `k/2>0`, `1/2>0`, `t<1/2`); its output
  `(r/(r−t))^a` is exactly `((1/2)/((1/2)−t))^(k/2)`.
- `integral_id_chiSquared`: `integral_id_gammaMeasure` gives `a/r = (k/2)/(1/2) = k` (`field_simp`/`norm_num`).
- `variance_chiSquared`: `variance_gammaMeasure` gives `∫(x−a/r)² = a/r²`; here `a/r = k` (so the `(x−k)²`
  matches) and `a/r² = (k/2)/(1/2)² = 2k`. Rewrite the center `a/r` to `k` first.

## Hard: `map_sum_sq_eq_chiSquared` — `∑ᵢ Zᵢ² ∼ χ²ₙ` for i.i.d. `Zᵢ ∼ N(0,1)`
Two routes; **first search** for the missing bricks before deciding.

**Route A — characteristic function** (Mathlib HAS `MeasureTheory.Measure.ext_of_charFun`):
prove `charFun (map (∑Zᵢ²) μ) = charFun (chiSquared n)` then apply it.
- `charFun (map (∑Zᵢ²) μ) t = E[e^{it∑Zᵢ²}] = ∏ᵢ E[e^{itZᵢ²}]` by independence (search
  `'"charFun"' '"sum"'`, `'"iIndepFun"' '"charFun"'`, or `map_sum = conv` + `charFun_conv`).
  `E[e^{itZ²}]` under `N(0,1)` `= (1−2it)^{−1/2}` (complex analogue of the real integral
  `∫ e^{lx²} dN(0,1) = (1−2l)^{−1/2}` in `CompressedSensing/GaussianChiSquared.lean` — re-derive).
- `charFun (chiSquared n) t = charFun (Gamma(n/2,1/2)) t = (1−2it)^{−n/2}`. **Search whether Mathlib
  has the Gamma characteristic function** (`./tools/loogle.sh '"charFun"' '"gamma"'`,
  `./tools/api.sh .lake/packages/mathlib/Mathlib/Probability/Distributions/Gamma.lean`). If absent,
  this is the blocker — derive from the density (complex Gamma integral) or fall back.

**Route B — PDF change-of-variables + Gamma additivity** (uniqueness-free):
- `map (·²) (gaussianReal 0 1) = gammaMeasure (1/2) (1/2)`: the density of `Z²` is the Gamma(½,½)
  density (`f_{Z²}(y) = (2πy)^{−1/2} e^{−y/2}` for `y>0`, the 2-to-1 map). Mathlib pushforward-density
  / `MeasureTheory.Measure.map` of a `withDensity` (search `'"map"' '"withDensity"'`,
  change-of-variables `'"integral_comp"'`, `Real.Gamma_one_half` `= √π`).
- Gamma additivity `gammaMeasure a (1/2) ⋆ gammaMeasure b (1/2) = gammaMeasure (a+b) (1/2)` via
  `MeasureTheory.Measure.conv` + density convolution (Beta integral
  `∫₀¹ x^{a−1}(1−x)^{b−1} = Γ(a)Γ(b)/Γ(a+b)`; search `'"betaIntegral"'`,
  `'"Gamma_mul_Gamma"'`). Then induct on `n`: `map (∑ Zᵢ²) μ = conv^n (Gamma(1/2,1/2)) = Gamma(n/2,1/2)`
  (`iIndepFun.map_sum_eq_conv`-style; search `'"map_add"' '"conv"'`, `IndepFun.map_add_eq_map_conv_map`).

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + `-- USER-INPUT` tags. Named `private` helpers
only; any residual `sorry` must be ONLY `map_sum_sq_eq_chiSquared`. Commit to `mt/chisquared-dist`
(`mt(chisq): χ²ₖ:=Gamma(k/2,½) + moments [+ sum-of-squares law] (Candès L2)`).

## DONE
`lake build StatLean.MultipleTesting.ForMathlib.ChiSquared` exits 0. Report build status, sorry count
(4 easy MUST be 0-sorry; law 0 or 1 named sorry), whether Mathlib had the Gamma charFun / Beta
integral / conv-of-map lemmas, and the route attempted for the law.
