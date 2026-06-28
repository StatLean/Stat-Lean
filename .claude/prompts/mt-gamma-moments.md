# mt-gamma-moments — MGF / mean / variance of Gamma(a,r) (Candès L2 → χ² law)

You are a Lean 4 proof subagent on branch `mt/gamma-moments` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with
plain `lake build`, ITERATE to 0 errors / 0 sorries. Never `lake update`. **Time-box** the MGF
lemma; if it resists, leave it as a *named* `sorry` and close the other two (see DONE).

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/ForMathlib/GammaMoments.lean`

Do not touch any other file. You MAY add `private` helper lemmas within the touch-set.

## Goal
Close the 3 `sorry`s (ideally all; MGF may be left as a documented named `sorry` if time-boxed out).
`lake build StatLean.MultipleTesting.ForMathlib.GammaMoments` green.

## The lemmas (`gammaMeasure a r` = Gamma with shape `a`, rate `r`; density `r^a/Γ(a) x^{a-1}e^{-rx}`)
1. `mgf_gammaMeasure` (`t < r`): `∫ e^{tx} ∂Gamma(a,r) = (r/(r−t))^a` (rpow).
2. `integral_id_gammaMeasure`: `∫ x ∂Gamma(a,r) = a/r`.
3. `variance_gammaMeasure`: `∫ (x − a/r)² ∂Gamma(a,r) = a/r²`.

## Proof routes
**First search** for existing Gamma moment/MGF/integral lemmas:
`./tools/api.sh .lake/packages/mathlib/Mathlib/Probability/Distributions/Gamma.lean`,
`./tools/loogle.sh '"gammaMeasure"'`, `'"gammaPDF"'`, `'"Gamma_eq_integral"'`,
`./tools/explore.sh "moments of the gamma distribution"`. Useful Mathlib facts:
`Real.Gamma_eq_integral` (`Γ(a)=∫₀^∞ e^{-x}x^{a-1}`), `Real.Gamma_add_one` (`Γ(a+1)=a·Γ(a)`),
`isProbabilityMeasure_gammaMeasure`. The measure is `volume.withDensity (gammaPDF a r)`, so reduce
`∫ f ∂gammaMeasure a r` to `∫ x, f x · gammaPDFReal a r x` (search
`'"integral_gammaMeasure"'` / `integral_withDensity_eq_integral_smul` + `toReal_gammaPDF`).

**Core integral** (prove once as a `private` helper, then reuse): for `0 < b`, `0 < s`,
`∫ x in Ioi 0, x^{b-1} · exp(−s·x) = Real.Gamma b / s^b` (substitution `x ↦ x/s` in
`Real.Gamma_eq_integral`; search `'"integral_comp_smul"'`, `'"integral_rpow_mul_exp"'`,
`'"Gamma_eq_integral"'`, the `MeasureTheory.integral_Ioi` substitution lemmas). `x^{b-1}` is `rpow`.

- **(1) MGF**: `∫ e^{tx} · r^a/Γ(a) x^{a-1} e^{-rx} = r^a/Γ(a) ∫ x^{a-1} e^{-(r-t)x}`
  `= r^a/Γ(a) · Γ(a)/(r−t)^a = (r/(r−t))^a` (core integral with `s = r−t > 0`, `b = a`); finish with
  `Real.rpow` algebra (`Real.div_rpow`, `Real.rpow_natCast`-free; keep everything `rpow`).
- **(2) mean**: `E[X] = ∫ x · pdf = r^a/Γ(a) ∫ x^a e^{-rx} = r^a/Γ(a) · Γ(a+1)/r^{a+1}`
  `= Γ(a+1)/(Γ(a)·r) = a/r` (core integral with `b = a+1`, `s = r`; `Real.Gamma_add_one`).
- **(3) variance**: expand `(x−a/r)² = x² − 2(a/r)x + (a/r)²`; `E[X²] = Γ(a+2)/(Γ(a)r²) = a(a+1)/r²`
  (core integral `b = a+2`; `Gamma_add_one` twice); then `a(a+1)/r² − 2(a/r)(a/r) + (a/r)² = a/r²`
  by `field_simp; ring`. Needs integrability of `x`,`x²` under the measure (from the core integral's
  finiteness / `memLp`-style); `integral_add`/`integral_sub`.

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + citation. Named `private` helpers only; any
residual `sorry` must be the named top-level `mgf_gammaMeasure` (no anonymous sorries). Commit to
`mt/gamma-moments` (`mt(gamma): Gamma(a,r) MGF/mean/variance (Candès L2)`).

## DONE
`lake build StatLean.MultipleTesting.ForMathlib.GammaMoments` exits 0. Report build status, sorry
count (0 ideal; if MGF time-boxed, exactly 1 named sorry on `mgf_gammaMeasure` with a one-line
note why), which Mathlib Gamma lemmas existed vs. were derived, and the core-integral lemma added.
