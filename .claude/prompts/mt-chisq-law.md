# mt-chisq-law — squared-Gaussian MGF brick + close the χ² sum-of-squares law (Candès L2)

You are a Lean 4 proof subagent on branch `mt/chisq-law` (based on `mt/batch8`). Project: **StatLean**
— read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain
`lake build`, ITERATE. Never `lake update`.

## Touch-set (edit ONLY these two files)
- `StatLean/MultipleTesting/ForMathlib/GaussianSquareMGF.lean`   (prove the 2 MGF lemmas)
- `StatLean/MultipleTesting/ForMathlib/ChiSquared.lean`          (close the 1 `sorry` — the law)

Merged & read-only otherwise. `ChiSquared.lean` already has `chiSquared`, `mgf_chiSquared`, etc.
proved; only `map_sum_sq_eq_chiSquared` is `sorry`. You may add `import
StatLean.MultipleTesting.ForMathlib.GaussianSquareMGF` to `ChiSquared.lean`. Do not change any public
signature.

## Part 1 — `GaussianSquareMGF.lean` (MUST land 0-sorry)
Prove `mgf_exp_sq_stdGaussian` (`∫ exp(l x²) dN(0,1) = (√(1−2l))⁻¹`, `l < 1/2`) and
`integrable_exp_sq_stdGaussian`. **READ**
`StatLean/HighDimensionalStatistics/CompressedSensing/GaussianChiSquared.lean` — it proves exactly
these `private`ly (`integral_exp_mul_sq_stdGaussian`, `integrable_exp_mul_sq_stdGaussian`,
`gaussianPDF_mul_exp_sq`): replicate that derivation here (via `gaussianReal_of_var_ne_zero`,
`integral_gaussianReal_eq_integral_smul`, `integral_gaussian`, `integrable_exp_neg_mul_sq`).

## Part 2 — close `map_sum_sq_eq_chiSquared` (attempt; this is the hard step)
The existing proof comment in `ChiSquared.lean` records the route. Carry it out:
- **Reduce to MGF via the complex bridge**: `MeasureTheory.Measure.ext_of_charFun` needs
  `charFun (μ.map (∑Zᵢ²)) = charFun (chiSquared n)`. On each `t`, `complexMGF · (t·I) = charFun · t`
  (`ProbabilityTheory.complexMGF_mul_I` / `complexMGF_id_mul_I`), and
  `ProbabilityTheory.eqOn_complexMGF_of_mgf` gives `EqOn (complexMGF X μ) (complexMGF id (chiSquared n))`
  from a real-MGF equality, on the vertical strip — verify these names with
  `./tools/loogle.sh '"complexMGF"'`, `'"eqOn_complexMGF"'`, `'"complexMGF_mul_I"'`.
- **Obligation A — real MGF equality** `mgf (fun ω => ∑ᵢ (Zᵢ ω)²) μ = mgf id (chiSquared n)` on ℝ:
  for `l < 1/2`, LHS `= ∏ᵢ E[exp(l Zᵢ²)] = ((√(1−2l))⁻¹)^n` (`mgf` def `=∫exp(l·)`,
  `ProbabilityTheory.iIndepFun.mgf_sum` / independence of `Zᵢ²`, `mgf_exp_sq_stdGaussian` via
  `integral_map`); RHS `= mgf_chiSquared = ((1/2)/((1/2)−l))^{n/2}`; bridge by rpow algebra
  `((√(1−2l))⁻¹)^n = ((1/2)/((1/2)−l))^{n/2}` (both `= (1−2l)^{−n/2}`). For `l ≥ 1/2` both MGFs are
  `0` (non-integrable; `mgf` of a non-integrable integrand is `0`).
- **Obligation B — integrability neighborhood**: `0 ∈ interior (integrableExpSet (∑Zᵢ²) μ)` (a
  Gaussian-tail fact: `exp(l·∑Zᵢ²)` integrable for `|l| < 1/2`, from `integrable_exp_sq_stdGaussian`
  + independence). Search `'"integrableExpSet"'`, `'"mem_interior"'`.

If, after real effort, Part 2 does not fully close, leave `map_sum_sq_eq_chiSquared` as the single
named `sorry` (Part 1 must still be 0-sorry) and report exactly which obligation blocked.

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + tags. Named `private` helpers only. Commit to
`mt/chisq-law` (`mt(chisq-law): squared-Gaussian MGF brick + close ∑Zᵢ²~χ²ₙ (Candès L2)`).

## DONE
`lake build StatLean.MultipleTesting.ForMathlib.GaussianSquareMGF StatLean.MultipleTesting.ForMathlib.ChiSquared`
exits 0. Report build status, sorry counts per file (GaussianSquareMGF MUST be 0; ChiSquared 0 or 1),
and — if Part 2 blocked — which obligation (A/B/bridge) and why.
