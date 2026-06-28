# mt-gauss-moments — low-order moments of N(0,1) (Candès L2)

You are a Lean 4 proof subagent on branch `mt/gauss-moments` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with
plain `lake build`, ITERATE to 0 errors / 0 sorries. Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/ForMathlib/GaussianMoments.lean`

Do not touch any other file. You MAY add `private` helper lemmas within the touch-set.

## Goal
Close all 4 `sorry`s to 0-sorry / 0-error. Verify
`lake build StatLean.MultipleTesting.ForMathlib.GaussianMoments` green.

## The lemmas (`Z ∼ N(0,1)` = `gaussianReal 0 1`)
1. `integral_sq_stdGaussian` : `∫ x², ∂N(0,1) = 1`.
2. `integral_cube_stdGaussian` : `∫ x³ ∂N(0,1) = 0`.
3. `integral_pow_four_stdGaussian` : `∫ x⁴ ∂N(0,1) = 3`.
4. `variance_sq_stdGaussian` : `∫ (x²−1)² ∂N(0,1) = 2`.

## Proof routes (cheapest first; search before deriving)
- **First search** whether Mathlib already has these as moment lemmas:
  `./tools/loogle.sh '"gaussianReal"'`, `'"moment"'`, `'"integral_pow"'`,
  `./tools/explore.sh "moments of the gaussian distribution"`. Look for
  `ProbabilityTheory.integral_*_gaussianReal`, central-moment, or even-moment lemmas. Also
  `variance_fun_id_gaussianReal` (gives `∫ x² = 1` after `variance_eq_integral`), `memLp_id_gaussianReal`
  (integrability of powers), `integral_id_gaussianReal` (`∫ x = 0`).
- **(1)** `E[Z²] = Var Z + (E Z)² = 1 + 0`. Mirror the inline derivation already in
  `HighDimensionalStatistics/CompressedSensing/GaussianChiSquared.lean` (`hEsq` via
  `variance_fun_id_gaussianReal` + `variance_eq_integral`). READ that file for the exact incantation.
- **(2)** Odd moment = 0: the integrand `x³ · pdf(x)` is odd and the standard Gaussian is symmetric.
  Search `'"integral_comp_neg"'` / `'"integral_eq_zero_of_odd"'` / a reflection lemma for
  `gaussianReal 0 _`; or push to the density (`gaussianReal_of_var_ne_zero` → `withDensity` →
  `integral_withDensity_eq_integral_smul`) and use that `x ↦ x³ exp(−x²/2)` is odd
  (`MeasureTheory.integral_eq_zero_of_odd` over `volume` on ℝ).
- **(3)** `E[Z⁴] = 3`: either the Gaussian moment recursion `E[Zⁿ] = (n−1)·E[Zⁿ⁻²]` (so
  `E[Z⁴] = 3·E[Z²] = 3`; prove the recursion by IBP, or just the `n=4` case), or differentiate the
  Gaussian integral `∫ exp(−b x²) = √(π/b)` (`integral_gaussian`) twice in `b` to read off
  `∫ x⁴ exp(−b x²)`, evaluated through the `N(0,1)` density. Push to the density as in (2).
- **(4)** Expand `(x²−1)² = x⁴ − 2x² + 1`; `integral_add`/`integral_sub` with integrability of each
  power (from `memLp_id_gaussianReal`), then `3 − 2·1 + 1 = 2` using (1) and (3).

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + citation. Named `private` helpers only.
Commit to `mt/gauss-moments` (`mt(gauss): low-order N(0,1) moments E[Z²,Z³,Z⁴], Var[Z²] (Candès L2)`).

## DONE
`lake build StatLean.MultipleTesting.ForMathlib.GaussianMoments` exits 0; `grep -c sorry` is 0 for
the file. Report build status, sorry count, which Mathlib moment lemmas existed vs. were derived,
and the route used for `E[Z⁴]`.
