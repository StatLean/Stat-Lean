# Close Prop 15.1 selector + Le Cam two-point/convex-hull/functional cruxes

Lean 4 / Mathlib engineer on **StatLean** (CLAUDE.md §2,§6,§7). Pin v4.29.1. ON cluster, srun. FOREGROUND builds.

## Touch-set (edit ONLY)
- `StatLean/Minimaxity/EstimationToTesting.lean`  (`mul_bayesRisk_zeroOne_le` — the nearest-point selector)
- `StatLean/Minimaxity/LeCam/TwoPoint.lean`        (`binary_testingError_eq_tvDist` crux, Eq 15.13)
- `StatLean/Minimaxity/LeCam/ConvexHull.lean`      (Lemma 15.9 crux)
- `StatLean/Minimaxity/LeCam/Functional.lean`      (Cor 15.6 crux)
Keep public signatures/docstrings UNCHANGED. Helpers `private`. Black-box (may be proven in parallel):
`tvDist_eq_half_lintegral`, `one_sub_tvDist_eq_iInf`, `lecam_tv_le_hellinger`, `sqHellinger_pi_le_nsmul`.

## `mul_bayesRisk_zeroOne_le` (Prop 15.1 geometric core): `Φ δ · bayesRisk(01) ≤ bayesRisk(Φ∘edist)`
For any Markov estimator `κ : Kernel 𝓧 Ω`, define the nearest-point test `T : Ω → Fin M`,
`T y = argmin_ℓ edist (gfam ℓ) y` (measurable: `Finset.univ.argmin`/`MeasurableSet`; use
`Measurable.find`/`measurableSet_le` over the finite index, or build `T` as the first index attaining the
min). Pointwise: if `T y ≠ j` then `edist (gfam j) y ≥ δ` (triangle ineq + `2δ`-separation: else `y` closer
to `gfam j` than to `gfam (T y)`, contradicting argmin given separation), so `Φ δ · 𝟙[T y ≠ j] ≤ Φ(edist (gfam j) y)`
(`Monotone Φ`). Integrate (push `T` through `κ`: the 0–1 test is `κ` then `T`, a data-processing of the
estimator) ⇒ `Φ δ · bayesRisk(01) ≤ bayesRisk(Φ∘edist)`. Use `bayesRisk` monotonicity + `bayesRisk_le_bayesRisk_map`/comp.
This is the hardest; isolate the measurable-argmin existence as ONE named `private` lemma if needed.

## `binary_testingError_eq_tvDist` (Eq 15.13): `multiwayTestingError Q = ½(1 − tvDist (Q 0)(Q 1))`, M=2
Unfold `bayesRisk (zeroOneLoss 2) Q (uniformPrior 2)`. Optimal test = likelihood-ratio; the inf over Markov
kernels `κ : 𝓧 → Fin 2` of `½(κ-error under Q0 + under Q1)` equals `½(1 − tvDist)`. Use the variational/sup
form: `inf_κ … = ½ − ½ sup_A (Q0 A − Q1 A) = ½(1−tvDist)`. Reduce `bayesRisk` to the `iInf` over `{0,1}`-tests
(deterministic suffice) via `bayesRisk_of_subsingleton`-style / `Kernel.const` argument.

## `minimax_le_cam_convex_hull` crux, `minimax_functional_modulus` crux
ConvexHull: from `minimax_ge_testing_error` (binary) + `one_sub_tvDist_eq_iInf` on the two mixtures.
Functional: instantiate two-point at the modulus-achieving pair; bound product TV ≤ ¼ via
`lecam_tv_le_hellinger` + `sqHellinger_pi_le_nsmul` (n-fold). 

GOAL: close all; reduce residuals to SMALLER named `private` sorries + `-- TODO(mmx)`.
## DONE: build the 4 modules green; `git add` ONLY them; commit. Report per-lemma closed/residual.
