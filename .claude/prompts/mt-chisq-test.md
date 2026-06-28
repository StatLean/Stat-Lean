# mt-chisq-test — χ² test statistic mean/variance under H₀/H₁ (Candès L2 §2.3)

You are a Lean 4 proof subagent on branch `mt/chisq-test` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with
plain `lake build`, ITERATE to 0 errors / 0 sorries. Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/ChiSquaredTest/Distribution.lean`

The merged `ForMathlib/GaussianMoments.lean` is imported, read-only — reuse `integral_sq_stdGaussian`
(`E[z²]=1`), `integral_cube_stdGaussian` (`E[z³]=0`), `integral_pow_four_stdGaussian` (`E[z⁴]=3`),
`variance_sq_stdGaussian` (`∫(z²−1)²=2`). Do not touch other files.

## Goal
Prove the 4 moment lemmas (0-sorry). `lake build StatLean.MultipleTesting.ChiSquaredTest.Distribution` green.

## The lemmas (`zᵢ ∼ N(0,1)` i.i.d.; `‖θ‖² = ∑θᵢ²`)
H₀ (`Tₙ=∑zᵢ²`): `E[Tₙ]=n`, `Var[Tₙ]=∫(Tₙ−n)²=2n`.
H₁ (`Tₙ=∑(θᵢ+zᵢ)²`): `E[Tₙ]=‖θ‖²+n`, `Var[Tₙ]=∫(Tₙ−(‖θ‖²+n))²=2n+4‖θ‖²`.

## Proof roadmap
**Per-coordinate moments** (push to the law via `integral_map (h.aemeasurable) (by fun_prop)`):
`∫ zᵢ ∂P = 0` (`integral_id_gaussianReal`), `∫ zᵢ² ∂P = 1`, `∫ zᵢ³ ∂P = 0`, `∫ zᵢ⁴ ∂P = 3`,
`∫ (zᵢ²−1)² ∂P = 2`. Integrability of each power: `memLp_id_gaussianReal'` /
`MemLp.integrable_*` pushed through the law (mirror `EmpiricalBayes/BayesRisk.lean coord_facts`).

- **`chiSq_H0_mean`**: `integral_finset_sum` (each `zᵢ²` integrable) `= ∑ᵢ ∫zᵢ² = ∑ᵢ 1 = n`.
- **`chiSq_H1_mean`**: `∫(θᵢ+zᵢ)² = ∫(θᵢ²+2θᵢzᵢ+zᵢ²) = θᵢ²+2θᵢ·0+1 = θᵢ²+1`; sum `= ‖θ‖²+n`.
- **Variances — search first** for `variance` of an independent sum:
  `./tools/loogle.sh '"iIndepFun"' '"variance"'`, `'"variance_sum"'`, `'"IndepFun.variance_add"'`,
  `ProbabilityTheory.variance`. If a `Var[∑ Xᵢ] = ∑ Var[Xᵢ]` (independent) lemma exists, use it:
  - H₀: `Var[∑zᵢ²] = ∑Var[zᵢ²] = ∑(∫(zᵢ²−1)²) = ∑2 = 2n` (note `∫(Tₙ−n)²` is `Var[Tₙ]` since
    `E[Tₙ]=n`; bridge `variance`↔`∫(·−mean)²` via `variance_eq_integral`).
  - H₁: `Var[∑(θᵢ+zᵢ)²] = ∑Var[(θᵢ+zᵢ)²] = ∑(4θᵢ²+2) = 4‖θ‖²+2n`. Per coord
    `Var[(θᵢ+zᵢ)²] = ∫(2θᵢzᵢ+(zᵢ²−1))² = 4θᵢ²·1 + 2 + 4θᵢ·∫zᵢ(zᵢ²−1)`, and
    `∫zᵢ(zᵢ²−1) = ∫zᵢ³ − ∫zᵢ = 0−0 = 0`.
- **If no `variance_sum` lemma**: expand directly. `∑Wᵢ` with `Wᵢ = zᵢ²−1` (H₀) or
  `2θᵢzᵢ+(zᵢ²−1)` (H₁), each `∫Wᵢ = 0`. `(∑Wᵢ)² = ∑Wᵢ² + ∑_{i≠j} WᵢWⱼ` (`Finset.sum_mul_sum` /
  `Finset.sum_pow_two`); integrate: cross terms `∫WᵢWⱼ = (∫Wᵢ)(∫Wⱼ) = 0` by
  `(hindep.indepFun hij).integral_fun_mul_eq_mul_integral` (mirror `BayesRisk.lean`'s cross-term
  handling); diagonal `∑∫Wᵢ²`. Needs integrability of `Wᵢ`, `Wᵢ²`, `WᵢWⱼ` (powers + Hölder).

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + `-- USER-INPUT` tags. Named `private` helpers
only; no anonymous `sorry`. Commit to `mt/chisq-test`
(`mt(chi): χ² test statistic mean/variance under H₀/H₁ (Candès L2 §2.3)`).

## DONE
`lake build StatLean.MultipleTesting.ChiSquaredTest.Distribution` exits 0; 0 sorry. Report build
status, sorry count, whether a Mathlib `variance`-of-independent-sum lemma existed (vs direct
expansion), and helpers added.
