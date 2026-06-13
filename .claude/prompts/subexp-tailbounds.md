Read CLAUDE.md (repo root) first and obey it — §2 (hypothesis tags), §6 (search tools), §7, §9, §10.
Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh '<name>'`. Never `lake update`.

# CONTEXT
`StatLean/ConcentrationInequalities/SubExponential/Defs.lean` already defines (do NOT modify it):
`structure IsSubExponential (X : Ω → ℝ) (α : ℝ≥0) (μ)` with fields
  `mgf_le : ∀ l, |l| ≤ 1/α → mgf (fun ω => X ω - ∫ x, X x ∂μ) μ l ≤ Real.exp (l^2 * α^2 / 2)`
  `integrable_exp_mul : ∀ l, |l| ≤ 1/α → Integrable (fun ω => Real.exp (l*(X ω - ∫ x,X x ∂μ))) μ`
and `IsSubExponential.mgf_le_of_mem_Icc` (the `0 ≤ l ≤ 1/α` specialization).

# TASK
Create `StatLean/ConcentrationInequalities/SubExponential/TailBounds.lean`
(namespace `StatLean.ConcentrationInequalities`) formalizing Lu *Big Data Analysis* §3.2
**Sub-Exponential tail probability** (`thm:sub-exp`): if `X` is sub-exponential with parameter `α`
(`α > 0`), then for the centered `Y = X − E[X]` and `0 ≤ t`,

  μ {ω | t < Y ω} ≤ ENNReal.ofReal (exp(−t²/(2α²)))     when 0 ≤ t < α  (quadratic regime)
  μ {ω | t < Y ω} ≤ ENNReal.ofReal (exp(−t/(2α)))       when α ≤ t      (linear regime)

State it as ONE theorem returning the `min`/two-case bound, OR two theorems
(`measure_sub_integral_lt_le_quadratic`, `_linear`) — your choice; two is cleaner. Prove BOTH
regimes, ZERO sorry.

# PROOF (book §3.2)
Chernoff: for `λ ∈ [0, 1/α]`, `μ{t < Y} ≤ exp(−λt) · mgf Y λ ≤ exp(−λt + λ²α²/2)` using the
`mgf_le_of_mem_Icc` field. Then optimize `λ`:
- quadratic regime (`t/α² ≤ 1/α`, i.e. `t ≤ α`): optimal `λ = t/α²`, gives `exp(−t²/(2α²))`.
- linear regime (`t > α`): clamp `λ = 1/α`, gives `exp(−t/α + 1/2) ≤ exp(−t/(2α))` since `1/2 ≤ t/(2α)`.
Engine for "Chernoff from mgf": Mathlib `ProbabilityTheory.measure_ge_le_exp_mul_mgf` (or
`measure_ge_le_exp_cgf`) — check its exact signature with `./tools/check.sh` and mirror its
`μ.real`/ENNReal shape exactly (the same bridge used in `SubGaussian/TailBounds.lean`, read that
file for the `ENNReal.ofReal_le_ofReal` + `measure_ne_top` pattern). You will need
`IsSubExponential` to force `IsFiniteMeasure μ` (derive privately, as `SubGaussian/TailBounds` does
from its `integrable_exp_mul` at `l = 0`).

`α > 0` is `-- USER-INPUT: α > 0; Lu-BDA §3.2 (thm:sub-exp)`. `0 ≤ t` (book splits `0≤t<α` / `t≥α`)
mirror faithfully. Document any constant you must weaken.

# TOUCH-SET
Create/modify ONLY `StatLean/ConcentrationInequalities/SubExponential/TailBounds.lean`. Do NOT touch
`Defs.lean`, the umbrella, `StatLean.lean`, lakefile/manifest/toolchain, `notes/`.

# BUILD
  lake build StatLean.ConcentrationInequalities.SubExponential.TailBounds

# DONE = build exits 0; ZERO sorries; §2 tags; small commit
(`conc(subexp): two-regime tail (Lu-BDA §3.2 thm:sub-exp)`). Print declaration names, build status,
constant deviations. Independently re-verified; a vacuous bound is rejected.
