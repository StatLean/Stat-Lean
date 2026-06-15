Read CLAUDE.md (repo root) first — §2, §6, §7, §10. Use the search tools. Never `lake update`.
You are inside an srun allocation — build with plain `lake build`, ITERATE.

# CONTEXT (do NOT modify; READ it carefully)
`Bernstein/Defs.lean`: `HasBernsteinCondition X σ2 b μ` (mean_zero, variance_eq, moment_le via `∫⁻`).
`Bernstein/MGFBound.lean` (imported, now 0-sorry): `isSubExponential_of_hasBernsteinCondition`
  and (READ THE FILE) the underlying per-variable MGF bound — there is a lemma giving, for
  `|λ| < 1/b`, `mgf X μ λ ≤ exp(λ²σ²/(2(1 − |λ|b)))` (the `bernstein_key`/MGF core). Use whichever
  exact lemma name the file exposes.
`SubGaussian/Chernoff.lean` / Mathlib `ProbabilityTheory.measure_ge_le_exp_mul_mgf`: Chernoff engine.

# TASK
Create `StatLean/ConcentrationInequalities/Bernstein/Bernstein.lean`
(namespace `StatLean.ConcentrationInequalities`) proving Lu *Big Data Analysis* §4.1 **Bernstein
Inequality**: for `X : Fin n → Ω → ℝ` independent, each `E Xᵢ = 0`, `Var Xᵢ = σ²`, satisfying the
Bernstein condition with parameter `b`, the sample mean `X̄ₙ = (1/n)∑Xᵢ` obeys, for `t > 0`:
  `μ {ω | t < X̄ₙ ω} ≤ ENNReal.ofReal (exp(−n t² / (2(σ² + b t))))`.

# PROOF (Lu §4.1, Step 2)
Chernoff on `X̄ₙ`: for `λ ∈ (0, 1/b)`,
  `μ{t < X̄ₙ} ≤ exp(−λ n t) · ∏ᵢ mgf Xᵢ μ (λ) ≤ exp(−λ n t) · exp(n λ²σ²/(2(1−λb)))`
  `= exp(n(−λ t + λ²σ²/(2(1−λb))))`   (independence ⇒ mgf of sum factorises; per-term bound from
  MGFBound's MGF lemma — supply the `Measurable Xᵢ` hyps it needs). Choose `λ = t/(σ² + b t)` (which
  lies in `(0, 1/b)` since `t>0`), giving `−λt + λ²σ²/(2(1−λb)) ≤ −t²/(2(σ²+bt))`. Hence the bound.
  (Do the `λ = t/(σ²+bt)` algebra carefully; `1 − λb = σ²/(σ²+bt)`, so `λ²σ²/(2(1−λb)) = λ²(σ²+bt)/2`,
  and `−λt + λ²(σ²+bt)/2 = −t²/(2(σ²+bt))` exactly.) Bridge `μ.real → μ` ENNReal as in
  `SubGaussian/TailBounds.lean`.

ZERO sorry. Independence, `E Xᵢ=0`, `Var=σ²`, Bernstein condition, `Measurable Xᵢ`, `b>0`, `σ²>0`,
`t>0` are `-- USER-INPUT: …; Lu-BDA §4.1`. Constant: state the provable `(σ²+bt)` form; document any
deviation. The mgf-of-sum factorisation: search `./tools/loogle.sh '"iIndepFun"' '"mgf"'` /
`'"iIndepFun.mgf_sum"'` / `'"mgf_sum"'`.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/Bernstein/Bernstein.lean`.
# BUILD: lake build StatLean.ConcentrationInequalities.Bernstein.Bernstein
# DONE = build exits 0; ZERO sorries; §2 tags; commit
(`conc(bernstein): Bernstein inequality (Lu-BDA §4.1)`). Report build + sorry count + constants.
