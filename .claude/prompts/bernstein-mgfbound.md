Read CLAUDE.md (repo root) first and obey it — §2, §6 (search tools), §7, §9, §10.
Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh '<name>'`. Never `lake update`.

# CONTEXT (do NOT modify these files)
`Bernstein/Defs.lean`: `structure HasBernsteinCondition (X) (σ2 b : ℝ≥0) (μ)` with fields
  `mean_zero : ∫ X = 0`, `variance_eq : ∫ (X)^2 = σ2`,
  `moment_le : ∀ k ≥ 3, ∫ |X|^k ≤ (σ2/2)·k!·b^(k-2)`.
`SubExponential/Defs.lean`: `structure IsSubExponential (X) (α : ℝ≥0) (μ)` with fields
  `mgf_le : ∀ l, |l| ≤ 1/α → mgf (X − E X) μ l ≤ exp(l²α²/2)`,
  `integrable_exp_mul : ∀ l, |l| ≤ 1/α → Integrable (fun ω => exp(l·(X ω − E X))) μ`.

# TASK
Create `StatLean/ConcentrationInequalities/Bernstein/MGFBound.lean`
(namespace `StatLean.ConcentrationInequalities`) proving **Bernstein ⇒ sub-exponential**
(Lu *Big Data Analysis* §4.1, Step 1 of the Bernstein-inequality proof):

  theorem `isSubExponential_of_hasBernsteinCondition`
    `HasBernsteinCondition X σ2 b μ → IsSubExponential X (2 * (σ2 ⊔ b)) μ`

i.e. a Bernstein-condition variable with parameters `(σ², b)` is sub-exponential with parameter
`α = 2·(σ² ∨ b)`.

# PROOF (book §4.1)
For the centered `X` (here `E X = 0` so `X` IS centered), expand the MGF as a Taylor series and use
the moment bound:
  `E e^{λX} = Σ_{k≥0} λ^k/k! · E[X^k] = 1 + λ²σ²/2 + Σ_{k≥3} λ^k/k! E[X^k]`
  `≤ 1 + λ²σ²/2 + Σ_{k≥3} |λ|^k/k! · (σ²/2)k! b^{k−2} = 1 + (λ²σ²/2)·Σ_{k≥0}(|λ|b)^k`
  `= 1 + (λ²σ²/2)/(1−|λ|b) ≤ exp(λ²σ²/(2(1−|λ|b)))`  for `|λ| < 1/b`  (geometric series + `1+x≤eˣ`).
Then for `|λ| ≤ 1/(2(σ²∨b))` we have `|λ|b ≤ 1/2`, so `1/(1−|λ|b) ≤ 2`, giving
  `E e^{λX} ≤ exp(λ²σ²) ≤ exp(λ²·2(σ²∨b)/2)`.
Match to `IsSubExponential` with `α = 2(σ²∨b)` (note `1/α = 1/(2(σ²∨b))`, exactly the range).

This is the hard analytic file: the Taylor expansion `mgf = Σ λ^k/k! E[X^k]` needs Mathlib's MGF
power-series. Search: `./tools/loogle.sh '"mgf"'`, `./tools/loogle.sh '"taylor"'`,
`Mathlib/Probability/Moments/*` for `mgf` ↔ `∑' n, t^n/n! * moment`, e.g.
`ProbabilityTheory.mgf` series lemmas / `ProbabilityTheory.measure…`. The integrability field of
`IsSubExponential` needs the MGF to exist on the range — derive from absolute convergence of the
series (the moment bounds give it for `|λ|<1/b`).

§2 tags: the parameters `σ2`, `b` and `0 < b`, `0 < σ2` are USER-INPUT (Lu-BDA §4.1); integrability/
summability side-conditions are LEAN-ONLY.

# HARD RULE — aim for ZERO sorry.
If the MGF↔series identity or the summability is a genuine Mathlib gap, isolate it as ONE named
`sorry` lemma with a precise docstring (statement + lemmas tried) and prove everything else on top
of it. Report the sorry status prominently. Do NOT weaken `α` to something vacuous.

# TOUCH-SET
Create/modify ONLY `StatLean/ConcentrationInequalities/Bernstein/MGFBound.lean`. Do NOT touch any
`Defs.lean`, the umbrella, `StatLean.lean`, lakefile/manifest/toolchain, `notes/`.

# BUILD
  srun -p shared -c 8 --mem=24G -t 1:00:00 lake build StatLean.ConcentrationInequalities.Bernstein.MGFBound

# DONE = build exits 0; ZERO sorries (or exactly one named, if truly blocked); §2 tags; small commit
(`conc(bernstein): Bernstein ⇒ sub-exponential, α=2(σ²∨b) (Lu-BDA §4.1)`). Print declaration names,
build status, exact sorry status, constant deviations. Independently re-verified.
