Read CLAUDE.md (repo root) first and obey it — §2, §6 (search tools), §7, §10, §11–16 (kernel/condExp
gotchas). Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh`. Never `lake update`.
HARD ITEM — search Mathlib's martingale/Azuma + condExp API thoroughly; budget generously.

# CONTEXT (do NOT modify)
`McDiarmid/CondHoeffding.lean` provides (MERGED):
  `theorem condExp_hoeffding_mgf [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {Z : Ω → ℝ} {a b : ℝ}
     (hZ_int : Integrable Z μ) (hbound : ∀ᵐ ω ∂μ, Z ω - μ[Z|m] ω ∈ Set.Icc a b) (lam : ℝ) :
     ∀ᵐ ω ∂μ, μ[fun ω' => exp(lam·(Z ω' − μ[Z|m] ω')) | m] ω ≤ exp(lam²·(b−a)²/8)`.

# TASK
Create `StatLean/ConcentrationInequalities/McDiarmid/DoobDecomposition.lean`
(namespace `StatLean.ConcentrationInequalities`) building the Doob-martingale machinery that turns
the bounded-differences hypothesis into a global sub-Gaussian MGF bound for
`g := f(X₁,…,Xₙ) − E[f]`, en route to McDiarmid (Lu *Big Data Analysis* §3.1, `McDiarmid`).

Concretely, for `X : Fin n → Ω → 𝓧ᵢ` independent and `f : (Π i, 𝓧ᵢ) → ℝ` with bounded differences
`Dᵢf ≤ cᵢ`, build the filtration `Fₖ = σ(X₁,…,Xₖ)`, the Doob martingale `Mₖ = E[f | Fₖ]` (so
`M₀ = E f`, `Mₙ = f`), its increments `Δₖ = Mₖ − Mₖ₋₁`, and prove:
  (a) each `Δₖ` is conditionally bounded in an interval of length `≤ cₖ` given `Fₖ₋₁`
      (the bounded-differences ⇒ conditional range step), and hence by `condExp_hoeffding_mgf`
      `E[exp(λ Δₖ) | Fₖ₋₁] ≤ exp(λ² cₖ² / 8)` a.s.;
  (b) the telescoping MGF bound `E[exp(λ (f − E f))] ≤ exp(λ² (∑ₖ cₖ²) / 8)` (tower property:
      condition successively on `Fₙ₋₁, …, F₀`, pulling out each conditional MGF factor).

State (b) as the headline lemma `mgf_sub_expectation_le` (a global, unconditional sub-Gaussian MGF
bound with proxy `(∑ cₖ²)/4`). Search Mathlib FIRST for an existing Azuma/martingale-MGF result:
`./tools/loogle.sh '"Azuma"'`, `'"HasCondSubgaussianMGF"'`, `'"measure_sum_ge_le"'`,
`Mathlib/Probability/Martingale/*`, `Mathlib/Probability/Moments/SubGaussian.lean` (conditional
section). If Mathlib already has the conditional-sub-Gaussian ⇒ sum tail (`measure_sum_ge_le_of_hasCondSubgaussianMGF`
or similar), assemble (b) on top of it + `condExp_hoeffding_mgf` rather than reproving the telescope.

# ZERO sorry is the bar. If a genuine Mathlib gap remains after thorough effort, isolate it as ONE
named `sorry` lemma with a precise docstring (goal + lemmas tried) and prove the rest on top; report
prominently for escalation. Do NOT launder the bounded-differences-⇒-conditional-range step into a
hypothesis — DERIVE it.

§2 tags: independence of `X`, the bounded-differences `Dᵢf ≤ cᵢ`, and `f` measurable are USER-INPUT
(Lu §3.1); filtration/integrability regularity is LEAN-ONLY.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/McDiarmid/DoobDecomposition.lean`.
# BUILD (you are ALREADY inside an srun allocation — run lake DIRECTLY, do NOT nest srun/sbatch):
#   lake build StatLean.ConcentrationInequalities.McDiarmid.DoobDecomposition
# DONE = build exits 0; ZERO sorries (or exactly one named, if truly blocked); §2 tags; commit
(`conc(mcdiarmid): Doob martingale MGF bound (Lu-BDA §3.1)`). Report build status, exact sorry
status, and whether Mathlib's Azuma machinery was reused. Independently re-verified.
