Read CLAUDE.md (repo root) first — §2, §6, §7, §10, §11–16 (condExp/kernel gotchas). Use the search
tools EXHAUSTIVELY. Never `lake update`. You are inside an srun allocation — `lake build`, ITERATE.

# GOAL
`StatLean/ConcentrationInequalities/McDiarmid/DoobDecomposition.lean` builds with ONE named sorry
`increment_bounded_of_bounded_differences` (~line 193). Close it to ZERO sorry. Do NOT change other
declarations' statements.

# THE LEMMA
It states that the Doob increment `Δₖ = μ[f∘X | Fₖ] − μ[f∘X | Fₖ₋₁]` of a bounded-differences function
`f` (with `Dᵢf ≤ cᵢ`) over INDEPENDENT coordinates `X` lies in an interval of length `≤ cₖ` given
`Fₖ₋₁` (the conditional range bound), which feeds `condExp_hoeffding_mgf`.

# KEY FACT TO ESTABLISH (the flagged gap)
Under `iIndepFun X`, the conditional law of `Xₖ` given `Fₖ₋₁ = σ(X₀,…,Xₖ₋₁)` is the MARGINAL law:
`condDistrib Xₖ (Fₖ₋₁-measurable data) μ = μ.map Xₖ` a.e. — i.e. conditioning on the past does not
change `Xₖ`'s distribution. SEARCH HARD before concluding it's missing:
`./tools/loogle.sh '"condDistrib"'`, `'"condIndep"'`, `'"iIndepFun"' '"condExp"'`,
`'"condExp_indep"'`, `'"indepFun"' '"condDistrib"'`, `Mathlib/Probability/{Independence,ConditionalProbability,Kernel}/*`,
`ProbabilityTheory.condExp_indepFun`, `ProbabilityTheory.condDistrib_eq_map_of_indep`-style names.
If Mathlib has `condExp_indepFun`/`condIndepFun` giving `μ[g∘Xₖ | Fₖ₋₁] = μ[g∘Xₖ]` for independent
`Xₖ ⟂ Fₖ₋₁`, USE IT — that is exactly enough: the increment
`Δₖ = E_{Xₖ}[f(…,Xₖ,…)|past] − E_{Xₖ,Xₖ outer}[…]` then has range `≤ sup−inf ≤ cₖ` by the
bounded-difference bound applied pointwise under the (marginal) `Xₖ`-integral.

# If the fact is GENUINELY absent from Mathlib: prove the minimal version you need as a `private`
helper in THIS file (do NOT create new files): for `Xₖ` independent of a sub-σ-algebra `m` and `g`
bounded measurable, `μ[g ∘ Xₖ | m] =ᵐ μ[g ∘ Xₖ]` (const). Derive from `iIndepFun` ⇒
`IndepFun Xₖ (m-measurable)` and `condExp` of an independent integrable function = its mean
(`MeasureTheory.condExp_indep_eq`? `condExp_of_indepFun`? search). Then the increment range bound
follows.

# ZERO sorry is the bar. If after a THOROUGH, documented effort the independence⇒conditional fact is
truly unprovable on the pin without a large ForMathlib development, leave EXACTLY the one named sorry
with an updated docstring (precise missing statement + every lemma tried) and print
"ESCALATE: increment_bounded needs <exact Mathlib lemma>, not available" — the orchestrator will
decide whether to build it as a ForMathlib lemma.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/McDiarmid/DoobDecomposition.lean`.
# BUILD: lake build StatLean.ConcentrationInequalities.McDiarmid.DoobDecomposition
# DONE = build exits 0; ZERO sorries (or 1 named + ESCALATE); commit
(`conc(mcdiarmid): close increment_bounded via independence⇒conditional (Lu-BDA §3.1)`). Report build
+ exact sorry status + whether you found the Mathlib lemma or built the helper.
