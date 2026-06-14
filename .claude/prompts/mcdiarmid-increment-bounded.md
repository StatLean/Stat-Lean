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

# CONFIRMED (twice): the RANGE bound on the increment needs the DISTRIBUTION-level fact
#   `IndepFun X Y μ → condDistrib Y X μ =ᵐ[μ.map X] Kernel.const _ (μ.map Y)`
# (the condExp/mean version below is NOT enough for a sup−inf range bound). This is genuinely absent
# from Mathlib — so PROVE IT as a `private` lemma in this file (do NOT create new files), via
# DISINTEGRATION UNIQUENESS:
#   1. Under independence, the joint law factorises: `μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod (μ.map Y)`
#      — search `IndepFun.map_prod_eq_prod` / `IndepFun` ⇒ `μ.map (X,Y) = (μ.map X).prod (μ.map Y)`
#      (`./tools/loogle.sh '"IndepFun"' '"map"'`, `'"indepFun_iff_map_prod_eq_prod"'`).
#   2. `condDistrib Y X μ` is THE (a.e.-unique) disintegrating kernel: `(μ.map X) ⊗ₖ condDistrib Y X μ
#      = μ.map (X,Y)` (`ProbabilityTheory.compProd_condDistrib` / `condDistrib_compProd`). The constant
#      kernel `Kernel.const _ (μ.map Y)` ALSO disintegrates the product: `(μ.map X) ⊗ₖ const _ (μ.map Y)
#      = (μ.map X).prod (μ.map Y)` (`Kernel.compProd_const` / `Measure.compProd_const`).
#   3. By a.e.-uniqueness of disintegration (`ProbabilityTheory.Kernel.apply_eq_…`/`eq_condDistrib_of_…`,
#      or `Measure.ext` on the compProd + `Kernel.ext_ae`), conclude `condDistrib Y X μ =ᵐ const _ (μ.map Y)`.
#   Needs `[StandardBorelSpace]`/`IsFiniteMeasure` instances — supply them (the McDiarmid setup has them).
# Then the increment range bound: `μ[f|Fₖ] − μ[f|Fₖ₋₁]` integrates `Xₖ` against `μ.map Xₖ` in both
# terms, so the difference is bounded by `sup_{xₖ,xₖ'} |f(…xₖ…) − f(…xₖ'…)| ≤ Dₖf ≤ cₖ` pointwise.

# (LEGACY note — the condExp/mean version, insufficient alone:)
# THE LEMMA EXISTS IN MATHLIB (a prior session searched `condDistrib` and missed the `condExp`
# formulation). USE THESE — do NOT re-search from scratch, do NOT escalate:
#   • `MeasureTheory.condExp_indep_eq (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) [SigmaFinite (μ.trim hle₂)]
#       (hf : StronglyMeasurable[m₁] f) (hindp : Indep m₁ m₂ μ) : μ[f | m₂] =ᵐ[μ] fun _ => μ[f]`
#     — conditioning an `m₁`-measurable `f` on an INDEPENDENT σ-algebra `m₂` gives the unconditional mean.
#   • `ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt (hf : ∀ i, StronglyMeasurable (f i))
#       (hfi : iIndepFun f μ) (hij : i < j) : μ[f j | Filtration.natural f hf i] =ᵐ[μ] fun _ => μ[f j]`
#     — the EXACT filtration version: `Xⱼ` conditioned on the natural filtration of the past `= E[Xⱼ]`.
# `./tools/check.sh 'MeasureTheory.condExp_indep_eq'` and
# `./tools/check.sh 'ProbabilityTheory.iIndepFun.condExp_natural_ae_eq_of_lt'` to confirm, then build
# the increment range bound on top: the `Xₖ`-fibre of `μ[f∘X|Fₖ₋₁]` integrates out `Xₖ` against its
# marginal (by the above), so `Δₖ = μ[f|Fₖ] − μ[f|Fₖ₋₁]` differs only in the `Xₖ` coordinate and its
# range is `≤ Dₖf ≤ cₖ` by the bounded-difference hypothesis applied pointwise.

# KEY FACT (now resolved — see above):
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
