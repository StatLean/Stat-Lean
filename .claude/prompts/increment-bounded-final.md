Read CLAUDE.md (repo root) first — §2, §6, §7, §10–16. Use the search tools / `./tools/check.sh`.
Never `lake update`. You are inside an srun allocation — build with plain `lake build`, ITERATE to 0 sorry.
This is the LAST sorry in the whole project. Budget generously (Opus, max thinking).

# GOAL
Close `increment_bounded_of_bounded_differences` (the one `sorry`, ~line 193) in
`StatLean/ConcentrationInequalities/McDiarmid/DoobDecomposition.lean` to ZERO sorry. The full proof
path now EXISTS in Mathlib — assemble it. You MAY also edit `McDiarmid/McDiarmid.lean` (the only
downstream consumer) to thread new instance hypotheses. Do NOT weaken any theorem's conclusion.

# STEP 0 — ADD STANDARD-BOREL INSTANCES (the missing piece).
The coordinate spaces `β : Fin n → Type*` currently have only `[(i) → MeasurableSpace (β i)]`.
`condDistrib` on `β k` needs `[StandardBorelSpace (β k)]` and `[Nonempty (β k)]`. Add to the `variable`
block (and propagate to every lemma that needs it, incl. `increment_hasCondSubgaussianMGF`,
`mgf_sub_expectation_le`, and the McDiarmid theorems in `McDiarmid.lean`):
  `[∀ i, StandardBorelSpace (β i)] [∀ i, Nonempty (β i)]`
This is a mild, standard restriction (Polish/finite/countable coordinate spaces all qualify);
document it with a `-- LEAN-ONLY: standard-Borel coordinate spaces; needed for condDistrib`.

# STEP 1 — PROVE THE KEY HELPER (independence ⇒ conditional law = marginal).
Add a `private lemma` in DoobDecomposition.lean:
  `condDistrib_eq_const_of_indepFun {α γ} [MeasurableSpace α] [MeasurableSpace γ] [StandardBorelSpace γ]
     [Nonempty γ] {μ : Measure α} [IsProbabilityMeasure μ] {W : α → β'} {Z : α → γ}
     (hW : Measurable W) (hZ : Measurable Z) (h : IndepFun W Z μ) :
     condDistrib Z W μ =ᵐ[μ.map W] Kernel.const _ (μ.map Z)`
PROOF (these are the exact Mathlib bricks — confirm each with `./tools/check.sh`):
  1. `(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hZ.aemeasurable).1 h`
     gives `μ.map (fun a => (W a, Z a)) = (μ.map W).prod (μ.map Z)`.
  2. `MeasureTheory.Measure.compProd_const : (μ.map W) ⊗ₘ (Kernel.const _ (μ.map Z)) = (μ.map W).prod (μ.map Z)`
     (`SFinite` instances hold for finite measures). So
     `μ.map (fun a => (W a, Z a)) = (μ.map W) ⊗ₘ (Kernel.const _ (μ.map Z))`.
  3. `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd W hZ.aemeasurable (κ := Kernel.const _ (μ.map Z)) <the eq from step 2>`
     (`Kernel.const` of a probability measure is `IsFiniteKernel` — instance should fire) gives the goal.

# STEP 2 — USE IT in `increment_bounded_of_bounded_differences`.
The increment `Δₖ₊₁ = μ[f∘allVars X | F_{k+1}] − μ[f∘allVars X | F_k]`. Conditioning on `F_k = σ(X₀..X_{k-1})`
integrates the `Xₖ`-coordinate against its MARGINAL law (by Step 1, since `Xₖ ⟂ F_k` from `iIndepFun`
— extract `IndepFun (X ⟨k,hk⟩) (the F_k-data)` via `iIndepFun`'s consequences, e.g.
`iIndepFun.indepFun_finset` / independence of `Xₖ` from `(X₀,…,X_{k-1})`). Bridge the fiber kernel
`condExpKernel μ (natFiltration X hX k)` to `condDistrib` via
`ProbabilityTheory.condExpKernel_apply_eq_condDistrib` (Mathlib/Probability/Kernel/Condexp.lean) where
needed. Then both Icc bounds follow from the bounded-difference hypothesis `hbd` applied pointwise:
the conditional mean `g(y) = E[f(…,y,…)|rest]` has range `sup_y g − inf_y g ≤ cₖ`, and subtracting the
`F_k`-conditional mean (= integral of `g` against `Xₖ`'s marginal) lands `Δₖ₊₁` in an interval of
length `≤ cₖ`. The `a` in the fiber-wise `Icc a (a+cₖ)` is `inf_y g(y) − E_{Xₖ}[g]`.

# If a sub-step is still genuinely missing after THIS path, isolate ONE minimal named sorry with the
# exact remaining goal + lemmas tried + ESCALATE. But the bricks above are a complete path — push hard.

# TOUCH-SET: `McDiarmid/DoobDecomposition.lean` (primary) and `McDiarmid/McDiarmid.lean` (only to thread
#   the StandardBorelSpace/Nonempty instances). Do NOT touch other files/umbrellas/Defs.
# BUILD: lake build StatLean.ConcentrationInequalities.McDiarmid.McDiarmid   (builds both)
# DONE = build exits 0; ZERO sorries in BOTH files; §2 tags on any new hyp; commit
(`conc(mcdiarmid): close increment_bounded via condDistrib_eq_const_of_indepFun (Lu-BDA §3.1)`).
Report build + exact sorry status (must be 0) + the instances you added.
