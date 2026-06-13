Read CLAUDE.md (repo root) first and obey it — §2, §6, §7, §10, §11–16. Use the search tools.
Never `lake update`. You are ALREADY inside an srun allocation — build with plain `lake build` and
ITERATE until 0 errors (do NOT submit async and stop).

# CONTEXT
`StatLean/ConcentrationInequalities/McDiarmid/DoobDecomposition.lean` is MOSTLY written (Doob
martingale, telescope, increments, `doobCY` recursion) but a preemption left it BROKEN. Current
`lake build StatLean.ConcentrationInequalities.McDiarmid.DoobDecomposition` errors:
- 71:8  `typeclass instance problem is stuck`  (likely a missing `Fintype`/`MeasurableSpace`/
  filtration instance annotation — make it explicit, e.g. `(by infer_instance)` or name the instance).
- 119:14 `unsolved goals` (finish the proof step).
- 156:11 `No goals to be solved` (drop the stray trailing tactic, §7.10).
- 242:26 `typeclass instance problem is stuck` (same kind as 71).
- 177:6  `declaration uses sorry` — `increment_hasCondSubgaussianMGF` (the named sorry).

# CLOSE THE SORRY using the MERGED conditional-Hoeffding lemma.
`McDiarmid/CondHoeffding.lean` (imported) provides
`condExp_hoeffding_mgf (hm : m ≤ mΩ) (hZ_int) (hbound : ∀ᵐ ω, Z ω − μ[Z|m] ω ∈ Set.Icc a b) (lam) :
   ∀ᵐ ω, μ[exp(lam·(Z − μ[Z|m]))|m] ω ≤ exp(lam²(b−a)²/8)`.
`increment_hasCondSubgaussianMGF` claims the Doob increment `Δₖ = Mₖ − Mₖ₋₁` is conditionally
sub-Gaussian with proxy `(cₖ/2)² = cₖ²/4` given `Fₖ₋₁`. Since `HasCondSubgaussianMGF … proxy` unfolds
to the a.e. bound `μ[exp(lam·Δₖ)|Fₖ₋₁] ≤ exp(lam²·proxy/2) = exp(lam²·cₖ²/8)`, this is EXACTLY
`condExp_hoeffding_mgf` applied to `Z = Mₖ` (or the per-coordinate variable) with the conditional
bounded-difference hypothesis `Δₖ ∈ [aₖ, aₖ+cₖ]`. Map the increment's conditional range to
`condExp_hoeffding_mgf`'s `hbound` and discharge. Do NOT re-prove Hoeffding; wrap the merged lemma.

# ZERO sorry is the bar. Fix all 4 compile errors AND close `increment_hasCondSubgaussianMGF`. If the
increment→condExp_hoeffding_mgf mapping needs the conditional bounded-difference as an added
hypothesis on the theorem, add it tagged `-- USER-INPUT: bounded differences Dᵢf ≤ cᵢ; Lu-BDA §3.1`
(it's the genuine McDiarmid input). If a TRULY irreducible gap remains, leave exactly ONE named sorry
+ ESCALATE note.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/McDiarmid/DoobDecomposition.lean`.
# BUILD: lake build StatLean.ConcentrationInequalities.McDiarmid.DoobDecomposition
# DONE = build exits 0; ZERO sorries (or 1 named + ESCALATE); §2 tags; commit
(`conc(mcdiarmid): fix+close Doob MGF bound (Lu-BDA §3.1)`). Report build + exact sorry status.
