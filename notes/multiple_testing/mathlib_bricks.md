# MultipleTesting — verified Mathlib bricks (pin: Mathlib v4.29.1)

Names verified via `tools/loogle.sh` + repo import grep. Confirm with `tools/check.sh` before use.

## Optional stopping / martingales — `Mathlib.Probability.Martingale.{Basic,OptionalStopping}`
* `MeasureTheory.Supermartingale (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ)` — supermartingale.
* `MeasureTheory.Martingale`, `MeasureTheory.Submartingale`.
* `MeasureTheory.Supermartingale.neg : Supermartingale f ℱ μ → Submartingale (-f) ℱ μ` (dual; for the bridge).
* `MeasureTheory.Submartingale.expected_stoppedValue_mono` — for `τ ≤ π` stopping times, `π`
  bounded (`∀ ω, π ω ≤ (N:ℕ∞)`), `∫ stoppedValue f τ ≤ ∫ stoppedValue f π`. **This is the engine
  for `thm:optstop`.** Stopping times are `Ω → ℕ∞`, process `f : ℕ → Ω → E`.
* `MeasureTheory.IsStoppingTime`, `MeasureTheory.stoppedValue`, `MeasureTheory.Filtration`,
  `MeasureTheory.SigmaFiniteFiltration`.

## Independence — `Mathlib.Probability.Independence.Basic`
* `ProbabilityTheory.iIndepFun (f : ι → Ω → β) (μ)` — joint independence of a family (used by BH
  `hindep` and `KnockoffScore.signs_iIndep`; index `↥H₀` for the latter).
* `ProbabilityTheory.IndepFun (f g) (μ)` — pairwise independence of two functions
  (`KnockoffScore.signs_indep_mag`: sign vector ⟂ magnitude vector).

## Order statistics — `Mathlib.Data.Fin.Tuple.Sort`
* `Tuple.sort (v : Fin n → α) : Equiv.Perm (Fin n)` — sorting permutation.
* `Tuple.monotone_sort : Monotone (v ∘ Tuple.sort v)` (the lemma to close `orderStat_monotone`;
  verify exact name with `check.sh`).

## Integral / measure — `Mathlib.MeasureTheory.Integral.Bochner.Basic`
* `MeasureTheory.integral` (`∫ ω, f ω ∂μ`); `Finset.card`, `Finset.filter`, `Finset.sup`,
  `Set.indicator`, `Finset.sum_boole` for the counting arguments.
* Conditional expectation (for BH tower property): `MeasureTheory.condExp` (`μ[f|m]`),
  `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic` — proof-only import.

## NOT in Mathlib (defined in this area)
FDP / FDR / FWER, SuperUniform, KnockoffScore. **PRDS not needed** (book BH is the independent case).
