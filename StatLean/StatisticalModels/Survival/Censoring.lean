import StatLean.StatisticalModels.Survival.CumulativeHazard
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Right censoring — the random censorship model and crude = net hazard

The observation side of survival analysis. Full datum `(T, C)` — event time and censoring
time — is observed as `(T ∧ C, 1{T ≤ C})`:

* `censorObserve` — the coarsening map;
* `censoredLaw μT μC` — the observed-data law under **independent censoring** (the random
  censorship model: the product joint law made structural);
* `observedTimeLaw P` / `uncensoredSubLaw P` — the law of the observed time `T̃` and the
  `Δ = 1` sub-distribution `P(T̃ ∈ ·, Δ = 1)` of an arbitrary observed-data law `P`;
* `crudeCumHazard P` — the crude (observable) cumulative hazard: `Δ = 1` event increments
  over the at-risk denominator `P(T̃ ≥ t)`.

**Headline (S2.3, `crudeCumHazard_censoredLaw`).** Under independent censoring the crude
hazard **is** the net hazard of `T` on the region where censoring survives:
$$\tilde\Lambda(dt) = \Lambda_T(dt)\quad\text{on } \{t : S_C(t^-) > 0\}.$$
This is the identifiability theorem licensing Nelson–Aalen/Kaplan–Meier estimation from
censored data, in exact measure form — no continuity, no atomlessness. Its engine is the
fully general sub-distribution formula (S2.2): `P(T̃ ∈ dt, Δ = 1) = S_C(t^-)\,dF_T(t)`.

**Reference.** ABGK §III.2 (random censorship, the observed intensities) (verify §);
E. L. Kaplan and P. Meier, *J. Amer. Statist. Assoc.* **53** (1958), 457–481, §2 (the
crude-vs-net identification) (`KM58 §2`); the nonidentifiability of the joint law without
independence: A. Tsiatis, "A nonidentifiability aspect of the problem of competing risks,"
*Proc. Nat. Acad. Sci.* **72** (1975), 20–22 (`Tsiatis75`) — documented as a non-theorem
here; the dependent-censoring counterexample construction is a named future debt.

**Proof formalization notes.** Tie convention `Δ = decide (T ≤ C)` (ties count as events) —
*Book vs Lean:* ABGK assume `P(T = C) = 0`, making the convention immaterial there. S2.2 is
`Measure.prod` + Fubini section computation (`{c | t ≤ c} = Ici t`) — the β-reduction gotcha
of `Measure.prod_apply` applies (use `simp_rw`/`change`). S2.3 merges the two `withDensity`
layers and cancels `S_C(t^-) · (S_T(t^-) S_C(t^-))⁻¹ = S_T(t^-)⁻¹` in `ℝ≥0∞`; on
`{S_C(t^-) = 0}` the ENNReal convention `0 · ∞ = 0` makes the crude side vanish — that region
is exactly what the `restrict` in the statement removes.

**Bibliographic comments.** The random censorship model is Gilbert's 1962 thesis and
Breslow–Crowley, *Ann. Statist.* **2** (1974), 437–453; the measure-level crude/net calculus
follows ABGK §III.2.
-/

open MeasureTheory Set
open scoped ENNReal

namespace StatLean.StatisticalModels.Survival

/-- The right-censoring coarsening map `(t, c) ↦ (t ∧ c, 1{t ≤ c})`
(tie convention: ties are events; KM58 §2). -/
noncomputable def censorObserve : ℝ × ℝ → ℝ × Bool :=
  fun p => (min p.1 p.2, decide (p.1 ≤ p.2))

/-- The coarsening map is measurable (LEAN-ONLY plumbing). -/
theorem measurable_censorObserve : Measurable censorObserve := by
  refine (measurable_fst.min measurable_snd).prodMk (measurable_to_bool ?_)
  have hset : (fun p : ℝ × ℝ => decide (p.1 ≤ p.2)) ⁻¹' {true} = {p : ℝ × ℝ | p.1 ≤ p.2} := by
    ext p; simp
  rw [hset]
  exact measurableSet_le measurable_fst measurable_snd

/-- The **random censorship model**: the observed-data law under independent censoring —
the product joint `(T, C) ∼ μT ⊗ μC` pushed through `censorObserve` (ABGK §III.2;
Breslow–Crowley 1974). Independence is structural here, not a hypothesis. -/
noncomputable def censoredLaw (μT μC : Measure ℝ) : Measure (ℝ × Bool) :=
  (μT.prod μC).map censorObserve

instance (μT μC : Measure ℝ) [IsProbabilityMeasure μT] [IsProbabilityMeasure μC] :
    IsProbabilityMeasure (censoredLaw μT μC) := by
  sorry

/-- The law of the observed time `T̃` of an observed-data law. -/
noncomputable def observedTimeLaw (P : Measure (ℝ × Bool)) : Measure ℝ :=
  P.map Prod.fst

/-- The `Δ = 1` (uncensored) **sub-distribution** `P(T̃ ∈ ·, Δ = 1)`. -/
noncomputable def uncensoredSubLaw (P : Measure (ℝ × Bool)) : Measure ℝ :=
  (P.restrict {p | p.2 = true}).map Prod.fst

/-- The **crude cumulative hazard** of an observed-data law: uncensored event increments
over the at-risk probability `P(T̃ ≥ t)` (ABGK §III.2). -/
noncomputable def crudeCumHazard (P : Measure (ℝ × Bool)) : Measure ℝ :=
  (uncensoredSubLaw P).withDensity fun t => (observedTimeLaw P (Ici t))⁻¹

/-- **S2.1 (observed survival factorizes, `Ioi` form)**: under independent censoring
`P(T̃ > t) = S_T(t) · S_C(t)` (ABGK §III.2). -/
theorem observedTimeLaw_censoredLaw_Ioi (μT μC : Measure ℝ) [IsProbabilityMeasure μT]
    [IsProbabilityMeasure μC] (t : ℝ) :
    observedTimeLaw (censoredLaw μT μC) (Ioi t) = μT (Ioi t) * μC (Ioi t) := by
  sorry

/-- **S2.1 (`Ici` form)**: `P(T̃ ≥ t) = S_T(t^-) · S_C(t^-)`. -/
theorem observedTimeLaw_censoredLaw_Ici (μT μC : Measure ℝ) [IsProbabilityMeasure μT]
    [IsProbabilityMeasure μC] (t : ℝ) :
    observedTimeLaw (censoredLaw μT μC) (Ici t) = μT (Ici t) * μC (Ici t) := by
  sorry

/-- **S2.2 (sub-distribution formula, fully general)**: under independent censoring,
`P(T̃ ∈ dt, Δ = 1) = S_C(t^-)\,dF_T(t)` — exactly, for arbitrary (atomic or not) laws
(ABGK §III.2; KM58 §2). -/
theorem uncensoredSubLaw_censoredLaw (μT μC : Measure ℝ) [IsProbabilityMeasure μT]
    [IsProbabilityMeasure μC] :
    uncensoredSubLaw (censoredLaw μT μC) = μT.withDensity fun t => μC (Ici t) := by
  sorry

/-- **S2.3, HEADLINE (crude = net hazard)**: under independent censoring the crude cumulative
hazard of the observed data equals the net cumulative hazard of the event-time law, restricted
to the region where censoring survives — the exact identifiability theorem licensing
Nelson–Aalen/Kaplan–Meier from censored data (ABGK §III.2; KM58 §2; positively resolving the
region where `Tsiatis75` nonidentifiability cannot bite). -/
theorem crudeCumHazard_censoredLaw (μT μC : Measure ℝ) [IsProbabilityMeasure μT]
    [IsProbabilityMeasure μC] :
    crudeCumHazard (censoredLaw μT μC) = (cumHazard μT).restrict {t | 0 < μC (Ici t)} := by
  sorry

/-- The uncensored sub-law is dominated by the observed-time law (LEAN-ONLY; the
restrict-monotonicity workhorse for S2.3). -/
theorem uncensoredSubLaw_le (P : Measure (ℝ × Bool)) {A : Set ℝ} (hA : MeasurableSet A) :
    uncensoredSubLaw P A ≤ observedTimeLaw P A := by
  sorry

end StatLean.StatisticalModels.Survival
