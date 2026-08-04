import StatLean.StatisticalModels.Survival.Censoring

/-!
# Competing risks — cause-specific hazards and cumulative incidence

Marked event-history observations `(T̃, κ) : ℝ × Option (Fin k)` — `none` = censored,
`some j` = failure from cause `j` (the `k = 1` case subsumes the `ℝ × Bool` censoring
carrier through `toBoolObs`):

* `causeSubLaw P j` — the cause-`j` sub-distribution `P(T̃ ∈ ·, κ = j)`; `cumIncidence` —
  the cumulative incidence function `F_j(t)`;
* `causeSpecificCumHazard P j` — cause-`j` event increments over the all-cause at-risk
  probability (`ABGK §IV.4`-style crude cause-specific hazard);
* **`sum_causeSpecificCumHazard` (S6.1)** — cause-specific hazards add up to the all-cause
  hazard;
* **`causeSubLaw_eq_withDensity` (S6.2)** — the exact CIF identity
  `F_j(dt) = S(t^-)\,Λ_j(dt)` in measure form;
* **`causeSpecificCumHazard_crLaw₂` (S6.3)** — for two *independent* latent cause times,
  the crude cause-specific hazard equals the net hazard of that cause where the other
  survives — the competing-risks mirror of the censoring headline (S2.3), positively
  resolving the identifiable region of Tsiatis's nonidentifiability;
* `graySubCumHazard` — Gray's subdistribution hazard, with its comparison to the
  cause-specific hazard.

`k`-cause crude=net and Aalen–Johansen/multistate are named future debts (D-S6, D-S1).

**Reference.** ABGK §IV.4 (competing risks, cause-specific quantities) (verify §);
R. L. Prentice et al., "The analysis of failure times in the presence of competing risks,"
*Biometrics* **34** (1978), 541–554; A. Tsiatis, *Proc. Nat. Acad. Sci.* **72** (1975),
20–22 (`Tsiatis75`); R. J. Gray, "A class of K-sample tests for comparing the cumulative
incidence of a competing risk," *Ann. Statist.* **16** (1988), 1141–1154 (`Gray88`);
J. P. Fine and R. J. Gray, "A proportional hazards model for the subdistribution of a
competing risk," *JASA* **94** (1999), 496–509 (defs only).

**Proof formalization notes.** All identities are `restrict`/`withDensity`/`map`
bookkeeping in the style of the closed `Censoring.lean` (whose `withDensity`-merge and
`0·∞ = 0` conventions are reused); S6.1 is countable additivity of `restrict` over the
disjoint cause slices; S6.3 replays the S2.3 density-merge with the roles of the two laws
symmetrized. Tie convention in `crObserve₂`: ties go to cause `0` (*Book vs Lean:* the
references assume no ties a.s.).

**Bibliographic comments.** Cause-specific hazards and their sum rule are classical
(Prentice et al. 1978); the CIF-vs-hazard identity is the competing-risks form of the
product-limit relation; the subdistribution hazard is Gray's (1988).
-/

open MeasureTheory Set Finset
open scoped ENNReal

namespace StatLean.StatisticalModels.Survival

variable {k : ℕ}

/-- The mark space carries the discrete σ-algebra (LEAN-ONLY: the pin has no
`MeasurableSpace (Option _)` instance; on a finite type `⊤` is the correct one — it is
exactly what `Bool` carries on the censoring carrier). -/
instance : MeasurableSpace (Option (Fin k)) := ⊤

/-- The observed-time law of a marked observation. -/
noncomputable def observedTimeLawCR (P : Measure (ℝ × Option (Fin k))) : Measure ℝ :=
  P.map Prod.fst

/-- The cause-`j` **sub-distribution** `P(T̃ ∈ ·, κ = j)` (ABGK §IV.4). -/
noncomputable def causeSubLaw (P : Measure (ℝ × Option (Fin k))) (j : Fin k) : Measure ℝ :=
  (P.restrict {p | p.2 = some j}).map Prod.fst

/-- The all-cause (uncensored) sub-distribution `P(T̃ ∈ ·, κ ≠ none)`. -/
noncomputable def allCauseSubLaw (P : Measure (ℝ × Option (Fin k))) : Measure ℝ :=
  (P.restrict {p | p.2 ≠ none}).map Prod.fst

/-- The **cumulative incidence function** `F_j(t) = P(T̃ ≤ t, κ = j)` (Prentice et al.
1978). -/
noncomputable def cumIncidence (P : Measure (ℝ × Option (Fin k))) (j : Fin k) (t : ℝ) :
    ℝ≥0∞ :=
  causeSubLaw P j (Iic t)

/-- The crude **cause-specific cumulative hazard**: cause-`j` increments over the all-cause
at-risk probability (ABGK §IV.4). -/
noncomputable def causeSpecificCumHazard (P : Measure (ℝ × Option (Fin k))) (j : Fin k) :
    Measure ℝ :=
  (causeSubLaw P j).withDensity fun t => (observedTimeLawCR P (Ici t))⁻¹

/-- The all-cause crude cumulative hazard. -/
noncomputable def allCauseCumHazard (P : Measure (ℝ × Option (Fin k))) : Measure ℝ :=
  (allCauseSubLaw P).withDensity fun t => (observedTimeLawCR P (Ici t))⁻¹

/-- **Gray's subdistribution cumulative hazard** (`Gray88`): cause-`j` increments over the
subdistribution at-risk mass `P(Ω) − F_j(t^-)`. -/
noncomputable def graySubCumHazard (P : Measure (ℝ × Option (Fin k))) (j : Fin k) :
    Measure ℝ :=
  (causeSubLaw P j).withDensity fun t => (P univ - causeSubLaw P j (Iio t))⁻¹

/-- The `k = 1` marked carrier collapses to the censoring carrier. -/
def toBoolObs : ℝ × Option (Fin 1) → ℝ × Bool :=
  fun p => (p.1, p.2.isSome)

/-- Bridge: the single-cause sub-law is the uncensored sub-law of the collapsed
observation. -/
theorem causeSubLaw_eq_uncensoredSubLaw (P : Measure (ℝ × Option (Fin 1)))
    [IsFiniteMeasure P] (j : Fin 1) :
    causeSubLaw P j = uncensoredSubLaw (P.map toBoolObs) := by
  sorry

/-- Sub-laws are dominated by the observed-time law (the restrict-monotonicity
workhorse). -/
theorem causeSubLaw_le (P : Measure (ℝ × Option (Fin k))) (j : Fin k) {A : Set ℝ}
    (hA : MeasurableSet A) :
    causeSubLaw P j A ≤ observedTimeLawCR P A := by
  sorry

/-- **S6.1, hazard additivity** (Prentice et al. 1978; ABGK §IV.4): the cause-specific
cumulative hazards sum to the all-cause crude hazard. -/
theorem sum_causeSpecificCumHazard (P : Measure (ℝ × Option (Fin k))) [IsFiniteMeasure P] :
    ∑ j : Fin k, causeSpecificCumHazard P j = allCauseCumHazard P := by
  sorry

/-- **S6.2, the exact CIF identity** `F_j(dt) = S(t^-) Λ_j(dt)` in measure form
(ABGK §IV.4): recovering the sub-distribution from its cause-specific hazard. -/
theorem causeSubLaw_eq_withDensity (P : Measure (ℝ × Option (Fin k))) [IsFiniteMeasure P]
    (j : Fin k) :
    causeSubLaw P j
      = (causeSpecificCumHazard P j).withDensity fun t => observedTimeLawCR P (Ici t) := by
  sorry

/-- Two independent latent cause times observed as (first failure, cause); ties to cause 0
(*Book vs Lean* note in module docstring). -/
noncomputable def crObserve₂ : ℝ × ℝ → ℝ × Option (Fin 2) :=
  fun p => (min p.1 p.2, if p.1 ≤ p.2 then some 0 else some 1)

/-- The two-cause independent competing-risks law. -/
noncomputable def crLaw₂ (μ₁ μ₂ : Measure ℝ) : Measure (ℝ × Option (Fin 2)) :=
  (μ₁.prod μ₂).map crObserve₂

/-- **S6.3, crude = net for independent competing risks** (`Tsiatis75` positively resolved
on the identifiable region; the S2.3 mirror): the crude cause-0 hazard is the net hazard of
`T₁` where `T₂` survives. -/
theorem causeSpecificCumHazard_crLaw₂ (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] :
    causeSpecificCumHazard (crLaw₂ μ₁ μ₂) 0
      = (cumHazard μ₁).restrict {t | 0 < μ₂ (Ici t)} := by
  sorry

/-- **S6.4, Gray vs cause-specific** (`Gray88`): the subdistribution at-risk mass dominates
the all-cause at-risk mass, so the Gray hazard is dominated by the cause-specific hazard. -/
theorem graySubCumHazard_le (P : Measure (ℝ × Option (Fin k))) [IsProbabilityMeasure P]
    (j : Fin k) {A : Set ℝ} (hA : MeasurableSet A) :
    graySubCumHazard P j A ≤ causeSpecificCumHazard P j A := by
  sorry

end StatLean.StatisticalModels.Survival
