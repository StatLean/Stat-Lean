import StatLean.CausalInference.IV.Defs

/-!
# Compliance types — the partition and what the IV assumptions say about it

Elementary structure theory of the four compliance types: they partition the population,
monotonicity is exactly the absence of defiers, one-sided noncompliance removes always
takers as well, and the observed treatment is determined by the type together with the
instrument. These facts are what turn the mixture arguments of the LATE theorem into
finite bookkeeping.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §21.2.1 (p. 282) for the taxonomy;
Assumption 21.2 (p. 283) for monotonicity and its testable implication eq. (21.2);
§21.2 for one-sided noncompliance. (`Ding §21.2; Assumption 21.2`.) See also
G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
Sciences*, Cambridge University Press, 2015, ch. 23 (one-sided) and ch. 24 (two-sided).
(`IR chs. 23–24`.)

**Proof formalization notes.** `ComplianceType.of` is defined by a `match` on the two
`Bool`s, so every statement here is a four-way case split closed by `decide`/`simp`. The
observed-treatment characterizations are the bridge to data: only the *union* of the
always-taker and complier events is observed in the treated arm, which is the fundamental
identification difficulty that monotonicity resolves.

**Bibliographic comments.** See `IV.Defs` for the Imbens–Angrist and Angrist–Imbens–Rubin
references.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z d1 d0 : Ω → Bool}

/-- The compliance-type events are pairwise disjoint. -/
theorem typeSet_disjoint {s t : ComplianceType} (hst : s ≠ t) :
    Disjoint (typeSet d1 d0 s) (typeSet d1 d0 t) := by
  sorry

/-- Every unit has a compliance type: the four events cover the sample space. -/
theorem iUnion_typeSet : (⋃ t : ComplianceType, typeSet d1 d0 t) = Set.univ := by
  sorry

/-- Characterization of the complier event. -/
theorem mem_typeSet_complier {ω : Ω} :
    ω ∈ typeSet d1 d0 ComplianceType.complier ↔ d1 ω = true ∧ d0 ω = false := by
  sorry

/-- Characterization of the defier event. -/
theorem mem_typeSet_defier {ω : Ω} :
    ω ∈ typeSet d1 d0 ComplianceType.defier ↔ d1 ω = false ∧ d0 ω = true := by
  sorry

/-- **Monotonicity is exactly the absence of defiers** (Ding Assumption 21.2). -/
theorem noDefiers_iff_typeSet_defier_eq_empty :
    NoDefiers d1 d0 ↔ typeSet d1 d0 ComplianceType.defier = ∅ := by
  sorry

/-- **One-sided noncompliance removes always takers and defiers** (`IR` ch. 23): if nobody
can take the treatment without being assigned it, only compliers and never takers remain.
In particular monotonicity holds automatically. -/
theorem oneSided_noDefiers (h : OneSidedNoncompliance d0) : NoDefiers d1 d0 := by
  sorry

/-- Under one-sided noncompliance there are no always takers. -/
theorem oneSided_typeSet_alwaysTaker_eq_empty (h : OneSidedNoncompliance d0) :
    typeSet d1 d0 ComplianceType.alwaysTaker = ∅ := by
  sorry

/-- The **individual treatment effect of the instrument on the treatment received** is the
complier indicator minus the defier indicator. -/
theorem ind_d1_sub_ind_d0 (ω : Ω) :
    ind (d1 ω) - ind (d0 ω)
      = (if ω ∈ typeSet d1 d0 ComplianceType.complier then (1 : ℝ) else 0)
        - (if ω ∈ typeSet d1 d0 ComplianceType.defier then (1 : ℝ) else 0) := by
  sorry

/-- In the treated arm the observed treatment equals `D(1)`; in the control arm it equals
`D(0)` — the observed-treatment analogue of the consistency assumption. -/
theorem obsTreat_eq (ω : Ω) : obsTreat Z d1 d0 ω = if Z ω then d1 ω else d0 ω := rfl

/-- Under monotonicity, a unit takes the treatment when assigned to it exactly when it is
a complier or an always taker. -/
theorem d1_eq_true_iff (h : NoDefiers d1 d0) (ω : Ω) :
    d1 ω = true ↔ ω ∈ typeSet d1 d0 ComplianceType.complier
                    ∪ typeSet d1 d0 ComplianceType.alwaysTaker := by
  sorry

/-- A unit takes the treatment when *not* assigned to it exactly when it is an always
taker, under monotonicity. -/
theorem d0_eq_true_iff (h : NoDefiers d1 d0) (ω : Ω) :
    d0 ω = true ↔ ω ∈ typeSet d1 d0 ComplianceType.alwaysTaker := by
  sorry

/-- **The exclusion restriction pins the outcome on non-compliers** (Ding Assumption
21.3): always takers and never takers have the same potential outcome under both
assignments. -/
theorem y_eq_of_exclusion {y1 y0 : Ω → ℝ} (h : ExclusionRestriction d1 d0 y1 y0) {ω : Ω}
    (hω : ω ∈ typeSet d1 d0 ComplianceType.alwaysTaker
            ∪ typeSet d1 d0 ComplianceType.neverTaker) :
    y1 ω = y0 ω := by
  sorry

end StatLean.CausalInference
