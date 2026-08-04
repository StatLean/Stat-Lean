import StatLean.StatisticalModels.Survival.Cox.Defs
import StatLean.StatisticalModels.Survival.HazardBridges

/-!
# The canonical Cox law — construction and realization

The construction side of the Cox model: for a continuous, locally finite baseline `Λ₀`
concentrated on `(0, ∞)`, the survival function `coxSurvival β Λ₀ z` is a genuine
(sub-)survival curve; its Stieltjes law `coxMeasure β Λ₀ z` is an event-time law exactly when
the total baseline hazard is infinite (else the defect is the cure mass); and — the
realization theorem **S5.2** — the constructed family has exactly the proportional-hazards
structure it was built from: `cumHazard (coxMeasure β Λ₀ z) = e^{⟪β,z⟫} • Λ₀`.

S5.2 is this batch's designated hard theorem (it rides the S-B4 analytic bricks); it is the
single allowed carry if the bridge batch slips.

**Reference.** `Cox72 §2`; ABGK §III.1.2 (verify §): the multiplicative-hazard model and its
absolutely-continuous construction.

**Proof formalization notes.** Monotonicity/right-continuity of `1 − coxSurvival` come from
monotonicity and continuity-from-above of `Λ₀(Ioc 0 ·]` (no atoms ⇒ continuity, whence the
Stieltjes packaging); probability-vs-defect is the `t → ∞` limit against
`Tendsto (Λ₀ (Ioc 0 ·)) atTop (𝓝 ⊤)`. S5.2 reduces, per evaluation set, to the
scalar Stieltjes-FTC identity `∫_{(a,b]} c·e^{−c·G(t)} dΛ₀(t) = e^{−c·G(a)} − e^{−c·G(b)}`
with `G t = Λ₀(Ioc 0 t]` — shared machinery with `HazardBridges` (S4.1's Route A/B bricks).

**Bibliographic comments.** The exponential-of-integrated-hazard construction is classical
(actuarial); Cox (1972) §2 uses it implicitly; ABGK III.1.2 states it in measure form.
-/

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.Survival

variable {p : ℕ} (β : EuclideanSpace ℝ (Fin p)) (Λ₀ : Measure ℝ)
  (z : EuclideanSpace ℝ (Fin p))

/-- The Cox survival function is antitone (given a locally finite baseline). -/
theorem antitone_coxSurvival
    -- USER-INPUT: locally finite baseline hazard (Λ₀(0,t] < ∞); Cox72 §2
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) :
    Antitone (coxSurvival β Λ₀ z) := by
  sorry

/-- The Cox survival function takes values in `(0, 1]` for finite baseline hazard. -/
theorem coxSurvival_mem_Ioc
    -- USER-INPUT: locally finite baseline; Cox72 §2
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) (t : ℝ) :
    coxSurvival β Λ₀ z t ∈ Ioc (0 : ℝ) 1 := by
  sorry

/-- The **canonical Cox law**: the Stieltjes measure of `1 − coxSurvival` (`Cox72 §2`).
Packaged as a sorried Stieltjes construction with its spec lemma; the closure builds the
monotone/right-continuous structure from `antitone_coxSurvival` + continuity of `Λ₀`. -/
noncomputable def coxSF
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] : StieltjesFunction :=
  sorry

@[simp]
theorem coxSF_apply (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] (t : ℝ) :
    coxSF β Λ₀ z hfin t = 1 - coxSurvival β Λ₀ z t := by
  sorry

/-- The canonical Cox event-time law. -/
noncomputable def coxMeasure (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] : Measure ℝ :=
  (coxSF β Λ₀ z hfin).measure

/-- The Cox law is a (possibly defective) event-time law: mass on `[0, ∞)`, total at most
one; it is a probability law **iff** the total baseline hazard diverges (else the defect is
the cure fraction — documented, ABGK §II.1 defective case). -/
theorem isSubEventTimeLaw_coxMeasure
    -- USER-INPUT: baseline concentrated on the positive axis; Cox72 §2
    (hΛ0 : Λ₀ (Iic 0) = 0)
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] :
    IsSubEventTimeLaw (coxMeasure β Λ₀ z hfin) := by
  sorry

/-- Probability (no cure) under diverging total baseline hazard. -/
theorem isEventTimeLaw_coxMeasure
    -- USER-INPUT: baseline concentrated on the positive axis; Cox72 §2
    (hΛ0 : Λ₀ (Iic 0) = 0)
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀]
    -- USER-INPUT: infinite total baseline hazard (no cure mass); ABGK §II.1
    (htot : Tendsto (fun t => Λ₀ (Ioc 0 t)) atTop (𝓝 ⊤)) :
    IsEventTimeLaw (coxMeasure β Λ₀ z hfin) := by
  sorry

/-- **S5.2, the realization theorem** (`Cox72 §2`; ABGK §III.1.2): the constructed Cox law
has exactly the proportional-hazards structure — its cumulative-hazard measure is
`e^{⟪β,z⟫} • Λ₀` (restricted to the positive axis carrying the baseline). Designated hard
theorem of this batch (rides the S-B4 bricks; the single allowed carry). -/
theorem cumHazard_coxMeasure
    -- USER-INPUT: baseline concentrated on the positive axis; Cox72 §2
    (hΛ0 : Λ₀ (Iic 0) = 0)
    (hfin : ∀ t, Λ₀ (Ioc 0 t) ≠ ⊤) [NoAtoms Λ₀] :
    cumHazard (coxMeasure β Λ₀ z hfin) = ENNReal.ofReal (Real.exp ⟪β, z⟫_ℝ) • Λ₀ := by
  sorry

end StatLean.StatisticalModels.Survival
