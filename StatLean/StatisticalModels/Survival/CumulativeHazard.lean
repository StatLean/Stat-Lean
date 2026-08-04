import StatLean.StatisticalModels.Survival.Survival

/-!
# The cumulative-hazard measure — hygiene and atom calculus

The load-bearing facts about `cumHazard μ = μ.withDensity (t ↦ (μ [t,∞))⁻¹)`:

* **the hygiene lemma** `measure_survivalLeft_zero` — the set where `S(t−) = 0` is `μ`-null,
  so the ENNReal inverse in the hazard density is a.e. finite and the `0⁻¹ = ∞` junk never
  carries mass (proved FIRST; every later hazard argument in the slice cites it);
* the evaluation formula `cumHazard_apply`;
* the **atom formula** `ΔΛ(t) = μ{t} / S(t−)` and its unconditional bound `ΔΛ(t) ≤ 1`;
* local finiteness of `Λ` on `{S(t−) > 0}`;
* vanishing on the negative half-line for event-time laws.

**Reference.** ABGK §II.1 (verify §): `Λ(t) = ∫₀ᵗ dF/S(s−)`, `ΔΛ = ΔF/S(−) ≤ 1`, finiteness
of `Λ` before the endpoint of the support.

**Proof formalization notes.** The hygiene lemma: `{t | μ [t,∞) = 0}` is an up-set, hence an
interval `(a, ∞)` or `[a, ∞)`; its measure is the decreasing limit of `μ [tₙ, ∞) = 0` by
continuity of measure — 10–20 lines of order-topology care, no atomlessness. The atom formula
is `withDensity_apply` on a singleton; the `≤ 1` bound holds *unconditionally* — where
`S(t−) = 0` monotonicity forces `μ{t} = 0` and the ENNReal convention `0 · ∞ = 0` gives
`ΔΛ = 0` (consciously exploited, documented here once). Local finiteness bounds the density on
`(-∞, t]` by antitonicity.

**Bibliographic comments.** Aalen 1978 (*Ann. Statist.* **6**, 701–726) for the cumulative
hazard as compensator; the `ΔΛ ≤ 1` normalization is the discrete-hazard bound underlying the
product-limit construction (Kaplan–Meier 1958).
-/

open MeasureTheory Set

namespace StatLean.StatisticalModels.Survival

variable {μ : Measure ℝ}

/-- The hazard-density integrand is measurable (antitone set function of the endpoint). -/
theorem measurable_survivalLeft_inv (μ : Measure ℝ) :
    Measurable fun t => (μ (Ici t))⁻¹ := by
  sorry

/-- **Hygiene lemma** (LEAN-ONLY; no book analogue): the region where the left-limit survival
vanishes is null for the law itself. Consequently the hazard density is `μ`-a.e. finite and
every downstream `0⁻¹ = ∞` corner is measure-theoretically invisible. -/
theorem measure_survivalLeft_zero (μ : Measure ℝ) :
    μ {t | μ (Ici t) = 0} = 0 := by
  sorry

/-- A.e. finiteness of the hazard density (the usable form of the hygiene lemma). -/
theorem ae_inv_survivalLeft_lt_top (μ : Measure ℝ) :
    ∀ᵐ t ∂μ, (μ (Ici t))⁻¹ < ⊤ := by
  sorry

/-- Evaluation of the cumulative-hazard measure. -/
theorem cumHazard_apply (μ : Measure ℝ) {A : Set ℝ}
    -- LEAN-ONLY: the evaluation set is measurable (withDensity_apply)
    (hA : MeasurableSet A) :
    cumHazard μ A = ∫⁻ t in A, (μ (Ici t))⁻¹ ∂μ := by
  sorry

/-- **Atom formula** `ΔΛ(t) = μ{t}/S(t−)` where the denominator does not vanish
(ABGK §II.1: `ΔΛ = ΔF/S(−)`). -/
theorem cumHazardJump_eq (μ : Measure ℝ) {t : ℝ}
    -- USER-INPUT: the left-limit survival is positive at t (inside the support);
    -- ABGK §II.1
    (ht : μ (Ici t) ≠ 0) :
    cumHazardJump μ t = μ {t} / μ (Ici t) := by
  sorry

/-- The hazard jump is at most one, **unconditionally**: where `S(t−) = 0`, monotonicity
forces `μ{t} = 0` and `0 · ∞ = 0` (the one place the ENNReal convention is load-bearing). -/
theorem cumHazardJump_le_one (μ : Measure ℝ) (t : ℝ) :
    cumHazardJump μ t ≤ 1 := by
  sorry

/-- Local finiteness: up to any time with positive left-limit survival, the cumulative hazard
is bounded by `S(t−)⁻¹` (ABGK §II.1: `Λ` finite before the support endpoint). -/
theorem cumHazard_Iic_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    cumHazard μ (Iic t) ≤ (μ (Ici t))⁻¹ := by
  sorry

/-- Event-time laws accumulate no hazard on the negative half-line. -/
theorem cumHazard_Iio_zero
    -- USER-INPUT: event-time law; ABGK §II.1
    (h : IsEventTimeLaw μ) :
    cumHazard μ (Iio 0) = 0 := by
  sorry

end StatLean.StatisticalModels.Survival
