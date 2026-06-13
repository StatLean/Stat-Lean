import StatLean.MultipleTesting.Knockoff.Procedure
import StatLean.MultipleTesting.Knockoff.Defs
import StatLean.MultipleTesting.Knockoff.Initial
import StatLean.MultipleTesting.ForMathlib.OptionalStopping
import StatLean.MultipleTesting.ForMathlib.OrderStatistics

/-!
# Knock-off master inequality (Lu-BDA §19) — the supermartingale core

`knockoff_ratio_stopped_le_one`: `E[V₊(t*)/(1+V₋(t*))] ≤ 1`. The heart of the knock-off proof.

Strategy (maximizing Mathlib reuse — this file is where the martingale construction lives, so the
process/filtration definitions co-evolve with their proofs):

* Reveal the null coordinates in **increasing `|W|`** order; the forward process
  `Yproc n = V₊/(1+V₋)` over the `N₀−n` largest-magnitude nulls is a forward supermartingale,
  with `Yproc 0` = the all-nulls ratio (`knockoff_initial_le`) and `Yproc N₀ = 0`.
* `𝒢rev = Filtration.natural` of `(magnitudes, revealed signs)`; the next sign is independent of
  the past (`KnockoffScore.signs_*`), so `μ[next sign | 𝒢rev n] = ½`.
* `supermartingale_nat` reduces the supermartingale to the one-step inequality `step_condExp_le`
  (the single high-risk lemma); `tauStar` is a bounded `IsStoppingTime`; the proven
  `supermartingale_integral_stoppedValue_le` gives `E[Y_{t*}] ≤ E[Y₀] ≤ 1`.

The construction (`Yproc`, `𝒢rev`, `tauStar`) and the one-step lemma `step_condExp_le` are authored
here by the prover session, alongside this theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-! ## 1. Process construction -/

/-- The n-th smallest magnitude among the null coordinates `{|W j ω| : j ∈ H₀}`, via
`orderStat` on the `H₀`-indexed absolute-value tuple. Uses `Finset.orderEmbOfFin` to enumerate
`H₀`'s elements as `Fin H₀.card → Fin d` (0-indexed: `θ ⟨0,h⟩ ω` = minimum null magnitude).
- **USER-INPUT**: `W`, `H₀` determine the null magnitudes; Lu-BDA §19. -/
noncomputable def θ (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (n : Fin H₀.card) (ω : Ω) : ℝ :=
  orderStat (fun (i : Fin H₀.card) => |W (H₀.orderEmbOfFin rfl i) ω|) n

/-- `Yproc n ω = V₊(θ_n ω)/(1 + V₋(θ_n ω))`, the V₊/V₋ ratio at the n-th null-magnitude
threshold. For n = 0, `θ_0 ω` is the smallest null magnitude, so all nulls are above threshold
and `Yproc 0 = V₊(0)/(1+V₋(0))` (the initial ratio). For n ≥ H₀.card, `Yproc n = 0`.
- **USER-INPUT**: `W`, `H₀` supply the knock-off scores and null set; Lu-BDA §19.
- **LEAN-ONLY**: the ℕ-indexed extension with `Yproc n = 0` for n ≥ H₀.card pads the process for
  `supermartingale_nat`; the supermartingale property holds on the non-trivial range. -/
noncomputable def Yproc (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ) (ω : Ω) : ℝ :=
  if h : n < H₀.card
  then (Vplus W H₀ (θ W H₀ ⟨n, h⟩ ω) ω : ℝ) / (1 + (Vminus W H₀ (θ W H₀ ⟨n, h⟩ ω) ω : ℝ))
  else 0

/-! ## 2. Elementary bounds -/

omit mΩ in
/-- `Yproc n ω ≥ 0`: V₊ ≥ 0 and denominator 1 + V₋ ≥ 1. -/
lemma Yproc_nonneg (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ) (ω : Ω) :
    0 ≤ Yproc W H₀ n ω := by
  unfold Yproc
  split_ifs with h
  · apply div_nonneg
    · exact_mod_cast Nat.zero_le _
    · have : (0 : ℝ) ≤ (Vminus W H₀ (θ W H₀ ⟨n, h⟩ ω) ω : ℝ) := by exact_mod_cast Nat.zero_le _
      linarith
  · exact le_refl _

/-- `Yproc 0 ω = V₊(0)/(1+V₋(0))`: the threshold `θ 0 ω` = min null magnitude is ≤ |W j ω| for
all j ∈ H₀ (since it is the minimum), so V₊/V₋ at threshold θ₀ equals V₊/V₋ at threshold 0.
- **USER-INPUT**: equality of counts at threshold θ₀ vs 0; Lu-BDA §19. -/
lemma Yproc_zero_eq (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    Yproc W H₀ 0 ω = (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) := by
  sorry

/-! ## 3. Filtration (𝒢rev) -/

/-- The reverse filtration: `𝒢rev W H₀ n` exposes all null magnitudes plus the signs of the n
null coordinates with the n smallest magnitudes. Constructed via `Filtration.natural` of the
sign-revelation process; the sign at index n+1 in `H₀.card`-many i.i.d. `Ber(½)` signs is
independent of `𝒢rev n` by `KnockoffScore.signs_iIndep`/`signs_indep_mag`.
- **USER-INPUT**: `W`, `H₀` determine the sign process; Lu-BDA §19 (Def. `kos` cond. 3). -/
noncomputable def 𝒢rev (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) : Filtration ℕ mΩ :=
  sorry

/-- `Yproc W H₀` is strongly adapted to `𝒢rev W H₀`: at step n, the ratio V₊(θ_n)/(1+V₋(θ_n))
is measurable given the n revealed signs and the (always-known) magnitudes.
- **USER-INPUT**: adaptation follows from the KnockoffScore sign structure; Lu-BDA §19. -/
lemma Yproc_adapted (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) :
    StronglyAdapted (𝒢rev W H₀) (Yproc W H₀) := by
  sorry

/-- `Yproc W H₀ n` is μ-integrable: it is bounded in `[0, H₀.card]` and μ is a probability
measure (hence finite), so integrability follows from `integrable_const` + `Integrable.mono'`.
- **LEAN-ONLY**: integrability from the finiteness of μ and the bound H₀.card on Yproc. -/
lemma Yproc_integrable (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    Integrable (Yproc W H₀ n) μ := by
  sorry

/-! ## 4. One-step supermartingale inequality -/

/-- **One-step conditional expectation inequality** (the high-risk core lemma):
`μ[Yproc (n+1) | 𝒢rev n] ≤ᵐ[μ] Yproc n`. Revealing the (n+1)-th null's sign adds a fresh
`Ber(½)` independent of `𝒢rev n` (by `KnockoffScore.signs_iIndep`/`signs_indep_mag`); after
integrating out via `iIndepFun.condExp_natural_ae_eq_of_lt`, the ratio decreases in expectation.
- **USER-INPUT**: sign independence from `hW.signs_iIndep`, `hW.signs_fair`, `hW.signs_indep_mag`;
  Lu-BDA §19 (Def. `kos` cond. 3). -/
lemma step_condExp_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ) (n : ℕ) :
    μ[Yproc W H₀ (n + 1) | 𝒢rev W H₀ n] ≤ᵐ[μ] Yproc W H₀ n := by
  sorry

/-- `Yproc W H₀` is a supermartingale w.r.t. `𝒢rev W H₀`. Assembled from `supermartingale_nat`
applied to the sorry'd `step_condExp_le`; all hypotheses of `supermartingale_nat` are in scope. -/
lemma knockoff_supermartingale (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ) :
    Supermartingale (Yproc W H₀) (𝒢rev W H₀) μ :=
  supermartingale_nat
    (Yproc_adapted W H₀)
    (fun n => Yproc_integrable W H₀ μ n)
    (fun n => step_condExp_le W H₀ μ hW n)

/-! ## 5. Stopping time (tauStar) -/

/-- `tauStar W H₀ α ω` is the index in `{0, …, H₀.card}` corresponding to the knock-off
threshold `tStar W α ω` in the `Yproc` index space: the first n for which the threshold `θ n ω`
satisfies `FDPhat(θ n ω) ≤ α`. Bounded by H₀.card. Defined via `hittingBtwn`.
- **USER-INPUT**: the index-to-threshold correspondence; Lu-BDA §19. -/
noncomputable def tauStar (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) : Ω → ℕ∞ :=
  sorry

/-- `tauStar W H₀ α` is an `IsStoppingTime` for `𝒢rev W H₀`, being a hitting time of an
adapted process to a measurable set.
- **USER-INPUT**: stopping-time property from `Adapted.isStoppingTime_hittingBtwn`; Lu-BDA §19. -/
lemma tauStar_isStoppingTime (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) :
    IsStoppingTime (𝒢rev W H₀) (tauStar W H₀ α) := by
  sorry

/-- `tauStar W H₀ α ω ≤ H₀.card` for all ω: bounded by the total number of nulls.
- **LEAN-ONLY**: from `hittingBtwn_le` applied to the hitting time bound. -/
lemma tauStar_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) (ω : Ω) :
    tauStar W H₀ α ω ≤ (H₀.card : ℕ∞) := by
  sorry

/-! ## 6. Bridge: stoppedValue = V₊(t*)/(1+V₋(t*)) -/

/-- The stopped value `stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω` equals the ratio
`V₊(tStar W α ω)/(1+V₋(tStar W α ω))`: the `hittingBtwn`-based stopping time lands on the
index whose `θ`-threshold matches `tStar W α ω`.
- **USER-INPUT**: bridge between the Yproc index space and the tStar threshold value; Lu-BDA §19. -/
lemma ratio_eq_stoppedValue (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) (ω : Ω) :
    (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) =
    stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω := by
  sorry

/-! ## 7. Master theorem -/

/-- **Master inequality** (Lu-BDA §19): `E[V₊(t*)/(1+V₋(t*))] ≤ 1`, by exhibiting the
threshold-indexed ratio as a supermartingale (one-step inequality from the conditional `Ber(½)`
sign field) and applying optional stopping (`supermartingale_integral_stoppedValue_le`) plus the
initial bound `knockoff_initial_le`. -/
theorem knockoff_ratio_stopped_le_one (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ) :
    ∫ ω, (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ ≤ 1 := by
  haveI : SigmaFiniteFiltration μ (𝒢rev W H₀) := IsFiniteMeasure.sigmaFiniteFiltration μ _
  have h_ratio_eq :
      ∫ ω, (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ =
      ∫ ω, stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall (ratio_eq_stoppedValue W H₀ α))
  rw [h_ratio_eq]
  calc ∫ ω, stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω ∂μ
      ≤ ∫ ω, Yproc W H₀ 0 ω ∂μ :=
          supermartingale_integral_stoppedValue_le
            (knockoff_supermartingale W H₀ μ hW)
            (tauStar_isStoppingTime W H₀ α)
            (tauStar_le W H₀ α)
    _ = ∫ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall (Yproc_zero_eq W H₀))
    _ ≤ 1 := knockoff_initial_le μ W H₀ hW

end StatLean.MultipleTesting
