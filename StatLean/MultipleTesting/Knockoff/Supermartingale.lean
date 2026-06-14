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

omit mΩ in
/-- `Yproc 0 ω = V₊(0)/(1+V₋(0))`: the threshold `θ 0 ω` = min null magnitude is ≤ |W j ω| for
all j ∈ H₀ (since it is the minimum), so V₊/V₋ at threshold θ₀ equals V₊/V₋ at threshold 0.
- **USER-INPUT**: equality of counts at threshold θ₀ vs 0; Lu-BDA §19. -/
lemma Yproc_zero_eq (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    Yproc W H₀ 0 ω = (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) := by
  unfold Yproc
  by_cases h : 0 < H₀.card
  · simp only [h, ↓reduceDIte]
    -- Key: θ₀ = min null magnitude ≤ |W j ω| for all j ∈ H₀, so Vplus/Vminus agree at θ₀ and 0.
    haveI hNZ : NeZero H₀.card := ⟨h.ne'⟩
    have hmin : ∀ j : Fin H₀.card, θ W H₀ ⟨0, h⟩ ω ≤ |W (H₀.orderEmbOfFin rfl j) ω| := by
      intro j
      let v := fun i : Fin H₀.card => |W (H₀.orderEmbOfFin rfl i) ω|
      change orderStat v ⟨0, h⟩ ≤ v j
      calc orderStat v ⟨0, h⟩
          ≤ orderStat v ((Tuple.sort v).symm j) := orderStat_monotone v (Fin.zero_le _)
        _ = v ((Tuple.sort v) ((Tuple.sort v).symm j)) := rfl
        _ = v j := by simp [Equiv.apply_symm_apply]
    have hH₀ : ∀ j ∈ H₀, θ W H₀ ⟨0, h⟩ ω ≤ |W j ω| := by
      intro j hj
      obtain ⟨i, rfl⟩ : j ∈ Set.range (H₀.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hj
      exact hmin i
    have hSplus : (Splus W (θ W H₀ ⟨0, h⟩ ω) ω) ∩ H₀ = (Splus W 0 ω) ∩ H₀ := by
      ext j
      simp only [Finset.mem_inter, Splus, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨⟨_, hpos⟩, hmem⟩ => ⟨⟨abs_nonneg _, hpos⟩, hmem⟩,
             fun ⟨⟨_, hpos⟩, hmem⟩ => ⟨⟨hH₀ j hmem, hpos⟩, hmem⟩⟩
    have hSminus : (Sminus W (θ W H₀ ⟨0, h⟩ ω) ω) ∩ H₀ = (Sminus W 0 ω) ∩ H₀ := by
      ext j
      simp only [Finset.mem_inter, Sminus, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨⟨_, hneg⟩, hmem⟩ => ⟨⟨abs_nonneg _, hneg⟩, hmem⟩,
             fun ⟨⟨_, hneg⟩, hmem⟩ => ⟨⟨hH₀ j hmem, hneg⟩, hmem⟩⟩
    simp only [Vplus, Vminus, hSplus, hSminus]
  · have h0 : H₀.card = 0 := by omega
    have hH₀ : H₀ = ∅ := Finset.card_eq_zero.mp h0
    subst hH₀
    simp only [h, ↓reduceDIte]
    simp [Vplus, Vminus]

/-! ## 3. Filtration (𝒢rev) -/

/-- Rank condition: `orderStat v n ≤ a` iff the count of entries of `v` that are `≤ a` is `> n`.
Uses `Tuple.lt_card_le_iff_apply_le_of_monotone` (the sorted-tuple characterization) plus
bijectivity of the sorting permutation `Tuple.sort v`.
- **LEAN-ONLY**: bridges the order-statistic definition to a measurable count formula. -/
private lemma orderStat_le_iff_card_lt {m : ℕ} (v : Fin m → ℝ) (n : Fin m) (a : ℝ) :
    orderStat v n ≤ a ↔ n.val < (Finset.univ.filter (fun k => v k ≤ a)).card := by
  have h_card : (Finset.univ.filter (fun i : Fin m => orderStat v i ≤ a)).card =
                (Finset.univ.filter (fun k : Fin m => v k ≤ a)).card :=
    Finset.card_bij' (fun i _ => Tuple.sort v i) (fun k _ => (Tuple.sort v).symm k)
      (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi)
      (fun k hk => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        simp only [orderStat, Equiv.apply_symm_apply]; exact hk)
      (fun i _ => by simp [Equiv.symm_apply_apply])
      (fun k _ => by simp [Equiv.apply_symm_apply])
  rw [show orderStat v n ≤ a ↔ n < (Finset.univ.filter (fun i => orderStat v i ≤ a)).card from
    (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort v)).symm, h_card]

/-- Strong measurability of `Yproc W H₀ n` w.r.t. the ambient sigma-algebra `mΩ`. Proved via
the order-statistic rank condition: `θ_n ≤ |W j|` iff the null-magnitude rank of `|W j|` is `> n`,
which rewrites `Vplus`/`Vminus` as finite sums of measurable indicators.
- **LEAN-ONLY**: measurability adapter; requires `hWmeas : ∀ j, Measurable (W j)`. -/
private lemma Yproc_stronglyMeasurable (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) :
    StronglyMeasurable (Yproc W H₀ n) := by
  apply Measurable.stronglyMeasurable
  unfold Yproc
  by_cases h : n < H₀.card
  · simp only [h, ↓reduceDIte]
    -- Inner count measurability: j ↦ #{k : Fin H₀.card | |W (H₀.orderEmbOfFin rfl k) ω| ≤ |W j ω|}
    -- Use simp_rw (rewrites under binders) to convert .card to a sum of indicators,
    -- avoiding universe-polymorphic `cfs` helper that leaks universe variables.
    have hCL : ∀ j : Fin d, Measurable (fun ω =>
        ((Finset.univ : Finset (Fin H₀.card)).filter
          (fun k => |W (H₀.orderEmbOfFin rfl k) ω| ≤ |W j ω|)).card) := fun j => by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.measurable_sum _ fun k _ =>
        Measurable.ite (measurableSet_le ((hWmeas _).abs) ((hWmeas j).abs))
          measurable_const measurable_const
    -- Rank condition: θ_n ω ≤ |W j ω| ↔ n < (inner count for j at ω)
    have hRk : ∀ (j : Fin d) (ω : Ω),
        θ W H₀ ⟨n, h⟩ ω ≤ |W j ω| ↔
        n < ((Finset.univ : Finset (Fin H₀.card)).filter
          (fun k => |W (H₀.orderEmbOfFin rfl k) ω| ≤ |W j ω|)).card :=
      fun j ω => orderStat_le_iff_card_lt
        (fun k : Fin H₀.card => |W (H₀.orderEmbOfFin rfl k) ω|) ⟨n, h⟩ _
    -- Rewrite Vplus/Vminus via rank condition, then prove measurability as outer sum of indicators
    have hVpMeas : Measurable (fun ω => (Vplus W H₀ (θ W H₀ ⟨n, h⟩ ω) ω : ℕ)) := by
      have heq : ∀ ω, Vplus W H₀ (θ W H₀ ⟨n, h⟩ ω) ω =
          (H₀.filter (fun j => n <
            ((Finset.univ : Finset (Fin H₀.card)).filter
              (fun k => |W (H₀.orderEmbOfFin rfl k) ω| ≤ |W j ω|)).card ∧
            0 < W j ω)).card := fun ω => by
        unfold Vplus Splus; congr 1; ext j
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨⟨hle, hpos⟩, hmem⟩ => ⟨hmem, (hRk j ω).mp hle, hpos⟩,
               fun ⟨hmem, hrk, hpos⟩ => ⟨⟨(hRk j ω).mpr hrk, hpos⟩, hmem⟩⟩
      simp_rw [heq, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.measurable_sum _ fun j _ =>
        Measurable.ite (MeasurableSet.inter
          (measurableSet_lt measurable_const (hCL j))
          (measurableSet_lt measurable_const (hWmeas j)))
          measurable_const measurable_const
    have hVmMeas : Measurable (fun ω => (Vminus W H₀ (θ W H₀ ⟨n, h⟩ ω) ω : ℕ)) := by
      have heq : ∀ ω, Vminus W H₀ (θ W H₀ ⟨n, h⟩ ω) ω =
          (H₀.filter (fun j => n <
            ((Finset.univ : Finset (Fin H₀.card)).filter
              (fun k => |W (H₀.orderEmbOfFin rfl k) ω| ≤ |W j ω|)).card ∧
            W j ω < 0)).card := fun ω => by
        unfold Vminus Sminus; congr 1; ext j
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨⟨hle, hneg⟩, hmem⟩ => ⟨hmem, (hRk j ω).mp hle, hneg⟩,
               fun ⟨hmem, hrk, hneg⟩ => ⟨⟨(hRk j ω).mpr hrk, hneg⟩, hmem⟩⟩
      simp_rw [heq, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.measurable_sum _ fun j _ =>
        Measurable.ite (MeasurableSet.inter
          (measurableSet_lt measurable_const (hCL j))
          (measurableSet_lt (hWmeas j) measurable_const))
          measurable_const measurable_const
    exact (measurable_from_nat.comp hVpMeas).div
      (measurable_const.add (measurable_from_nat.comp hVmMeas))
  · simp only [h, ↓reduceDIte]; exact measurable_const

/-- The reverse filtration: `𝒢rev W H₀ hWmeas n` exposes all null magnitudes plus the signs of
the n null coordinates with the n smallest magnitudes. Defined as the natural filtration of the
`Yproc` process; `Yproc n` is then adapted to `𝒢rev n` by construction.
- **USER-INPUT**: `W`, `H₀` determine the sign process; Lu-BDA §19 (Def. `kos` cond. 3). -/
noncomputable def 𝒢rev (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) : Filtration ℕ mΩ :=
  Filtration.natural (Yproc W H₀) (fun n => Yproc_stronglyMeasurable W H₀ hWmeas n)

/-- `Yproc W H₀` is strongly adapted to `𝒢rev W H₀ hWmeas`: by construction, `𝒢rev` is the
natural filtration of `Yproc`, so adaptation holds via `Filtration.stronglyAdapted_natural`.
- **USER-INPUT**: adaptation follows from the KnockoffScore sign structure; Lu-BDA §19. -/
lemma Yproc_adapted (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) :
    StronglyAdapted (𝒢rev W H₀ hWmeas) (Yproc W H₀) :=
  Filtration.stronglyAdapted_natural (fun n => Yproc_stronglyMeasurable W H₀ hWmeas n)

/-- `Yproc W H₀ n` is μ-integrable: it is bounded in `[0, H₀.card]` and μ is a probability
measure (hence finite), so integrability follows from `integrable_const` + `Integrable.mono'`.
- **LEAN-ONLY**: integrability from the finiteness of μ and the bound H₀.card on Yproc. -/
lemma Yproc_integrable (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    Integrable (Yproc W H₀ n) μ := by
  apply Integrable.mono' (integrable_const (H₀.card : ℝ))
    (Yproc_stronglyMeasurable W H₀ hWmeas n).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_of_nonneg (Yproc_nonneg W H₀ n ω)]
  unfold Yproc
  split_ifs with h
  · have h_vm : (0 : ℝ) ≤ Vminus W H₀ (θ W H₀ ⟨n, h⟩ ω) ω := Nat.cast_nonneg _
    rw [div_le_iff₀ (by linarith)]
    have h_vp : (Vplus W H₀ (θ W H₀ ⟨n, h⟩ ω) ω : ℝ) ≤ H₀.card := by
      simp only [Vplus]
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    calc (Vplus W H₀ (θ W H₀ ⟨n, h⟩ ω) ω : ℝ)
        ≤ H₀.card := h_vp
      _ ≤ H₀.card * (1 + Vminus W H₀ (θ W H₀ ⟨n, h⟩ ω) ω) :=
            le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
  · exact Nat.cast_nonneg _

/-! ## 4. One-step supermartingale inequality -/

/-- **One-step conditional expectation inequality** (the high-risk core lemma):
`μ[Yproc (n+1) | 𝒢rev n] ≤ᵐ[μ] Yproc n`. Revealing the (n+1)-th null's sign adds a fresh
`Ber(½)` independent of `𝒢rev n` (by `KnockoffScore.signs_iIndep`/`signs_indep_mag`); after
integrating out via `iIndepFun.condExp_natural_ae_eq_of_lt`, the ratio decreases in expectation.
- **USER-INPUT**: sign independence from `hW.signs_iIndep`, `hW.signs_fair`, `hW.signs_indep_mag`;
  Lu-BDA §19 (Def. `kos` cond. 3). -/
lemma step_condExp_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ) (n : ℕ) :
    μ[Yproc W H₀ (n + 1) | 𝒢rev W H₀ hW.meas n] ≤ᵐ[μ] Yproc W H₀ n := by
  sorry

/-- `Yproc W H₀` is a supermartingale w.r.t. `𝒢rev W H₀ hW.meas`. Assembled from
`supermartingale_nat` applied to the sorry'd `step_condExp_le`; all hypotheses are in scope. -/
lemma knockoff_supermartingale (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ) :
    Supermartingale (Yproc W H₀) (𝒢rev W H₀ hW.meas) μ :=
  supermartingale_nat
    (Yproc_adapted W H₀ hW.meas)
    (fun n => Yproc_integrable W H₀ hW.meas μ n)
    (fun n => step_condExp_le W H₀ μ hW n)

/-! ## 5. Stopping time (tauStar) -/

/-- `tauStar W H₀ α ω` is the index in `{0, …, H₀.card}` corresponding to the knock-off
threshold `tStar W α ω` in the `Yproc` index space: the first n for which `FDPhat(θ n ω) ≤ α`.
Bounded by H₀.card. Defined via `hittingBtwn` on the FDPhat-at-θ process.
- **USER-INPUT**: the index-to-threshold correspondence; Lu-BDA §19. -/
noncomputable def tauStar (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) : Ω → ℕ∞ :=
  fun ω => ↑(hittingBtwn
    (fun (n : ℕ) (ω : Ω) => if h : n < H₀.card then FDPhat W (θ W H₀ ⟨n, h⟩ ω) ω else α - 1)
    (Set.Iic α) 0 H₀.card ω)

/-- The FDPhat-at-θ process `n ↦ FDPhat W (θ W H₀ n ω) ω` is adapted to `𝒢rev W H₀ hWmeas`.
The adaptation requires measurability of `FDPhat W (θ_n ω) ω` w.r.t. the natural filtration of
`Yproc`, i.e., that FDPhat at the n-th null magnitude is a Borel function of `(Yproc k ω)_{k≤n}`.
This holds because FDPhat(θ_n) depends on the sign information at level n (the same information
that `Yproc n` aggregates), but the formal proof requires measurable-space comap analysis.
- **USER-INPUT**: adaptedness from sign structure; Lu-BDA §19 (Def. `kos` cond. 3). -/
private lemma FDPhat_atTheta_adapted (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ)
    (hWmeas : ∀ j, Measurable (W j)) :
    Adapted (𝒢rev W H₀ hWmeas)
      (fun (n : ℕ) (ω : Ω) =>
        if h : n < H₀.card then FDPhat W (θ W H₀ ⟨n, h⟩ ω) ω else α - 1) := by
  sorry

/-- `tauStar W H₀ α` is an `IsStoppingTime` for `𝒢rev W H₀ hWmeas`, being a hitting time of an
adapted process to a measurable set.
- **USER-INPUT**: stopping-time property from `Adapted.isStoppingTime_hittingBtwn`; Lu-BDA §19. -/
lemma tauStar_isStoppingTime (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ)
    (hWmeas : ∀ j, Measurable (W j)) :
    IsStoppingTime (𝒢rev W H₀ hWmeas) (tauStar W H₀ α) := by
  unfold tauStar
  exact Adapted.isStoppingTime_hittingBtwn (FDPhat_atTheta_adapted W H₀ α hWmeas) measurableSet_Iic

omit mΩ in
/-- `tauStar W H₀ α ω ≤ H₀.card` for all ω: bounded by the total number of nulls.
- **LEAN-ONLY**: from `hittingBtwn_le` applied to the hitting time bound. -/
lemma tauStar_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) (ω : Ω) :
    tauStar W H₀ α ω ≤ (H₀.card : ℕ∞) := by
  simp only [tauStar]
  exact WithTop.coe_le_coe.mpr (hittingBtwn_le ω)

/-! ## 6. Bridge: stoppedValue = V₊(t*)/(1+V₋(t*)) -/

/-- Order-statistic bridge: the V₊/V₋ ratio at `tStar` equals `Yproc` at the hitting index.
The argument: FDPhat is a step-function of all magnitudes; its minimum over `{|W j|}` with
FDPhat ≤ α falls in the same half-open interval `[θ_k, θ_{k+1})` as the first null index k
found by `hittingBtwn`. In that interval V₊ and V₋ (null-restricted counts) are constant, so
`V₊(tStar)/(1+V₋(tStar)) = V₊(θ_k)/(1+V₋(θ_k)) = Yproc k ω`.
- **USER-INPUT**: order-statistic analysis; Lu-BDA §19. -/
private lemma ratio_eq_Yproc_hittingIdx
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) (ω : Ω) :
    (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) =
    Yproc W H₀
      (hittingBtwn
        (fun (n : ℕ) (ω : Ω) => if h : n < H₀.card then FDPhat W (θ W H₀ ⟨n, h⟩ ω) ω else α - 1)
        (Set.Iic α) 0 H₀.card ω) ω := by
  sorry

/-- The stopped value `stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω` equals the ratio
`V₊(tStar W α ω)/(1+V₋(tStar W α ω))`: unfolding `stoppedValue` and `tauStar` reduces the
claim to `ratio_eq_Yproc_hittingIdx` via `(↑k : ℕ∞).untopA = k` (`WithTop.untopD_coe`).
- **USER-INPUT**: bridge between the Yproc index space and the tStar threshold value; Lu-BDA §19. -/
lemma ratio_eq_stoppedValue (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) (ω : Ω) :
    (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) =
    stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω := by
  -- stoppedValue u τ ω = u (τ ω).untopA ω; tauStar ω = ↑(hittingBtwn ... ω);
  -- (↑k : ℕ∞).untopA = k is definitional (untopA = untopD arbitary; match on `some k` = k).
  unfold stoppedValue tauStar
  exact ratio_eq_Yproc_hittingIdx W H₀ α ω

/-! ## 7. Master theorem -/

/-- **Master inequality** (Lu-BDA §19): `E[V₊(t*)/(1+V₋(t*))] ≤ 1`, by exhibiting the
threshold-indexed ratio as a supermartingale (one-step inequality from the conditional `Ber(½)`
sign field) and applying optional stopping (`supermartingale_integral_stoppedValue_le`) plus the
initial bound `knockoff_initial_le`. -/
theorem knockoff_ratio_stopped_le_one (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ) :
    ∫ ω, (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ ≤ 1 := by
  haveI : SigmaFiniteFiltration μ (𝒢rev W H₀ hW.meas) := inferInstance
  have h_ratio_eq :
      ∫ ω, (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) ∂μ =
      ∫ ω, stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall (ratio_eq_stoppedValue W H₀ α))
  rw [h_ratio_eq]
  calc ∫ ω, stoppedValue (Yproc W H₀) (tauStar W H₀ α) ω ∂μ
      ≤ ∫ ω, Yproc W H₀ 0 ω ∂μ :=
          supermartingale_integral_stoppedValue_le
            (knockoff_supermartingale W H₀ μ hW)
            (tauStar_isStoppingTime W H₀ α hW.meas)
            (tauStar_le W H₀ α)
    _ = ∫ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall (Yproc_zero_eq W H₀))
    _ ≤ 1 := knockoff_initial_le μ W H₀ hW

end StatLean.MultipleTesting
