import StatLean.MultipleTesting.Knockoff.Procedure
import StatLean.MultipleTesting.Knockoff.Defs
import StatLean.MultipleTesting.Knockoff.Initial
import StatLean.MultipleTesting.ForMathlib.OptionalStopping
import StatLean.MultipleTesting.ForMathlib.OrderStatistics
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Knock-off master inequality (Lu-BDA §19) — the supermartingale core

`knockoff_ratio_stopped_le_one`: `E[V₊(t*)/(1+V₋(t*))] ≤ 1`. The heart of the knock-off proof.

Strategy (maximizing Mathlib reuse — this file is where the martingale construction lives, so the
process/filtration definitions co-evolve with their proofs):

* Reveal the coordinates in **increasing `|W|`** order over **all `d` magnitudes**; the forward
  process `Yproc n = V₊/(1+V₋)` indexed by the order statistics of `{|W j| : j : Fin d}` is a
  forward supermartingale, with `Yproc 0` = the all-nulls ratio (`knockoff_initial_le`,
  via `Yproc_zero_eq`) and `Yproc d = 0`. Indexing over **all `d`** magnitudes (Candès STATS-300C
  Lecture 11 §11.5) is what aligns the hitting time `tauStar` over `θ` with the procedure's
  threshold `tStar = min{ t ∈ {|W_j|} : FDPhat ≤ α }`, which ranges over *all* magnitudes.
* `𝒢rev = Filtration.natural` of `(magnitudes, revealed non-null signs, null split-counts)`; the
  null counts `V₊, V₋` still count only `H₀`, so at a step crossing a *non-null* coordinate the
  counts are unchanged (trivial step) and at a *null* step the removed null's sign is uniform among
  the remaining (`KnockoffScore.signs_*`), so the ratio decreases in expectation.
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

/-- The n-th smallest magnitude among ALL `d` coordinates `{|W j ω| : j : Fin d}`, via `orderStat`
on the absolute-value tuple (0-indexed: `θ W ⟨0,h⟩ ω` = minimum magnitude over all coordinates).
- **USER-INPUT**: `W` determines all `d` magnitudes; Lu-BDA §19 (Candès STATS-300C §11.5). -/
noncomputable def θ (W : Fin d → Ω → ℝ) (n : Fin d) (ω : Ω) : ℝ :=
  orderStat (fun (i : Fin d) => |W i ω|) n

/-- `Yproc n ω = V₊(θ_n ω)/(1 + V₋(θ_n ω))`, the V₊/V₋ ratio at the n-th magnitude threshold over
all `d` coordinates. For n = 0, `θ_0 ω` is the smallest magnitude (over **all** coordinates), so
every coordinate — in particular every null — is above threshold and `Yproc 0 = V₊(0)/(1+V₋(0))`
(the initial ratio). For n ≥ d, `Yproc n = 0`.
- **USER-INPUT**: `W`, `H₀` supply the knock-off scores and null set; Lu-BDA §19.
- **LEAN-ONLY**: the ℕ-indexed extension with `Yproc n = 0` for n ≥ d pads the process for
  `supermartingale_nat`; the supermartingale property holds on the non-trivial range. -/
noncomputable def Yproc (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ) (ω : Ω) : ℝ :=
  if h : n < d
  then (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) / (1 + (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ))
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
    · have : (0 : ℝ) ≤ (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) := by exact_mod_cast Nat.zero_le _
      linarith
  · exact le_refl _

omit mΩ in
/-- `Yproc 0 ω = V₊(0)/(1+V₋(0))`: the threshold `θ 0 ω` = the global minimum magnitude is ≤ |W j ω|
for **all** j (since it is the minimum over all `d` coordinates), so in particular ≤ |W j ω| for
every null j ∈ H₀, and hence V₊/V₋ at threshold θ₀ equals V₊/V₋ at threshold 0.
- **USER-INPUT**: equality of counts at threshold θ₀ vs 0; Lu-BDA §19. -/
lemma Yproc_zero_eq (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    Yproc W H₀ 0 ω = (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) := by
  unfold Yproc
  by_cases h : 0 < d
  · simp only [h, ↓reduceDIte]
    -- Key: θ₀ = global min magnitude ≤ |W j ω| for all j, so Vplus/Vminus agree at θ₀ and 0.
    haveI hNZ : NeZero d := ⟨h.ne'⟩
    have hmin : ∀ j : Fin d, θ W ⟨0, h⟩ ω ≤ |W j ω| := by
      intro j
      let v := fun i : Fin d => |W i ω|
      change orderStat v ⟨0, h⟩ ≤ v j
      calc orderStat v ⟨0, h⟩
          ≤ orderStat v ((Tuple.sort v).symm j) := orderStat_monotone v (Fin.zero_le _)
        _ = v ((Tuple.sort v) ((Tuple.sort v).symm j)) := rfl
        _ = v j := by simp [Equiv.apply_symm_apply]
    have hH₀ : ∀ j ∈ H₀, θ W ⟨0, h⟩ ω ≤ |W j ω| := fun j _ => hmin j
    have hSplus : (Splus W (θ W ⟨0, h⟩ ω) ω) ∩ H₀ = (Splus W 0 ω) ∩ H₀ := by
      ext j
      simp only [Finset.mem_inter, Splus, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨⟨_, hpos⟩, hmem⟩ => ⟨⟨abs_nonneg _, hpos⟩, hmem⟩,
             fun ⟨⟨_, hpos⟩, hmem⟩ => ⟨⟨hH₀ j hmem, hpos⟩, hmem⟩⟩
    have hSminus : (Sminus W (θ W ⟨0, h⟩ ω) ω) ∩ H₀ = (Sminus W 0 ω) ∩ H₀ := by
      ext j
      simp only [Finset.mem_inter, Sminus, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨⟨_, hneg⟩, hmem⟩ => ⟨⟨abs_nonneg _, hneg⟩, hmem⟩,
             fun ⟨⟨_, hneg⟩, hmem⟩ => ⟨⟨hH₀ j hmem, hneg⟩, hmem⟩⟩
    simp only [Vplus, Vminus, hSplus, hSminus]
  · -- d = 0: `Fin d` is empty, so H₀ = ∅ and both sides vanish.
    have hcard : H₀.card ≤ d := by
      calc H₀.card ≤ Finset.univ.card := Finset.card_le_univ H₀
        _ = d := by rw [Finset.card_univ, Fintype.card_fin]
    have hH₀ : H₀ = ∅ := Finset.card_eq_zero.mp (by omega)
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

/-- Inner count `j ↦ #{ k : Fin d | |W k| ≤ |W j| }` is measurable. -/
private lemma measurable_innerCount (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (j : Fin d) :
    Measurable (fun ω => ((Finset.univ : Finset (Fin d)).filter
      (fun k => |W k ω| ≤ |W j ω|)).card) := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.measurable_sum _ fun k _ =>
    Measurable.ite (measurableSet_le ((hWmeas _).abs) ((hWmeas j).abs))
      measurable_const measurable_const

/-- `V₊(θ_n)` (the null-positive count at the n-th magnitude threshold) is measurable. -/
private lemma measurable_Vplus_theta (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) (h : n < d) :
    Measurable (fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ)) := by
  have hRk : ∀ (j : Fin d) (ω : Ω), θ W ⟨n, h⟩ ω ≤ |W j ω| ↔
      n < ((Finset.univ : Finset (Fin d)).filter
        (fun k => |W k ω| ≤ |W j ω|)).card :=
    fun j ω => orderStat_le_iff_card_lt _ ⟨n, h⟩ _
  have heq : ∀ ω, (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ) =
      ∑ j ∈ H₀, if (n < ((Finset.univ : Finset (Fin d)).filter
            (fun k => |W k ω| ≤ |W j ω|)).card ∧ 0 < W j ω)
          then (1 : ℕ) else 0 := fun ω => by
    have hstep : Vplus W H₀ (θ W ⟨n, h⟩ ω) ω =
        (H₀.filter (fun j => n < ((Finset.univ : Finset (Fin d)).filter
            (fun k => |W k ω| ≤ |W j ω|)).card ∧ 0 < W j ω)).card := by
      unfold Vplus Splus; congr 1; ext j
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨⟨hle, hpos⟩, hmem⟩ => ⟨hmem, (hRk j ω).mp hle, hpos⟩,
             fun ⟨hmem, hrk, hpos⟩ => ⟨⟨(hRk j ω).mpr hrk, hpos⟩, hmem⟩⟩
    rw [hstep]; nth_rw 1 [Finset.card_eq_sum_ones]; rw [Finset.sum_filter]
  simp_rw [heq]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (MeasurableSet.inter
      (measurableSet_lt measurable_const (measurable_innerCount W H₀ hWmeas j))
      (measurableSet_lt measurable_const (hWmeas j)))
      measurable_const measurable_const

/-- `V₋(θ_n)` (the null-negative count at the n-th magnitude threshold) is measurable. -/
private lemma measurable_Vminus_theta (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) (h : n < d) :
    Measurable (fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ)) := by
  have hRk : ∀ (j : Fin d) (ω : Ω), θ W ⟨n, h⟩ ω ≤ |W j ω| ↔
      n < ((Finset.univ : Finset (Fin d)).filter
        (fun k => |W k ω| ≤ |W j ω|)).card :=
    fun j ω => orderStat_le_iff_card_lt _ ⟨n, h⟩ _
  have heq : ∀ ω, (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ) =
      ∑ j ∈ H₀, if (n < ((Finset.univ : Finset (Fin d)).filter
            (fun k => |W k ω| ≤ |W j ω|)).card ∧ W j ω < 0)
          then (1 : ℕ) else 0 := fun ω => by
    have hstep : Vminus W H₀ (θ W ⟨n, h⟩ ω) ω =
        (H₀.filter (fun j => n < ((Finset.univ : Finset (Fin d)).filter
            (fun k => |W k ω| ≤ |W j ω|)).card ∧ W j ω < 0)).card := by
      unfold Vminus Sminus; congr 1; ext j
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨⟨hle, hneg⟩, hmem⟩ => ⟨hmem, (hRk j ω).mp hle, hneg⟩,
             fun ⟨hmem, hrk, hneg⟩ => ⟨⟨(hRk j ω).mpr hrk, hneg⟩, hmem⟩⟩
    rw [hstep]; nth_rw 1 [Finset.card_eq_sum_ones]; rw [Finset.sum_filter]
  simp_rw [heq]
  exact Finset.measurable_sum _ fun j _ =>
    Measurable.ite (MeasurableSet.inter
      (measurableSet_lt measurable_const (measurable_innerCount W H₀ hWmeas j))
      (measurableSet_lt (hWmeas j) measurable_const))
      measurable_const measurable_const

/-- Strong measurability of `Yproc W H₀ n` w.r.t. the ambient sigma-algebra `mΩ`. Proved via
the order-statistic rank condition: `θ_n ≤ |W j|` iff the magnitude rank of `|W j|` among all `d`
coordinates is `> n`, which rewrites `Vplus`/`Vminus` as finite sums of measurable indicators.
- **LEAN-ONLY**: measurability adapter; requires `hWmeas : ∀ j, Measurable (W j)`. -/
private lemma Yproc_stronglyMeasurable (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) :
    StronglyMeasurable (Yproc W H₀ n) := by
  apply Measurable.stronglyMeasurable
  unfold Yproc
  by_cases h : n < d
  · simp only [h, ↓reduceDIte]
    -- Inner count measurability: j ↦ #{k : Fin d | |W k ω| ≤ |W j ω|}
    -- Use simp_rw (rewrites under binders) to convert .card to a sum of indicators,
    -- avoiding universe-polymorphic `cfs` helper that leaks universe variables.
    have hCL : ∀ j : Fin d, Measurable (fun ω =>
        ((Finset.univ : Finset (Fin d)).filter
          (fun k => |W k ω| ≤ |W j ω|)).card) := fun j => by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.measurable_sum _ fun k _ =>
        Measurable.ite (measurableSet_le ((hWmeas _).abs) ((hWmeas j).abs))
          measurable_const measurable_const
    -- Rank condition: θ_n ω ≤ |W j ω| ↔ n < (inner count for j at ω)
    have hRk : ∀ (j : Fin d) (ω : Ω),
        θ W ⟨n, h⟩ ω ≤ |W j ω| ↔
        n < ((Finset.univ : Finset (Fin d)).filter
          (fun k => |W k ω| ≤ |W j ω|)).card :=
      fun j ω => orderStat_le_iff_card_lt
        (fun k : Fin d => |W k ω|) ⟨n, h⟩ _
    -- Rewrite Vplus/Vminus via rank condition, then prove measurability as outer sum of indicators.
    -- heq converts Vplus/Vminus directly to sum form while preserving the inner count as .card,
    -- so that hCL j (which has .card type) unifies correctly in the final Measurable.ite call.
    -- simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter] would also rewrite inner .card to sum
    -- form, breaking the type match with hCL j — so we bake the conversion into heq instead.
    have hVpMeas : Measurable (fun ω => (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ)) := by
      have heq : ∀ ω, (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ) =
          ∑ j ∈ H₀, if (n < ((Finset.univ : Finset (Fin d)).filter
                (fun k => |W k ω| ≤ |W j ω|)).card ∧
              0 < W j ω) then (1 : ℕ) else 0 := fun ω => by
        have hstep : Vplus W H₀ (θ W ⟨n, h⟩ ω) ω =
            (H₀.filter (fun j => n <
              ((Finset.univ : Finset (Fin d)).filter
                (fun k => |W k ω| ≤ |W j ω|)).card ∧
              0 < W j ω)).card := by
          unfold Vplus Splus; congr 1; ext j
          simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun ⟨⟨hle, hpos⟩, hmem⟩ => ⟨hmem, (hRk j ω).mp hle, hpos⟩,
                 fun ⟨hmem, hrk, hpos⟩ => ⟨⟨(hRk j ω).mpr hrk, hpos⟩, hmem⟩⟩
        -- Convert outer .card to sum; nth_rw 1 avoids rewriting the inner .card in the predicate
        rw [hstep]; nth_rw 1 [Finset.card_eq_sum_ones]; rw [Finset.sum_filter]
      simp_rw [heq]
      exact Finset.measurable_sum _ fun j _ =>
        Measurable.ite (MeasurableSet.inter
          (measurableSet_lt measurable_const (hCL j))
          (measurableSet_lt measurable_const (hWmeas j)))
          measurable_const measurable_const
    have hVmMeas : Measurable (fun ω => (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ)) := by
      have heq : ∀ ω, (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℕ) =
          ∑ j ∈ H₀, if (n < ((Finset.univ : Finset (Fin d)).filter
                (fun k => |W k ω| ≤ |W j ω|)).card ∧
              W j ω < 0) then (1 : ℕ) else 0 := fun ω => by
        have hstep : Vminus W H₀ (θ W ⟨n, h⟩ ω) ω =
            (H₀.filter (fun j => n <
              ((Finset.univ : Finset (Fin d)).filter
                (fun k => |W k ω| ≤ |W j ω|)).card ∧
              W j ω < 0)).card := by
          unfold Vminus Sminus; congr 1; ext j
          simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun ⟨⟨hle, hneg⟩, hmem⟩ => ⟨hmem, (hRk j ω).mp hle, hneg⟩,
                 fun ⟨hmem, hrk, hneg⟩ => ⟨⟨(hRk j ω).mpr hrk, hneg⟩, hmem⟩⟩
        rw [hstep]; nth_rw 1 [Finset.card_eq_sum_ones]; rw [Finset.sum_filter]
      simp_rw [heq]
      exact Finset.measurable_sum _ fun j _ =>
        Measurable.ite (MeasurableSet.inter
          (measurableSet_lt measurable_const (hCL j))
          (measurableSet_lt (hWmeas j) measurable_const))
          measurable_const measurable_const
    exact (measurable_from_nat.comp hVpMeas).div
      (measurable_const.add (measurable_from_nat.comp hVmMeas))
  · simp only [h, ↓reduceDIte]; exact measurable_const

/-- The data revealed by step `n` of the knock-off filter (the **count filtration** generators,
Lu-BDA §19): all magnitudes `|W|`, the non-null signs (`0` padded on nulls), and the null
split-counts `(V₊(θ_n), V₋(θ_n))`. Its natural filtration `𝒢rev` exposes `Yproc n` and `FDPhat(θ_n)`
(both functions of these) while keeping the individual null-sign *assignment* above `θ_n` hidden —
the exchangeability that makes `Yproc` a supermartingale. See `notes/.../construction_audit.md`.
- **USER-INPUT**: `W`, `H₀` determine the revealed data; Lu-BDA §19 (Def. `kos` cond. 3). -/
noncomputable def cproc (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (n : ℕ) (ω : Ω) :
    (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ :=
  (fun j => |W j ω|,
   fun j => if j ∈ H₀ then 0 else sgnReal W j ω,
   (if h : n < d then (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) else 0),
   (if h : n < d then (Vminus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) else 0))

private lemma measurable_cproc (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) (n : ℕ) : Measurable (cproc W H₀ n) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_))
  · exact measurable_pi_iff.mpr fun j => (hWmeas j).abs
  · refine measurable_pi_iff.mpr fun j => ?_
    by_cases hj : j ∈ H₀
    · simp only [hj, if_true]; exact measurable_const
    · simp only [hj, if_false]
      exact Measurable.ite (measurableSet_le measurable_const (hWmeas j))
        measurable_const measurable_const
  · by_cases h : n < d
    · simp only [h, ↓reduceDIte]
      exact measurable_from_top.comp (measurable_Vplus_theta W H₀ hWmeas n h)
    · simp only [h, ↓reduceDIte]; exact measurable_const
  · by_cases h : n < d
    · simp only [h, ↓reduceDIte]
      exact measurable_from_top.comp (measurable_Vminus_theta W H₀ hWmeas n h)
    · simp only [h, ↓reduceDIte]; exact measurable_const

/-- The count filtration: the natural filtration of `cproc`. -/
noncomputable def 𝒢rev (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) : Filtration ℕ mΩ :=
  Filtration.natural (cproc W H₀) (fun n => (measurable_cproc W H₀ hWmeas n).stronglyMeasurable)

/-- `Yproc W H₀` is strongly adapted to the count filtration `𝒢rev`: `Yproc n = V₊(θ_n)/(1+V₋(θ_n))`
is a Borel function of `cproc n` (its count components), which is `𝒢rev n`-measurable. -/
lemma Yproc_adapted (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (hWmeas : ∀ j, Measurable (W j)) :
    StronglyAdapted (𝒢rev W H₀ hWmeas) (Yproc W H₀) := by
  intro n
  have hcproc : StronglyMeasurable[𝒢rev W H₀ hWmeas n] (cproc W H₀ n) :=
    Filtration.stronglyAdapted_natural
      (fun n => (measurable_cproc W H₀ hWmeas n).stronglyMeasurable) n
  have hg : Measurable (fun x : (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ =>
      if n < d then x.2.2.1 / (1 + x.2.2.2) else 0) := by
    by_cases h : n < d
    · simp only [h, if_true]
      exact (measurable_fst.comp (measurable_snd.comp measurable_snd)).div
        (measurable_const.add (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    · simp only [h, if_false]; exact measurable_const
  have heq : Yproc W H₀ n = (fun x : (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ =>
      if n < d then x.2.2.1 / (1 + x.2.2.2) else 0) ∘ (cproc W H₀ n) := by
    funext ω
    simp only [Function.comp_apply, Yproc, cproc]
    by_cases h : n < d <;> simp [h]
  rw [heq]
  exact (hg.comp hcproc.measurable).stronglyMeasurable

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
  · have h_vm : (0 : ℝ) ≤ Vminus W H₀ (θ W ⟨n, h⟩ ω) ω := Nat.cast_nonneg _
    rw [div_le_iff₀ (by linarith)]
    have h_vp : (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ) ≤ H₀.card := by
      simp only [Vplus]
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    calc (Vplus W H₀ (θ W ⟨n, h⟩ ω) ω : ℝ)
        ≤ H₀.card := h_vp
      _ ≤ H₀.card * (1 + Vminus W H₀ (θ W ⟨n, h⟩ ω) ω) :=
            le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith)
  · exact Nat.cast_nonneg _

/-! ## 4. One-step supermartingale inequality -/

/-- **One-step conditional expectation inequality** (the high-risk core lemma):
`μ[Yproc (n+1) | 𝒢rev n] ≤ᵐ[μ] Yproc n`. The step is a supermartingale by the **count filtration**
/ exchangeability, not a "fresh independent coin":

* At a step `n → n+1` whose crossed coordinate `θ_n → θ_{n+1}` is a **non-null** coordinate, the
  null counts `V₊, V₋` (which count only `H₀`) are unchanged, so `Yproc (n+1) = Yproc n` — a trivial
  (deterministic) martingale step.
* At a **null** step, the removed null's sign is uniform among the remaining nulls (exchangeability
  of the i.i.d. fair null signs given the outer data, `count_condExp`): with `A = V₊(θ_n)`,
  `B = V₋(θ_n)` and `k = A + B`, the crossed null is positive with probability `A/k` (then
  `V₊ → A−1`, `V₋ → B`) and negative with probability `B/k` (then `V₊ → A`, `V₋ → B−1`), so
  `E[Yproc (n+1) | 𝒢rev n] = (A/k)·(A−1)/(1+B) + (B/k)·A/B = A/(1+B) = Yproc n`.

- **USER-INPUT**: sign exchangeability from `hW.signs_iIndep`/`signs_fair`/`signs_indep_outer`;
  Lu-BDA §19. -/
lemma step_condExp_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    -- USER-INPUT: a.s. distinct magnitudes (continuous knock-off statistics, no |Wᵢ| ties); Lu-BDA §19.
    -- Needed so each threshold step removes exactly one coordinate (the single-null exchangeable step).
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) (n : ℕ) :
    μ[Yproc W H₀ (n + 1) | 𝒢rev W H₀ hW.meas n] ≤ᵐ[μ] Yproc W H₀ n := by
  sorry

/-- `Yproc W H₀` is a supermartingale w.r.t. `𝒢rev W H₀ hW.meas`. Assembled from
`supermartingale_nat` applied to the sorry'd `step_condExp_le`; all hypotheses are in scope. -/
lemma knockoff_supermartingale (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d))
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
    Supermartingale (Yproc W H₀) (𝒢rev W H₀ hW.meas) μ :=
  supermartingale_nat
    (Yproc_adapted W H₀ hW.meas)
    (fun n => Yproc_integrable W H₀ hW.meas μ n)
    (fun n => step_condExp_le W H₀ μ hW hmag n)

/-! ## 5. Stopping time (tauStar) -/

/-- `tauStar W H₀ α ω` is the index in `{0, …, d}` corresponding to the knock-off threshold
`tStar W α ω` in the `Yproc` index space: the first n for which `FDPhat(θ n ω) ≤ α`, where `θ`
ranges over the order statistics of **all `d`** magnitudes. Bounded by `d`. Defined via
`hittingBtwn` on the FDPhat-at-θ process. Re-indexing over all `d` magnitudes (Candès §11.5) is
what makes `tauStar` align with `tStar = min{ t ∈ {|W_j|} : FDPhat ≤ α }`.
- **USER-INPUT**: the index-to-threshold correspondence; Lu-BDA §19. -/
noncomputable def tauStar (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) : Ω → ℕ∞ :=
  fun ω => ↑(hittingBtwn
    (fun (n : ℕ) (ω : Ω) => if h : n < d then FDPhat W (θ W ⟨n, h⟩ ω) ω else α - 1)
    (Set.Iic α) 0 d ω)

/-- `#S⁺(t)` splits into the null count `V₊(t)` plus the non-null positives above `t`. -/
private lemma Splus_card_decomp (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (t : ℝ) (ω : Ω) :
    (Splus W t ω).card =
      Vplus W H₀ t ω + (H₀ᶜ.filter (fun j => t ≤ |W j ω| ∧ 0 < W j ω)).card := by
  have key := Finset.card_inter_add_card_sdiff (Splus W t ω) H₀
  have hsd : Splus W t ω \ H₀ = H₀ᶜ.filter (fun j => t ≤ |W j ω| ∧ 0 < W j ω) := by
    ext j
    simp only [Finset.mem_sdiff, Splus, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl]
    tauto
  rw [hsd] at key
  simp only [Vplus]; omega

/-- `#S⁻(t)` splits into the null count `V₋(t)` plus the non-null negatives above `t`. -/
private lemma Sminus_card_decomp (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (t : ℝ) (ω : Ω) :
    (Sminus W t ω).card =
      Vminus W H₀ t ω + (H₀ᶜ.filter (fun j => t ≤ |W j ω| ∧ W j ω < 0)).card := by
  have key := Finset.card_inter_add_card_sdiff (Sminus W t ω) H₀
  have hsd : Sminus W t ω \ H₀ = H₀ᶜ.filter (fun j => t ≤ |W j ω| ∧ W j ω < 0) := by
    ext j
    simp only [Finset.mem_sdiff, Sminus, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl]
    tauto
  rw [hsd] at key
  simp only [Vminus]; omega

/-- The FDPhat-at-θ process is adapted to the count filtration `𝒢rev`: `FDPhat(θ_n)` is a Borel
function of `cproc n`. `#S±(θ_n) = V±(θ_n) + (non-null count above θ_n)`, where `V±(θ_n)` are the
count components of `cproc n` and the non-null counts are functions of the magnitudes + non-null
signs (also in `cproc n`); the threshold `θ_n ≤ |W_j|` is the rank condition `n < #{k | …}` over all
`d` coordinates.
- **USER-INPUT**: adaptedness from the count-filtration structure; Lu-BDA §19. -/
private lemma FDPhat_atTheta_adapted (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ)
    (hWmeas : ∀ j, Measurable (W j)) :
    Adapted (𝒢rev W H₀ hWmeas)
      (fun (n : ℕ) (ω : Ω) =>
        if h : n < d then FDPhat W (θ W ⟨n, h⟩ ω) ω else α - 1) := by
  intro n
  -- The rank predicate, as a function of a magnitude vector `m`, over all `d` coordinates.
  let rank : (Fin d → ℝ) → Fin d → ℕ := fun m j =>
    ((Finset.univ : Finset (Fin d)).filter
      (fun k => m k ≤ m j)).card
  -- The Borel function `G` of `cproc n` computing the process value.
  let G : ((Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ) → ℝ := fun x =>
    if n < d then
      (x.2.2.2 + ((H₀ᶜ.filter (fun j => n < rank x.1 j ∧ x.2.1 j = -1)).card : ℝ) + 1)
        / max (x.2.2.1 + ((H₀ᶜ.filter
            (fun j => n < rank x.1 j ∧ x.2.1 j = 1 ∧ x.1 j ≠ 0)).card : ℝ)) 1
    else α - 1
  have hc : StronglyMeasurable[𝒢rev W H₀ hWmeas n] (cproc W H₀ n) :=
    Filtration.stronglyAdapted_natural
      (fun n => (measurable_cproc W H₀ hWmeas n).stronglyMeasurable) n
  -- `G` is measurable.
  have hrank_meas : ∀ j, Measurable (fun x : (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ => rank x.1 j) :=
    fun j => by
      simp only [rank]
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.measurable_sum _ fun k _ =>
        Measurable.ite (measurableSet_le
          ((measurable_pi_apply _).comp measurable_fst)
          ((measurable_pi_apply j).comp measurable_fst)) measurable_const measurable_const
  have hcnt_meas : ∀ (P : Fin d → (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ → Prop)
      [∀ j x, Decidable (P j x)],
      (∀ j, MeasurableSet {x | P j x}) →
      Measurable (fun x : (Fin d → ℝ) × (Fin d → ℝ) × ℝ × ℝ =>
        ((H₀ᶜ.filter (fun j => P j x)).card : ℝ)) := by
    intro P _ hP
    apply measurable_from_top.comp
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.measurable_sum _ fun j _ =>
      Measurable.ite (hP j) measurable_const measurable_const
  have hGmeas : Measurable G := by
    simp only [G]
    by_cases h : n < d
    · simp only [h, if_true]
      apply Measurable.div
      · apply Measurable.add
        · apply Measurable.add (measurable_snd.comp (measurable_snd.comp measurable_snd))
          exact hcnt_meas _ fun j => (measurableSet_lt measurable_const (hrank_meas j)).inter
            (measurableSet_eq_fun ((measurable_pi_apply j).comp
              (measurable_fst.comp measurable_snd)) measurable_const)
        · exact measurable_const
      · refine Measurable.max (Measurable.add
          (measurable_fst.comp (measurable_snd.comp measurable_snd)) ?_) measurable_const
        exact hcnt_meas _ fun j => (measurableSet_lt measurable_const (hrank_meas j)).inter
          ((measurableSet_eq_fun ((measurable_pi_apply j).comp
            (measurable_fst.comp measurable_snd)) measurable_const).inter
            (measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_fst)
              measurable_const).compl)
    · simp only [h, if_false]; exact measurable_const
  -- The process value equals `G (cproc n)`.
  have hval : (fun ω => if h : n < d then FDPhat W (θ W ⟨n, h⟩ ω) ω else α - 1)
      = G ∘ cproc W H₀ n := by
    funext ω
    simp only [Function.comp_apply, G, cproc]
    by_cases h : n < d
    · simp only [h, ↓reduceDIte, if_true]
      have hrankθ : ∀ j, θ W ⟨n, h⟩ ω ≤ |W j ω| ↔ n < rank (fun j => |W j ω|) j := by
        intro j; exact orderStat_le_iff_card_lt _ ⟨n, h⟩ _
      have hpos : ∀ j ∈ H₀ᶜ, (θ W ⟨n, h⟩ ω ≤ |W j ω| ∧ 0 < W j ω) ↔
          (n < rank (fun j => |W j ω|) j ∧
            (if j ∈ H₀ then (0:ℝ) else sgnReal W j ω) = 1 ∧ |W j ω| ≠ 0) := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [hrankθ j, if_neg hj]
        refine and_congr_right (fun _ => ?_)
        constructor
        · intro hp; exact ⟨if_pos hp.le, by positivity⟩
        · rintro ⟨hs, hne⟩
          have h0 : 0 ≤ W j ω := by by_contra hc; rw [sgnReal, if_neg hc] at hs; norm_num at hs
          rcases lt_or_eq_of_le h0 with hlt | heq
          · exact hlt
          · exact absurd (by rw [← heq]; simp) hne
      have hneg : ∀ j ∈ H₀ᶜ, (θ W ⟨n, h⟩ ω ≤ |W j ω| ∧ W j ω < 0) ↔
          (n < rank (fun j => |W j ω|) j ∧ (if j ∈ H₀ then (0:ℝ) else sgnReal W j ω) = -1) := by
        intro j hj
        rw [Finset.mem_compl] at hj
        rw [hrankθ j, if_neg hj, sgnReal]
        refine and_congr_right (fun _ => ?_)
        constructor
        · intro hlt; rw [if_neg (not_le.mpr hlt)]
        · intro hs; by_contra hc; rw [if_pos (not_lt.mp hc)] at hs; norm_num at hs
      rw [FDPhat, Splus_card_decomp W H₀ _ ω, Sminus_card_decomp W H₀ _ ω,
        Finset.filter_congr hpos, Finset.filter_congr hneg]
      push_cast
      ring
    · simp only [h, ↓reduceDIte, if_false]
  have hsm := hGmeas.comp hc.measurable
  rw [← hval] at hsm
  exact hsm

/-- `tauStar W H₀ α` is an `IsStoppingTime` for `𝒢rev W H₀ hWmeas`, being a hitting time of an
adapted process to a measurable set.
- **USER-INPUT**: stopping-time property from `Adapted.isStoppingTime_hittingBtwn`; Lu-BDA §19. -/
lemma tauStar_isStoppingTime (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ)
    (hWmeas : ∀ j, Measurable (W j)) :
    IsStoppingTime (𝒢rev W H₀ hWmeas) (tauStar W H₀ α) := by
  unfold tauStar
  exact Adapted.isStoppingTime_hittingBtwn (FDPhat_atTheta_adapted W H₀ α hWmeas) measurableSet_Iic

omit mΩ in
/-- `tauStar W H₀ α ω ≤ d` for all ω: bounded by the total number of coordinates.
- **LEAN-ONLY**: from `hittingBtwn_le` applied to the hitting time bound. -/
lemma tauStar_le (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) (ω : Ω) :
    tauStar W H₀ α ω ≤ (d : ℕ∞) := by
  simp only [tauStar]
  exact WithTop.coe_le_coe.mpr (hittingBtwn_le ω)

/-! ## 6. Bridge: stoppedValue = V₊(t*)/(1+V₋(t*)) -/

omit mΩ in
/-- Every magnitude `|W j ω|` is realised as some order statistic `θ W m ω`: take `m` to be the
inverse sorting permutation applied to `j`.
- **LEAN-ONLY**: surjectivity of the order-statistic indexing onto the magnitude multiset. -/
private lemma exists_orderStat_eq_abs (W : Fin d → Ω → ℝ) (ω : Ω) (j : Fin d) :
    ∃ m : Fin d, θ W m ω = |W j ω| := by
  refine ⟨(Tuple.sort (fun i => |W i ω|)).symm j, ?_⟩
  change orderStat (fun i => |W i ω|) ((Tuple.sort (fun i => |W i ω|)).symm j) = |W j ω|
  simp only [orderStat, Equiv.apply_symm_apply]

omit mΩ in
/-- `θ W ⟨n, h⟩ ω` is one of the magnitudes `{|W j ω|}` (it is `|W·ω|` at the sorted index).
- **LEAN-ONLY**: the order statistic is a value of the magnitude tuple. -/
private lemma theta_mem_image (W : Fin d → Ω → ℝ) (ω : Ω) (n : ℕ) (h : n < d) :
    θ W ⟨n, h⟩ ω ∈ (Finset.univ : Finset (Fin d)).image (fun j => |W j ω|) := by
  rw [Finset.mem_image]
  exact ⟨Tuple.sort (fun i => |W i ω|) ⟨n, h⟩, Finset.mem_univ _, rfl⟩

/-- Order-statistic bridge: the V₊/V₋ ratio at `tStar` equals `Yproc` at the hitting index.
The argument: FDPhat is a step-function of all magnitudes; its minimizer over `{|W j|}` with
FDPhat ≤ α (the threshold `tStar`) is itself one of the order statistics `θ_k` (now ranging over
**all `d`** magnitudes), and is exactly the magnitude at the first hitting index `k` found by
`hittingBtwn`. There `V₊(tStar) = V₊(θ_k)` and `V₋(tStar) = V₋(θ_k)`, so
`V₊(tStar)/(1+V₋(tStar)) = V₊(θ_k)/(1+V₋(θ_k)) = Yproc k ω`.
- **USER-INPUT**: order-statistic analysis; Lu-BDA §19 (Candès STATS-300C §11.5). -/
private lemma ratio_eq_Yproc_hittingIdx
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (α : ℝ) (ω : Ω) :
    (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) =
    Yproc W H₀
      (hittingBtwn
        (fun (n : ℕ) (ω : Ω) => if h : n < d then FDPhat W (θ W ⟨n, h⟩ ω) ω else α - 1)
        (Set.Iic α) 0 d ω) ω := by
  -- The FDPhat-at-θ process `P` and its hitting index `k` over the magnitude order statistics.
  set P : ℕ → Ω → ℝ :=
    (fun (n : ℕ) (ω : Ω) => if h : n < d then FDPhat W (θ W ⟨n, h⟩ ω) ω else α - 1) with hP_def
  set k : ℕ := hittingBtwn P (Set.Iic α) 0 d ω with hk_def
  -- The candidate magnitudes `tStar` minimises over.
  obtain ⟨cands, hcands⟩ :
      ∃ c : Finset ℝ, c = ((Finset.univ : Finset (Fin d)).image (fun j => |W j ω|)).filter
        (fun t => FDPhat W t ω ≤ α) := ⟨_, rfl⟩
  have mem_cands : ∀ x, x ∈ cands ↔
      x ∈ (Finset.univ : Finset (Fin d)).image (fun j => |W j ω|) ∧ FDPhat W x ω ≤ α := fun x => by
    rw [hcands]; exact Finset.mem_filter
  have htStar_eq : tStar W α ω =
      if h : cands.Nonempty then cands.min' h else 1 + ∑ j, |W j ω| := by
    rw [hcands]; rfl
  -- `P` evaluated on the two branches of its dependent `if`.
  have hPval : ∀ (n : ℕ) (h : n < d), P n ω = FDPhat W (θ W ⟨n, h⟩ ω) ω := fun n h => by
    simp only [hP_def]; exact dif_pos h
  have hPd : P d ω = α - 1 := by simp only [hP_def]; exact dif_neg (lt_irrefl d)
  -- There is always a hit (at `n = d`, where `P d ω = α - 1 ≤ α`); hence `k ≤ d` and `P k ω ≤ α`.
  have hExists : ∃ j ∈ Set.Icc (0 : ℕ) d, P j ω ∈ Set.Iic α := by
    refine ⟨d, Set.mem_Icc.mpr ⟨Nat.zero_le d, le_refl d⟩, ?_⟩
    rw [Set.mem_Iic, hPd]; linarith
  have hk_le : k ≤ d := by rw [hk_def]; exact hittingBtwn_le ω
  have hPk_le : P k ω ≤ α := by
    have h := hittingBtwn_mem_set hExists
    rw [← hk_def] at h
    exact Set.mem_Iic.mp h
  by_cases hne : cands.Nonempty
  · -- Non-degenerate: `tStar = min cands`; show the hitting index `k < d` and `θ_k = tStar`.
    obtain ⟨j₁, -, hj₁⟩ :
        ∃ j ∈ (Finset.univ : Finset (Fin d)), |W j ω| = cands.min' hne :=
      Finset.mem_image.mp ((mem_cands _).mp (Finset.min'_mem cands hne)).1
    obtain ⟨m₁, hθm₁⟩ := exists_orderStat_eq_abs W ω j₁
    have hθm₁' : θ W m₁ ω = cands.min' hne := hθm₁.trans hj₁
    -- `FDPhat(θ_{m₁}) = FDPhat(tStar) ≤ α`, so `m₁` is in the hitting set ⇒ `k ≤ m₁ < d`.
    have hPm₁mem : P m₁.val ω ∈ Set.Iic α := by
      rw [Set.mem_Iic, hPval m₁.val m₁.isLt,
        show θ W ⟨m₁.val, m₁.isLt⟩ ω = cands.min' hne from hθm₁']
      exact ((mem_cands _).mp (Finset.min'_mem cands hne)).2
    have hk_m₁ : k ≤ m₁.val := by
      rw [hk_def]
      exact hittingBtwn_le_of_mem (Nat.zero_le m₁.val) (le_of_lt m₁.isLt) hPm₁mem
    have hk_lt : k < d := lt_of_le_of_lt hk_m₁ m₁.isLt
    -- `tStar ≤ θ_k`: `θ_k` is a candidate (magnitude with `FDPhat ≤ α`), and `tStar = min cands`.
    have hFDPk : FDPhat W (θ W ⟨k, hk_lt⟩ ω) ω ≤ α := by rw [← hPval k hk_lt]; exact hPk_le
    have hθk_cands : θ W ⟨k, hk_lt⟩ ω ∈ cands :=
      (mem_cands _).mpr ⟨theta_mem_image W ω k hk_lt, hFDPk⟩
    have h1 : cands.min' hne ≤ θ W ⟨k, hk_lt⟩ ω := Finset.min'_le cands _ hθk_cands
    -- `θ_k ≤ tStar = θ_{m₁}` by monotonicity of the order statistics (`k ≤ m₁`).
    have hfin_le : (⟨k, hk_lt⟩ : Fin d) ≤ m₁ := by rw [Fin.le_iff_val_le_val]; exact hk_m₁
    have h2 : θ W ⟨k, hk_lt⟩ ω ≤ cands.min' hne := by
      rw [← hθm₁']; exact orderStat_monotone (fun i => |W i ω|) hfin_le
    have key : cands.min' hne = θ W ⟨k, hk_lt⟩ ω := le_antisymm h1 h2
    rw [htStar_eq, dif_pos hne, key]
    have hRHS : Yproc W H₀ k ω =
        (Vplus W H₀ (θ W ⟨k, hk_lt⟩ ω) ω : ℝ) / (1 + (Vminus W H₀ (θ W ⟨k, hk_lt⟩ ω) ω : ℝ)) := by
      unfold Yproc; rw [dif_pos hk_lt]
    rw [hRHS]
  · -- Degenerate: no candidate, `tStar = 1 + ∑|W|` exceeds every magnitude, `k = d`, both sides 0.
    have hk_eq_d : k = d := by
      rcases hk_le.lt_or_eq with hlt | heq
      · exact absurd ⟨θ W ⟨k, hlt⟩ ω,
          (mem_cands _).mpr ⟨theta_mem_image W ω k hlt,
            by rw [← hPval k hlt]; exact hPk_le⟩⟩ hne
      · exact heq
    -- `tStar = 1 + ∑|W|` strictly exceeds every magnitude `|W j ω|`.
    have htStar_gt : ∀ j : Fin d, |W j ω| < 1 + ∑ i, |W i ω| := fun j => by
      have hle : |W j ω| ≤ ∑ i, |W i ω| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (W i ω)) (Finset.mem_univ j)
      linarith
    have hSplus_empty : Splus W (1 + ∑ j, |W j ω|) ω = ∅ := by
      unfold Splus
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      rw [Finset.mem_filter] at hj
      exact absurd hj.2.1 (not_le.mpr (htStar_gt j))
    have hSminus_empty : Sminus W (1 + ∑ j, |W j ω|) ω = ∅ := by
      unfold Sminus
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      rw [Finset.mem_filter] at hj
      exact absurd hj.2.1 (not_le.mpr (htStar_gt j))
    have hVplus0 : Vplus W H₀ (1 + ∑ j, |W j ω|) ω = 0 := by
      unfold Vplus; rw [hSplus_empty, Finset.empty_inter, Finset.card_empty]
    have hVminus0 : Vminus W H₀ (1 + ∑ j, |W j ω|) ω = 0 := by
      unfold Vminus; rw [hSminus_empty, Finset.empty_inter, Finset.card_empty]
    have hYd : Yproc W H₀ d ω = 0 := by simp [Yproc]
    rw [htStar_eq, dif_neg hne, hk_eq_d, hYd, hVplus0, hVminus0]
    norm_num

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
threshold-indexed ratio as a supermartingale (one-step inequality from the exchangeable null-sign
field) and applying optional stopping (`supermartingale_integral_stoppedValue_le`) plus the
initial bound `knockoff_initial_le`. -/
theorem knockoff_ratio_stopped_le_one (μ : Measure Ω) [IsProbabilityMeasure μ] (α : ℝ)
    (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (hW : KnockoffScore W H₀ μ)
    (hmag : ∀ᵐ ω ∂μ, ∀ i j : Fin d, i ≠ j → |W i ω| ≠ |W j ω|) :
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
            (knockoff_supermartingale W H₀ μ hW hmag)
            (tauStar_isStoppingTime W H₀ α hW.meas)
            (tauStar_le W H₀ α)
    _ = ∫ ω, (Vplus W H₀ 0 ω : ℝ) / (1 + (Vminus W H₀ 0 ω : ℝ)) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall (Yproc_zero_eq W H₀))
    _ ≤ 1 := knockoff_initial_le μ W H₀ hW

end StatLean.MultipleTesting
