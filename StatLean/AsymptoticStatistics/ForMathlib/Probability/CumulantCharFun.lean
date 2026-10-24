/-
Copyright (c) 2026 Benjamin O. Harrison, Gustavo Canavire Bacarreza, David Jacho-Chavez and
Fernando Rios-Avila.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Jacho-Chávez
-/
import Mathlib.Analysis.Complex.TaylorSeries
import StatLean.AsymptoticStatistics.ForMathlib.Probability.Cumulant
import StatLean.AsymptoticStatistics.ForMathlib.Probability.Marcinkiewicz

/-!
# Cumulants and the characteristic function

This file connects the set-partition cumulants of `Cumulant.lean` to the
characteristic function, proving Lemma 2 of Janson (1988) in the case where the cumulants
vanish from some order on, and composes it with Marcinkiewicz's theorem
(`Marcinkiewicz.lean`). The link is the moment–cumulant recursion
`α_{n+1} = ∑_{j ≤ n} C (n, j) κ_{j+1} α_{n-j}`.

## Main results

* `mixedCumulant_const_fun`: a mixed cumulant of copies of `X` is the univariate cumulant.
* `moment_recursion`: the moment–cumulant recursion.
* `charFun_eq_exp_charPoly`: Janson's Lemma 2 for eventually vanishing cumulants.
* `cumulant_eq_zero_of_three_le`, `eq_gaussianReal_of_cumulant_eq_zero`: Marcinkiewicz's
  theorem in cumulant form; such a law is `gaussianReal κ₁ κ₂`.
* `cumulant_gaussianReal`: the cumulants of a Gaussian.
* `mixedCumulant_update_add`, `mixedCumulant_update_smul`: multilinearity in one argument.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped Nat NNReal ENNReal

namespace StatLean.AsymptoticStatistics

namespace Cumulant

/-! ### The cardinality reduction and the moment–cumulant recursion -/

section Reduction

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A sum over the subsets of `s` containing a marked point `i₀`, grouped by cardinality. There
are `C (#s - 1, r)` such subsets with `r + 1` elements. -/
lemma sum_filter_mem_card {ι : Type*} [DecidableEq ι] {s : Finset ι} {i₀ : ι} (hi : i₀ ∈ s)
    (F : ℕ → ℝ) :
    ∑ D ∈ s.powerset.filter (fun D => i₀ ∈ D), F #D
      = ∑ r ∈ Finset.range #s, ((#s - 1).choose r : ℝ) * F (r + 1) := by
  classical
  have hn : i₀ ∉ s.erase i₀ := Finset.notMem_erase i₀ s
  have hbij : ∑ D ∈ s.powerset.filter (fun D => i₀ ∈ D), F #D
      = ∑ E ∈ (s.erase i₀).powerset, F (#E + 1) := by
    rw [Finset.sum_filter]
    conv_lhs => rw [← Finset.insert_erase hi]
    rw [Finset.sum_powerset_insert hn,
      Finset.sum_eq_zero fun E hE => ite_eq_right fun h => hn (Finset.mem_powerset.mp hE h),
      zero_add]
    refine Finset.sum_congr rfl fun E hE => ?_
    rw [ite_eq_left (Finset.mem_insert_self _ _),
      Finset.card_insert_of_notMem fun h => hn (Finset.mem_powerset.mp hE h)]
  rw [hbij, Finset.sum_powerset_apply_card (fun r => F (r + 1)),
    Finset.card_erase_of_mem hi]
  simp only [nsmul_eq_mul]
  have h1 : #s - 1 + 1 = #s := by
    have : 1 ≤ #s := Finset.card_pos.mpr ⟨i₀, hi⟩
    omega
  rw [h1]

/-- `partSum` of the cumulants of a constant family is the corresponding raw moment. -/
lemma partSum_mixedCumulant_const (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    {ι : Type*} [DecidableEq ι] (t : Finset ι) :
    partSum (mixedCumulant μ (fun _ : ι => X)) t = ∫ ω, X ω ^ #t ∂μ := by
  rw [show partSum (mixedCumulant μ (fun _ : ι => X)) t
        = ∑ π : Finpartition t, ∏ B ∈ π.parts, mixedCumulant μ (fun _ : ι => X) B from rfl,
    partSum_mixedCumulant μ (fun _ : ι => X) t, jointMoment_const_fun]

/-- The right-hand side of the block recursion once every proper block cumulant has been
replaced by the univariate cumulant of the corresponding order. It depends on `s` only through
`#s`. -/
noncomputable def constFormula (μ : Measure Ω) (X : Ω → ℝ) (n : ℕ) : ℝ :=
  (∫ ω, X ω ^ n ∂μ)
    - (∑ r ∈ Finset.range n,
        ((n - 1).choose r : ℝ) * (cumulant X (r + 1) μ * ∫ ω, X ω ^ (n - (r + 1)) ∂μ)
      - cumulant X n μ)

/-- **The block recursion for a constant family**, with the top block isolated. This is
`partSum_recursion` read through `partSum_mixedCumulant`, so that the joint moment of `#s`
copies of `X` is the cumulant of `s` plus the contributions of the proper blocks through `i₀`. -/
lemma moment_eq_mixedCumulant_add (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {i₀ : ι} (hi : i₀ ∈ s) :
    (∫ ω, X ω ^ #s ∂μ)
      = mixedCumulant μ (fun _ : ι => X) s
        + ∑ D ∈ (s.powerset.filter (fun D => i₀ ∈ D)).erase s,
            mixedCumulant μ (fun _ : ι => X) D * ∫ ω, X ω ^ (#s - #D) ∂μ := by
  classical
  have hsmem : s ∈ s.powerset.filter (fun D => i₀ ∈ D) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (subset_refl s), hi⟩
  have hrec := partSum_recursion (mixedCumulant μ (fun _ : ι => X)) hi
  rw [← Finset.add_sum_erase _ _ hsmem, Finset.sdiff_self] at hrec
  simp only [partSum_mixedCumulant_const μ X] at hrec
  rw [hrec, Finset.card_empty]
  simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun D hD => ?_
  rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset] at hD
  rw [Finset.card_sdiff_of_subset hD.2.1]

/-- With every proper block cumulant replaced by the univariate cumulant of its order, the
cumulant of `s` is `constFormula μ X #s`, which depends on `s` only through its cardinality. -/
lemma mixedCumulant_const_of_ih (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (hs : s.Nonempty)
    (hIH : ∀ D : Finset ι, D ⊆ s → D ≠ s → mixedCumulant μ (fun _ : ι => X) D
      = cumulant X #D μ) :
    mixedCumulant μ (fun _ : ι => X) s = constFormula μ X #s := by
  classical
  obtain ⟨i₀, hi⟩ := hs
  have hkey := moment_eq_mixedCumulant_add μ X hi
  have hsmem : s ∈ s.powerset.filter (fun D => i₀ ∈ D) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (subset_refl s), hi⟩
  set F : ℕ → ℝ := fun d => cumulant X d μ * ∫ ω, X ω ^ (#s - d) ∂μ with hF
  have hterm : ∀ D ∈ (s.powerset.filter (fun D => i₀ ∈ D)).erase s,
      mixedCumulant μ (fun _ : ι => X) D * (∫ ω, X ω ^ (#s - #D) ∂μ) = F #D := by
    intro D hD
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset] at hD
    rw [hIH D hD.2.1 hD.1]
  rw [Finset.sum_congr rfl hterm] at hkey
  have hsplit : ∑ D ∈ (s.powerset.filter (fun D => i₀ ∈ D)).erase s, F #D
      = (∑ D ∈ s.powerset.filter (fun D => i₀ ∈ D), F #D) - F #s := by
    rw [← Finset.add_sum_erase _ (fun D => F #D) hsmem]; ring
  rw [hsplit, sum_filter_mem_card hi F] at hkey
  have hFs : F #s = cumulant X #s μ := by
    rw [hF]
    simp only [Nat.sub_self]
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
  rw [hFs, hF] at hkey
  simp only [constFormula]
  linarith [hkey]

/-- A mixed cumulant of a constant family is the univariate cumulant of the corresponding
order. The index type is in `Type 0`. -/
theorem mixedCumulant_const_fun (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) :
    ∀ (n : ℕ) {ι : Type} [DecidableEq ι] (s : Finset ι), #s = n →
      mixedCumulant μ (fun _ : ι => X) s = cumulant X n μ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ s hs
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [Finset.card_eq_zero.mp hs, mixedCumulant_empty, cumulant_zero]
    · have hne : s.Nonempty := Finset.card_pos.mp (by omega)
      have h1 : mixedCumulant μ (fun _ : ι => X) s = constFormula μ X n := by
        rw [mixedCumulant_const_of_ih μ X hne ?_, hs]
        intro D hD hDs
        have hlt : #D < #s := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hD, hDs⟩)
        rw [hs] at hlt
        exact ih #D hlt D rfl
      have hu : #(univ : Finset (Fin n)) = n := by simp
      have hune : (univ : Finset (Fin n)).Nonempty := Finset.card_pos.mp (by omega)
      have h2 : mixedCumulant μ (fun _ : Fin n => X) univ = constFormula μ X n := by
        rw [mixedCumulant_const_of_ih μ X hune ?_, hu]
        intro D hD hDs
        have hlt : #D < #(univ : Finset (Fin n)) :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hD, hDs⟩)
        rw [hu] at hlt
        exact ih #D hlt D rfl
      rw [h1, cumulant, h2]

/-- **The moment–cumulant recursion.** `α_{n+1} = ∑_{j ≤ n} C (n, j) κ_{j+1} α_{n-j}`,
the identity `M' = P' M` between the moment and cumulant exponential generating functions.
It holds as an identity of Bochner integrals without integrability hypotheses (a non-integrable
moment is `0`), and is meaningful when the moments up to order `n + 1` are finite. -/
theorem moment_recursion (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (n : ℕ) :
    (∫ ω, X ω ^ (n + 1) ∂μ)
      = ∑ j ∈ Finset.range (n + 1),
          (n.choose j : ℝ) * cumulant X (j + 1) μ * ∫ ω, X ω ^ (n - j) ∂μ := by
  classical
  have hi : (0 : Fin (n + 1)) ∈ (univ : Finset (Fin (n + 1))) := Finset.mem_univ _
  have hu : #(univ : Finset (Fin (n + 1))) = n + 1 := by simp
  have hrec := partSum_recursion (mixedCumulant μ (fun _ : Fin (n + 1) => X)) hi
  simp only [partSum_mixedCumulant_const μ X] at hrec
  have hterm : ∀ D ∈ (univ : Finset (Fin (n + 1))).powerset.filter
      (fun D => (0 : Fin (n + 1)) ∈ D),
      mixedCumulant μ (fun _ : Fin (n + 1) => X) D
          * (∫ ω, X ω ^ #((univ : Finset (Fin (n + 1))) \ D) ∂μ)
        = (fun d => cumulant X d μ * ∫ ω, X ω ^ (n + 1 - d) ∂μ) #D := by
    intro D hD
    rw [Finset.mem_filter, Finset.mem_powerset] at hD
    rw [Finset.card_sdiff_of_subset hD.1, hu, mixedCumulant_const_fun μ X #D D rfl]
  rw [Finset.sum_congr rfl hterm,
    sum_filter_mem_card hi (fun d => cumulant X d μ * ∫ ω, X ω ^ (n + 1 - d) ∂μ), hu] at hrec
  rw [hrec]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hsub : n + 1 - (j + 1) = n - j := by omega
  rw [hsub]
  ring

end Reduction


/-! ### Growth of the moments when the cumulants vanish

If `κ_j = 0` for `j ≥ m`, the moments satisfy `|α_n| ≤ C (ε) ε ^ n n !` for every `ε > 0`.
-/

section Growth

/-- A sequence obeying the moment–cumulant recursion with at most `d` nonzero cumulants
satisfies `|m n| ≤ C ε ^ n n !` for every `ε > 0`. -/
lemma exists_bound_of_recursion {m k : ℕ → ℝ} {d : ℕ} {A : ℝ}
    (hd : 1 ≤ d) (hA : ∀ j, |k (j + 1)| ≤ A)
    (hk : ∀ j, d ≤ j → k (j + 1) = 0)
    (hrec : ∀ n, m (n + 1)
      = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * k (j + 1) * m (n - j))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, |m n| ≤ C * ε ^ n * (n ! : ℝ) := by
  classical
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA 0)
  have hεd : (0 : ℝ) < ε ^ d := pow_pos hε0 d
  -- the recursion, truncated to the `d` possibly nonzero cumulants
  have hstep : ∀ n, |m (n + 1)| ≤ ∑ j ∈ Finset.range d, (n.choose j : ℝ) * A * |m (n - j)| := by
    intro n
    rw [hrec n]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have h1 : ∑ j ∈ Finset.range (n + 1), |(n.choose j : ℝ) * k (j + 1) * m (n - j)|
        = ∑ j ∈ Finset.range (n + 1 + d), |(n.choose j : ℝ) * k (j + 1) * m (n - j)| := by
      refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
      intro x _ hx
      rw [Finset.mem_range] at hx
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    have h2 : ∑ j ∈ Finset.range d, |(n.choose j : ℝ) * k (j + 1) * m (n - j)|
        = ∑ j ∈ Finset.range (n + 1 + d), |(n.choose j : ℝ) * k (j + 1) * m (n - j)| := by
      refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
      intro x _ hx
      rw [Finset.mem_range] at hx
      rw [hk x (by omega)]
      simp
    rw [h1, ← h2]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_mul, Nat.abs_cast]
    have hchoose : (0 : ℝ) ≤ (n.choose j : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA j) hchoose) (abs_nonneg _)
  -- an index `N` past which the induction step closes
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (A * (d : ℝ) / ε ^ d)
  set N : ℕ := max d N₀ with hNdef
  have hNd : d ≤ N := le_max_left _ _
  have hNbig : A * (d : ℝ) ≤ ε ^ d * ((N : ℝ) + 1) := by
    have h1 : (N₀ : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.cast_le.mpr (le_max_right d N₀)
    have h2 : A * (d : ℝ) / ε ^ d < (N : ℝ) + 1 := by linarith [hN₀]
    rw [div_lt_iff₀ hεd] at h2
    calc A * (d : ℝ) ≤ ((N : ℝ) + 1) * ε ^ d := h2.le
      _ = ε ^ d * ((N : ℝ) + 1) := by ring
  -- a constant covering the indices below `N`
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ i ∈ Finset.range (N + 1),
      |m i| / (ε ^ i * (i ! : ℝ)) ≤ C₀ := by
    refine ⟨(Finset.range (N + 1)).sup' ⟨0, by simp⟩
      (fun i => |m i| / (ε ^ i * (i ! : ℝ))), fun i hi => ?_⟩
    exact Finset.le_sup' (fun i => |m i| / (ε ^ i * (i ! : ℝ))) hi
  refine ⟨max C₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  set C : ℝ := max C₀ 1 with hCdef
  have hC1 : (0 : ℝ) < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCC : C₀ ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hsmall : ∀ i, i ≤ N → |m i| ≤ C * ε ^ i * (i ! : ℝ) := by
    intro i hi
    have hpos : (0 : ℝ) < ε ^ i * (i ! : ℝ) := by
      have : (0 : ℝ) < (i ! : ℝ) := by exact_mod_cast Nat.factorial_pos i
      exact mul_pos (pow_pos hε0 i) this
    have hdiv := hC₀ i (Finset.mem_range.mpr (by omega))
    rw [div_le_iff₀ hpos] at hdiv
    calc |m i| ≤ C₀ * (ε ^ i * (i ! : ℝ)) := hdiv
      _ ≤ C * (ε ^ i * (i ! : ℝ)) := mul_le_mul_of_nonneg_right hCC hpos.le
      _ = C * ε ^ i * (i ! : ℝ) := by ring
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n (N + 1) with hle | hgt
    · exact hsmall n (by omega)
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hn'N : N ≤ n' := by omega
      have hn'd : d ≤ n' := le_trans hNd hn'N
      have hAC : (0 : ℝ) ≤ A * C := mul_nonneg hA0 hC1.le
      have hfacpos : (0 : ℝ) < (n' ! : ℝ) := by exact_mod_cast Nat.factorial_pos n'
      -- every term of the truncated recursion is at most `A * C * n' ! * ε ^ (n' + 1 - d)`
      have hterm : ∀ j ∈ Finset.range d,
          (n'.choose j : ℝ) * A * |m (n' - j)| ≤ A * C * (n' ! : ℝ) * ε ^ (n' + 1 - d) := by
        intro j hj
        rw [Finset.mem_range] at hj
        have hjn : j ≤ n' := by omega
        have hih : |m (n' - j)| ≤ C * ε ^ (n' - j) * ((n' - j)! : ℝ) := ih (n' - j) (by omega)
        have hfac : (n'.choose j : ℝ) * ((n' - j)! : ℝ) ≤ (n' ! : ℝ) := by
          have hj1 : 1 ≤ j ! := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
          have hnat : n'.choose j * (n' - j)! ≤ n' ! := by
            calc n'.choose j * (n' - j)! = n'.choose j * 1 * (n' - j)! := by ring
              _ ≤ n'.choose j * j ! * (n' - j)! :=
                  Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) hj1) (le_refl _)
              _ = n' ! := Nat.choose_mul_factorial_mul_factorial hjn
          exact_mod_cast Nat.cast_le.mpr hnat
        have hpow : ε ^ (n' - j) ≤ ε ^ (n' + 1 - d) :=
          pow_le_pow_of_le_one hε0.le hε1 (by omega)
        have hchoose : (0 : ℝ) ≤ (n'.choose j : ℝ) := by positivity
        calc (n'.choose j : ℝ) * A * |m (n' - j)|
            ≤ (n'.choose j : ℝ) * A * (C * ε ^ (n' - j) * ((n' - j)! : ℝ)) :=
              mul_le_mul_of_nonneg_left hih (mul_nonneg hchoose hA0)
          _ = A * C * ((n'.choose j : ℝ) * ((n' - j)! : ℝ)) * ε ^ (n' - j) := by ring
          _ ≤ A * C * (n' ! : ℝ) * ε ^ (n' - j) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hAC)
                (pow_pos hε0 (n' - j)).le
          _ ≤ A * C * (n' ! : ℝ) * ε ^ (n' + 1 - d) :=
              mul_le_mul_of_nonneg_left hpow (mul_nonneg hAC hfacpos.le)
      have hsum : |m (n' + 1)| ≤ (d : ℝ) * (A * C * (n' ! : ℝ) * ε ^ (n' + 1 - d)) := by
        refine le_trans (hstep n') ?_
        calc ∑ j ∈ Finset.range d, (n'.choose j : ℝ) * A * |m (n' - j)|
            ≤ ∑ _j ∈ Finset.range d, A * C * (n' ! : ℝ) * ε ^ (n' + 1 - d) :=
              Finset.sum_le_sum hterm
          _ = (d : ℝ) * (A * C * (n' ! : ℝ) * ε ^ (n' + 1 - d)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      refine le_trans hsum ?_
      have hsplit : ε ^ (n' + 1) = ε ^ (n' + 1 - d) * ε ^ d := by
        rw [← pow_add]
        congr 1
        omega
      have hfacs : ((n' + 1)! : ℝ) = ((n' : ℝ) + 1) * (n' ! : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hsplit, hfacs]
      have hpowpos : (0 : ℝ) < ε ^ (n' + 1 - d) := pow_pos hε0 _
      have hmono : ε ^ d * ((N : ℝ) + 1) ≤ ε ^ d * ((n' : ℝ) + 1) := by
        have hNn : (N : ℝ) ≤ (n' : ℝ) := by exact_mod_cast hn'N
        exact mul_le_mul_of_nonneg_left (by linarith) hεd.le
      have hkey : A * (d : ℝ) ≤ ε ^ d * ((n' : ℝ) + 1) := le_trans hNbig hmono
      have hCFP : (0 : ℝ) ≤ C * (n' ! : ℝ) * ε ^ (n' + 1 - d) :=
        mul_nonneg (mul_nonneg hC1.le hfacpos.le) hpowpos.le
      calc (d : ℝ) * (A * C * (n' ! : ℝ) * ε ^ (n' + 1 - d))
          = A * (d : ℝ) * (C * (n' ! : ℝ) * ε ^ (n' + 1 - d)) := by ring
        _ ≤ (ε ^ d * ((n' : ℝ) + 1)) * (C * (n' ! : ℝ) * ε ^ (n' + 1 - d)) :=
            mul_le_mul_of_nonneg_right hkey hCFP
        _ = C * (ε ^ (n' + 1 - d) * ε ^ d) * (((n' : ℝ) + 1) * (n' ! : ℝ)) := by ring

end Growth

/-! ### Finiteness of exponential moments

The moments grow slower than `ε ^ n n !` for every `ε`, so the `cosh` series integrates term by
term; only the even moments are used.
-/

section ExpMoments

variable {μ : Measure ℝ}

/-- The moments of `μ` are bounded by `C ε ^ n n !` for every `ε > 0` when the cumulants
vanish from some order on. -/
theorem exists_moment_bound [IsProbabilityMeasure μ] {m₀ : ℕ} (hm₀ : 1 ≤ m₀)
    (hzero : ∀ j, m₀ ≤ j → cumulant id j μ = 0) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, |∫ x : ℝ, x ^ n ∂μ| ≤ C * ε ^ n * (n ! : ℝ) := by
  classical
  set A : ℝ := ∑ j ∈ Finset.range m₀, |cumulant id (j + 1) μ| with hAdef
  have hA0 : (0 : ℝ) ≤ A := Finset.sum_nonneg fun j _ => abs_nonneg _
  refine exists_bound_of_recursion (m := fun n => ∫ x : ℝ, x ^ n ∂μ)
    (k := fun j => cumulant id j μ) (d := m₀) (A := A) hm₀ ?_ ?_ ?_ hε0 hε1
  · intro j
    rcases Nat.lt_or_ge j m₀ with hj | hj
    · exact Finset.single_le_sum (f := fun i => |cumulant id (i + 1) μ|)
        (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hj)
    · rw [hzero (j + 1) (by omega), abs_zero]
      exact hA0
  · intro j hj
    exact hzero (j + 1) (by omega)
  · intro n
    simpa only [id_eq] using moment_recursion μ id n

/-- All exponential moments are finite when the cumulants vanish from some order on. -/
theorem hasAllExpMoments_of_cumulant_eq_zero [IsProbabilityMeasure μ]
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hzero : ∀ j, m₀ ≤ j → cumulant id j μ = 0) :
    integrableExpSet id μ = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun c => ?_
  change Integrable (fun x : ℝ => Real.exp (c * x)) μ
  -- a radius small enough that the `cosh` series is geometric
  set ε : ℝ := min 1 (1 / (2 * (|c| + 1))) with hεdef
  have hcpos : (0 : ℝ) < 2 * (|c| + 1) := by positivity
  have hε0 : (0 : ℝ) < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hcε : |c| * ε ≤ 1 / 2 := by
    have h1 : ε ≤ 1 / (2 * (|c| + 1)) := min_le_right _ _
    have h2 : |c| * ε ≤ |c| * (1 / (2 * (|c| + 1))) :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
    have h3 : |c| * (1 / (2 * (|c| + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ hcpos (by norm_num : (0:ℝ) < 2)]
      nlinarith [abs_nonneg c]
    linarith
  obtain ⟨C, hC0, hC⟩ := exists_moment_bound hm₀ hzero hε0 hε1
  -- the terms of the `cosh` series
  set F : ℕ → ℝ := fun n => c ^ (2 * n) * (∫ x : ℝ, x ^ (2 * n) ∂μ) / ((2 * n)! : ℝ) with hFdef
  have hcabs : ∀ n : ℕ, c ^ (2 * n) = |c| ^ (2 * n) := by
    intro n
    rw [← abs_pow, abs_of_nonneg]
    rw [pow_mul]
    positivity
  have hmomnn : ∀ n : ℕ, (0 : ℝ) ≤ ∫ x : ℝ, x ^ (2 * n) ∂μ := by
    intro n
    refine integral_nonneg fun x => ?_
    rw [pow_mul]
    positivity
  have hFnn : ∀ n, 0 ≤ F n := by
    intro n
    rw [hFdef]
    have h1 : (0 : ℝ) ≤ c ^ (2 * n) := by rw [pow_mul]; positivity
    have h2 : (0 : ℝ) < ((2 * n)! : ℝ) := by exact_mod_cast Nat.factorial_pos (2 * n)
    exact div_nonneg (mul_nonneg h1 (hmomnn n)) h2.le
  have hFle : ∀ n, F n ≤ C * ((|c| * ε) ^ 2) ^ n := by
    intro n
    have hfacpos : (0 : ℝ) < ((2 * n)! : ℝ) := by exact_mod_cast Nat.factorial_pos (2 * n)
    have hmom : (∫ x : ℝ, x ^ (2 * n) ∂μ) ≤ C * ε ^ (2 * n) * ((2 * n)! : ℝ) :=
      le_trans (le_abs_self _) (hC (2 * n))
    have habs : (0 : ℝ) ≤ |c| ^ (2 * n) := by positivity
    have hnum : c ^ (2 * n) * (∫ x : ℝ, x ^ (2 * n) ∂μ)
        ≤ |c| ^ (2 * n) * (C * ε ^ (2 * n) * ((2 * n)! : ℝ)) := by
      rw [hcabs n]
      exact mul_le_mul_of_nonneg_left hmom habs
    rw [hFdef, div_le_iff₀ hfacpos]
    refine le_trans hnum ?_
    have hrw : ((|c| * ε) ^ 2) ^ n = |c| ^ (2 * n) * ε ^ (2 * n) := by
      rw [← pow_mul, mul_pow]
    rw [hrw]
    exact le_of_eq (by ring)
  have hgeom : Summable (fun n : ℕ => C * ((|c| * ε) ^ 2) ^ n) := by
    refine Summable.mul_left C (summable_geometric_of_lt_one ?_ ?_)
    · positivity
    · have h1 : (0 : ℝ) ≤ |c| * ε := by positivity
      nlinarith [hcε, h1]
  have hFsummable : Summable F :=
    hgeom.of_nonneg_of_le hFnn hFle
  -- the `cosh` series, integrated term by term
  have hterm : ∀ n : ℕ, ∫ x : ℝ, (c * x) ^ (2 * n) / ((2 * n)! : ℝ) ∂μ = F n := by
    intro n
    have hcast : ∀ x : ℝ, (c * x) ^ (2 * n) / ((2 * n)! : ℝ)
        = (c ^ (2 * n) / ((2 * n)! : ℝ)) * x ^ (2 * n) := by
      intro x; rw [mul_pow]; ring
    simp_rw [hcast]
    rw [integral_const_mul, hFdef]
    ring
  have hIint : ∀ n : ℕ, Integrable (fun x : ℝ => (c * x) ^ (2 * n) / ((2 * n)! : ℝ)) μ := by
    intro n
    have hI := (hint (2 * n)).const_mul (c ^ (2 * n) / ((2 * n)! : ℝ))
    refine hI.congr (Filter.Eventually.of_forall fun x => ?_)
    change c ^ (2 * n) / ((2 * n)! : ℝ) * x ^ (2 * n) = (c * x) ^ (2 * n) / ((2 * n)! : ℝ)
    rw [mul_pow]; ring
  have hlint : ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh (c * x)) ∂μ
      ≤ ENNReal.ofReal (∑' n : ℕ, F n) := by
    have hstep1 : ∀ x : ℝ, ENNReal.ofReal (Real.cosh (c * x))
        = ∑' n : ℕ, ENNReal.ofReal ((c * x) ^ (2 * n) / ((2 * n)! : ℝ)) := by
      intro x
      rw [← (Real.hasSum_cosh (c * x)).tsum_eq]
      exact ENNReal.ofReal_tsum_of_nonneg (fun n => by rw [pow_mul]; positivity)
        (Real.hasSum_cosh (c * x)).summable
    calc ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh (c * x)) ∂μ
        = ∫⁻ x : ℝ, ∑' n : ℕ, ENNReal.ofReal ((c * x) ^ (2 * n) / ((2 * n)! : ℝ)) ∂μ := by
          simp_rw [hstep1]
      _ = ∑' n : ℕ, ∫⁻ x : ℝ, ENNReal.ofReal ((c * x) ^ (2 * n) / ((2 * n)! : ℝ)) ∂μ :=
          lintegral_tsum (fun n => by fun_prop)
      _ = ∑' n : ℕ, ENNReal.ofReal (F n) := by
          refine tsum_congr fun n => ?_
          rw [← hterm n]
          refine (ofReal_integral_eq_lintegral_ofReal (hIint n) ?_).symm
          filter_upwards with x
          rw [pow_mul]
          positivity
      _ ≤ ENNReal.ofReal (∑' n : ℕ, F n) :=
          le_of_eq (ENNReal.ofReal_tsum_of_nonneg hFnn hFsummable).symm
  have hcoshint : Integrable (fun x : ℝ => Real.cosh (c * x)) μ := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (Real.cosh_pos _).le)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  refine Integrable.mono' (hcoshint.const_mul 2) (by fun_prop)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.cosh_eq]
  have hpos := Real.exp_pos (-(c * x))
  linarith

end ExpMoments

/-! ### Janson's Lemma 2 for eventually vanishing cumulants

If the cumulants vanish from some order on, `φ (t) = exp (∑ κ_j / j ! (i t) ^ j)` for every real
`t`. The moment-generating function and `exp ∘ Q` are entire with the same Taylor coefficients
at `0`, since both satisfy the moment–cumulant recursion.
-/

section LemmaTwo

variable {μ : Measure ℝ}

/-- The coefficients of a finite sum of monomials. -/
lemma coeff_sum_C_mul_X_pow (a : ℕ → ℂ) (s : Finset ℕ) (k : ℕ) :
    (∑ j ∈ s, Polynomial.C (a j) * Polynomial.X ^ j).coeff k = if k ∈ s then a k else 0 := by
  classical
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq s k a

/-- The iterated derivatives of a polynomial at the origin are its coefficients. -/
lemma iteratedDeriv_polynomial_zero (P : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => P.eval z) 0 = (n ! : ℂ) * P.coeff n := by
  have key : ∀ (k : ℕ) (R : Polynomial ℂ),
      iteratedDeriv k (fun z : ℂ => R.eval z)
        = fun z : ℂ => (Polynomial.derivative^[k] R).eval z := by
    intro k
    induction k with
    | zero => intro R; funext z; simp
    | succ k ih =>
      intro R
      rw [iteratedDeriv_succ']
      have hd : deriv (fun z : ℂ => R.eval z) = fun z : ℂ => R.derivative.eval z := by
        funext z; exact R.deriv
      rw [hd, ih R.derivative, Function.iterate_succ_apply]
  rw [key n P]
  change (Polynomial.derivative^[n] P).eval 0 = (n ! : ℂ) * P.coeff n
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self]

/-- The iterated derivatives of `exp ∘ Q` at the origin satisfy
`f (n+1) = ∑ i, C (n, i) (i ! Q' i) f (n-i)`. -/
lemma iteratedDeriv_exp_poly_succ (Q : Polynomial ℂ) (n : ℕ) :
    iteratedDeriv (n + 1) (fun z : ℂ => Complex.exp (Q.eval z)) 0
      = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * ((i ! : ℂ) * Q.derivative.coeff i)
          * iteratedDeriv (n - i) (fun z : ℂ => Complex.exp (Q.eval z)) 0 := by
  have hQc : ContDiffAt ℂ (n : ℕ) (fun z : ℂ => Q.derivative.eval z) 0 :=
    Q.derivative.differentiable.contDiff.contDiffAt
  have hHc : ContDiffAt ℂ (n : ℕ) (fun z : ℂ => Complex.exp (Q.eval z)) 0 :=
    (Complex.differentiable_exp.comp Q.differentiable).contDiff.contDiffAt
  have hderiv : deriv (fun z : ℂ => Complex.exp (Q.eval z))
      = (fun z : ℂ => Q.derivative.eval z) * (fun z : ℂ => Complex.exp (Q.eval z)) := by
    funext z
    have h1 : HasDerivAt (fun w : ℂ => Q.eval w) (Q.derivative.eval z) z := Q.hasDerivAt z
    rw [h1.cexp.deriv]
    change Complex.exp (Q.eval z) * Q.derivative.eval z
      = Q.derivative.eval z * Complex.exp (Q.eval z)
    ring
  rw [iteratedDeriv_succ', hderiv, iteratedDeriv_mul hQc hHc]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_polynomial_zero]

/-- Two entire functions with the same iterated derivatives at the origin are equal. This is
Mathlib's Taylor expansion of an entire function, read as a uniqueness statement. -/
lemma eq_of_iteratedDeriv_zero {G H : ℂ → ℂ} (hG : Differentiable ℂ G) (hH : Differentiable ℂ H)
    (h : ∀ n, iteratedDeriv n G 0 = iteratedDeriv n H 0) (z : ℂ) : G z = H z := by
  rw [← Complex.taylorSeries_eq_of_entire' hG (c := 0) (z := z),
    ← Complex.taylorSeries_eq_of_entire' hH (c := 0) (z := z)]
  exact tsum_congr fun n => by rw [h n]

/-- The cumulant polynomial `Q (z) = ∑_{j=1}^{N} κ_j z ^ j / j !`. -/
noncomputable def cumPoly (μ : Measure ℝ) (N : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.Icc 1 N, Polynomial.C ((cumulant id j μ : ℂ) / (j ! : ℂ)) * Polynomial.X ^ j

/-- The polynomial `p (t) = ∑_{j=1}^{N} κ_j (i t) ^ j / j !`, that is, `cumPoly` composed with
multiplication by `i`. -/
noncomputable def charPoly (μ : Measure ℝ) (N : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.Icc 1 N,
    Polynomial.C ((cumulant id j μ : ℂ) * Complex.I ^ j / (j ! : ℂ)) * Polynomial.X ^ j

lemma coeff_charPoly (μ : Measure ℝ) (N k : ℕ) :
    (charPoly μ N).coeff k
      = if k ∈ Finset.Icc 1 N then (cumulant id k μ : ℂ) * Complex.I ^ k / (k ! : ℂ) else 0 :=
  coeff_sum_C_mul_X_pow _ _ _

lemma eval_charPoly (μ : Measure ℝ) (N : ℕ) (t : ℂ) :
    (charPoly μ N).eval t = (cumPoly μ N).eval (t * Complex.I) := by
  simp only [charPoly, cumPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow]
  ring

lemma eval_cumPoly_zero (μ : Measure ℝ) (N : ℕ) : (cumPoly μ N).eval 0 = 0 := by
  simp only [cumPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [zero_pow (by omega), mul_zero]

/-- `i ! Q' i = κ (i+1)` for every `i`; above `N` both sides vanish. -/
lemma factorial_mul_coeff_derivative_cumPoly {m₀ N : ℕ} (hN : m₀ ≤ N)
    (hzero : ∀ j, m₀ ≤ j → cumulant id j μ = 0) (i : ℕ) :
    (i ! : ℂ) * (cumPoly μ N).derivative.coeff i = ((cumulant id (i + 1) μ : ℝ) : ℂ) := by
  classical
  rw [Polynomial.coeff_derivative, cumPoly, coeff_sum_C_mul_X_pow]
  have hfac0 : ((i ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have hi0 : ((i : ℂ) + 1) ≠ 0 := by
    exact_mod_cast Nat.cast_add_one_ne_zero (R := ℂ) i
  simp only [Finset.mem_Icc]
  split_ifs with h
  · have hfac : (((i + 1)! : ℕ) : ℂ) = ((i : ℂ) + 1) * ((i ! : ℕ) : ℂ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac]
    field_simp
  · rw [hzero (i + 1) (by omega)]
    push_cast
    ring

/-- The Taylor coefficients of `exp ∘ Q` at `0` are the moments of `μ`. -/
theorem iteratedDeriv_exp_cumPoly [IsProbabilityMeasure μ] {m₀ N : ℕ} (hN : m₀ ≤ N)
    (hzero : ∀ j, m₀ ≤ j → cumulant id j μ = 0) :
    ∀ n : ℕ, iteratedDeriv n (fun z : ℂ => Complex.exp ((cumPoly μ N).eval z)) 0
      = ((∫ x : ℝ, x ^ n ∂μ : ℝ) : ℂ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      rw [iteratedDeriv_zero, eval_cumPoly_zero, Complex.exp_zero]
      norm_num
    | (n + 1) =>
      rw [iteratedDeriv_exp_poly_succ]
      have hterm : ∀ i ∈ Finset.range (n + 1),
          (n.choose i : ℂ) * ((i ! : ℂ) * (cumPoly μ N).derivative.coeff i)
              * iteratedDeriv (n - i) (fun z : ℂ => Complex.exp ((cumPoly μ N).eval z)) 0
            = (((n.choose i : ℝ) * cumulant id (i + 1) μ * ∫ x : ℝ, x ^ (n - i) ∂μ : ℝ) : ℂ) := by
        intro i hi
        rw [factorial_mul_coeff_derivative_cumPoly hN hzero i, ih (n - i) (by omega)]
        push_cast
        ring
      rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum]
      have hrec := moment_recursion μ id n
      simp only [id_eq] at hrec
      rw [← hrec]

/-- **Janson's Lemma 2** for eventually vanishing cumulants: if the cumulants vanish from
order `m₀` on, the characteristic function is `exp ∘ p` at every real `t`. -/
theorem charFun_eq_exp_charPoly [IsProbabilityMeasure μ]
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hzero : ∀ j, m₀ ≤ j → cumulant id j μ = 0) (t : ℝ) :
    charFun μ t = Complex.exp ((charPoly μ m₀).eval (t : ℂ)) := by
  have hmom : integrableExpSet id μ = Set.univ :=
    hasAllExpMoments_of_cumulant_eq_zero hint hm₀ hzero
  have hGdiff : Differentiable ℂ (complexMGF id μ) := fun z =>
    (analyticAt_complexMGF
      (by simp [hmom])).differentiableAt
  have hHdiff : Differentiable ℂ (fun z : ℂ => Complex.exp ((cumPoly μ m₀).eval z)) :=
    Complex.differentiable_exp.comp (cumPoly μ m₀).differentiable
  have hGderiv : ∀ n : ℕ,
      iteratedDeriv n (complexMGF id μ) 0 = ((∫ x : ℝ, x ^ n ∂μ : ℝ) : ℂ) := by
    intro n
    have hz : (0 : ℂ).re ∈ interior (integrableExpSet id μ) := by
      simp [hmom]
    rw [iteratedDeriv_complexMGF hz n]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one]
    rw [← _root_.integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    push_cast
    ring
  have hEq : ∀ z : ℂ, complexMGF id μ z = Complex.exp ((cumPoly μ m₀).eval z) :=
    eq_of_iteratedDeriv_zero hGdiff hHdiff
      (fun n => by rw [hGderiv n, iteratedDeriv_exp_cumPoly (le_refl m₀) hzero n])
  rw [← complexMGF_id_mul_I t, hEq, eval_charPoly]

end LemmaTwo

/-! ### Marcinkiewicz's theorem in cumulant form

If the cumulants of `X` vanish for all sufficiently large orders, `X` is normal.
-/

section Normal

variable {μ : Measure ℝ}

/-- `κ_2` is the variance (`cumulant_two_eq_variance`), hence nonnegative. -/
lemma cumulant_two_nonneg [IsProbabilityMeasure μ] (h2 : Integrable (fun x : ℝ => x ^ 2) μ) :
    0 ≤ cumulant id 2 μ := by
  have hL2 : MemLp id 2 μ := (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr h2
  have h := variance_nonneg id μ
  rw [variance_eq_sub hL2] at h
  rw [cumulant_two]
  exact h

/-- **Marcinkiewicz's theorem in cumulant form.** If the cumulants of `μ` vanish from some
order on, they vanish from order `3` on. -/
theorem cumulant_eq_zero_of_three_le [IsProbabilityMeasure μ]
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hzero : ∀ j, m₀ ≤ j → cumulant id j μ = 0)
    {j : ℕ} (hj : 3 ≤ j) : cumulant id j μ = 0 := by
  rcases Nat.lt_or_ge j m₀ with h | h
  · have hdeg : (charPoly μ m₀).degree ≤ 2 :=
      Marcinkiewicz.charFun_eq_exp_polynomial_degree_le_two
        (fun t => charFun_eq_exp_charPoly hint hm₀ hzero t)
    have hnd : (charPoly μ m₀).natDegree ≤ 2 := Polynomial.natDegree_le_iff_degree_le.mpr hdeg
    have hc : (charPoly μ m₀).coeff j = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hmem : j ∈ Finset.Icc 1 m₀ := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [coeff_charPoly, ite_eq_left hmem] at hc
    have hf : ((j ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hI : (Complex.I : ℂ) ^ j ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
    have h1 : ((cumulant id j μ : ℝ) : ℂ) * Complex.I ^ j = 0 :=
      (div_eq_zero_iff.mp hc).resolve_right hf
    have h2 : ((cumulant id j μ : ℝ) : ℂ) = 0 := (mul_eq_zero.mp h1).resolve_right hI
    exact_mod_cast h2
  · exact hzero j h

/-- If the cumulants vanish from order `3` on, the cumulant polynomial reduces to its linear and
quadratic terms. -/
lemma eval_charPoly_of_cumulant_eq_zero {m₀ : ℕ} (hm₀ : 1 ≤ m₀)
    (hzero : ∀ j, m₀ ≤ j → cumulant id j μ = 0)
    (h3 : ∀ j, 3 ≤ j → cumulant id j μ = 0) (t : ℂ) :
    (charPoly μ m₀).eval t
      = t * (cumulant id 1 μ : ℂ) * Complex.I - (cumulant id 2 μ : ℂ) * t ^ 2 / 2 := by
  classical
  set f : ℕ → ℂ := fun j => (cumulant id j μ : ℂ) * Complex.I ^ j / (j ! : ℂ) * t ^ j with hf
  have hzerof : ∀ j, cumulant id j μ = 0 → f j = 0 := by
    intro j hj
    rw [hf]
    simp only
    rw [hj]
    push_cast
    ring
  have heval : (charPoly μ m₀).eval t = ∑ j ∈ Finset.Icc 1 m₀, f j := by
    simp only [charPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, hf]
  have hbig : ∑ j ∈ Finset.Icc 1 m₀, f j = ∑ j ∈ Finset.Icc 1 (m₀ + 2), f j := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      rw [Finset.mem_Icc] at hx ⊢
      omega
    · intro x hx hnx
      rw [Finset.mem_Icc] at hx hnx
      refine hzerof x (hzero x ?_)
      by_contra hcon
      exact hnx ⟨hx.1, by omega⟩
  have hsmall : ∑ j ∈ ({1, 2} : Finset ℕ), f j = ∑ j ∈ Finset.Icc 1 (m₀ + 2), f j := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_Icc]
      omega
    · intro x hx hnx
      rw [Finset.mem_Icc] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnx
      obtain ⟨hn1, hn2⟩ := hnx
      exact hzerof x (h3 x (by omega))
  rw [heval, hbig, ← hsmall, Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2), hf]
  simp only [pow_one, Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat,
    div_one, Complex.I_sq]
  ring

/-- The characteristic function is Gaussian. -/
theorem charFun_eq_exp_gaussian [IsProbabilityMeasure μ]
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hzero : ∀ j, m₀ ≤ j → cumulant id j μ = 0) (t : ℝ) :
    charFun μ t = Complex.exp ((t : ℂ) * (cumulant id 1 μ : ℂ) * Complex.I
      - (cumulant id 2 μ : ℂ) * (t : ℂ) ^ 2 / 2) := by
  rw [charFun_eq_exp_charPoly hint hm₀ hzero t,
    eval_charPoly_of_cumulant_eq_zero hm₀ hzero
      (fun j hj => cumulant_eq_zero_of_three_le hint hm₀ hzero hj)]

/-- A probability measure on `ℝ` with all moments whose cumulants vanish from some order on
is the Gaussian law with mean `κ_1` and variance `κ_2` (a Dirac mass when `κ_2 = 0`). -/
theorem eq_gaussianReal_of_cumulant_eq_zero [IsProbabilityMeasure μ]
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hzero : ∀ j, m₀ ≤ j → cumulant id j μ = 0) :
    μ = gaussianReal (cumulant id 1 μ) (cumulant id 2 μ).toNNReal := by
  have h1 : Integrable (fun x : ℝ => x) μ := by
    have h := hint 1
    simpa using h
  have hv : ((cumulant id 2 μ).toNNReal : ℝ) = cumulant id 2 μ :=
    Real.coe_toNNReal _ (cumulant_two_nonneg (hint 2))
  refine MeasureTheory.Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_eq_exp_gaussian hint hm₀ hzero t, charFun_gaussianReal, hv]

end Normal

/-! ### The cumulants of a Gaussian

A law whose two-sided Laplace transform is `exp ∘ q`, for a polynomial `q`, has cumulants read
off `q`.
-/

section Converse

variable {μ : Measure ℝ}

/-- A real sequence obeying the moment–cumulant recursion against the moments of `μ` is the
cumulant sequence of `μ`. -/
theorem cumulant_unique [IsProbabilityMeasure μ] {k : ℕ → ℝ}
    (hrec : ∀ n : ℕ, (∫ x : ℝ, x ^ (n + 1) ∂μ)
      = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * k (j + 1) * ∫ x : ℝ, x ^ (n - j) ∂μ) :
    ∀ j : ℕ, 1 ≤ j → cumulant id j μ = k j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    have h1 := moment_recursion μ id n
    simp only [id_eq] at h1
    rw [hrec n] at h1
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at h1
    have hagree : ∑ i ∈ Finset.range n,
          (n.choose i : ℝ) * cumulant id (i + 1) μ * ∫ x : ℝ, x ^ (n - i) ∂μ
        = ∑ i ∈ Finset.range n, (n.choose i : ℝ) * k (i + 1) * ∫ x : ℝ, x ^ (n - i) ∂μ := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [ih (i + 1) (by omega) (by omega)]
    rw [hagree] at h1
    have hz : (∫ x : ℝ, x ^ (n - n) ∂μ) = 1 := by
      rw [Nat.sub_self]
      simp
    rw [hz] at h1
    simp only [Nat.choose_self, Nat.cast_one, one_mul, mul_one] at h1
    linarith

/-- The cumulants read off an exponential-polynomial Laplace transform. -/
theorem cumulant_of_complexMGF_eq_exp [IsProbabilityMeasure μ]
    (hmom : integrableExpSet id μ = Set.univ) {q : Polynomial ℂ} {k : ℕ → ℝ}
    (hq : ∀ z : ℂ, complexMGF id μ z = Complex.exp (q.eval z))
    (hk : ∀ i : ℕ, (i ! : ℂ) * q.derivative.coeff i = ((k (i + 1) : ℝ) : ℂ)) :
    ∀ j : ℕ, 1 ≤ j → cumulant id j μ = k j := by
  have hG : ∀ n : ℕ,
      iteratedDeriv n (complexMGF id μ) 0 = ((∫ x : ℝ, x ^ n ∂μ : ℝ) : ℂ) := by
    intro n
    have hz : (0 : ℂ).re ∈ interior (integrableExpSet id μ) := by
      simp [hmom]
    rw [iteratedDeriv_complexMGF hz n]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one]
    rw [← _root_.integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    push_cast
    ring
  have hfun : (fun z : ℂ => Complex.exp (q.eval z)) = complexMGF id μ := (funext hq).symm
  have hH : ∀ n : ℕ, iteratedDeriv n (fun z : ℂ => Complex.exp (q.eval z)) 0
      = ((∫ x : ℝ, x ^ n ∂μ : ℝ) : ℂ) := by
    intro n
    rw [hfun]
    exact hG n
  refine cumulant_unique (k := k) fun n => ?_
  have hL := iteratedDeriv_exp_poly_succ q n
  rw [hH (n + 1)] at hL
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * ((i ! : ℂ) * q.derivative.coeff i)
          * iteratedDeriv (n - i) (fun z : ℂ => Complex.exp (q.eval z)) 0
        = (((n.choose i : ℝ) * k (i + 1) * ∫ x : ℝ, x ^ (n - i) ∂μ : ℝ) : ℂ) := by
    intro i _
    rw [hk i, hH (n - i)]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum] at hL
  exact_mod_cast hL

/-- The coefficients of the Gaussian Laplace-transform polynomial. -/
noncomputable def gaussCoeff (m : ℝ) (v : ℝ≥0) : ℕ → ℂ :=
  fun j => if j = 1 then (m : ℂ) else (v : ℂ) / 2

/-- The polynomial whose exponential is the two-sided Laplace transform of `N (m, v)`. -/
noncomputable def gaussMGFPoly (m : ℝ) (v : ℝ≥0) : Polynomial ℂ :=
  ∑ j ∈ ({1, 2} : Finset ℕ), Polynomial.C (gaussCoeff m v j) * Polynomial.X ^ j

/-- The cumulant sequence of `N (m, v)`: `κ_1 = m`, `κ_2 = v`, and `κ_j = 0` for `j ≥ 3`. -/
noncomputable def gaussCumulants (m : ℝ) (v : ℝ≥0) : ℕ → ℝ :=
  fun j => if j = 1 then m else if j = 2 then (v : ℝ) else 0

lemma coeff_gaussMGFPoly (m : ℝ) (v : ℝ≥0) (k : ℕ) :
    (gaussMGFPoly m v).coeff k
      = if k ∈ ({1, 2} : Finset ℕ) then gaussCoeff m v k else 0 :=
  coeff_sum_C_mul_X_pow _ _ _

/-- The cumulants of a Gaussian: `κ_1 = m`, `κ_2 = v`, and `κ_j = 0` for `j ≥ 3`. -/
theorem cumulant_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∀ j : ℕ, 1 ≤ j → cumulant id j (gaussianReal m v) = gaussCumulants m v j := by
  refine cumulant_of_complexMGF_eq_exp
    integrableExpSet_id_gaussianReal (q := gaussMGFPoly m v) ?_ ?_
  · intro z
    rw [complexMGF_id_gaussianReal]
    congr 1
    rw [gaussMGFPoly]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]
    simp only [gaussCoeff, pow_one]
    norm_num
    ring
  · intro i
    rw [Polynomial.coeff_derivative, coeff_gaussMGFPoly]
    match i with
    | 0 =>
      norm_num [gaussCoeff, gaussCumulants]
    | 1 =>
      norm_num [gaussCoeff, gaussCumulants]
    | (i + 2) =>
      have hmem : (i + 2 + 1) ∉ ({1, 2} : Finset ℕ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hg : gaussCumulants m v (i + 2 + 1) = 0 := by
        simp only [gaussCumulants]
        split_ifs with ha hb
        · exact absurd ha (by omega)
        · exact absurd hb (by omega)
        · rfl
      rw [ite_eq_right hmem, hg]
      push_cast
      ring

end Converse

/-! ### Examples

The main theorems are applied to `N (2, 3)` at `m₀ = 5`, so that the Marcinkiewicz step is used
at `j = 3 < m₀`, and to the skewed law `SkewWitness.skewLaw`.
-/

section Witness

/-- All moments of a Gaussian are finite. -/
lemma integrable_pow_gaussianReal (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal m v) := by
  simpa using integrable_pow_of_mem_interior_integrableExpSet (X := id) (μ := gaussianReal m v)
    (by simp) n

/-- The hypothesis of the main theorems, at `m₀ = 5`, for `N (2, 3)`. -/
lemma gauss23_cumulant_eq_zero :
    ∀ j : ℕ, 5 ≤ j → cumulant id j (gaussianReal 2 3) = 0 := by
  intro j hj
  rw [cumulant_gaussianReal 2 3 j (by omega)]
  simp only [gaussCumulants]
  split_ifs with ha hb
  · exact absurd ha (by omega)
  · exact absurd hb (by omega)
  · rfl

/-- Janson's Lemma 2 for `N (2, 3)` at `m₀ = 5`. -/
theorem gaussian_lemma_two_witness (t : ℝ) :
    charFun (gaussianReal 2 3) t
      = Complex.exp ((charPoly (gaussianReal 2 3) 5).eval (t : ℂ)) :=
  charFun_eq_exp_charPoly (integrable_pow_gaussianReal 2 3) (by norm_num)
    gauss23_cumulant_eq_zero t

/-- The quadratic coefficient of the polynomial for `N (2, 3)` is `-3/2`. -/
theorem charPoly_gauss23_coeff_two :
    (charPoly (gaussianReal 2 3) 5).coeff 2 = -(3 / 2 : ℂ) := by
  have hmem : (2 : ℕ) ∈ Finset.Icc 1 5 := by decide
  rw [coeff_charPoly, ite_eq_left hmem, cumulant_gaussianReal 2 3 2 (by norm_num)]
  simp only [gaussCumulants]
  norm_num [Complex.I_sq, Nat.factorial_two]

/-- `κ_3 = 0` for `N (2, 3)`, derived through `cumulant_eq_zero_of_three_le` at `m₀ = 5`. -/
theorem gaussian_marcinkiewicz_witness : cumulant id 3 (gaussianReal 2 3) = 0 :=
  cumulant_eq_zero_of_three_le (integrable_pow_gaussianReal 2 3) (m₀ := 5) (by norm_num)
    gauss23_cumulant_eq_zero (by norm_num)

/-- `eq_gaussianReal_of_cumulant_eq_zero` for `N (2, 3)`, recovering `κ_1 = 2` and `κ_2 = 3`. -/
theorem gaussian_normality_witness :
    cumulant id 1 (gaussianReal 2 3) = 2
      ∧ cumulant id 2 (gaussianReal 2 3) = 3
      ∧ gaussianReal (2 : ℝ) (3 : ℝ≥0)
          = gaussianReal (cumulant id 1 (gaussianReal 2 3))
              (cumulant id 2 (gaussianReal 2 3)).toNNReal := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cumulant_gaussianReal 2 3 1 (by norm_num)]
    simp [gaussCumulants]
  · rw [cumulant_gaussianReal 2 3 2 (by norm_num)]
    simp [gaussCumulants]
  · exact eq_gaussianReal_of_cumulant_eq_zero (integrable_pow_gaussianReal 2 3) (m₀ := 5)
      (by norm_num) gauss23_cumulant_eq_zero

/-- No probability measure on `ℝ` with all moments has cumulants vanishing from order `5` on
and a nonzero fourth cumulant. -/
theorem no_measure_with_nonzero_fourth_cumulant (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (h5 : ∀ j, 5 ≤ j → cumulant id j μ = 0) (h4 : cumulant id 4 μ ≠ 0) : False :=
  h4 (cumulant_eq_zero_of_three_le hint (by norm_num) h5 (by norm_num))

/-- `SkewWitness.skewLaw = ¼ δ_4 + ¾ δ_0` has `κ_3 = 6 ≠ 0`, so its cumulants do not vanish
from any order on. -/
theorem skew_cumulants_not_eventually_zero :
    ¬ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ j, m₀ ≤ j → cumulant id j SkewWitness.skewLaw = 0 := by
  rintro ⟨m₀, hm₀, hzero⟩
  exact SkewWitness.skew_cumulant_three_ne_zero
    (cumulant_eq_zero_of_three_le
      (fun n => SkewWitness.integrable_skew (by fun_prop)) hm₀ hzero (by norm_num))

/-- The moment–cumulant recursion on the skewed law, where no term vanishes:
`16 = 1·1·4 + 2·3·1 + 1·6·1`. -/
theorem skew_moment_recursion_witness :
    ∑ j ∈ Finset.range 3, ((2 : ℕ).choose j : ℝ) * cumulant id (j + 1) SkewWitness.skewLaw
        * (∫ x : ℝ, x ^ (2 - j) ∂SkewWitness.skewLaw) = 16 := by
  have h := moment_recursion SkewWitness.skewLaw id 2
  simp only [id_eq] at h
  rw [← h]
  exact SkewWitness.skew_moment_three

/-- The three terms of that recursion, each nonzero. -/
theorem skew_recursion_terms_witness :
    ((2 : ℕ).choose 0 : ℝ) * cumulant id 1 SkewWitness.skewLaw
        * (∫ x : ℝ, x ^ 2 ∂SkewWitness.skewLaw) = 4
      ∧ ((2 : ℕ).choose 1 : ℝ) * cumulant id 2 SkewWitness.skewLaw
        * (∫ x : ℝ, x ^ 1 ∂SkewWitness.skewLaw) = 6
      ∧ ((2 : ℕ).choose 2 : ℝ) * cumulant id 3 SkewWitness.skewLaw
        * (∫ x : ℝ, x ^ 0 ∂SkewWitness.skewLaw) = 6 := by
  have h1 : (∫ x : ℝ, x ^ 1 ∂SkewWitness.skewLaw) = 1 := by simp
  have h0 : (∫ x : ℝ, x ^ 0 ∂SkewWitness.skewLaw) = 1 := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [SkewWitness.skew_cumulant_one, SkewWitness.skew_moment_two]
    norm_num
  · rw [SkewWitness.skew_cumulant_two, h1]
    norm_num
  · rw [SkewWitness.skew_cumulant_three, h0]
    norm_num

/-- The cardinality reduction on the skewed law. The mixed cumulant of three copies of the
coordinate, over an index set of size three other than `Fin 3`, is `κ_3 = 6`. -/
theorem skew_cardinality_reduction_witness :
    mixedCumulant SkewWitness.skewLaw (fun _ : Fin 5 => (id : ℝ → ℝ))
        ({0, 1, 2} : Finset (Fin 5)) = 6 := by
  rw [mixedCumulant_const_fun SkewWitness.skewLaw id 3 ({0, 1, 2} : Finset (Fin 5)) (by decide)]
  exact SkewWitness.skew_cumulant_three

end Witness

/-! ### Multilinearity of the mixed cumulant

Each summand `∏_B E ∏_{i ∈ B} X_i` of the set-partition formula contains `X_{i₀}` in exactly
one factor, so the mixed cumulant is linear in `X_{i₀}`. Additivity requires integrability of
the two partial products; homogeneity does not.
-/

section Multilinear

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [DecidableEq ι]

/-- A joint moment over a block that misses `i₀` is unchanged by an update at `i₀`. -/
lemma jointMoment_update_of_notMem (μ : Measure Ω) (X : ι → Ω → ℝ) (i₀ : ι) (f : Ω → ℝ)
    {B : Finset ι} (h : i₀ ∉ B) :
    jointMoment μ (Function.update X i₀ f) B = jointMoment μ X B := by
  have hpt : ∀ ω, ∏ i ∈ B, (Function.update X i₀ f) i ω = ∏ i ∈ B, X i ω := by
    intro ω
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ i₀ := by
      rintro rfl
      exact h hi
    rw [Function.update_of_ne hne f X]
  simp only [jointMoment, hpt]

/-- A joint moment over a block containing `i₀` factors the updated variable out. -/
lemma jointMoment_update_of_mem (μ : Measure Ω) (X : ι → Ω → ℝ) (i₀ : ι) (f : Ω → ℝ)
    {B : Finset ι} (h : i₀ ∈ B) :
    jointMoment μ (Function.update X i₀ f) B
      = ∫ ω, f ω * ∏ i ∈ B.erase i₀, X i ω ∂μ := by
  have hpt : ∀ ω, ∏ i ∈ B, (Function.update X i₀ f) i ω = f ω * ∏ i ∈ B.erase i₀, X i ω := by
    intro ω
    rw [← Finset.mul_prod_erase B (fun i => (Function.update X i₀ f) i ω) h,
      Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi) f X]
  simp only [jointMoment, hpt]

/-- The product over the blocks of `π`, split at the block containing `i₀`. Every other factor
is unchanged by an update at `i₀`. -/
lemma prod_parts_update (μ : Measure Ω) (X : ι → Ω → ℝ) {i₀ : ι} {s : Finset ι} (hi : i₀ ∈ s)
    (π : Finpartition s) (f : Ω → ℝ) :
    ∏ B ∈ π.parts, jointMoment μ (Function.update X i₀ f) B
      = jointMoment μ (Function.update X i₀ f) (π.part i₀)
          * ∏ B ∈ π.parts.erase (π.part i₀), jointMoment μ X B := by
  classical
  have hPmem : π.part i₀ ∈ π.parts := (Finpartition.part_mem π).mpr hi
  rw [← Finset.mul_prod_erase π.parts
    (fun B => jointMoment μ (Function.update X i₀ f) B) hPmem]
  congr 1
  refine Finset.prod_congr rfl fun B hB => ?_
  refine jointMoment_update_of_notMem μ X i₀ f ?_
  intro hc
  exact (Finset.mem_erase.mp hB).1
    (Finpartition.part_eq_of_mem π (Finset.mem_of_mem_erase hB) hc).symm

/-- Additivity of the mixed cumulant in one argument, given integrability of the product
over the block of `i₀` with that variable removed. -/
theorem mixedCumulant_update_add (μ : Measure Ω) (X : ι → Ω → ℝ) {i₀ : ι} {s : Finset ι}
    (hi : i₀ ∈ s) (Y Z : Ω → ℝ)
    (hY : ∀ B : Finset ι, Integrable (fun ω => Y ω * ∏ i ∈ B.erase i₀, X i ω) μ)
    (hZ : ∀ B : Finset ι, Integrable (fun ω => Z ω * ∏ i ∈ B.erase i₀, X i ω) μ) :
    mixedCumulant μ (Function.update X i₀ (fun ω => Y ω + Z ω)) s
      = mixedCumulant μ (Function.update X i₀ Y) s
        + mixedCumulant μ (Function.update X i₀ Z) s := by
  classical
  rw [mixedCumulant, mixedCumulant, mixedCumulant, mobius, mobius, mobius,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hi₀P : i₀ ∈ π.part i₀ := (Finpartition.mem_part_self π).mpr hi
  have hadd : jointMoment μ (Function.update X i₀ (fun ω => Y ω + Z ω)) (π.part i₀)
      = jointMoment μ (Function.update X i₀ Y) (π.part i₀)
        + jointMoment μ (Function.update X i₀ Z) (π.part i₀) := by
    rw [jointMoment_update_of_mem μ X i₀ _ hi₀P, jointMoment_update_of_mem μ X i₀ Y hi₀P,
      jointMoment_update_of_mem μ X i₀ Z hi₀P, ← integral_add (hY (π.part i₀)) (hZ (π.part i₀))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    ring
  rw [prod_parts_update μ X hi π, prod_parts_update μ X hi π, prod_parts_update μ X hi π, hadd]
  ring

/-- Homogeneity of the mixed cumulant in one argument. -/
theorem mixedCumulant_update_smul (μ : Measure Ω) (X : ι → Ω → ℝ) {i₀ : ι} {s : Finset ι}
    (hi : i₀ ∈ s) (a : ℝ) (Y : Ω → ℝ) :
    mixedCumulant μ (Function.update X i₀ (fun ω => a * Y ω)) s
      = a * mixedCumulant μ (Function.update X i₀ Y) s := by
  classical
  rw [mixedCumulant, mixedCumulant, mobius, mobius, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hi₀P : i₀ ∈ π.part i₀ := (Finpartition.mem_part_self π).mpr hi
  have hsmul : jointMoment μ (Function.update X i₀ (fun ω => a * Y ω)) (π.part i₀)
      = a * jointMoment μ (Function.update X i₀ Y) (π.part i₀) := by
    rw [jointMoment_update_of_mem μ X i₀ _ hi₀P, jointMoment_update_of_mem μ X i₀ Y hi₀P,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    ring
  rw [prod_parts_update μ X hi π, prod_parts_update μ X hi π, hsmul]
  ring

/-- Additivity on the skewed law: `κ (X + X, X) = κ (X, X) + κ (X, X) = 3 + 3 = 6`. -/
theorem skew_multilinear_witness :
    mixedCumulant SkewWitness.skewLaw
        (Function.update (fun _ : Fin 2 => (id : ℝ → ℝ)) 0 (fun x : ℝ => id x + id x))
        (univ : Finset (Fin 2)) = 6 := by
  have hint : ∀ B : Finset (Fin 2),
      Integrable (fun x : ℝ => id x * ∏ i ∈ B.erase 0, (fun _ : Fin 2 => (id : ℝ → ℝ)) i x)
        SkewWitness.skewLaw := fun B => SkewWitness.integrable_skew (by fun_prop)
  rw [mixedCumulant_update_add SkewWitness.skewLaw (fun _ : Fin 2 => (id : ℝ → ℝ))
    (Finset.mem_univ 0) id id hint hint]
  rw [Function.update_eq_self]
  have h2 : mixedCumulant SkewWitness.skewLaw (fun _ : Fin 2 => (id : ℝ → ℝ))
      (univ : Finset (Fin 2)) = 3 := SkewWitness.skew_cumulant_two
  rw [h2]
  norm_num

/-- Homogeneity at `a = 2` on the same configuration, `κ (2X, X) = 2 κ_2 = 6`. -/
theorem skew_multilinear_smul_witness :
    mixedCumulant SkewWitness.skewLaw
        (Function.update (fun _ : Fin 2 => (id : ℝ → ℝ)) 0 (fun x : ℝ => 2 * id x))
        (univ : Finset (Fin 2)) = 6 := by
  rw [mixedCumulant_update_smul SkewWitness.skewLaw (fun _ : Fin 2 => (id : ℝ → ℝ))
    (Finset.mem_univ 0) 2 id, Function.update_eq_self]
  have h2 : mixedCumulant SkewWitness.skewLaw (fun _ : Fin 2 => (id : ℝ → ℝ))
      (univ : Finset (Fin 2)) = 3 := SkewWitness.skew_cumulant_two
  rw [h2]
  norm_num

end Multilinear

end Cumulant

end StatLean.AsymptoticStatistics
