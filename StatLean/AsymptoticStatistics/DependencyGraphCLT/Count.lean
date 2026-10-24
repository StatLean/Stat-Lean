/-
Copyright (c) 2026 Benjamin O. Harrison, Gustavo Canavire Bacarreza, David Jacho-Chavez and
Fernando Rios-Avila.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Jacho-Chávez
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# The connected-subgraph count of Janson's Lemma 4

Let $R$ be a relation on a finite vertex set $V$ in which every vertex is $R$-related to at most
$M + 1$ vertices, and let $t \subseteq V$ have $N$ elements. A *slot family*
$\varphi : \{1, \dots, j\} \to t$ is *connected* for $R$ when its slots cannot be split into two
nonempty parts with no $R$-link across. This file proves that at most
$$ j!\,(j-1)!\,N\,(M+1)^{j-1} $$
slot families of length $j$ are connected. The dependency graph enters only as the abstract
relation `R : V → V → Prop`; no measure or random variable appears.

**Reference.** S. Janson, "Normal convergence by higher semiinvariants with applications to
sums of dependent random variables and random graphs", *Ann. Probab.* **16** (1988), 305–312,
the counting step in the proof of Lemma 4.

**Proof formalization notes.** A connected family is first reordered by a permutation of its
slots (`Janson.exists_search_perm`) so that every slot after the first is $R$-linked to an
earlier one; this is the search order, grown one slot at a time from the connectedness
hypothesis. The reordered sequences are then counted slot by slot: the unfilled slots are set to
a padding value `v₀`, which turns the count into a chain of `Finset` fibre bounds
(`Janson.card_prefixFams_one`, `Janson.card_prefixFams_succ`). The factor $j!$ accounts for the
choice of permutation.

## Main results

* `Janson.exists_search_perm`: a connected family can be reordered so that every slot after the
  first is `R`-linked to an earlier one.
* `Janson.card_prefixFams_le`: the number of such prefix-connected sequences.
* `Janson.card_conn_le`: the connected-subgraph count.
-/

open Finset

namespace StatLean.AsymptoticStatistics.Janson

/-- A slot family `φ : Fin j → V` is **connected** for `R` when the slots cannot be split into
two nonempty parts with no `R`-link across. By Lemma 3 of Janson (1988), a family that is not
connected for a dependency graph has vanishing mixed semiinvariant. -/
def IsConnFam {V : Type*} (R : V → V → Prop) {j : ℕ} (φ : Fin j → V) : Prop :=
  ∀ a : Finset (Fin j), a.Nonempty → aᶜ.Nonempty → ∃ k ∈ a, ∃ l ∈ aᶜ, R (φ k) (φ l)

/-! ### The search order

A connected family can be reordered so that each prefix is connected. The prefix is grown one
slot at a time; connectedness provides a slot outside the prefix linked to one inside it. -/

/-- `e : Fin m → Fin j` enumerates the first `m` slots of the search order; each slot after the
first is `R`-linked to an earlier one. -/
theorem exists_search_injection {V : Type*} {R : V → V → Prop} {j : ℕ} {φ : Fin j → V}
    (hconn : IsConnFam R φ) (hj : 0 < j) :
    ∀ m : ℕ, m ≤ j → ∃ e : Fin m → Fin j, Function.Injective e ∧
      ∀ k : Fin m, 0 < k.val → ∃ l : Fin m, l.val < k.val ∧ R (φ (e l)) (φ (e k)) := by
  classical
  intro m
  induction m with
  | zero => intro _; exact ⟨Fin.elim0, fun a => a.elim0, fun k => k.elim0⟩
  | succ m ih =>
      intro hm
      obtain ⟨e, hinj, hprop⟩ := ih (Nat.le_of_succ_le hm)
      by_cases hm0 : m = 0
      · subst hm0
        refine ⟨fun _ => ⟨0, hj⟩, fun a b _ => ?_, fun k hk => ?_⟩
        · have ha := a.isLt
          have hb := b.isLt
          exact Fin.val_injective (by omega)
        · have hk' := k.isLt
          exact absurd hk (by omega)
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        have hcardS : #(Finset.image e univ) = m := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
        have hSne : (Finset.image e univ).Nonempty := by
          rw [← Finset.card_pos, hcardS]; omega
        have hScne : (Finset.image e univ)ᶜ.Nonempty := by
          rw [← Finset.card_pos, Finset.card_compl, hcardS, Fintype.card_fin]; omega
        obtain ⟨k, hkS, l, hlSc, hRkl⟩ := hconn (Finset.image e univ) hSne hScne
        have hlS : l ∉ Finset.image e univ := by simpa using hlSc
        refine ⟨Fin.snoc e l, ?_, ?_⟩
        · intro a b hab
          rcases Fin.eq_castSucc_or_eq_last a with ⟨p, rfl⟩ | rfl <;>
            rcases Fin.eq_castSucc_or_eq_last b with ⟨q, rfl⟩ | rfl
          · rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hab
            exact congrArg Fin.castSucc (hinj hab)
          · rw [Fin.snoc_castSucc, Fin.snoc_last] at hab
            exact absurd (hab ▸ Finset.mem_image_of_mem e (Finset.mem_univ p)) hlS
          · rw [Fin.snoc_castSucc, Fin.snoc_last] at hab
            exact absurd (hab ▸ Finset.mem_image_of_mem e (Finset.mem_univ q)) hlS
          · rfl
        · intro k' hk'
          rcases Fin.eq_castSucc_or_eq_last k' with ⟨p, rfl⟩ | rfl
          · have hp : 0 < p.val := by simpa using hk'
            obtain ⟨l', hl'lt, hl'R⟩ := hprop p hp
            refine ⟨Fin.castSucc l', by simpa using hl'lt, ?_⟩
            rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
            exact hl'R
          · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hkS
            refine ⟨Fin.castSucc p, by simp, ?_⟩
            rw [Fin.snoc_castSucc, Fin.snoc_last, hp]
            exact hRkl

/-- **The search order**, as a permutation of the slots, after which every slot but the
first is `R`-linked to an earlier one. -/
theorem exists_search_perm {V : Type*} {R : V → V → Prop} {j : ℕ} {φ : Fin j → V}
    (hconn : IsConnFam R φ) (hj : 0 < j) :
    ∃ σ : Equiv.Perm (Fin j), ∀ k : Fin j, 0 < k.val →
      ∃ l : Fin j, l.val < k.val ∧ R (φ (σ l)) (φ (σ k)) := by
  obtain ⟨e, hinj, hprop⟩ := exists_search_injection hconn hj j le_rfl
  refine ⟨Equiv.ofBijective e (Finite.injective_iff_bijective.mp hinj), ?_⟩
  simpa only [Equiv.ofBijective_apply] using hprop

/-! ### The prefix count

The slots are filled left to right; the unfilled ones are set to a padding value `v₀`, which turns
the count into a chain of `Finset` fibre bounds. -/

section Count

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
/-- The families whose first `m` slots are filled from `t`, each after the first linked by `R`
to an earlier slot, and whose remaining slots equal the padding value `v₀`. -/
noncomputable def prefixFams (R : V → V → Prop) (t : Finset V) (v₀ : V) (j m : ℕ) :
    Finset (Fin j → V) :=
  univ.filter (fun ψ : Fin j → V =>
    (∀ k : Fin j, k.val < m → ψ k ∈ t ∧
        (0 < k.val → ∃ l : Fin j, l.val < k.val ∧ R (ψ l) (ψ k)))
      ∧ ∀ k : Fin j, m ≤ k.val → ψ k = v₀)

lemma mem_prefixFams {R : V → V → Prop} {t : Finset V} {v₀ : V} {j m : ℕ} {ψ : Fin j → V} :
    ψ ∈ prefixFams R t v₀ j m ↔
      ((∀ k : Fin j, k.val < m → ψ k ∈ t ∧
          (0 < k.val → ∃ l : Fin j, l.val < k.val ∧ R (ψ l) (ψ k)))
        ∧ ∀ k : Fin j, m ≤ k.val → ψ k = v₀) := by
  classical
  simp [prefixFams]

/-- The first slot may be chosen in `N = #t` ways. -/
lemma card_prefixFams_one (R : V → V → Prop) (t : Finset V) (v₀ : V) {j : ℕ} (hj : 0 < j) :
    #(prefixFams R t v₀ j 1) ≤ #t := by
  classical
  have hsub : prefixFams R t v₀ j 1
      ⊆ t.image (fun v => Function.update (fun _ : Fin j => v₀) ⟨0, hj⟩ v) := by
    intro ψ hψ
    rw [mem_prefixFams] at hψ
    obtain ⟨h1, h2⟩ := hψ
    have h0 : ψ ⟨0, hj⟩ ∈ t := (h1 ⟨0, hj⟩ (by simp)).1
    refine Finset.mem_image.mpr ⟨ψ ⟨0, hj⟩, h0, ?_⟩
    funext k
    rcases eq_or_ne k (⟨0, hj⟩ : Fin j) with rfl | hne
    · simp
    · have hkpos : 1 ≤ k.val := by
        rcases Nat.eq_zero_or_pos k.val with h | h
        · exact absurd (Fin.val_injective (by simpa using h)) hne
        · exact h
      rw [Function.update_of_ne hne]
      exact (h2 k hkpos).symm
  calc #(prefixFams R t v₀ j 1) ≤ #(t.image _) := Finset.card_le_card hsub
    _ ≤ #t := Finset.card_image_le

/-- Filling the `(m+1)`-st slot: at most `m (M+1)` choices, since it must be `R`-linked to one
of the `m` slots already filled. -/
lemma card_prefixFams_succ (R : V → V → Prop) (t : Finset V) (v₀ : V) {j m M : ℕ}
    (hm : 0 < m) (hmj : m < j)
    (hdeg : ∀ x : V, ∀ S : Finset V, (∀ y ∈ S, R x y) → #S ≤ M + 1) :
    #(prefixFams R t v₀ j (m + 1)) ≤ (m * (M + 1)) * #(prefixFams R t v₀ j m) := by
  classical
  set i₀ : Fin j := ⟨m, hmj⟩ with hi₀
  set f : (Fin j → V) → (Fin j → V) := fun ψ => Function.update ψ i₀ v₀ with hf
  have hfapp : ∀ (ψ : Fin j → V) (k : Fin j), f ψ k = Function.update ψ i₀ v₀ k :=
    fun _ _ => rfl
  have hne_of_lt : ∀ k : Fin j, k.val < m → k ≠ i₀ := by
    intro k hk hc
    rw [hc] at hk
    exact absurd hk (by simp [hi₀])
  have himg : (prefixFams R t v₀ j (m + 1)).image f ⊆ prefixFams R t v₀ j m := by
    intro χ hχ
    obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp hχ
    rw [mem_prefixFams] at hψ ⊢
    obtain ⟨h1, h2⟩ := hψ
    constructor
    · intro k hk
      have hkne : k ≠ i₀ := hne_of_lt k hk
      obtain ⟨hkt, hklink⟩ := h1 k (by omega)
      refine ⟨by rwa [hfapp, Function.update_of_ne hkne], fun hkpos => ?_⟩
      obtain ⟨l, hl, hR⟩ := hklink hkpos
      have hlne : l ≠ i₀ := hne_of_lt l (by omega)
      exact ⟨l, hl, by rwa [hfapp, hfapp, Function.update_of_ne hlne,
        Function.update_of_ne hkne]⟩
    · intro k hk
      rcases eq_or_lt_of_le hk with heq | hlt
      · have hki : k = i₀ := Fin.val_injective (by simp [hi₀, heq])
        rw [hfapp, hki, Function.update_self]
      · have hkne : k ≠ i₀ := by
          intro hc
          rw [hc] at hlt
          exact absurd hlt (by simp [hi₀])
        rw [hfapp, Function.update_of_ne hkne]
        exact h2 k (by omega)
  have hfib : ∀ χ ∈ (prefixFams R t v₀ j (m + 1)).image f,
      #({ψ ∈ prefixFams R t v₀ j (m + 1) | f ψ = χ}) ≤ m * (M + 1) := by
    intro χ _
    set early : Finset (Fin j) := univ.filter (fun l : Fin j => l.val < m) with hearly
    set cand : Finset V := early.biUnion (fun l => univ.filter (fun y => R (χ l) y)) with hcand
    have hcard_early : #early ≤ m := by
      have hsubr : early.image (Fin.val) ⊆ Finset.range m := by
        intro r hr
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hr
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hl).2
      calc #early = #(early.image (Fin.val)) :=
            (Finset.card_image_of_injective _ Fin.val_injective).symm
        _ ≤ #(Finset.range m) := Finset.card_le_card hsubr
        _ = m := Finset.card_range m
    have hcard_cand : #cand ≤ m * (M + 1) := by
      calc #cand ≤ ∑ l ∈ early, #(univ.filter (fun y => R (χ l) y)) := Finset.card_biUnion_le
        _ ≤ ∑ _l ∈ early, (M + 1) :=
            Finset.sum_le_sum fun l _ =>
              hdeg (χ l) _ fun y hy => (Finset.mem_filter.mp hy).2
        _ = #early * (M + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ m * (M + 1) := Nat.mul_le_mul_right _ hcard_early
    have hsub : {ψ ∈ prefixFams R t v₀ j (m + 1) | f ψ = χ}
        ⊆ cand.image (fun v => Function.update χ i₀ v) := by
      intro ψ hψ
      rw [Finset.mem_filter] at hψ
      obtain ⟨hψmem, hψeq⟩ := hψ
      rw [mem_prefixFams] at hψmem
      obtain ⟨h1, _⟩ := hψmem
      have hoff : ∀ k : Fin j, k ≠ i₀ → χ k = ψ k := by
        intro k hk
        rw [← hψeq, hfapp, Function.update_of_ne hk]
      obtain ⟨hmem, hlink⟩ := h1 i₀ (by simp [hi₀])
      obtain ⟨l, hl, hR⟩ := hlink (by simp [hi₀, hm])
      have hlm : l.val < m := by simpa [hi₀] using hl
      have hlne : l ≠ i₀ := hne_of_lt l hlm
      refine Finset.mem_image.mpr ⟨ψ i₀, ?_, ?_⟩
      · exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlm⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hoff l hlne]⟩⟩
      · funext k
        rcases eq_or_ne k i₀ with rfl | hkne
        · simp
        · rw [Function.update_of_ne hkne, hoff k hkne]
    calc #({ψ ∈ prefixFams R t v₀ j (m + 1) | f ψ = χ}) ≤ #(cand.image _) :=
          Finset.card_le_card hsub
      _ ≤ #cand := Finset.card_image_le
      _ ≤ m * (M + 1) := hcard_cand
  calc #(prefixFams R t v₀ j (m + 1))
      ≤ (m * (M + 1)) * #((prefixFams R t v₀ j (m + 1)).image f) :=
        Finset.card_le_mul_card_image _ _ hfib
    _ ≤ (m * (M + 1)) * #(prefixFams R t v₀ j m) :=
        Nat.mul_le_mul_left _ (Finset.card_le_card himg)

/-- **The prefix count.** At most `N (m-1)! (M+1)^{m-1}` prefix-connected sequences. -/
lemma card_prefixFams_le (R : V → V → Prop) (t : Finset V) (v₀ : V) {j M : ℕ} (hj : 0 < j)
    (hdeg : ∀ x : V, ∀ S : Finset V, (∀ y ∈ S, R x y) → #S ≤ M + 1) :
    ∀ m : ℕ, 0 < m → m ≤ j →
      #(prefixFams R t v₀ j m) ≤ #t * (Nat.factorial (m - 1) * (M + 1) ^ (m - 1)) := by
  intro m
  induction m with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
      intro _ hmj
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · simpa using card_prefixFams_one R t v₀ hj
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have hstep : #(prefixFams R t v₀ j (m' + 1 + 1))
            ≤ ((m' + 1) * (M + 1)) * #(prefixFams R t v₀ j (m' + 1)) :=
          card_prefixFams_succ (j := j) R t v₀ (Nat.succ_pos m') (by omega) hdeg
        have hih : #(prefixFams R t v₀ j (m' + 1))
            ≤ #t * (Nat.factorial m' * (M + 1) ^ m') := by
          simpa using ih (Nat.succ_pos m') (by omega)
        have hred : m' + 1 + 1 - 1 = m' + 1 := by omega
        rw [hred]
        calc #(prefixFams R t v₀ j (m' + 1 + 1))
            ≤ ((m' + 1) * (M + 1)) * #(prefixFams R t v₀ j (m' + 1)) := hstep
          _ ≤ ((m' + 1) * (M + 1)) * (#t * (Nat.factorial m' * (M + 1) ^ m')) :=
              Nat.mul_le_mul_left _ hih
          _ = #t * (Nat.factorial (m' + 1) * (M + 1) ^ (m' + 1)) := by
              rw [Nat.factorial_succ, pow_succ]; ring

end Count

/-- **Janson's connected-subgraph count.** At most `j! (j-1)! N (M+1)^{j-1}` slot families
`φ : Fin j → V` take their values in `t` and are connected for `R`, where `N = #t` and `hdeg`
bounds every set of `R`-neighbours of a vertex by `M + 1`. -/
theorem card_conn_le {V : Type*} [Finite V] {R : V → V → Prop} (t : Finset V) {M : ℕ}
    (hdeg : ∀ x : V, ∀ S : Finset V, (∀ y ∈ S, R x y) → #S ≤ M + 1)
    {j : ℕ} (hj : 0 < j) (C : Finset (Fin j → V))
    (hC : ∀ φ ∈ C, (∀ k, φ k ∈ t) ∧ IsConnFam R φ) :
    #C ≤ Nat.factorial j * (#t * (Nat.factorial (j - 1) * (M + 1) ^ (j - 1))) := by
  classical
  have := Fintype.ofFinite V
  rcases t.eq_empty_or_nonempty with rfl | ⟨v₀, hv₀⟩
  · have hsub0 : C ⊆ (∅ : Finset (Fin j → V)) := fun φ hφ =>
      absurd ((hC φ hφ).1 ⟨0, hj⟩) (by simp)
    have hzero : #C = 0 := Nat.le_zero.mp (by simpa using Finset.card_le_card hsub0)
    simp [hzero]
  · have hsub : C ⊆ (univ : Finset (Equiv.Perm (Fin j))).biUnion
        (fun τ => (prefixFams R t v₀ j j).image (fun ψ => fun k => ψ (τ k))) := by
      intro φ hφ
      obtain ⟨hφt, hconn⟩ := hC φ hφ
      obtain ⟨σ, hσ⟩ := exists_search_perm hconn hj
      refine Finset.mem_biUnion.mpr ⟨σ.symm, Finset.mem_univ _, ?_⟩
      refine Finset.mem_image.mpr ⟨fun k => φ (σ k), ?_, ?_⟩
      · rw [mem_prefixFams]
        exact ⟨fun k _ => ⟨hφt _, fun hk => hσ k hk⟩,
          fun k hk => absurd k.isLt (by omega)⟩
      · funext k
        simp
    calc #C ≤ #((univ : Finset (Equiv.Perm (Fin j))).biUnion
            (fun τ => (prefixFams R t v₀ j j).image (fun ψ => fun k => ψ (τ k)))) :=
          Finset.card_le_card hsub
      _ ≤ ∑ τ ∈ (univ : Finset (Equiv.Perm (Fin j))),
            #((prefixFams R t v₀ j j).image (fun ψ => fun k => ψ (τ k))) :=
          Finset.card_biUnion_le
      _ ≤ ∑ _τ ∈ (univ : Finset (Equiv.Perm (Fin j))), #(prefixFams R t v₀ j j) :=
          Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ = #(univ : Finset (Equiv.Perm (Fin j))) * #(prefixFams R t v₀ j j) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = Nat.factorial j * #(prefixFams R t v₀ j j) := by
          rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      _ ≤ Nat.factorial j * (#t * (Nat.factorial (j - 1) * (M + 1) ^ (j - 1))) :=
          Nat.mul_le_mul_left _ (card_prefixFams_le R t v₀ hj hdeg j hj le_rfl)

end StatLean.AsymptoticStatistics.Janson
