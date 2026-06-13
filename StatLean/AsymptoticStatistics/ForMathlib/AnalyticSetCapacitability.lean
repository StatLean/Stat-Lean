import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Choquet capacitability for analytic sets in Polish spaces

This file develops the Choquet inner-approximation machinery used to show that any
analytic subset of a Polish space `β` is `NullMeasurableSet` for any s-finite Borel
measure `m` on `β`. The substantive content is a cylinder-tree construction on
`(ℕ → ℕ)` (Bertsekas-Shreve App.III.A / Kechris §29) supporting the Choquet
inner-approximation step: for any analytic `A` and finite `m`, there is a compact
`K ⊆ A` with `m(A \ K) ≤ ε`.

Headline declarations: `cylinder_tree_compact_iInter`, `konig_chain_of_compat`,
`cylinder_tree_range_diff_image_subset`, `cylinder_tree_mass_bound`.
-/

namespace MeasureTheory

open Set Filter Topology
open scoped ENNReal

/-!
### Inner approximation on a finite measure (the substantive Choquet step)
-/

/-! ### Cylinder-tree construction

The Bertsekas-Shreve App.III.A / Kechris §29 construction on `(ℕ → ℕ)` is
organized into atomic sub-lemmas:

1. `cylinder_tree_compact_iInter` — given compatible finite per-level
   cylinder choices `S_n ⊆ (Fin n → ℕ)`, the intersection
   `Q := ⋂_n ⋃_{σ ∈ S_n} cylinder_σ` is compact in `(ℕ → ℕ)`.

2. `cylinder_tree_mass_bound` — given compatible per-level mass bounds, the
   `f`-image of `Q` covers `range f` modulo `ε` in `m`-measure.

Each sub-lemma is a self-contained piece of the proof; the outer wrapper
composes them. -/
/-- **Cylinder-tree compactness**.

Given a compatible sequence of finite per-level cylinder sets
`S_n ⊆ (Fin n → ℕ)`, the intersection
`Q := ⋂_n ⋃_{σ ∈ S n} { α | ∀ i : Fin n, α i.val = σ i }`
is compact in `(ℕ → ℕ)` with the product topology.

**Proof idea**: `Q` is closed (intersection of finite unions of clopen
cylinders); at each coordinate `k`, the values that can occur in `Q` are
limited to those appearing in some `σ ∈ S (k+1)`, hence finite; the
infinite product of finite discrete sets is compact (Tychonoff).
Compatibility ensures the per-coordinate finite bounds are inherited
consistently across levels. -/
private theorem cylinder_tree_compact_iInter
    (S : ∀ n : ℕ, Finset (Fin n → ℕ))
    (_hS_compat : ∀ n : ℕ, ∀ σ ∈ S (n + 1),
      (fun i : Fin n => σ i.castSucc) ∈ S n) :
    IsCompact
      (⋂ n : ℕ, ⋃ σ ∈ S n, { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i }) := by
  classical
  -- Abbreviate the cylinder set and its level-`n` union.
  set C : ∀ n : ℕ, (Fin n → ℕ) → Set (ℕ → ℕ) :=
    fun n σ => { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i }
  set U : ℕ → Set (ℕ → ℕ) := fun n => ⋃ σ ∈ S n, C n σ
  set Q : Set (ℕ → ℕ) := ⋂ n : ℕ, U n
  -- Step 1. Each cylinder `C n σ` is closed: it's the intersection over
  -- `i : Fin n` of preimages of singletons under the continuous projections
  -- `α ↦ α i.val`. Singletons in `ℕ` (discrete) are closed.
  have hC_closed : ∀ n : ℕ, ∀ σ : Fin n → ℕ, IsClosed (C n σ) := by
    intro n σ
    have : C n σ = ⋂ i : Fin n, (fun α : ℕ → ℕ => α i.val) ⁻¹' {σ i} := by
      ext α; simp [C, Set.mem_iInter]
    rw [this]
    refine isClosed_iInter (fun i => ?_)
    exact (isClosed_singleton).preimage (continuous_apply _)
  -- Step 2. Each `U n = ⋃ σ ∈ S n, C n σ` is closed (finite union of closed).
  have hU_closed : ∀ n : ℕ, IsClosed (U n) := by
    intro n
    exact isClosed_biUnion_finset (fun σ _ => hC_closed n σ)
  -- Step 3. `Q` is closed (intersection of closed).
  have hQ_closed : IsClosed Q := isClosed_iInter hU_closed
  -- Step 4. For each coordinate `k : ℕ`, the set `F k` of possible values
  -- `α k` for `α ∈ Q` is a *finite* subset of `ℕ` — take `k`-th coordinate
  -- of every `σ ∈ S (k+1)`.
  let F : ℕ → Set ℕ := fun k =>
    ((S (k + 1)).image (fun σ : Fin (k + 1) → ℕ => σ ⟨k, Nat.lt_succ_self k⟩) : Set ℕ)
  have hF_finite : ∀ k : ℕ, (F k).Finite := fun k => (Finset.image _ _).finite_toSet
  -- Step 5. `Q ⊆ Set.univ.pi F`: for `α ∈ Q` and any coordinate `k`, the
  -- level-`(k+1)` membership `α ∈ U (k+1)` exhibits some `σ ∈ S (k+1)`
  -- with `α k = σ ⟨k, _⟩ ∈ F k`.
  have hQ_sub : Q ⊆ Set.univ.pi F := by
    intro α hα k _hk
    have hαU : α ∈ U (k + 1) := Set.mem_iInter.mp hα (k + 1)
    -- Unpack the finite biUnion.
    rcases Set.mem_iUnion₂.mp hαU with ⟨σ, hσS, hσC⟩
    have hαk : α k = σ ⟨k, Nat.lt_succ_self k⟩ := hσC ⟨k, Nat.lt_succ_self k⟩
    -- Hence `α k ∈ F k`.
    refine (Finset.mem_coe).mpr (Finset.mem_image.mpr ⟨σ, hσS, ?_⟩)
    exact hαk.symm
  -- Step 6. `Set.univ.pi F` is compact (Tychonoff of finite sets).
  have hF_compact : ∀ k : ℕ, IsCompact (F k) := fun k => (hF_finite k).isCompact
  have hPi_compact : IsCompact (Set.univ.pi F) := isCompact_univ_pi hF_compact
  -- Step 7. `Q` is closed and contained in a compact set ⇒ `Q` is compact.
  exact hPi_compact.of_isClosed_subset hQ_closed hQ_sub

/-- **König's lemma for ℕ-indexed finitely-branching trees of `Fin n → ℕ` labels.**

A private helper for `cylinder_tree_range_diff_image_subset`. Given a sequence
of nonempty finite sets `G n ⊆ (Fin n → ℕ)` such that the prefix-restriction
`τ ↦ τ ∘ Fin.castSucc` maps `G (n+1)` into `G n`, there exists an infinite
branch `α : ℕ → ℕ` whose first `n` coordinates lie in `G n` for every `n`.

This is the standard König lemma specialised to label trees on `ℕ`. The proof
uses the pigeonhole argument: at each level the "good ancestors" — labels with
descendants at arbitrarily large depths — form a nonempty downward-closed
sub-tree, from which we extract the branch by dependent choice. -/
private theorem konig_chain_of_compat
    (G : ∀ n : ℕ, Finset (Fin n → ℕ))
    (hG_nonempty : ∀ n : ℕ, (G n).Nonempty)
    (hG_compat : ∀ n : ℕ, ∀ τ ∈ G (n + 1),
      (fun i : Fin n => τ i.castSucc) ∈ G n) :
    ∃ α : ℕ → ℕ, ∀ n : ℕ, (fun i : Fin n => α i.val) ∈ G n := by
  classical
  -- Restriction operator: for `n ≤ m`, restrict a label at level m down to level n.
  let restr : ∀ {n m : ℕ}, n ≤ m → (Fin m → ℕ) → (Fin n → ℕ) :=
    fun {n m} h τ i => τ ⟨i.val, lt_of_lt_of_le i.isLt h⟩
  -- Iterated compatibility: for `n ≤ m`, `restr h τ ∈ G n` whenever `τ ∈ G m`.
  have hG_compat_le : ∀ n m (h : n ≤ m), ∀ τ ∈ G m, restr h τ ∈ G n := by
    intro n m h
    induction h with
    | refl =>
        intro τ hτ
        -- restr (le_refl n) τ = τ.
        have : restr (le_refl n) τ = τ := by
          funext i; rfl
        rw [this]; exact hτ
    | @step m hnm ih =>
        intro τ hτ
        -- Step from level m+1 down to level m via hG_compat.
        have hrestr_succ : (fun i : Fin m => τ i.castSucc) ∈ G m := hG_compat m τ hτ
        have hih := ih (fun i : Fin m => τ i.castSucc) hrestr_succ
        -- restr (le_succ_of_le hnm) τ equals restr hnm (τ ∘ Fin.castSucc), by defeq.
        exact hih
  -- "Good" labels at level n: have descendants at arbitrarily large levels.
  let Good : ∀ n : ℕ, Finset (Fin n → ℕ) :=
    fun n => (G n).filter (fun σ => ∀ m, ∀ (h : n ≤ m), ∃ τ ∈ G m, restr h τ = σ)
  -- Step 1: `Good n` is nonempty for every `n`.
  have hGood_nonempty : ∀ n : ℕ, (Good n).Nonempty := by
    intro n
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    -- For each σ ∈ G n, σ ∉ Good n ⟹ ∃ m ≥ n, no descendant.
    have hexists_bad : ∀ σ ∈ G n, ∃ m, ∃ (h : n ≤ m), ∀ τ ∈ G m, restr h τ ≠ σ := by
      intro σ hσ
      have hσnot : σ ∉ Good n := by rw [hempty]; exact Finset.notMem_empty σ
      have : ¬ ∀ m, ∀ (h : n ≤ m), ∃ τ ∈ G m, restr h τ = σ := by
        intro hcontra
        exact hσnot (Finset.mem_filter.mpr ⟨hσ, hcontra⟩)
      push Not at this
      obtain ⟨m, h, hbad⟩ := this
      exact ⟨m, h, hbad⟩
    -- Choose the bad witness m_σ for each σ ∈ G n.
    choose mσ hmσn hmσ_bad using hexists_bad
    -- Take the max over the (finite) attached set of G n.
    let M : ℕ := (G n).attach.sup (fun σ => mσ σ.1 σ.2)
    have hM_ge_n : n ≤ M := by
      obtain ⟨σ₀, hσ₀⟩ := hG_nonempty n
      have : (⟨σ₀, hσ₀⟩ : { σ // σ ∈ G n }) ∈ (G n).attach := Finset.mem_attach _ _
      have hmσ₀_le : mσ σ₀ hσ₀ ≤ M :=
        Finset.le_sup (f := fun σ : { σ // σ ∈ G n } => mσ σ.1 σ.2) this
      exact (hmσn σ₀ hσ₀).trans hmσ₀_le
    -- Pick any τ ∈ G M (nonempty by hG_nonempty).
    obtain ⟨τM, hτM⟩ := hG_nonempty M
    -- restr-down-to-n gives σ ∈ G n.
    let σ : Fin n → ℕ := restr hM_ge_n τM
    have hσ_mem : σ ∈ G n := hG_compat_le n M hM_ge_n τM hτM
    -- m_σ ≤ M, so restr τ to level m_σ is in G m_σ, and it restricts down to σ at level n.
    have hmσM : mσ σ hσ_mem ≤ M := by
      have : (⟨σ, hσ_mem⟩ : { τ // τ ∈ G n }) ∈ (G n).attach := Finset.mem_attach _ _
      exact Finset.le_sup (f := fun σ : { σ // σ ∈ G n } => mσ σ.1 σ.2) this
    -- Let τ' := restr to level m_σ.
    let τ' : Fin (mσ σ hσ_mem) → ℕ := restr hmσM τM
    have hτ'_mem : τ' ∈ G (mσ σ hσ_mem) := hG_compat_le (mσ σ hσ_mem) M hmσM τM hτM
    -- (restr (hmσn σ hσ_mem) τ' = σ) by composition of restrictions.
    have hτ'_restr : restr (hmσn σ hσ_mem) τ' = σ := by
      funext i; rfl
    -- This contradicts hmσ_bad σ hσ_mem.
    exact hmσ_bad σ hσ_mem τ' hτ'_mem hτ'_restr
  -- Step 2: Good is "extendable": ∀ σ ∈ Good n, ∃ τ ∈ Good (n+1), restr hn1 τ = σ.
  have hGood_extend : ∀ n : ℕ, ∀ σ ∈ Good n,
      ∃ τ ∈ Good (n + 1), (fun i : Fin n => τ i.castSucc) = σ := by
    intro n σ hσ
    rw [Finset.mem_filter] at hσ
    obtain ⟨hσG, hσ_desc⟩ := hσ
    -- Candidates: extensions τ ∈ G (n+1) with restr_to_n τ = σ.
    let Cand : Finset (Fin (n + 1) → ℕ) :=
      (G (n + 1)).filter (fun τ => (fun i : Fin n => τ i.castSucc) = σ)
    -- Cand nonempty (use σ_desc at m := n+1).
    have hCand_nonempty : Cand.Nonempty := by
      obtain ⟨τ, hτG, hτrestr⟩ := hσ_desc (n + 1) (Nat.le_succ n)
      refine ⟨τ, Finset.mem_filter.mpr ⟨hτG, ?_⟩⟩
      -- restr (Nat.le_succ n) τ unfolds to fun i : Fin n => τ ⟨i.val, _⟩,
      -- which equals fun i : Fin n => τ i.castSucc by Fin.val_castSucc.
      have : restr (Nat.le_succ n) τ = (fun i : Fin n => τ i.castSucc) := by
        funext i
        rfl
      rw [← this]; exact hτrestr
    -- Either there's a τ ∈ Cand which is itself in Good (n+1), or we derive contradiction.
    by_contra hno_ext
    push Not at hno_ext
    have hCand_no_good : ∀ τ ∈ Cand, τ ∉ Good (n + 1) := by
      intro τ hτC
      rw [Finset.mem_filter] at hτC
      intro hτGood
      exact hno_ext τ hτGood hτC.2
    -- Each τ ∈ Cand fails to be a "good ancestor" at level n+1.
    have hCand_bad : ∀ τ ∈ Cand, ∃ m, ∃ (h : n + 1 ≤ m), ∀ τ' ∈ G m,
        restr h τ' ≠ τ := by
      intro τ hτC
      have hτG : τ ∈ G (n + 1) := (Finset.mem_filter.mp hτC).1
      have hτnotGood : τ ∉ Good (n + 1) := hCand_no_good τ hτC
      rw [Finset.mem_filter] at hτnotGood
      push Not at hτnotGood
      have := hτnotGood hτG
      obtain ⟨m, h, hbad⟩ := this
      exact ⟨m, h, hbad⟩
    -- Pick a max m over the (finite) attached Cand.
    choose mτ hmτn hmτ_bad using hCand_bad
    let M' : ℕ := Cand.attach.sup (fun τ => mτ τ.1 τ.2)
    have hM'_ge : n + 1 ≤ M' := by
      obtain ⟨τ₀, hτ₀⟩ := hCand_nonempty
      have : (⟨τ₀, hτ₀⟩ : { τ // τ ∈ Cand }) ∈ Cand.attach := Finset.mem_attach _ _
      have hle : mτ τ₀ hτ₀ ≤ M' :=
        Finset.le_sup (f := fun τ : { τ // τ ∈ Cand } => mτ τ.1 τ.2) this
      exact (hmτn τ₀ hτ₀).trans hle
    -- Use σ_desc at level M' to get τM' ∈ G M' restricting to σ at level n.
    have hn_le_M' : n ≤ M' := (Nat.le_succ n).trans hM'_ge
    obtain ⟨τM', hτM'G, hτM'_restr⟩ := hσ_desc M' hn_le_M'
    -- Restrict τM' to level n+1.
    let τ' : Fin (n + 1) → ℕ := restr hM'_ge τM'
    have hτ'_mem : τ' ∈ G (n + 1) := hG_compat_le (n + 1) M' hM'_ge τM' hτM'G
    -- τ' ∈ Cand: it restricts to σ at level n.
    have hτ'_Cand : τ' ∈ Cand := by
      refine Finset.mem_filter.mpr ⟨hτ'_mem, ?_⟩
      have heq : (fun i : Fin n => τ' i.castSucc) = restr hn_le_M' τM' := by
        funext i; rfl
      rw [heq]
      exact hτM'_restr
    -- Now mτ τ' hτ'_Cand ≤ M', use hmτ_bad with the further-restricted ancestor.
    have hmτ'M' : mτ τ' hτ'_Cand ≤ M' := by
      have : (⟨τ', hτ'_Cand⟩ : { τ // τ ∈ Cand }) ∈ Cand.attach := Finset.mem_attach _ _
      exact Finset.le_sup (f := fun τ : { τ // τ ∈ Cand } => mτ τ.1 τ.2) this
    -- restr τM' to level mτ τ' is in G _ and restricts further to τ'.
    let τ'' : Fin (mτ τ' hτ'_Cand) → ℕ := restr hmτ'M' τM'
    have hτ''_mem : τ'' ∈ G (mτ τ' hτ'_Cand) :=
      hG_compat_le (mτ τ' hτ'_Cand) M' hmτ'M' τM' hτM'G
    have hτ''_restr : restr (hmτn τ' hτ'_Cand) τ'' = τ' := by
      funext i; rfl
    exact hmτ_bad τ' hτ'_Cand τ'' hτ''_mem hτ''_restr
  -- Step 3: extract the chain via dependent choice.
  -- We build `chain n : Good n` such that `chain (n+1) ∘ Fin.castSucc = chain n`.
  let chain : ∀ n : ℕ, { σ : Fin n → ℕ // σ ∈ Good n } := by
    intro n
    induction n with
    | zero => exact ⟨(hGood_nonempty 0).choose, (hGood_nonempty 0).choose_spec⟩
    | succ k ih =>
        obtain ⟨σ, hσ⟩ := ih
        have h := hGood_extend k σ hσ
        exact ⟨h.choose, h.choose_spec.1⟩
  -- Compatibility of the chain.
  have hchain_compat : ∀ n : ℕ,
      (fun i : Fin n => (chain (n + 1)).1 i.castSucc) = (chain n).1 := by
    intro n
    -- chain (n+1) is defined as h.choose where h := hGood_extend n (chain n).1 (chain n).2.
    -- h.choose_spec.2 is the equality we need.
    exact (hGood_extend n (chain n).1 (chain n).2).choose_spec.2
  -- Define α from the chain: α k := (chain (k+1)).1 ⟨k, lt⟩.
  let α : ℕ → ℕ := fun k => (chain (k + 1)).1 ⟨k, Nat.lt_succ_self k⟩
  -- Key lemma: for any k < n, (chain (k+1)).1 ⟨k, _⟩ = (chain n).1 ⟨k, hk⟩.
  -- I.e., the chain is consistent across levels.
  have hchain_pointwise : ∀ k n, ∀ (hk : k < n),
      (chain (k + 1)).1 ⟨k, Nat.lt_succ_self k⟩ = (chain n).1 ⟨k, hk⟩ := by
    intro k n hk
    have hkn : k + 1 ≤ n := hk
    -- Auxiliary helper: prove via Nat.le_induction.
    suffices h : ∀ j, ∀ (hj : k + 1 ≤ j),
        (chain (k + 1)).1 ⟨k, Nat.lt_succ_self k⟩ =
          (chain j).1 ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hj⟩ from h n hkn
    intro j hj
    induction hj with
    | refl => rfl
    | @step m hkm ih =>
        rw [ih]
        have := congrFun (hchain_compat m) ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hkm⟩
        simp only [Fin.castSucc_mk] at this
        exact this.symm
  refine ⟨α, ?_⟩
  intro n
  -- Show: (fun i : Fin n => α i.val) ∈ G n.
  -- α(i.val) = (chain (i.val + 1)).1 ⟨i.val, _⟩. By iterated compatibility, this equals
  -- (chain n).1 i.
  suffices h : (fun i : Fin n => α i.val) = (chain n).1 by
    rw [h]; exact Finset.mem_filter.mp (chain n).2 |>.1
  funext i
  -- α i.val = (chain (i.val + 1)).1 ⟨i.val, _⟩ = (chain n).1 ⟨i.val, i.isLt⟩ = (chain n).1 i.
  change (chain (i.val + 1)).1 ⟨i.val, Nat.lt_succ_self i.val⟩ = (chain n).1 i
  exact hchain_pointwise i.val n i.isLt

/-- **König's-lemma inclusion for the cylinder tree**.

For a continuous `f : (ℕ → ℕ) → β` and compatible cylinder choices `S_n`,
the complement of the image of `Q = ⋂_n ⋃_{σ ∈ S_n} N_σ` is contained in
the union of the per-level complements:

`range f \ f '' Q ⊆ ⋃_n (range f \ V_n)` where `V_n = ⋃_{σ ∈ S_n} f '' N_σ`.

**Proof outline (König's lemma)**: Given `y ∈ range f \ f '' Q`, suppose by
contradiction `y ∈ V_n` for every `n`. For each `n`, the set of "good"
labels `G_n := {σ ∈ S_n | y ∈ f '' N_σ}` is finite and nonempty. By
compatibility, the family `⋃_n G_n` is a finitely-branching infinite tree
under prefix-restriction (`τ ∈ G_{n+1} ⟹ τ|_n ∈ G_n` since
`N_τ ⊆ N_{τ|_n}` and compatibility lands `τ|_n` in `S_n`). König's lemma
(`konig_chain_of_compat`) yields a coordinate sequence `α : ℕ → ℕ` with
`α|_n ∈ G_n` for every `n`, hence `α ∈ Q`. By continuity of `f`, choosing
witnesses `β_n ∈ N_{α|_n}` with `f(β_n) = y` gives `β_n → α` (they agree on
the first `n` coordinates), so `f(α) = y`. Thus `y ∈ f '' Q`, contradiction. -/
private theorem cylinder_tree_range_diff_image_subset
    {β : Type*} [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β]
    (f : (ℕ → ℕ) → β) (_hf_cont : Continuous f)
    (S : ∀ n : ℕ, Finset (Fin n → ℕ))
    (_hS_compat : ∀ n : ℕ, ∀ σ ∈ S (n + 1),
      (fun i : Fin n => σ i.castSucc) ∈ S n) :
    (Set.range f \ f ''
        (⋂ n : ℕ, ⋃ σ ∈ S n, { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i }))
      ⊆ ⋃ n : ℕ, (Set.range f \
        ⋃ σ ∈ S n, f '' { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i }) := by
  classical
  intro y hy
  obtain ⟨hyRange, hynotImage⟩ := hy
  -- Proof by contradiction: suppose y ∉ ⋃_n (range f \ V_n).
  by_contra hno
  -- Derive: for every n, y ∈ V_n (since y ∈ range f).
  have hyVn : ∀ n : ℕ,
      y ∈ ⋃ σ ∈ S n, f '' { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i } := by
    intro n
    by_contra hyV
    apply hno
    exact Set.mem_iUnion.mpr ⟨n, hyRange, hyV⟩
  -- Define G n := {σ ∈ S n | y ∈ f '' N_σ}.
  let G : ∀ n : ℕ, Finset (Fin n → ℕ) :=
    fun n => (S n).filter (fun σ => y ∈ f '' { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i })
  have hG_nonempty : ∀ n : ℕ, (G n).Nonempty := by
    intro n
    rcases Set.mem_iUnion₂.mp (hyVn n) with ⟨σ, hσS, hyImg⟩
    refine ⟨σ, ?_⟩
    exact Finset.mem_filter.mpr ⟨hσS, hyImg⟩
  have hG_compat : ∀ n : ℕ, ∀ τ ∈ G (n + 1),
      (fun i : Fin n => τ i.castSucc) ∈ G n := by
    intro n τ hτG
    rw [Finset.mem_filter] at hτG
    obtain ⟨hτS, hyImg⟩ := hτG
    refine Finset.mem_filter.mpr ⟨_hS_compat n τ hτS, ?_⟩
    -- y ∈ f '' N_τ implies y ∈ f '' N_{τ ∘ Fin.castSucc}.
    obtain ⟨α, hα_mem, hα_eq⟩ := hyImg
    refine ⟨α, ?_, hα_eq⟩
    intro i
    -- α (i.val) = τ (i.castSucc) by hα_mem i.castSucc and Fin.val_castSucc.
    have := hα_mem i.castSucc
    simpa [Fin.val_castSucc] using this
  -- Apply König's lemma.
  obtain ⟨α, hα⟩ := konig_chain_of_compat G hG_nonempty hG_compat
  -- α ∈ Q (the big intersection).
  have hα_in_Q :
      α ∈ ⋂ n : ℕ, ⋃ σ ∈ S n, { β : ℕ → ℕ | ∀ i : Fin n, β i.val = σ i } := by
    rw [Set.mem_iInter]
    intro n
    have hαn : (fun i : Fin n => α i.val) ∈ G n := hα n
    rw [Finset.mem_filter] at hαn
    obtain ⟨hσS, _⟩ := hαn
    refine Set.mem_iUnion₂.mpr ⟨(fun i : Fin n => α i.val), hσS, ?_⟩
    intro i; rfl
  -- For each n, pick a witness β n ∈ N_{α|_n} with f(β n) = y.
  have hwitness : ∀ n : ℕ, ∃ β : ℕ → ℕ,
      (∀ i : Fin n, β i.val = α i.val) ∧ f β = y := by
    intro n
    have hαn : (fun i : Fin n => α i.val) ∈ G n := hα n
    rw [Finset.mem_filter] at hαn
    obtain ⟨_, hyImg⟩ := hαn
    obtain ⟨β, hβ_mem, hβ_eq⟩ := hyImg
    exact ⟨β, hβ_mem, hβ_eq⟩
  choose β hβ_mem hβ_eq using hwitness
  -- β n → α in (ℕ → ℕ) product topology: pointwise, for each k, eventually β n k = α k.
  have hβ_tendsto : Filter.Tendsto β Filter.atTop (𝓝 α) := by
    rw [tendsto_pi_nhds]
    intro k
    -- For n ≥ k+1, β n k = α k.
    refine tendsto_atTop_of_eventually_const (i₀ := k + 1) ?_
    intro n hn
    exact hβ_mem n ⟨k, hn⟩
  -- By continuity of f, f(β n) → f(α). But f(β n) = y is constant, so f(α) = y.
  have hf_tendsto : Filter.Tendsto (fun n => f (β n)) Filter.atTop (𝓝 (f α)) :=
    (_hf_cont.tendsto α).comp hβ_tendsto
  have hf_const : (fun n => f (β n)) = fun _ => y := by
    funext n; exact hβ_eq n
  rw [hf_const] at hf_tendsto
  have hfα_eq : f α = y :=
    tendsto_nhds_unique hf_tendsto (tendsto_const_nhds (x := y))
  -- Then y = f α ∈ f '' Q, contradicting hynotImage.
  exact hynotImage ⟨α, hα_in_Q, hfα_eq⟩

/-- **Cylinder-tree mass bound**.

Given compatible per-level cylinder choices `S_n` satisfying the geometric
mass-bound, the `f`-image of the intersection
`Q = ⋂_n ⋃_{σ ∈ S n} cylinder_σ` covers `range f` modulo `ε` in `m`-measure:

`m (range f \ f '' Q) ≤ ε`.

**Proof idea**: For `y ∈ range f \ f '' Q`, no preimage of `y` lies in any
`⋂_n ⋃_{σ ∈ S n} cylinder_σ`. By a König's-lemma / compactness argument on
the tree of "compatible cylinder ancestors of preimages" (see
`cylinder_tree_range_diff_image_subset`), this forces `y` to lie outside
the level-`n` cylinder *image* union `V_n = ⋃_{σ ∈ S_n} f '' N_σ` for
some `n`. The level-image sets `D_n := range f \ V_n` are monotonically
increasing (compatibility gives `V_{n+1} ⊆ V_n`), so by continuity from
below `m(⋃_n D_n) = ⨆_n m(D_n) ≤ ε(1 - 2^{-n}) ≤ ε`.

This is the per-level → global mass-transfer step. The compatibility +
finite-branching structure of `S` is essential: without it, a `y` could
have preimages in every level-`n` union while no single preimage is in
`Q`. -/
private theorem cylinder_tree_mass_bound
    {β : Type*} [TopologicalSpace β] [PolishSpace β]
    [MeasurableSpace β] [BorelSpace β]
    (f : (ℕ → ℕ) → β) (hf_cont : Continuous f)
    (m : Measure β) [IsFiniteMeasure m]
    {ε : ℝ≥0∞}
    (S : ∀ n : ℕ, Finset (Fin n → ℕ))
    (hS_compat : ∀ n : ℕ, ∀ σ ∈ S (n + 1),
      (fun i : Fin n => σ i.castSucc) ∈ S n)
    (hS_mass : ∀ n : ℕ,
      m (Set.range f \
          ⋃ σ ∈ S n, f '' { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i })
        ≤ ε * (1 - (2 : ℝ≥0∞)⁻¹ ^ n)) :
    m (Set.range f \ f ''
        (⋂ n : ℕ, ⋃ σ ∈ S n, { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i }))
      ≤ ε := by
  classical
  -- Abbreviate the level-`n` difference `D_n := range f \ V_n`.
  set D : ℕ → Set β := fun n =>
    Set.range f \ ⋃ σ ∈ S n, f '' { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i }
    with hD_def
  -- Step 1: König's-lemma inclusion.
  have hsub : (Set.range f \ f ''
      (⋂ n : ℕ, ⋃ σ ∈ S n, { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i }))
      ⊆ ⋃ n : ℕ, D n :=
    cylinder_tree_range_diff_image_subset f hf_cont S hS_compat
  -- Step 2: monotonicity of `D_n`. Compatibility `S (n+1) → S n` makes
  -- `V_{n+1} ⊆ V_n`, hence `D_n ⊆ D_{n+1}`.
  have hV_mono : ∀ n,
      (⋃ σ ∈ S (n + 1), f '' { α : ℕ → ℕ | ∀ i : Fin (n + 1), α i.val = σ i }) ⊆
      (⋃ σ ∈ S n, f '' { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i }) := by
    intro n y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨τ, hτS, hyImg⟩
    rcases hyImg with ⟨α, hα_mem, hα_eq⟩
    -- τ|_n := fun i : Fin n => τ i.castSucc; lies in S n by compatibility.
    refine Set.mem_iUnion₂.mpr ⟨fun i : Fin n => τ i.castSucc, hS_compat n τ hτS, ?_⟩
    refine ⟨α, ?_, hα_eq⟩
    intro i
    have := hα_mem i.castSucc
    simpa [Fin.val_castSucc] using this
  have hD_mono : Monotone D := by
    intro n₁ n₂ hn x hx
    have hxRange : x ∈ Set.range f := hx.1
    have hxNotV₁ : x ∉ ⋃ σ ∈ S n₁, f '' { α : ℕ → ℕ | ∀ i : Fin n₁, α i.val = σ i } := hx.2
    refine ⟨hxRange, ?_⟩
    intro hxV₂
    apply hxNotV₁
    -- Iterate `hV_mono` from `n₂` down to `n₁`.
    clear hx
    induction hn with
    | refl => exact hxV₂
    | step _ ih => exact ih (hV_mono _ hxV₂)
  -- Step 3: measure of the increasing union equals supremum.
  have hmU : m (⋃ n : ℕ, D n) = ⨆ n, m (D n) := hD_mono.measure_iUnion
  -- Step 4: each `m (D n) ≤ ε`.
  have hD_le_ε : ∀ n, m (D n) ≤ ε := by
    intro n
    refine (hS_mass n).trans ?_
    -- ε * (1 - 2^{-n}) ≤ ε.
    have h_one_sub_le_one : (1 - (2 : ℝ≥0∞)⁻¹ ^ n) ≤ 1 := tsub_le_self
    calc ε * (1 - (2 : ℝ≥0∞)⁻¹ ^ n)
        ≤ ε * 1 := by gcongr
      _ = ε := mul_one ε
  -- Step 5: combine.
  calc m (Set.range f \ f ''
            (⋂ n : ℕ, ⋃ σ ∈ S n, { α : ℕ → ℕ | ∀ i : Fin n, α i.val = σ i }))
      ≤ m (⋃ n : ℕ, D n) := measure_mono hsub
    _ = ⨆ n, m (D n) := hmU
    _ ≤ ε := iSup_le hD_le_ε

end MeasureTheory
