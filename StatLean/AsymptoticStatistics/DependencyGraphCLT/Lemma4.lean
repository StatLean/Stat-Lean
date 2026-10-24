/-
Copyright (c) 2026 Benjamin O. Harrison, Gustavo Canavire Bacarreza, David Jacho-Chavez and
Fernando Rios-Avila.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Jacho-Chávez
-/
import StatLean.AsymptoticStatistics.DependencyGraphCLT.CumulantExpansion
import StatLean.AsymptoticStatistics.DependencyGraphCLT.Count
import StatLean.AsymptoticStatistics.DependencyGraphCLT.DepGraph

/-!
# Janson's Lemma 4: cumulants of a sum over a dependency graph

Let $\Gamma$ be a dependency graph for real random variables $X_1, \dots, X_N$ with maximal
degree $M$, and suppose $|X_i| \le A$ almost surely. Janson's Lemma 4 bounds the cumulants of
the sum $S = \sum_i X_i$:
$$ |\kappa_j(S)| \;\le\; C'_j\, N\, (M+1)^{j-1} A^j \qquad (j \ge 1), $$
here with the explicit constant $C'_j = j!\,(j-1)!\,C_j$, where $C_j$ is the constant of the
mixed-cumulant bound (4.4). A standardized form bounds $\kappa_j(S/\sigma + c)$ for $j \ge 2$.

**Reference.** S. Janson, "Normal convergence by higher semiinvariants with applications to
sums of dependent random variables and random graphs", *Ann. Probab.* **16** (1988), 305–312,
Lemmas 3 and 4.

**Proof formalization notes.** The inputs are the expansion (4.2)
(`Cumulant.cumulant_sum_eq`), the vanishing Lemma 3
(`Cumulant.mixedCumulant_eq_zero_of_indepFun`), the bound (4.4)
(`Cumulant.abs_mixedCumulant_le`) and the connected-subgraph count (`Janson.card_conn_le`).
After the expansion, every slot family that is not connected for the graph contributes `0`,
and each connected one contributes at most $C_j A^j$. `DepGraph.nbhd` is the closed
neighbourhood, so Janson's degree bound reads `#((D.nbhd i).erase i) ≤ M`. The section
*Examples* checks every hypothesis of Lemma 4 on a three-variable graph that is neither complete
nor empty, with $M = 1$ attained, and evaluates both sides at $j = 3$.

## Main results

* `Janson.mixedCumulant_eq_zero_of_not_connFam`: Lemma 3 on a dependency graph.
* `Janson.abs_cumulant_sum_le`: Lemma 4.
* `Janson.abs_cumulant_standardized_le`: Lemma 4 for the centred and scaled sum.
-/

open Finset MeasureTheory ProbabilityTheory

namespace StatLean.AsymptoticStatistics.Janson

section Lemma4

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Ω → ℝ}

omit [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι] in
/-- The dependency graph's independence, transported to the `splitPart` form used by
`Cumulant.mixedCumulant_eq_zero_of_indepFun`. -/
theorem indepFun_splitPart_of_sep (D : DepGraph X μ) {j : ℕ} (φ : Fin j → ι)
    (a b : Finset (Fin j)) (hsep : ∀ k ∈ a, ∀ l ∈ b, ¬ D.G (φ k) (φ l)) :
    IndepFun (Cumulant.splitPart (fun k => X (φ k)) a)
      (Cumulant.splitPart (fun k => X (φ k)) b) μ := by
  classical
  have hsep' : ∀ x ∈ a.image φ, ∀ y ∈ b.image φ, ¬ D.G x y := by
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hy
    exact hsep k hk l hl
  have hind := D.indep (a.image φ) (b.image φ) hsep'
  have hmap : ∀ c : Finset (Fin j),
      Measurable (fun v : (c.image φ) → ℝ => fun i : Fin j =>
        if h : i ∈ c then v ⟨φ i, Finset.mem_image_of_mem φ h⟩ else (1 : ℝ)) := by
    intro c
    refine Measurable.of_eval fun i => ?_
    by_cases hi : i ∈ c
    · have he : (fun v : (c.image φ) → ℝ =>
          if h : i ∈ c then v ⟨φ i, Finset.mem_image_of_mem φ h⟩ else (1 : ℝ))
          = fun v : (c.image φ) → ℝ => v ⟨φ i, Finset.mem_image_of_mem φ hi⟩ := by
        funext v; simp [hi]
      rw [he]
      exact measurable_pi_apply _
    · have he : (fun v : (c.image φ) → ℝ =>
          if h : i ∈ c then v ⟨φ i, Finset.mem_image_of_mem φ h⟩ else (1 : ℝ))
          = fun _ => (1 : ℝ) := by
        funext v; simp [hi]
      rw [he]
      exact measurable_const
  have hcomp : ∀ c : Finset (Fin j),
      ((fun v : (c.image φ) → ℝ => fun i : Fin j =>
          if h : i ∈ c then v ⟨φ i, Finset.mem_image_of_mem φ h⟩ else (1 : ℝ))
        ∘ (fun ω => fun x : (c.image φ) => X x ω))
        = Cumulant.splitPart (fun k => X (φ k)) c := by
    intro c
    funext ω
    funext i
    by_cases hi : i ∈ c
    · simp [Function.comp, Cumulant.splitPart, hi]
    · simp [Function.comp, Cumulant.splitPart, hi]
  have hres := hind.comp (hmap a) (hmap b)
  rwa [hcomp a, hcomp b] at hres

omit [Fintype ι] [DecidableEq ι] in
/-- **Janson's Lemma 3 on a dependency graph.** A slot family whose vertices do not form a
connected subgraph has mixed cumulant `0`. -/
theorem mixedCumulant_eq_zero_of_not_connFam (D : DepGraph X μ) {j : ℕ} (φ : Fin j → ι)
    (hnc : ¬ IsConnFam D.G φ) :
    Cumulant.mixedCumulant μ (fun k => X (φ k)) (univ : Finset (Fin j)) = 0 := by
  classical
  rw [IsConnFam] at hnc
  push Not at hnc
  obtain ⟨a, hane, hacne, hsep⟩ := hnc
  refine Cumulant.mixedCumulant_eq_zero_of_indepFun μ (fun k => D.meas (φ k))
    (disjoint_compl_right) (by simp) (indepFun_splitPart_of_sep D φ a aᶜ hsep) ?_ ?_
  · intro hc
    obtain ⟨l, hl⟩ := hacne
    exact (Finset.mem_compl.mp hl) (hc (Finset.mem_univ l))
  · intro hc
    obtain ⟨k, hk⟩ := hane
    exact (Finset.mem_compl.mp (hc (Finset.mem_univ k))) hk

/-- Janson's constant `C'_j = j! (j-1)! C_j`, with `C_j = Cumulant.mobiusBound j` the constant
of `(4.4)`. -/
noncomputable def jansonConst (j : ℕ) : ℝ :=
  (Nat.factorial j : ℝ) * (Nat.factorial (j - 1) : ℝ)
    * Cumulant.mobiusBound (univ : Finset (Fin j))

/-- **Janson's Lemma 4.** `|κ_j (∑ X_i)| ≤ C'_j N (M+1)^{j-1} A^j`. -/
theorem abs_cumulant_sum_le (D : DepGraph X μ) {M : ℕ}
    (hdeg : ∀ i : ι, #((D.nbhd i).erase i) ≤ M) {A : ℝ} (hA : 0 ≤ A)
    (hbd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ A) {j : ℕ} (hj : 0 < j) :
    |Cumulant.cumulant (fun ω => ∑ i, X i ω) j μ|
      ≤ jansonConst j * ((Fintype.card ι : ℝ) * ((M : ℝ) + 1) ^ (j - 1) * A ^ j) := by
  classical
  have h42 := Cumulant.cumulant_sum_eq (μ := μ) (Z := X) (t := (univ : Finset ι)) hA
    (fun a => D.meas a) (fun a _ => hbd a) j
  rw [Fintype.piFinset_univ] at h42
  rw [h42]
  set C : Finset (Fin j → ι) := univ.filter (fun φ => IsConnFam D.G φ) with hCdef
  have hvanish : ∀ φ ∈ (univ : Finset (Fin j → ι)), φ ∉ C →
      Cumulant.mixedCumulant μ (fun k => X (φ k)) (univ : Finset (Fin j)) = 0 := by
    intro φ _ hφ
    refine mixedCumulant_eq_zero_of_not_connFam D φ ?_
    intro hconn
    exact hφ (by rw [hCdef]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconn⟩)
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hvanish]
  have hterm : ∀ φ : Fin j → ι,
      |Cumulant.mixedCumulant μ (fun k => X (φ k)) (univ : Finset (Fin j))|
        ≤ Cumulant.mobiusBound (univ : Finset (Fin j)) * A ^ j := by
    intro φ
    have h := Cumulant.abs_mixedCumulant_le μ (fun k => X (φ k)) (fun k => D.meas (φ k))
      (fun k => hbd (φ k)) (univ : Finset (Fin j))
    simpa using h
  have hdeg' : ∀ x : ι, ∀ S : Finset ι, (∀ y ∈ S, D.G x y) → #S ≤ M + 1 := by
    intro x S hS
    have hsub : S ⊆ D.nbhd x := fun y hy => D.mem_nbhd_iff.mpr (hS y hy)
    calc #S ≤ #(D.nbhd x) := Finset.card_le_card hsub
      _ = #((D.nbhd x).erase x) + 1 := (Finset.card_erase_add_one (D.self_mem_nbhd x)).symm
      _ ≤ M + 1 := Nat.add_le_add_right (hdeg x) 1
  have hcount : #C ≤ Nat.factorial j
      * (Fintype.card ι * (Nat.factorial (j - 1) * (M + 1) ^ (j - 1))) := by
    have h := card_conn_le (R := D.G) (univ : Finset ι) hdeg' hj C
      (fun φ hφ => ⟨fun k => Finset.mem_univ _, (Finset.mem_filter.mp hφ).2⟩)
    simpa [Finset.card_univ] using h
  have hnn : (0 : ℝ) ≤ Cumulant.mobiusBound (univ : Finset (Fin j)) * A ^ j :=
    mul_nonneg (Cumulant.mobiusBound_nonneg _) (pow_nonneg hA j)
  calc |∑ φ ∈ C, Cumulant.mixedCumulant μ (fun k => X (φ k)) (univ : Finset (Fin j))|
      ≤ ∑ φ ∈ C, |Cumulant.mixedCumulant μ (fun k => X (φ k)) (univ : Finset (Fin j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _φ ∈ C, (Cumulant.mobiusBound (univ : Finset (Fin j)) * A ^ j) :=
        Finset.sum_le_sum fun φ _ => hterm φ
    _ = (#C : ℝ) * (Cumulant.mobiusBound (univ : Finset (Fin j)) * A ^ j) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Nat.factorial j * (Fintype.card ι * (Nat.factorial (j - 1) * (M + 1) ^ (j - 1))) :
          ℕ) : ℝ) * (Cumulant.mobiusBound (univ : Finset (Fin j)) * A ^ j) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hnn
    _ = jansonConst j * ((Fintype.card ι : ℝ) * ((M : ℝ) + 1) ^ (j - 1) * A ^ j) := by
        rw [jansonConst]
        push_cast
        ring
end Lemma4

/-! ### Examples -/

section Witness

open Cumulant Cumulant.SkewWitness

/-- The index map of the example, under which slots `0` and `1` read the first coordinate and
slot `2` the second. -/
def wπ : Fin 3 → Fin 2 := ![0, 0, 1]

/-- The dependency relation of the example, under which two variables are adjacent if and only
if they read the same coordinate. -/
def wG : Fin 3 → Fin 3 → Prop := fun i k => wπ i = wπ k

instance instDecidableRelWG : DecidableRel wG := fun i k =>
  inferInstanceAs (Decidable (wπ i = wπ k))

/-- The family of the example: `X 0 = X 1 = ω 0` and `X 2 = ω 1`, on two independent copies of the
skewed law `¼δ₄ + ¾δ₀`. -/
noncomputable def wX (i : Fin 3) : (Fin 2 → ℝ) → ℝ := coord (wπ i)

theorem coord_iIndep : iIndepFun coord pairLaw :=
  iIndepFun_pi (μ := fun _ : Fin 2 => skewLaw) (X := fun _ => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)

/-- The dependency graph of the example. -/
noncomputable def wDep : DepGraph wX pairLaw where
  G := wG
  decG := inferInstance
  refl := fun _ => rfl
  symm := fun _ _ h => h.symm
  meas := fun i => (measurable_pi_apply (wπ i) : Measurable (coord (wπ i)))
  indep := by
    intro A B hsep
    have hdisj : Disjoint (A.image wπ) (B.image wπ) := by
      rw [Finset.disjoint_left]
      intro c hc hc'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨b, hb, hb'⟩ := Finset.mem_image.mp hc'
      exact hsep a ha b hb hb'.symm
    have hind := coord_iIndep.indepFun_finset (A.image wπ) (B.image wπ) hdisj
      fun c => (measurable_pi_apply c : Measurable (coord c))
    have hmap : ∀ c : Finset (Fin 3),
        Measurable (fun v : (c.image wπ) → ℝ =>
          fun k : c => v ⟨wπ k, Finset.mem_image_of_mem wπ k.2⟩) :=
      fun c => Measurable.of_eval fun k => measurable_pi_apply _
    have hcomp : ∀ c : Finset (Fin 3),
        ((fun v : (c.image wπ) → ℝ => fun k : c => v ⟨wπ k, Finset.mem_image_of_mem wπ k.2⟩)
          ∘ (fun ω => fun x : (c.image wπ) => coord x ω))
          = fun ω => fun k : c => wX k ω := fun c => rfl
    have hres := hind.comp (hmap A) (hmap B)
    rwa [hcomp A, hcomp B] at hres

/-! #### The graph is neither complete nor empty, and `M = 1` is attained -/

/-- Slots `0` and `1` read the same coordinate, so the graph has an edge. -/
theorem wDep_G_eq : wDep.G = wG := rfl

theorem wDep_edge : wDep.G 0 1 := by rw [wDep_G_eq]; decide

/-- Slots `0` and `2` read different coordinates, so the graph is not complete. -/
theorem wDep_nonedge : ¬ wDep.G 0 2 := by rw [wDep_G_eq]; decide

theorem wDep_nbhd_eq (i : Fin 3) : wDep.nbhd i = univ.filter (fun k => wG i k) := by
  ext k
  rw [DepGraph.mem_nbhd_iff, Finset.mem_filter]
  exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩

/-- Janson's maximal degree of this graph is `M = 1`. -/
theorem wDep_degree (i : Fin 3) : #((wDep.nbhd i).erase i) ≤ 1 := by
  rw [wDep_nbhd_eq]
  revert i
  decide

/-- The degree bound `M = 1` is attained. -/
theorem wDep_degree_attained : #((wDep.nbhd 0).erase 0) = 1 := by
  rw [wDep_nbhd_eq]
  decide

/-! #### The summands are bounded and non-Gaussian -/

theorem coord_bdd (c : Fin 2) : ∀ᵐ ω ∂pairLaw, |coord c ω| ≤ 4 := by
  have h := SkewWitness.skew_bounded
  have hc : Measurable (coord c) := measurable_pi_apply c
  rw [← map_coord c, ae_map_iff hc.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)] at h
  exact h

theorem wX_bdd (i : Fin 3) : ∀ᵐ ω ∂pairLaw, |wX i ω| ≤ 4 := coord_bdd (wπ i)

theorem wSum_eq (ω : Fin 2 → ℝ) : ∑ i, wX i ω = 2 * coord 0 ω + coord 1 ω := by
  simp only [Fin.sum_univ_three, wX, wπ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, coord]
  ring

/-- The left-hand side of Lemma 4 is `54`: `κ_3 (2 ω₀ + ω₁) = 8·6 + 6`, by `(2.2)` and
`(2.3)`. -/
theorem w_cumulant_three : Cumulant.cumulant (fun ω => ∑ i, wX i ω) 3 pairLaw = 54 := by
  have hindep : IndepFun (fun ω => 2 * coord 0 ω) (coord 1) pairLaw := by
    have h := coord_indep.comp (measurable_id.const_mul (2 : ℝ)) (measurable_id (α := ℝ))
    exact h
  have hXi : ∀ r ≤ 3, Integrable (fun ω => (2 * coord 0 ω) ^ r) pairLaw := by
    intro r _
    have he : (fun ω => (2 * coord 0 ω) ^ r) = fun ω => 2 ^ r * (coord 0 ω ^ r) := by
      funext ω; rw [mul_pow]
    rw [he]
    exact (coord_integrable 0 r).const_mul _
  have hYi : ∀ r ≤ 3, Integrable (fun ω => coord 1 ω ^ r) pairLaw :=
    fun r _ => coord_integrable 1 r
  have hfun : (fun ω => ∑ i, wX i ω) = fun ω => 2 * coord 0 ω + coord 1 ω := by
    funext ω; exact wSum_eq ω
  have hc : ∀ i, Measurable (coord i) := fun i => measurable_pi_apply i
  rw [hfun, cumulant_add_of_indepFun ((hc 0).const_mul 2) (hc 1) hindep (by norm_num) hXi hYi,
    cumulant_const_smul (coord 0) 2 3 pairLaw, coord_cumulant, coord_cumulant,
    skew_cumulant_three]
  norm_num

/-- Lemma 4 at `j = 3`, on a graph that is neither complete nor empty, with `M = 1`
attained. -/
theorem w_lemma4_witness :
    |Cumulant.cumulant (fun ω => ∑ i, wX i ω) 3 pairLaw|
      ≤ jansonConst 3
        * ((Fintype.card (Fin 3) : ℝ) * (((1 : ℕ) : ℝ) + 1) ^ (3 - 1) * 4 ^ 3) :=
  abs_cumulant_sum_le wDep (M := 1) wDep_degree (A := 4) (by norm_num) wX_bdd (by norm_num)

/-- The quantity bounded in `w_lemma4_witness` equals `54`. -/
theorem w_lemma4_witness_lhs :
    |Cumulant.cumulant (fun ω => ∑ i, wX i ω) 3 pairLaw| = 54 := by
  rw [w_cumulant_three]
  norm_num

/-! #### Lemma 3 on the graph -/

/-- Slots `{0}` and `{1,2}` contain vertices `0` and `2`, which are not adjacent. -/
theorem w_not_connFam : ¬ IsConnFam wG ![0, 2, 2] := by
  intro h
  have hc := h {0} ⟨0, by decide⟩ ⟨1, by decide⟩
  revert hc
  decide

/-- The vanishing, through `mixedCumulant_eq_zero_of_not_connFam`. -/
theorem w_lemma3_witness :
    Cumulant.mixedCumulant pairLaw (fun k => wX (![0, 2, 2] k)) (univ : Finset (Fin 3)) = 0 :=
  mixedCumulant_eq_zero_of_not_connFam wDep ![0, 2, 2] w_not_connFam

theorem w_connFam_of_same : IsConnFam wG ![0, 1, 1] := by
  intro a ha hac
  obtain ⟨k, hk⟩ := ha
  obtain ⟨l, hl⟩ := hac
  have hall : ∀ k l : Fin 3, wG (![0, 1, 1] k) (![0, 1, 1] l) := by decide
  exact ⟨k, hk, l, hl, hall k l⟩

/-- At the same index set and measure, a slot family whose vertices form a connected subgraph
has mixed cumulant `6 ≠ 0`. -/
theorem w_lemma3_nonvacuous :
    Cumulant.mixedCumulant pairLaw (fun k => wX (![0, 1, 1] k)) (univ : Finset (Fin 3)) = 6 := by
  have hfun : (fun k : Fin 3 => wX (![0, 1, 1] k)) = fun _ : Fin 3 => coord 0 := by
    funext k; fin_cases k <;> rfl
  rw [hfun,
    show Cumulant.mixedCumulant pairLaw (fun _ : Fin 3 => coord 0) (univ : Finset (Fin 3))
      = Cumulant.cumulant (coord 0) 3 pairLaw from rfl, coord_cumulant, skew_cumulant_three]

/-! #### The expansion `(4.2)` -/

theorem w_not_connFam_two : ¬ IsConnFam wG ![0, 2] := by
  intro h
  have hc := h {0} ⟨0, by decide⟩ ⟨1, by decide⟩
  revert hc
  decide

theorem w_not_connFam_two' : ¬ IsConnFam wG ![2, 0] := by
  intro h
  have hc := h {0} ⟨0, by decide⟩ ⟨1, by decide⟩
  revert hc
  decide

/-- Janson's `(4.2)` at `j = 2` over the two independent summands `X 0` and `X 2`. -/
theorem w_42_witness :
    Cumulant.cumulant (fun ω => ∑ a ∈ ({0, 2} : Finset (Fin 3)), wX a ω) 2 pairLaw
      = ∑ φ ∈ Fintype.piFinset (fun _ : Fin 2 => ({0, 2} : Finset (Fin 3))),
          Cumulant.mixedCumulant pairLaw (fun k => wX (φ k)) (univ : Finset (Fin 2)) :=
  Cumulant.cumulant_sum_eq (μ := pairLaw) (Z := wX) (t := ({0, 2} : Finset (Fin 3)))
    (A := 4) (by norm_num) (fun a => (measurable_pi_apply (wπ a) : Measurable (coord (wπ a))))
    (fun a _ => wX_bdd a) 2

theorem w_42_lhs :
    Cumulant.cumulant (fun ω => ∑ a ∈ ({0, 2} : Finset (Fin 3)), wX a ω) 2 pairLaw = 6 := by
  have hfun : (fun ω => ∑ a ∈ ({0, 2} : Finset (Fin 3)), wX a ω)
      = fun ω => coord 0 ω + coord 1 ω := by
    funext ω
    rw [show ({0, 2} : Finset (Fin 3)) = insert 0 {2} from rfl,
      Finset.sum_insert (by decide), Finset.sum_singleton]
    rfl
  have hc : ∀ i, Measurable (coord i) := fun i => measurable_pi_apply i
  rw [hfun, cumulant_add_of_indepFun (hc 0) (hc 1) coord_indep (by norm_num)
      (fun r _ => coord_integrable 0 r) (fun r _ => coord_integrable 1 r),
    coord_cumulant, coord_cumulant, skew_cumulant_two]
  norm_num

/-- The four terms of the expansion are `3 + 0 + 0 + 3`; the two zero terms vanish by
Lemma 3. -/
theorem w_42_rhs :
    ∑ φ ∈ Fintype.piFinset (fun _ : Fin 2 => ({0, 2} : Finset (Fin 3))),
        Cumulant.mixedCumulant pairLaw (fun k => wX (φ k)) (univ : Finset (Fin 2)) = 6 := by
  have hpi : Fintype.piFinset (fun _ : Fin 2 => ({0, 2} : Finset (Fin 3)))
      = {![0, 0], ![0, 2], ![2, 0], ![2, 2]} := by decide
  have t00 : Cumulant.mixedCumulant pairLaw (fun k => wX ((![0, 0] : Fin 2 → Fin 3) k))
      (univ : Finset (Fin 2)) = 3 := by
    have hfun : (fun k : Fin 2 => wX ((![0, 0] : Fin 2 → Fin 3) k)) = fun _ : Fin 2 => coord 0 := by
      funext k; fin_cases k <;> rfl
    rw [hfun, show Cumulant.mixedCumulant pairLaw (fun _ : Fin 2 => coord 0)
        (univ : Finset (Fin 2)) = Cumulant.cumulant (coord 0) 2 pairLaw from rfl,
      coord_cumulant, skew_cumulant_two]
  have t22 : Cumulant.mixedCumulant pairLaw (fun k => wX ((![2, 2] : Fin 2 → Fin 3) k))
      (univ : Finset (Fin 2)) = 3 := by
    have hfun : (fun k : Fin 2 => wX ((![2, 2] : Fin 2 → Fin 3) k)) = fun _ : Fin 2 => coord 1 := by
      funext k; fin_cases k <;> rfl
    rw [hfun, show Cumulant.mixedCumulant pairLaw (fun _ : Fin 2 => coord 1)
        (univ : Finset (Fin 2)) = Cumulant.cumulant (coord 1) 2 pairLaw from rfl,
      coord_cumulant, skew_cumulant_two]
  have t02 : Cumulant.mixedCumulant pairLaw (fun k => wX ((![0, 2] : Fin 2 → Fin 3) k))
      (univ : Finset (Fin 2)) = 0 :=
    mixedCumulant_eq_zero_of_not_connFam wDep ![0, 2] w_not_connFam_two
  have t20 : Cumulant.mixedCumulant pairLaw (fun k => wX ((![2, 0] : Fin 2 → Fin 3) k))
      (univ : Finset (Fin 2)) = 0 :=
    mixedCumulant_eq_zero_of_not_connFam wDep ![2, 0] w_not_connFam_two'
  rw [hpi, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, t00, t02, t20, t22]
  norm_num

end Witness

/-! ### The standardized form

At orders `j ≥ 2` the cumulant is translation invariant, so Lemma 4 applies to
`S/σ + c` for an arbitrary shift `c`, with `A` replaced by `A/σ`.
-/

section Standardized

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Ω → ℝ}

omit [DecidableEq ι] in
/-- A power of the scaled sum is integrable, being bounded and measurable. No sign
hypothesis on `A` is needed. -/
theorem integrable_sum_div_pow (D : DepGraph X μ) {A : ℝ}
    (hbd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ A) (σ : ℝ) (r : ℕ) :
    Integrable (fun ω => ((∑ i, X i ω) / σ) ^ r) μ := by
  have hSm : Measurable (fun ω => ∑ i, X i ω) := Finset.measurable_sum _ fun i _ => D.meas i
  have hall : ∀ᵐ ω ∂μ, ∀ i, |X i ω| ≤ A := ae_all_iff.mpr hbd
  refine Integrable.of_bound ((hSm.div_const σ).pow_const r).aestronglyMeasurable
    (((Fintype.card ι : ℝ) * A / |σ|) ^ r) ?_
  filter_upwards [hall] with ω hω
  have h1 : |∑ i, X i ω| ≤ (Fintype.card ι : ℝ) * A := by
    calc |∑ i, X i ω| ≤ ∑ i, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, A := Finset.sum_le_sum fun i _ => hω i
      _ = (Fintype.card ι : ℝ) * A := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.norm_eq_abs, abs_pow]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ r
  rw [abs_div]
  exact div_le_div_of_nonneg_right h1 (abs_nonneg σ)

/-- **Lemma 4, standardized.** For `j ≥ 2`, the bound of `abs_cumulant_sum_le` holds for
the shifted and scaled sum, by `(2.3)` and translation invariance of cumulants. -/
theorem abs_cumulant_standardized_le (D : DepGraph X μ) {M : ℕ}
    (hdeg : ∀ i : ι, #((D.nbhd i).erase i) ≤ M) {A : ℝ} (hA : 0 ≤ A)
    (hbd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ A) {σ : ℝ} (hσ : 0 < σ) (c : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    |Cumulant.cumulant (fun ω => (∑ i, X i ω) / σ + c) j μ|
      ≤ jansonConst j * ((Fintype.card ι : ℝ) * ((M : ℝ) + 1) ^ (j - 1) * (A / σ) ^ j) := by
  have hSm : Measurable (fun ω => ∑ i, X i ω) := Finset.measurable_sum _ fun i _ => D.meas i
  rw [Cumulant.cumulant_add_const _ (hSm.div_const σ) c hj μ
      (fun r _ => integrable_sum_div_pow D hbd σ r),
    show (fun ω => (∑ i, X i ω) / σ) = fun ω => σ⁻¹ * (∑ i, X i ω) from
      funext fun ω => div_eq_inv_mul _ _,
    Cumulant.cumulant_const_smul (fun ω => ∑ i, X i ω) σ⁻¹ j μ, abs_mul, abs_pow,
    abs_of_pos (inv_pos.mpr hσ)]
  calc σ⁻¹ ^ j * |Cumulant.cumulant (fun ω => ∑ i, X i ω) j μ|
      ≤ σ⁻¹ ^ j
        * (jansonConst j * ((Fintype.card ι : ℝ) * ((M : ℝ) + 1) ^ (j - 1) * A ^ j)) :=
        mul_le_mul_of_nonneg_left (abs_cumulant_sum_le D hdeg hA hbd (by omega))
          (by positivity)
    _ = jansonConst j * ((Fintype.card ι : ℝ) * ((M : ℝ) + 1) ^ (j - 1) * (A / σ) ^ j) := by
        rw [div_pow, inv_pow, div_eq_mul_inv]
        ring

end Standardized

section StandardizedWitness

open Cumulant Cumulant.SkewWitness

/-- The standardized Lemma 4 at `σ = 2`, a shift of `-1` and `j = 3`. -/
theorem w_standardized_witness :
    |Cumulant.cumulant (fun ω => (∑ i, wX i ω) / 2 + (-1)) 3 pairLaw|
      ≤ jansonConst 3
        * ((Fintype.card (Fin 3) : ℝ) * (((1 : ℕ) : ℝ) + 1) ^ (3 - 1) * (4 / 2) ^ 3) :=
  abs_cumulant_standardized_le wDep (M := 1) wDep_degree (A := 4) (by norm_num) wX_bdd
    (by norm_num) (-1) (by norm_num)

/-- The quantity bounded in `w_standardized_witness` equals `27/4`. -/
theorem w_standardized_witness_lhs :
    |Cumulant.cumulant (fun ω => (∑ i, wX i ω) / 2 + (-1)) 3 pairLaw| = 27 / 4 := by
  have hSm : Measurable (fun ω => ∑ i, wX i ω) :=
    Finset.measurable_sum _ fun i _ => wDep.meas i
  rw [Cumulant.cumulant_add_const _ (hSm.div_const 2) (-1) (by norm_num) pairLaw
      (fun r _ => integrable_sum_div_pow wDep wX_bdd 2 r),
    show (fun ω => (∑ i, wX i ω) / 2) = fun ω => (2 : ℝ)⁻¹ * (∑ i, wX i ω) from
      funext fun ω => div_eq_inv_mul _ _,
    Cumulant.cumulant_const_smul (fun ω => ∑ i, wX i ω) (2 : ℝ)⁻¹ 3 pairLaw,
    w_cumulant_three]
  norm_num

end StandardizedWitness

end StatLean.AsymptoticStatistics.Janson
