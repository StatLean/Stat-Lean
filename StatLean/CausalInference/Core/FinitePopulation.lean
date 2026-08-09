import StatLean.CausalInference.Core.FiniteDefs

/-!
# The finite-population causal estimand and the fundamental problem

Elementary consequences of the definitions in `Core.FiniteDefs`: how the observed outcome
relates to the potential outcomes, the two forms of the finite-population average causal
effect, what the sharp null buys, and the **fundamental problem of causal inference** —
the observed data under a fixed assignment does not determine the average causal effect.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §2.2–2.3: the individual effect
`τᵢ = Yᵢ(1) - Yᵢ(0)`, the average causal effect `τ = n⁻¹∑τᵢ`, the observed outcome
equation (2.2), and §2.3's discussion of the missing potential outcome; §3.2 for the
sharp null. (`Ding §2.2–2.3; §3.2`.)

**Proof formalization notes.** The non-identification statement is the design-based form
of the fundamental problem: it fixes an assignment `z` under which some unit is *not*
treated and produces two science tables agreeing on every observed entry but with
different average causal effects. The two tables differ only in potential outcomes that
`z` never reveals, which is exactly the textbook argument.

**Bibliographic comments.** "The fundamental problem of causal inference" is
P. W. Holland's phrase, "Statistics and causal inference," *J. Amer. Statist. Assoc.*
**81** (1986), 945–960.
-/

namespace StatLean.CausalInference

variable {n : ℕ}

/-- The observed outcome of a treated unit is its treated potential outcome
(Ding eq. (2.2)). -/
theorem observed_eq_y1 (S : ScienceTable n) {z : Assignment n} {i : Fin n} (hi : z i = true) :
    S.observed z i = S.y1 i := by
  sorry

/-- The observed outcome of a control unit is its control potential outcome
(Ding eq. (2.2)). -/
theorem observed_eq_y0 (S : ScienceTable n) {z : Assignment n} {i : Fin n} (hi : z i = false) :
    S.observed z i = S.y0 i := by
  sorry

/-- The observed outcome equation in arithmetic form: `Yᵢ = ZᵢYᵢ(1) + (1 - Zᵢ)Yᵢ(0)`
(Ding eq. (2.2)). -/
theorem observed_eq_ind_combination (S : ScienceTable n) (z : Assignment n) (i : Fin n) :
    S.observed z i = ind (z i) * S.y1 i + (1 - ind (z i)) * S.y0 i := by
  sorry

/-- The average causal effect is the difference of the two potential-outcome means
(Ding §2.2). -/
theorem finiteATE_eq_sub_popMean (S : ScienceTable n) :
    S.finiteATE = popMean S.y1 - popMean S.y0 := by
  sorry

/-- Under the sharp null every observed outcome vector equals the control vector, so all
missing potential outcomes are imputable (Ding §3.2). -/
theorem SharpNull.observed_eq (S : ScienceTable n) (h : S.SharpNull) (z : Assignment n) :
    S.observed z = S.y0 := by
  sorry

/-- The sharp null implies the null average causal effect (the converse fails). -/
theorem SharpNull.finiteATE_eq_zero (S : ScienceTable n) (h : S.SharpNull) :
    S.finiteATE = 0 := by
  sorry

/-- The **average causal effect over a subgroup** of units. Junk value `0` on the empty
subgroup. -/
noncomputable def subgroupATE (S : ScienceTable n) (A : Finset (Fin n)) : ℝ :=
  (A.card : ℝ)⁻¹ * ∑ i ∈ A, S.unitEffect i

/-- **Subgroup decomposition** (Ding §2.2): the average causal effect is the
size-weighted average of the subgroup effects, for any partition of the units into the
level sets of a map `g`. Empty subgroups contribute `0`. -/
theorem finiteATE_eq_sum_subgroupATE (S : ScienceTable n) {K : Type*} [Fintype K]
    [DecidableEq K] (g : Fin n → K)
    -- LEAN-ONLY: a nonempty population, so that `n⁻¹` is not a junk value; no scope change
    (hn : 0 < n) :
    S.finiteATE
      = ∑ k : K, (((Finset.univ.filter fun i => g i = k).card : ℝ) / (n : ℝ))
          * subgroupATE S (Finset.univ.filter fun i => g i = k) := by
  sorry

/-- **The fundamental problem of causal inference** (Ding §2.3), design-based form: fix an
assignment under which some unit is untreated; then two science tables can agree on every
*observed* outcome yet have different average causal effects. Hence the observed data
alone never identifies `τ`. -/
theorem exists_sameObserved_ne_finiteATE (z : Assignment n)
    -- USER-INPUT: some unit is not treated, so some potential outcome is missing; Ding §2.3
    {i₀ : Fin n} (hi₀ : z i₀ = false) :
    ∃ S S' : ScienceTable n, S.observed z = S'.observed z ∧ S.finiteATE ≠ S'.finiteATE := by
  sorry

end StatLean.CausalInference
