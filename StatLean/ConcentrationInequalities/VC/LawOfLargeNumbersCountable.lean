import StatLean.ConcentrationInequalities.VC.LawOfLargeNumbers

/-!
# VC law of large numbers — countable-class lift

The finite-class core `vc_lln_finset` (Theorem 8.3.15, finite `F`) is lifted
to a countable class $\mathcal{C}$ by monotone exhaustion through finite
subfamilies and dominated convergence (constant dominant $1$, since every
integrand is bounded by $\max(\mu_n(S), \mu(S)) \le 1$):
$$ \mathbb{E} \sup_{S \in \mathcal{C}} |\mu_n(S) - \mu(S)|
   \;\le\; 5400 \sqrt{\mathrm{vc}(\mathcal{C})/n}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.6, Theorem 8.3.15.

**Proof formalization notes.** `Countable 𝒞` is LEAN-ONLY regularity per the
batch sup policy (the book ignores measurability of the uncountable
supremum; a countable class makes `⨆ S ∈ C` a genuine measurable countable
sup). The lift adds **no constant**: frozen numeral `5400` inherited from
`vc_lln_finset` (formula `2 × 40 × √6 × 27 = 2160√6 ≈ 5290.9 ≤ 5400`,
documented there). This work item's single named-sorry fallback is
`integral_biSup_le_of_forall_finset` (the dominated-convergence exhaustion
engine); `vc_lln_countable` itself is a short assembly over it and must
close.

**Bibliographic comments.** The exhaustion argument is folklore measure
theory; the uniform LLN over VC classes is Vapnik–Chervonenkis (1971), in
the in-expectation form of HDP §8.3.6.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*}

/-- Countable-sup lift engine (LEAN-ONLY, batch sup policy): if every finite
subfamily's expected sup obeys a bound `B`, so does the countable class's
expected sup — monotone exhaustion + dominated convergence with constant
dominant `1`. This work item's single named-sorry fallback. -/
lemma integral_biSup_le_of_forall_finset {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {C : Set (Set Ω)}
    -- LEAN-ONLY: countable class per the batch sup policy
    (hCc : C.Countable)
    -- LEAN-ONLY: nonempty class so the sup is genuine
    (hCne : C.Nonempty)
    {g : Set Ω → Ξ → ℝ}
    -- LEAN-ONLY: nonneg integrand (holds for |μ_n − μ|); monotone limits
    (hg0 : ∀ S ξ, 0 ≤ g S ξ)
    -- LEAN-ONLY: uniform bound 1 (dominant for dominated convergence)
    (hg1 : ∀ S ξ, g S ξ ≤ 1)
    -- LEAN-ONLY: measurability of each member's integrand
    (hgmeas : ∀ S ∈ C, Measurable (g S))
    {B : ℝ}
    -- LEAN-ONLY: the finite-subfamily bound being lifted
    (hB : ∀ (F : Finset (Set Ω)) (hFne : F.Nonempty), ↑F ⊆ C →
      ∫ ξ, F.sup' hFne (fun S => g S ξ) ∂P ≤ B) :
    ∫ ξ, ⨆ S ∈ C, g S ξ ∂P ≤ B := by sorry

/-- **Theorem 8.3.15 (VC law of large numbers), countable class** (HDP
§8.3.6; frozen numeral `5400`, inherited — formula in
`VC/LawOfLargeNumbers.lean`): `E sup_{S ∈ 𝒞} |μ_n(S) − μ(S)| ≤ 5400·√d/√n`
for `vc(𝒞) ≤ d`. `Countable 𝒞` is LEAN-ONLY regularity per the sup
policy. -/
theorem vc_lln_countable {Ξ : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; regularity
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: jointly independent sample; HDP Thm 8.3.15
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP Thm 8.3.15 (map form)
    (hlaw : ∀ i, P.map (X i) = μ)
    {C : Set (Set Ω)}
    -- LEAN-ONLY: countable class per the batch sup policy (documented)
    (hCc : C.Countable)
    -- LEAN-ONLY: nonempty class
    (hCne : C.Nonempty)
    -- LEAN-ONLY: measurable members (implicit in the book's setting)
    (hCmeas : ∀ S ∈ C, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP Thm 8.3.15
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.6
    (hd1 : 1 ≤ d)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.3.6 (implicit)
    (hn : 1 ≤ n) :
    ∫ ξ, ⨆ S ∈ C, |empFrac (fun i : Fin n => X i ξ) S - μ.real S| ∂P ≤
      5400 * Real.sqrt d / Real.sqrt n := by sorry

end StatLean.ConcentrationInequalities
