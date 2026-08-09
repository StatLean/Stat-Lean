import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# The pointwise (Birkhoff) ergodic theorem

The Mathlib pin carries the algebraic bookkeeping for `birkhoffSum`/`birkhoffAverage` and
von Neumann's *mean* (L²) ergodic theorem, but no maximal ergodic theorem and no a.e.
convergence statement. This file supplies them, for a measure-preserving map of a
probability space: the maximal ergodic theorem (Garsia's proof), a.e. convergence of
Birkhoff averages to the conditional expectation on the invariant σ-algebra, and the
ergodic corollary (limit = the space mean).

Consumed by `Mixing/LimitTheorems.slln_of_alphaMixing_debt` (FY Prop 2.8), whose closing
wave recorded the four-item build list this file is item (iii) of.

**Reference.** Birkhoff (1931); the maximal-inequality proof is Garsia (1965). FY cite
Doob 1953 / Ibragimov–Linnik 1971 for the mixing SLLN.

**Bibliographic comments.** The invariant σ-algebra and the condexp form follow the
standard modern treatment (e.g. Einsiedler–Ward, *Ergodic Theory*, ch. 2).
-/

open MeasureTheory Filter
open scoped Topology

namespace StatLean.TimeSeries

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}

/-- The **invariant σ-algebra** of a self-map: measurable sets with `f ⁻¹' s = s`.
Formalizes the almost-invariant information of the dynamics (edge behavior: for
non-measurable `f` this is still a σ-algebra, just not comparable to the ambient one
through `f`). -/
def invariantSigma (f : α → α) : MeasurableSpace α where
  MeasurableSet' s := MeasurableSet s ∧ f ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, rfl⟩
  measurableSet_compl s hs := ⟨hs.1.compl, by rw [Set.preimage_compl, hs.2]⟩
  measurableSet_iUnion g hg :=
    ⟨MeasurableSet.iUnion fun i => (hg i).1, by
      simp only [Set.preimage_iUnion]
      exact Set.iUnion_congr fun i => (hg i).2⟩

/-- The invariant σ-algebra is coarser than the ambient one.
-- LEAN-ONLY: needed to state the conditional expectation; no scope change -/
theorem invariantSigma_le (f : α → α) : invariantSigma f ≤ ‹MeasurableSpace α› :=
  fun _ hs => hs.1

/-! ### Garsia's running maximum

The proof of the maximal ergodic theorem below is Garsia's: with
`M_N x = max_{1 ≤ k ≤ N+1} S_k x` (`birkhoffMax`) one has the *pointwise* inequality
`M_N x ≤ g x + M_N⁺ (f x)`, which on `{M_N > 0}` reads `g ≥ M_N⁺ − M_N⁺ ∘ f`; integrating
and using measure preservation kills the right-hand side. -/

section Garsia

/-- Garsia's running maximum `max_{1 ≤ k ≤ N+1} birkhoffSum f g k x`.
-- LEAN-ONLY: auxiliary for `maximal_ergodic`; no scope change -/
private noncomputable def birkhoffMax (f : α → α) (g : α → ℝ) (N : ℕ) (x : α) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun k => birkhoffSum f g (k + 1) x

omit [MeasurableSpace α] in
private theorem le_birkhoffMax {g : α → ℝ} {N k : ℕ} (hk : k ≤ N) (x : α) :
    birkhoffSum f g (k + 1) x ≤ birkhoffMax f g N x :=
  Finset.le_sup' (fun k => birkhoffSum f g (k + 1) x) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

omit [MeasurableSpace α] in
private theorem birkhoffMax_mono {g : α → ℝ} (x : α) :
    Monotone fun N => birkhoffMax f g N x := by
  intro M N hMN
  refine Finset.sup'_le _ _ fun k hk => ?_
  exact le_birkhoffMax ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)).trans hMN) x

omit [MeasurableSpace α] in
/-- The Garsia inequality: `M_N ≤ g + M_N⁺ ∘ f` pointwise. -/
private theorem birkhoffMax_le {g : α → ℝ} (N : ℕ) (x : α) :
    birkhoffMax f g N x ≤ g x + max (birkhoffMax f g N (f x)) 0 := by
  refine Finset.sup'_le _ _ fun k hk => ?_
  have hkN : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [birkhoffSum_succ']
  have h : birkhoffSum f g k (f x) ≤ max (birkhoffMax f g N (f x)) 0 := by
    cases k with
    | zero => simp
    | succ j =>
        exact (le_birkhoffMax (le_trans (Nat.le_succ j) hkN) (f x)).trans (le_max_left _ _)
  linarith

omit [MeasurableSpace α] in
private theorem birkhoffMax_succ (f : α → α) (g : α → ℝ) (N : ℕ) (x : α) :
    birkhoffMax f g (N + 1) x = max (birkhoffSum f g (N + 2) x) (birkhoffMax f g N x) := by
  refine le_antisymm (Finset.sup'_le _ _ fun k hk => ?_) ?_
  · rcases Nat.lt_succ_iff_lt_or_eq.1 (Finset.mem_range.1 hk) with h | h
    · exact (le_birkhoffMax (Nat.lt_succ_iff.1 h) x).trans (le_max_right _ _)
    · subst h; exact le_max_left _ _
  · exact max_le (le_birkhoffMax (le_refl (N + 1)) x) (birkhoffMax_mono x (Nat.le_succ N))

private theorem measurable_birkhoffSum {g : α → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (n : ℕ) : Measurable (birkhoffSum f g n) := by
  unfold birkhoffSum
  exact Finset.measurable_sum _ fun k _ => hgm.comp (hfm.iterate k)

private theorem measurable_birkhoffMax {g : α → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (N : ℕ) : Measurable (birkhoffMax f g N) := by
  unfold birkhoffMax
  exact Finset.measurable_range_sup'' fun k _ => measurable_birkhoffSum hfm hgm (k + 1)

private theorem integrable_birkhoffSum (hf : MeasurePreserving f μ μ) {g : α → ℝ}
    (hg : Integrable g μ) (n : ℕ) : Integrable (birkhoffSum f g n) μ := by
  unfold birkhoffSum
  exact integrable_finset_sum _ fun k _ => (hf.iterate k).integrable_comp_of_integrable hg

private theorem integrable_birkhoffMax (hf : MeasurePreserving f μ μ) {g : α → ℝ}
    (hg : Integrable g μ) (N : ℕ) : Integrable (birkhoffMax f g N) μ := by
  induction N with
  | zero =>
      have h : birkhoffMax f g 0 = g := by
        funext x
        simp [birkhoffMax, birkhoffSum_one]
      rw [h]; exact hg
  | succ N ih =>
      have h : birkhoffMax f g (N + 1) = birkhoffSum f g (N + 2) ⊔ birkhoffMax f g N := by
        funext x
        rw [birkhoffMax_succ]
        rfl
      rw [h]
      exact (integrable_birkhoffSum hf hg _).sup ih

/-- Measure preservation moves the map through the integral. -/
private theorem integral_comp_self (hf : MeasurePreserving f μ μ) {F : α → ℝ}
    (hFm : AEStronglyMeasurable F μ) : ∫ x, F (f x) ∂μ = ∫ x, F x ∂μ := by
  conv_rhs => rw [← hf.map_eq]
  rw [integral_map hf.measurable.aemeasurable (by rwa [hf.map_eq])]

/-- The maximal ergodic theorem for a *measurable* observable; the general case follows by
passing to a measurable representative. -/
private theorem maximal_ergodic_aux (hf : MeasurePreserving f μ μ) {g : α → ℝ}
    (hgm : Measurable g) (hg : Integrable g μ) :
    0 ≤ ∫ x in {x | ∃ n : ℕ, 0 < birkhoffSum f g (n + 1) x}, g x ∂μ := by
  set E : ℕ → Set α := fun N => {x | 0 < birkhoffMax f g N x} with hE
  have hEm : ∀ N, MeasurableSet (E N) := fun N =>
    measurableSet_lt measurable_const (measurable_birkhoffMax hf.measurable hgm N)
  have hEmono : Monotone E := fun M N hMN x hx => lt_of_lt_of_le hx (birkhoffMax_mono x hMN)
  have hUnion : (⋃ N, E N) = {x | ∃ n : ℕ, 0 < birkhoffSum f g (n + 1) x} := by
    ext x
    simp only [Set.mem_iUnion, hE, Set.mem_setOf_eq]
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨k, _, hk⟩ := (Finset.lt_sup'_iff _).1 hN
      exact ⟨k, hk⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, lt_of_lt_of_le hn (le_birkhoffMax (le_refl n) x)⟩
  -- Garsia's estimate on each level set
  have key : ∀ N, 0 ≤ ∫ x in E N, g x ∂μ := by
    intro N
    set M : α → ℝ := fun x => max (birkhoffMax f g N x) 0 with hM
    have hMmeas : Measurable M :=
      (measurable_birkhoffMax hf.measurable hgm N).max measurable_const
    have hMint : Integrable M μ := by
      refine Integrable.mono' (integrable_birkhoffMax hf hg N).abs
        hMmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      simp only [hM, Real.norm_eq_abs]
      rcases le_or_gt (birkhoffMax f g N x) 0 with h | h
      · simp [max_eq_right h, abs_nonneg]
      · simp [max_eq_left h.le]
    have hMnn : ∀ x, 0 ≤ M x := fun x => le_max_right _ _
    have hMcompf : Integrable (fun x => M (f x)) μ := hf.integrable_comp_of_integrable hMint
    have hpt : ∀ x ∈ E N, M x - M (f x) ≤ g x := by
      intro x hx
      have h1 : M x = birkhoffMax f g N x := max_eq_left (le_of_lt hx)
      have h2 : M (f x) = max (birkhoffMax f g N (f x)) 0 := rfl
      have h3 := birkhoffMax_le (f := f) (g := g) N x
      rw [h1, h2]; linarith
    have hint1 : ∫ x in E N, (M x - M (f x)) ∂μ ≤ ∫ x in E N, g x ∂μ :=
      setIntegral_mono_on (hMint.sub hMcompf).integrableOn hg.integrableOn (hEm N) hpt
    have hsplit : ∫ x in E N, (M x - M (f x)) ∂μ
        = (∫ x in E N, M x ∂μ) - ∫ x in E N, M (f x) ∂μ :=
      integral_sub hMint.integrableOn hMcompf.integrableOn
    have hA : ∫ x in E N, M x ∂μ = ∫ x, M x ∂μ := by
      refine setIntegral_eq_integral_of_ae_compl_eq_zero
        (Filter.Eventually.of_forall fun x hx => ?_)
      simp only [hM]
      exact max_eq_right (not_lt.1 hx)
    have hB : ∫ x in E N, M (f x) ∂μ ≤ ∫ x, M (f x) ∂μ :=
      setIntegral_le_integral hMcompf (Filter.Eventually.of_forall fun x => hMnn (f x))
    have hC : ∫ x, M (f x) ∂μ = ∫ x, M x ∂μ :=
      integral_comp_self hf hMmeas.aestronglyMeasurable
    linarith
  rw [← hUnion]
  exact ge_of_tendsto (tendsto_setIntegral_of_monotone hEm hEmono hg.integrableOn)
    (Filter.Eventually.of_forall key)

end Garsia

/-- **The maximal ergodic theorem** (Garsia): for integrable `g`, the integral of `g`
over the set where some Birkhoff sum is positive is nonnegative.
-- USER-INPUT: measure-preserving dynamics and integrable observable; Birkhoff/Garsia -/
theorem maximal_ergodic (hf : MeasurePreserving f μ μ) {g : α → ℝ}
    (hg : Integrable g μ) :
    0 ≤ ∫ x in {x | ∃ n : ℕ, 0 < birkhoffSum f g (n + 1) x}, g x ∂μ := by
  -- replace `g` by a measurable representative; both the set and the integrand only change
  -- by a null set, because `f` is measure preserving
  set g' := hg.1.mk g with hg'def
  have hg'm : Measurable g' := hg.1.stronglyMeasurable_mk.measurable
  have hgg' : g =ᵐ[μ] g' := hg.1.ae_eq_mk
  have hg' : Integrable g' μ := hg.congr hgg'
  have hiter : ∀ᵐ x ∂μ, ∀ k : ℕ, g (f^[k] x) = g' (f^[k] x) := by
    rw [ae_all_iff]
    exact fun k => (hf.iterate k).quasiMeasurePreserving.ae hgg'
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffSum f g (n + 1) x = birkhoffSum f g' (n + 1) x := by
    filter_upwards [hiter] with x hx n
    exact Finset.sum_congr rfl fun k _ => hx k
  have hset : {x | ∃ n : ℕ, 0 < birkhoffSum f g (n + 1) x}
      =ᵐ[μ] {x | ∃ n : ℕ, 0 < birkhoffSum f g' (n + 1) x} := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hall] with x hx
    exact ⟨fun ⟨n, hn⟩ => ⟨n, (hx n) ▸ hn⟩, fun ⟨n, hn⟩ => ⟨n, (hx n).symm ▸ hn⟩⟩
  rw [setIntegral_congr_set hset,
    integral_congr_ae (ae_restrict_of_ae hgg' : g =ᵐ[μ.restrict _] g')]
  exact maximal_ergodic_aux hf hg'm hg'

/-- **The pointwise (Birkhoff) ergodic theorem, conditional-expectation form**: for a
measure-preserving `f` on a probability space and integrable `g`, the Birkhoff averages
converge a.e. to the conditional expectation of `g` on the invariant σ-algebra.
-- USER-INPUT: measure-preserving dynamics and integrable observable; Birkhoff 1931 -/
theorem birkhoffAverage_ae_tendsto_condexp [IsProbabilityMeasure μ]
    (hf : MeasurePreserving f μ μ) (hfm : Measurable f) {g : α → ℝ}
    (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ f g n x) atTop
      (𝓝 ((μ[g | invariantSigma f]) x)) := by
  sorry

/-- **Birkhoff for an ergodic map**: the averages converge a.e. to the space mean.
-- USER-INPUT: ergodic dynamics and integrable observable; Birkhoff 1931 -/
theorem birkhoffAverage_ae_tendsto_integral [IsProbabilityMeasure μ]
    (hf : Ergodic f μ) (hfm : Measurable f) {g : α → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ f g n x) atTop (𝓝 (∫ x, g x ∂μ)) := by
  -- for an ergodic map every `invariantSigma`-measurable set is null or conull, so the
  -- conditional expectation on `invariantSigma f` is a.e. the space mean
  have hconst : (fun _ : α => ∫ x, g x ∂μ) =ᵐ[μ] μ[g | invariantSigma f] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (invariantSigma_le f) hg
      (fun s _ _ => (integrable_const _).integrableOn) (fun s hs _ => ?_)
      aestronglyMeasurable_const
    have hs' : MeasurableSet s ∧ f ⁻¹' s = s := hs
    rcases hf.ae_empty_or_univ hs'.1 hs'.2 with h | h
    · rw [setIntegral_congr_set h, setIntegral_congr_set h]
      simp
    · rw [setIntegral_congr_set h, setIntegral_congr_set h]
      simp
  filter_upwards [birkhoffAverage_ae_tendsto_condexp hf.toMeasurePreserving hfm hg, hconst]
    with x h1 h2
  rwa [h2]

end StatLean.TimeSeries
