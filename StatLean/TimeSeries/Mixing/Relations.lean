import StatLean.TimeSeries.Mixing.Defs
import StatLean.TimeSeries.Process.Stationary
import StatLean.TimeSeries.Models.WhiteNoise
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Relations between the mixing coefficients (FY §2.6.1, pp. 68–71)

Basic properties of the five dependence coefficients of `Mixing/Defs.lean` and the
classical implication chain `ψ-mixing ⇒ φ-mixing ⇒ {β-, ρ-mixing} ⇒ α-mixing`
(FY §2.6.1 "basic facts", cited to Bradley 1986):

* set-level basics: the description sets are nonempty and bounded, the coefficients
  nonnegative; `α ≤ 1`, monotone in both σ-algebra arguments; process coefficients
  antitone in the lag;
* provable coefficient inequalities: `2α ≤ β`, `α ≤ φ`, `β ≤ φ`, `φ ≤ 2ψ`-form,
  `α ≤ ¼ρ` (FY's display `α(k) ≤ ¼ρ(k)`);
* the Bradley square-root relation `ρ ≤ 2√φ` (giving FY's `¼ρ(k) ≤ ½φ^{1/2}(k)`) —
  literature DEBT;
* heredity under instantaneous measurable transforms;
* the shift lemma: under strict stationarity the anchored coefficients equal the
  coefficients between any `k`-shifted past/future pair (the property FY uses silently
  in every block argument);
* the in-text non-example (ix): a deterministic recursion `X_{t+1} = m(X_t)` with a
  non-degenerate event is not α-mixing;
* literature statement DEBTS: Pham–Tran (causal ARMA with absolutely continuous iid
  innovations is exponentially β-mixing), Basrak–Davis–Mikosch (GARCH is exponentially
  α-mixing), Kolmogorov–Rozanov (Gaussian: ρ-mixing ⇔ α-mixing).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.1
(pp. 68–71). (`FY §2.6.1`.)

**Proof formalization notes.**
* `2α ≤ β`: the four-set partition `{A, Aᶜ} × {B, Bᶜ}` has partition sum
  `4|P(A∩B) − P(A)P(B)|`.
* `α ≤ φ`: `|P(A∩B) − P(A)P(B)| = P(A)·|P(B|A) − P(B)| ≤ φ` (the `P(A) = 0` term
  vanishes).
* `β ≤ φ`: for a partition pair, `Σ_j |P(B_j|A_i) − P(B_j)| ≤ 2 sup_B |P(B|A_i) − P(B)|`
  (split the sum by sign; each signed half is a single event).
* `α ≤ ¼ρ`: centered indicators, `Cov(1_A, 1_B) = P(A∩B) − P(A)P(B)` and
  `Var(1_A) = P(A)(1−P(A)) ≤ ¼`.
* The shift lemma transports the description sets through the path map; strict
  stationarity is exactly invariance of the path law under the shift.

**Bibliographic comments.** The implication chain and the sharp constants are collected
in R. C. Bradley, *Basic properties of strong mixing conditions* (in Eberlein–Taqqu,
1986) and his 2005 survey; `ρ ≤ 2√φ` is due to Peligrad (after Cogburn and Ibragimov).
Pham & Tran, *Some mixing properties of time series models*, SPA 1985; Basrak, Davis &
Mikosch, *Regular variation of GARCH processes*, SPA 2002; Kolmogorov & Rozanov 1960
for the Gaussian ρ ⇔ α equivalence.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-! ### Set-level basics

Two-σ-algebra statements follow the Mathlib `condExp` binder convention: the ambient
σ-algebra `mΩ` is a plain implicit bound *after* the sub-σ-algebras and immediately
before `μ`, so that local-instance resolution and unification agree (an
instance-implicit ambient would be shadowed by the sub-σ-algebra binders). -/

section TwoAlgebras

variable {Ω : Type*}

/-- On a probability space every measure is at most `1` after `toReal`. -/
private lemma toReal_le_one {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Set Ω) : (μ s).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ s))

/-- Every value in the α description set is bounded by `1`. -/
private lemma abs_alpha_term_le_one {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (A B : Set Ω) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ 1 := by
  have h1 := toReal_le_one (μ := μ) (A ∩ B)
  have h2 := toReal_le_one (μ := μ) A
  have h3 := toReal_le_one (μ := μ) B
  have h0 : (0 : ℝ) ≤ (μ (A ∩ B)).toReal := ENNReal.toReal_nonneg
  have h0a : (0 : ℝ) ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have h0b : (0 : ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> nlinarith

/-- The α description set contains `0` (take `A = ∅`). -/
theorem alphaMixCoeff_set_nonempty {m₁ m₂ mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    (0 : ℝ) ∈ {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      r = |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|} :=
  ⟨∅, ∅, @MeasurableSet.empty Ω m₁, @MeasurableSet.empty Ω m₂, by simp⟩

/-- On a probability space the α description set is bounded above by `1`. -/
theorem alphaMixCoeff_set_bddAbove {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    BddAbove {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      r = |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨A, B, -, -, rfl⟩
  exact abs_alpha_term_le_one A B

/-- `0 ≤ α`. -/
theorem alphaMixCoeff_nonneg {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    0 ≤ alphaMixCoeff μ m₁ m₂ :=
  le_csSup (alphaMixCoeff_set_bddAbove (mΩ := mΩ)) (alphaMixCoeff_set_nonempty (mΩ := mΩ) μ)

/-- `α ≤ 1` (indeed `α ≤ ¼`, but FY only uses boundedness). -/
theorem alphaMixCoeff_le_one {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    alphaMixCoeff μ m₁ m₂ ≤ 1 :=
  Real.sSup_le (by rintro r ⟨A, B, -, -, rfl⟩; exact abs_alpha_term_le_one A B) zero_le_one

/-- α is monotone in both σ-algebra arguments. -/
theorem alphaMixCoeff_mono {m₁ m₂ m₁' m₂' mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁' ≤ m₁) (h₂ : m₂' ≤ m₂) :
    alphaMixCoeff μ m₁' m₂' ≤ alphaMixCoeff μ m₁ m₂ := by
  refine csSup_le_csSup (alphaMixCoeff_set_bddAbove (mΩ := mΩ))
    ⟨0, alphaMixCoeff_set_nonempty (mΩ := mΩ) μ⟩ ?_
  rintro r ⟨A, B, hA, hB, rfl⟩
  exact ⟨A, B, h₁ _ hA, h₂ _ hB, rfl⟩

end TwoAlgebras

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The process α-coefficient is antitone in the lag (FY: "monotone nonincreasing",
used silently; from `sigmaGE X (n+1) ≤ sigmaGE X n`). -/
theorem alphaCoeff_antitone [IsProbabilityMeasure μ] (X : ℤ → Ω → ℝ) :
    Antitone fun n : ℕ => alphaCoeff X μ n := by
  intro a b hab
  refine alphaMixCoeff_mono le_rfl ?_
  refine iSup₂_le fun s hs => ?_
  have hs' : (b : ℤ) ≤ s := hs
  refine le_iSup₂_of_le s (Set.mem_Ici.mpr ?_) le_rfl
  exact le_trans (by exact_mod_cast hab) hs'

end Process

/-! ### Provable coefficient inequalities (FY §2.6.1 basic facts) -/

section TwoAlgebras2

variable {Ω : Type*}

private lemma toReal_inter_le {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A B : Set Ω) : (μ (A ∩ B)).toReal ≤ (μ A).toReal :=
  ENNReal.toReal_mono (measure_ne_top μ A) (measure_mono Set.inter_subset_left)

/-- Finite measurable partitions split any measurable set additively. -/
private lemma sum_toReal_inter {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {J : ℕ} {B : Fin J → Set Ω} (hB : ∀ j, MeasurableSet (B j))
    (hd : Pairwise fun j j' => Disjoint (B j) (B j')) (hcov : (⋃ j, B j) = Set.univ)
    {S : Set Ω} (hS : MeasurableSet S) :
    ∑ j, (μ (S ∩ B j)).toReal = (μ S).toReal := by
  have hmeas : μ S = ∑ j, μ (S ∩ B j) := by
    calc μ S = μ (⋃ j, S ∩ B j) := by rw [← Set.inter_iUnion, hcov, Set.inter_univ]
      _ = ∑' j, μ (S ∩ B j) :=
          measure_iUnion (fun j j' hjj' =>
            (hd hjj').mono Set.inter_subset_right Set.inter_subset_right)
            (fun j => hS.inter (hB j))
      _ = ∑ j, μ (S ∩ B j) := tsum_fintype _
  rw [hmeas, ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]

/-- The φ description set contains `0` (take `A = univ`, `B = ∅`). -/
private lemma phiMixCoeff_set_nonempty {m₁ m₂ mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (0 : ℝ) ∈ {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      0 < (μ A).toReal ∧
      r = |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal|} :=
  ⟨Set.univ, ∅, @MeasurableSet.univ Ω m₁, @MeasurableSet.empty Ω m₂, by simp, by simp⟩

private lemma abs_phi_term_le_one {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hA : 0 < (μ A).toReal) :
    |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal| ≤ 1 := by
  have h1 : (0 : ℝ) ≤ (μ (A ∩ B)).toReal / (μ A).toReal :=
    div_nonneg ENNReal.toReal_nonneg hA.le
  have h2 : (μ (A ∩ B)).toReal / (μ A).toReal ≤ 1 :=
    (div_le_one hA).2 (toReal_inter_le A B)
  have h3 := toReal_le_one (μ := μ) B
  have h4 : (0 : ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> linarith

private lemma phiMixCoeff_set_bddAbove {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    BddAbove {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      0 < (μ A).toReal ∧
      r = |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨A, B, -, -, hA, rfl⟩
  exact abs_phi_term_le_one hA

private lemma phiMixCoeff_nonneg {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] : 0 ≤ phiMixCoeff μ m₁ m₂ :=
  le_csSup (phiMixCoeff_set_bddAbove (mΩ := mΩ)) (phiMixCoeff_set_nonempty (mΩ := mΩ) μ)

/-- The core estimate behind both `α ≤ φ` and `β ≤ φ`. -/
private lemma abs_alpha_term_le_mul_phi {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hA : MeasurableSet[m₁] A)
    (hB : MeasurableSet[m₂] B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
      ≤ (μ A).toReal * phiMixCoeff μ m₁ m₂ := by
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : (0:ℝ) ≤ (μ A).toReal) with h0 | hpos
  · have hA0 : μ A = 0 := by
      have := (ENNReal.toReal_eq_zero_iff (μ A)).1 h0.symm
      exact this.resolve_right (measure_ne_top μ A)
    have hAB : μ (A ∩ B) = 0 := measure_mono_null Set.inter_subset_left hA0
    simp [hAB, hA0]
  · have key : |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
        = (μ A).toReal * |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal| := by
      have hne : (μ A).toReal ≠ 0 := ne_of_gt hpos
      have e1 : (μ A).toReal * ((μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal)
          = -((μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal) := by
        field_simp
        ring
      have e2 : |(μ A).toReal| * |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal|
          = |(μ A).toReal * ((μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal)| :=
        (abs_mul _ _).symm
      rw [abs_of_pos hpos] at e2
      rw [e2, e1, abs_neg]
    rw [key]
    refine mul_le_mul_of_nonneg_left ?_ hpos.le
    exact le_csSup (phiMixCoeff_set_bddAbove (mΩ := mΩ)) ⟨A, B, hA, hB, hpos, rfl⟩

/-- Splitting a set along a sub-family of a finite disjoint measurable family. -/
private lemma toReal_inter_biUnion {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {J : ℕ} {B : Fin J → Set Ω} (hB : ∀ j, MeasurableSet (B j))
    (hd : Pairwise fun j j' => Disjoint (B j) (B j')) (S : Finset (Fin J))
    {T : Set Ω} (hT : MeasurableSet T) :
    (μ (T ∩ ⋃ j ∈ S, B j)).toReal = ∑ j ∈ S, (μ (T ∩ B j)).toReal := by
  have hset : T ∩ (⋃ j ∈ S, B j) = ⋃ j ∈ S, (T ∩ B j) := by
    simp [Set.inter_iUnion]
  rw [hset, measure_biUnion_finset
      (fun j _ j' _ hjj' => (hd hjj').mono Set.inter_subset_right Set.inter_subset_right)
      (fun j _ => hT.inter (hB j)),
    ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]

/-- The partition sum defining `β` is at most `2φ`; the engine behind `β ≤ φ`. -/
private lemma beta_sum_le_two_mul_phi {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {I J : ℕ} {A : Fin I → Set Ω} {B : Fin J → Set Ω}
    (hA : ∀ i, MeasurableSet[m₁] (A i)) (hB : ∀ j, MeasurableSet[m₂] (B j))
    (hdA : Pairwise fun i i' => Disjoint (A i) (A i'))
    (hcA : (⋃ i, A i) = Set.univ)
    (hdB : Pairwise fun j j' => Disjoint (B j) (B j')) :
    ∑ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      ≤ 2 * phiMixCoeff μ m₁ m₂ := by
  have hBm : ∀ j, MeasurableSet (B j) := fun j => h₂ _ (hB j)
  have hAm : ∀ i, MeasurableSet (A i) := fun i => h₁ _ (hA i)
  -- Row bound: each `i`-row is at most `2 P(A i) φ`, by splitting the `j`'s by sign.
  have hrow : ∀ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      ≤ 2 * ((μ (A i)).toReal * phiMixCoeff μ m₁ m₂) := by
    intro i
    set d : Fin J → ℝ := fun j =>
      (μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal with hd
    -- The signed groups, each a single `m₂`-event.
    have hgroup : ∀ S : Finset (Fin J), ∑ j ∈ S, d j
        = (μ (A i ∩ ⋃ j ∈ S, B j)).toReal
          - (μ (A i)).toReal * (μ (⋃ j ∈ S, B j)).toReal := by
      intro S
      have h1 := toReal_inter_biUnion (μ := μ) hBm hdB S (hAm i)
      have huniv : MeasurableSet (Set.univ : Set Ω) := MeasurableSet.univ
      have h2 := toReal_inter_biUnion (μ := μ) hBm hdB S huniv
      simp only [Set.univ_inter] at h2
      rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have habs : ∀ S : Finset (Fin J), |∑ j ∈ S, d j|
        ≤ (μ (A i)).toReal * phiMixCoeff μ m₁ m₂ := by
      intro S
      rw [hgroup S]
      have hUm : MeasurableSet[m₂] (⋃ j ∈ S, B j) :=
        Finset.measurableSet_biUnion S (fun j _ => hB j)
      exact abs_alpha_term_le_mul_phi (hA i) hUm
    set P : Fin J → Prop := fun j => 0 ≤ d j with hP
    classical
    have hsplit : ∑ j, |d j|
        = (∑ j ∈ Finset.univ.filter P, d j)
          + (-∑ j ∈ Finset.univ.filter (fun j => ¬ P j), d j) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P (fun j => |d j|),
        ← Finset.sum_neg_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun j hj => abs_of_nonneg (Finset.mem_filter.1 hj).2
      · exact Finset.sum_congr rfl fun j hj =>
          abs_of_neg (lt_of_not_ge (Finset.mem_filter.1 hj).2)
    rw [hsplit]
    have e1 := (le_abs_self _).trans (habs (Finset.univ.filter P))
    have e2 := (neg_le_abs _).trans (habs (Finset.univ.filter (fun j => ¬ P j)))
    linarith
  calc ∑ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      ≤ ∑ i, 2 * ((μ (A i)).toReal * phiMixCoeff μ m₁ m₂) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = 2 * phiMixCoeff μ m₁ m₂ * ∑ i, (μ (A i)).toReal := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 2 * phiMixCoeff μ m₁ m₂ := by
        have : ∑ i, (μ (A i)).toReal = 1 := by
          have huniv : MeasurableSet (Set.univ : Set Ω) := MeasurableSet.univ
          have := sum_toReal_inter (μ := μ) hAm hdA hcA huniv
          simpa using this
        rw [this, mul_one]

/-- The β description set contains `0` (the trivial one-cell partitions). -/
private lemma betaMixCoeff_set_nonempty {m₁ m₂ mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (0 : ℝ) ∈ {r : ℝ | ∃ (I J : ℕ) (A : Fin I → Set Ω) (B : Fin J → Set Ω),
      (∀ i, MeasurableSet[m₁] (A i)) ∧ (∀ j, MeasurableSet[m₂] (B j)) ∧
      (Pairwise fun i i' => Disjoint (A i) (A i')) ∧
      (Pairwise fun j j' => Disjoint (B j) (B j')) ∧
      (⋃ i, A i) = Set.univ ∧ (⋃ j, B j) = Set.univ ∧
      r = (1 / 2) * ∑ i, ∑ j,
        |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|} := by
  refine ⟨1, 1, fun _ => Set.univ, fun _ => Set.univ, fun _ => MeasurableSet.univ,
    fun _ => MeasurableSet.univ, fun i i' h => absurd (Subsingleton.elim i i') h,
    fun j j' h => absurd (Subsingleton.elim j j') h,
    Set.univ_subset_iff.mp (Set.subset_iUnion (fun _ : Fin 1 => (Set.univ : Set Ω)) 0),
    Set.univ_subset_iff.mp (Set.subset_iUnion (fun _ : Fin 1 => (Set.univ : Set Ω)) 0), ?_⟩
  simp

private lemma betaMixCoeff_set_bddAbove {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    BddAbove {r : ℝ | ∃ (I J : ℕ) (A : Fin I → Set Ω) (B : Fin J → Set Ω),
      (∀ i, MeasurableSet[m₁] (A i)) ∧ (∀ j, MeasurableSet[m₂] (B j)) ∧
      (Pairwise fun i i' => Disjoint (A i) (A i')) ∧
      (Pairwise fun j j' => Disjoint (B j) (B j')) ∧
      (⋃ i, A i) = Set.univ ∧ (⋃ j, B j) = Set.univ ∧
      r = (1 / 2) * ∑ i, ∑ j,
        |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|} := by
  refine ⟨phiMixCoeff μ m₁ m₂, ?_⟩
  rintro r ⟨I, J, A, B, hA, hB, hdA, hdB, hcA, hcB, rfl⟩
  have := beta_sum_le_two_mul_phi (μ := μ) h₁ h₂ hA hB hdA hcA hdB
  linarith

private lemma betaMixCoeff_nonneg {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) : 0 ≤ betaMixCoeff μ m₁ m₂ :=
  le_csSup (betaMixCoeff_set_bddAbove h₁ h₂) (betaMixCoeff_set_nonempty (mΩ := mΩ) μ)

theorem alphaMixCoeff_le_phiMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    alphaMixCoeff μ m₁ m₂ ≤ phiMixCoeff μ m₁ m₂ := by
  refine Real.sSup_le ?_ (phiMixCoeff_nonneg (mΩ := mΩ) (μ := μ) (m₁ := m₁) (m₂ := m₂))
  rintro r ⟨A, B, hA, hB, rfl⟩
  refine (abs_alpha_term_le_mul_phi hA hB).trans ?_
  have h1 := toReal_le_one (μ := μ) A
  have h2 : (0 : ℝ) ≤ phiMixCoeff μ m₁ m₂ :=
    phiMixCoeff_nonneg (mΩ := mΩ) (μ := μ) (m₁ := m₁) (m₂ := m₂)
  nlinarith

theorem betaMixCoeff_le_phiMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    betaMixCoeff μ m₁ m₂ ≤ phiMixCoeff μ m₁ m₂ := by
  refine Real.sSup_le ?_ (phiMixCoeff_nonneg (mΩ := mΩ) (μ := μ) (m₁ := m₁) (m₂ := m₂))
  rintro r ⟨I, J, A, B, hA, hB, hdA, hdB, hcA, hcB, rfl⟩
  have := beta_sum_le_two_mul_phi (μ := μ) h₁ h₂ hA hB hdA hcA hdB
  linarith

/-- `μ (A ∩ Bᶜ) = μ A − μ (A ∩ B)` after `toReal`. -/
private lemma toReal_inter_compl {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (A : Set Ω) {B : Set Ω} (hB : MeasurableSet B) :
    (μ (A ∩ Bᶜ)).toReal = (μ A).toReal - (μ (A ∩ B)).toReal := by
  have h := measure_inter_add_diff (μ := μ) A hB
  have h2 : (μ (A ∩ B)).toReal + (μ (A \ B)).toReal = (μ A).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h]
  rw [Set.diff_eq] at h2
  linarith

theorem two_mul_alphaMixCoeff_le_betaMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    2 * alphaMixCoeff μ m₁ m₂ ≤ betaMixCoeff μ m₁ m₂ := by
  have hβ0 : 0 ≤ betaMixCoeff μ m₁ m₂ := betaMixCoeff_nonneg h₁ h₂
  have key : alphaMixCoeff μ m₁ m₂ ≤ betaMixCoeff μ m₁ m₂ / 2 := by
    refine Real.sSup_le ?_ (by linarith)
    rintro r ⟨A, B, hA, hB, rfl⟩
    have hAm : MeasurableSet A := h₁ _ hA
    have hBm : MeasurableSet B := h₂ _ hB
    -- The four cells of `{A, Aᶜ} × {B, Bᶜ}` all have the same discrepancy.
    have eAc : (μ Aᶜ).toReal = 1 - (μ A).toReal := by
      have := toReal_inter_compl (μ := μ) Set.univ hAm
      simpa using this
    have eBc : (μ Bᶜ).toReal = 1 - (μ B).toReal := by
      have := toReal_inter_compl (μ := μ) Set.univ hBm
      simpa using this
    have e01 : (μ (A ∩ Bᶜ)).toReal = (μ A).toReal - (μ (A ∩ B)).toReal :=
      toReal_inter_compl (μ := μ) A hBm
    have e10 : (μ (Aᶜ ∩ B)).toReal = (μ B).toReal - (μ (A ∩ B)).toReal := by
      have := toReal_inter_compl (μ := μ) B hAm
      rwa [Set.inter_comm B Aᶜ, Set.inter_comm B A] at this
    have e11 : (μ (Aᶜ ∩ Bᶜ)).toReal = (μ Aᶜ).toReal - (μ (Aᶜ ∩ B)).toReal :=
      toReal_inter_compl (μ := μ) Aᶜ hBm
    set A' : Fin 2 → Set Ω := ![A, Aᶜ] with hA'
    set B' : Fin 2 → Set Ω := ![B, Bᶜ] with hB'
    have hmem : 2 * |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
        ∈ {r : ℝ | ∃ (I J : ℕ) (A : Fin I → Set Ω) (B : Fin J → Set Ω),
          (∀ i, MeasurableSet[m₁] (A i)) ∧ (∀ j, MeasurableSet[m₂] (B j)) ∧
          (Pairwise fun i i' => Disjoint (A i) (A i')) ∧
          (Pairwise fun j j' => Disjoint (B j) (B j')) ∧
          (⋃ i, A i) = Set.univ ∧ (⋃ j, B j) = Set.univ ∧
          r = (1 / 2) * ∑ i, ∑ j,
            |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|} := by
      refine ⟨2, 2, A', B', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hA', hA, hA.compl]
      · intro j; fin_cases j <;> simp [hB', hB, hB.compl]
      · intro i i' h; fin_cases i <;> fin_cases i' <;>
          simp_all [disjoint_compl_right, disjoint_compl_left]
      · intro j j' h; fin_cases j <;> fin_cases j' <;>
          simp_all [disjoint_compl_right, disjoint_compl_left]
      · refine Set.univ_subset_iff.mp fun x _ => ?_
        by_cases hx : x ∈ A
        · exact Set.mem_iUnion.2 ⟨0, by simpa [hA'] using hx⟩
        · exact Set.mem_iUnion.2 ⟨1, by simpa [hA'] using hx⟩
      · refine Set.univ_subset_iff.mp fun x _ => ?_
        by_cases hx : x ∈ B
        · exact Set.mem_iUnion.2 ⟨0, by simpa [hB'] using hx⟩
        · exact Set.mem_iUnion.2 ⟨1, by simpa [hB'] using hx⟩
      · rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
        simp only [hA', hB', Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [e01, e11, e10, eAc, eBc]
        have t2 : (μ A).toReal - (μ (A ∩ B)).toReal
            - (μ A).toReal * (1 - (μ B).toReal)
            = -((μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal) := by ring
        have t3 : (μ B).toReal - (μ (A ∩ B)).toReal
            - (1 - (μ A).toReal) * (μ B).toReal
            = -((μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal) := by ring
        have t4 : 1 - (μ A).toReal - ((μ B).toReal - (μ (A ∩ B)).toReal)
            - (1 - (μ A).toReal) * (1 - (μ B).toReal)
            = (μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal := by ring
        rw [t2, t3, t4, abs_neg]
        ring
    have hcs : 2 * |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
        ≤ betaMixCoeff μ m₁ m₂ := le_csSup (betaMixCoeff_set_bddAbove h₁ h₂) hmem
    linarith
  linarith

/-- `φ ≤ ψ` in the calibrated form `|P(B) − P(B|A)| = P(B)|1 − P(B|A)/P(B)|`
(the `P(B) = 0` cell contributes `0` on both sides).

**Statement repaired 2026-08-05**: the unconditional form is FALSE — the classical
ψ-coefficient may be `+∞`, the ψ description set is then unbounded, and Lean's
`Real.sSup` junk convention makes `psiMixCoeff = 0` (formally verified counterexample
recorded in the proof body below). The finiteness hypothesis `hψbdd` restores the
classical statement (Bradley ch. 3: `φ ≤ ψ` whenever `ψ < ∞`). -/
theorem phiMixCoeff_le_psiMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    -- USER-INPUT: finiteness of ψ (the classical coefficient may be +∞); Bradley ch. 3
    (hψbdd : BddAbove {r : ℝ | ∃ A B : Set Ω,
      MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      0 < (μ A).toReal ∧ 0 < (μ B).toReal ∧
      r = |1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal|}) :
    phiMixCoeff μ m₁ m₂ ≤ psiMixCoeff μ m₁ m₂ := by
  -- **FALSE AS FROZEN — unplanned debt (formally verified counterexample).**
  -- The ψ description set `{|1 − P(A∩B)/(P(A)P(B))| : P(A)P(B) > 0}` is *unbounded above*
  -- in general (the classical ψ-coefficient may be `+∞`; Bradley, *Introduction to Strong
  -- Mixing Conditions*), and Lean's `Real.sSup` junk convention then returns `0`
  -- (`Real.sSup_of_not_bddAbove`), so `psiMixCoeff μ m₁ m₂ = 0` while `φ` stays positive.
  --
  -- Witness (checked in Lean, 0 sorries, against these very definitions):
  --   `μ₀ := volume.restrict (Set.Icc (0:ℝ) 1)` on `Ω = ℝ`, `m₁ = m₂ = mΩ = Borel ℝ`.
  --   * `A = B = Set.Icc 0 (1/(n+2))` gives the ψ-value `|1 − a/(a·a)| = n + 1` for every
  --     `n : ℕ`, so the ψ set is not `BddAbove` and `psiMixCoeff μ₀ = 0`;
  --   * `A = B = Set.Icc 0 (1/2)` gives the φ-value `|1/2 − (1/2)/(1/2)| = 1/2`, and the
  --     φ set *is* bounded by `1`, so `phiMixCoeff μ₀ ≥ 1/2 > 0 = psiMixCoeff μ₀`.
  --
  -- REPAIR (statement-level, for a future frozen-statement revision): either add the
  -- hypothesis `BddAbove {r | …ψ description set…}` (equivalently "ψ is finite"), or state
  -- the inequality in the `ℝ≥0∞`-valued form of ψ. Under either repair the intended proof
  -- goes through verbatim: for a φ-witness `(A, B)` with `P(A) > 0`, either `P(B) = 0`
  -- (both sides `0`) or `|P(B) − P(A∩B)/P(A)| = P(B)·|1 − P(A∩B)/(P(A)P(B))| ≤ ψ`.
  sorry

/-- Cauchy–Schwarz for real `L²` integrals. -/
private lemma abs_integral_mul_le {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ| ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  set F : Lp ℝ 2 μ := hf.toLp f with hFdef
  set G : Lp ℝ 2 μ := hg.toLp g with hGdef
  have hFae : (F : Ω → ℝ) =ᵐ[μ] f := MemLp.coeFn_toLp hf
  have hGae : (G : Ω → ℝ) =ᵐ[μ] g := MemLp.coeFn_toLp hg
  have hFG : (inner ℝ F G : ℝ) = ∫ ω, f ω * g ω ∂μ := by
    rw [MeasureTheory.L2.inner_def F G]
    refine integral_congr_ae ?_
    filter_upwards [hFae, hGae] with ω h1 h2
    rw [show (inner ℝ (F ω) (G ω) : ℝ) = G ω * F ω from rfl, h1, h2, mul_comm]
  have hFF : (‖F‖ : ℝ) = Real.sqrt (∫ ω, f ω ^ 2 ∂μ) := by
    have h : (‖F‖ : ℝ) ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def F F]
      refine integral_congr_ae ?_
      filter_upwards [hFae] with ω h1
      rw [show (inner ℝ (F ω) (F ω) : ℝ) = F ω * F ω from rfl, h1, sq]
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hGG : (‖G‖ : ℝ) = Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
    have h : (‖G‖ : ℝ) ^ 2 = ∫ ω, g ω ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def G G]
      refine integral_congr_ae ?_
      filter_upwards [hGae] with ω h1
      rw [show (inner ℝ (G ω) (G ω) : ℝ) = G ω * G ω from rfl, h1, sq]
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  rw [← hFG, ← hFF, ← hGG]
  exact abs_real_inner_le_norm _ _

/-- Cauchy–Schwarz for the covariance. -/
private lemma abs_covariance_le_sqrt_mul {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |cov[f, g; μ]| ≤ Real.sqrt (variance f μ) * Real.sqrt (variance g μ) := by
  have hF : MemLp (fun ω => f ω - μ[f]) 2 μ := hf.sub (memLp_const _)
  have hG : MemLp (fun ω => g ω - μ[g]) 2 μ := hg.sub (memLp_const _)
  have hcov : cov[f, g; μ] = ∫ ω, (f ω - μ[f]) * (g ω - μ[g]) ∂μ := rfl
  rw [hcov, variance_eq_integral hf.aestronglyMeasurable.aemeasurable,
    variance_eq_integral hg.aestronglyMeasurable.aemeasurable]
  exact abs_integral_mul_le hF hG

/-- The ρ description set contains `0` (take `f = g = 0`). -/
private lemma rhoMixCoeff_set_nonempty {m₁ m₂ mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (0 : ℝ) ∈ {r : ℝ | ∃ f g : Ω → ℝ, Measurable[m₁] f ∧ Measurable[m₂] g ∧
      MemLp f 2 μ ∧ MemLp g 2 μ ∧
      r = |cov[f, g; μ]| / (Real.sqrt (variance f μ) * Real.sqrt (variance g μ))} := by
  refine ⟨fun _ => 0, fun _ => 0, measurable_const, measurable_const,
    memLp_const 0, memLp_const 0, ?_⟩
  simp [covariance]

private lemma rhoMixCoeff_set_bddAbove {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    BddAbove {r : ℝ | ∃ f g : Ω → ℝ, Measurable[m₁] f ∧ Measurable[m₂] g ∧
      MemLp f 2 μ ∧ MemLp g 2 μ ∧
      r = |cov[f, g; μ]| / (Real.sqrt (variance f μ) * Real.sqrt (variance g μ))} := by
  refine ⟨1, ?_⟩
  rintro r ⟨f, g, -, -, hf, hg, rfl⟩
  exact div_le_one_of_le₀ (abs_covariance_le_sqrt_mul hf hg)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

private lemma rhoMixCoeff_nonneg {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] : 0 ≤ rhoMixCoeff μ m₁ m₂ :=
  le_csSup (rhoMixCoeff_set_bddAbove (mΩ := mΩ)) (rhoMixCoeff_set_nonempty (mΩ := mΩ) μ)

/-- **FY's display** `α ≤ ¼ρ` (centered indicators; `Var 1_A ≤ ¼`). -/
theorem alphaMixCoeff_le_quarter_mul_rhoMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    alphaMixCoeff μ m₁ m₂ ≤ (1 / 4) * rhoMixCoeff μ m₁ m₂ := by
  have hρ0 : 0 ≤ rhoMixCoeff μ m₁ m₂ := rhoMixCoeff_nonneg (mΩ := mΩ) (μ := μ)
  refine Real.sSup_le ?_ (by linarith)
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hAm : MeasurableSet A := h₁ _ hA
  have hBm : MeasurableSet B := h₂ _ hB
  set f : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hfdef
  set g : Ω → ℝ := B.indicator (fun _ => (1 : ℝ)) with hgdef
  have hfmeas : Measurable[m₁] f := Measurable.indicator measurable_const hA
  have hgmeas : Measurable[m₂] g := Measurable.indicator measurable_const hB
  have hfL : MemLp f 2 μ := MemLp.indicator hAm (memLp_const 1)
  have hgL : MemLp g 2 μ := MemLp.indicator hBm (memLp_const 1)
  have hfint : ∫ ω, f ω ∂μ = (μ A).toReal := by
    rw [hfdef]
    simpa using integral_indicator_const (μ := μ) (1 : ℝ) hAm
  have hgint : ∫ ω, g ω ∂μ = (μ B).toReal := by
    rw [hgdef]
    simpa using integral_indicator_const (μ := μ) (1 : ℝ) hBm
  have hmulint : ∫ ω, f ω * g ω ∂μ = (μ (A ∩ B)).toReal := by
    have he : (fun ω => f ω * g ω) = (A ∩ B).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      simpa [hfdef, hgdef] using (Set.inter_indicator_mul (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) ω).symm
    rw [he]
    simpa using integral_indicator_const (μ := μ) (1 : ℝ) (hAm.inter hBm)
  have hcov : cov[f, g; μ] = (μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal := by
    rw [covariance_eq_sub hfL hgL]
    have : μ[f * g] = ∫ ω, f ω * g ω ∂μ := by simp [Pi.mul_apply]
    rw [this, hmulint, hfint, hgint]
  -- `Var 1_A = P(A)(1 − P(A)) ≤ ¼`.
  have hsqf : (fun ω => f ω ^ 2) = f := by
    funext ω
    by_cases hx : ω ∈ A <;>
      simp [hfdef, Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hsqg : (fun ω => g ω ^ 2) = g := by
    funext ω
    by_cases hx : ω ∈ B <;>
      simp [hgdef, Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hvarf : variance f μ = (μ A).toReal - (μ A).toReal ^ 2 := by
    rw [variance_eq_sub hfL]
    have : μ[f ^ 2] = ∫ ω, f ω ^ 2 ∂μ := by simp [Pi.pow_apply]
    rw [this, hsqf, hfint]
  have hvarg : variance g μ = (μ B).toReal - (μ B).toReal ^ 2 := by
    rw [variance_eq_sub hgL]
    have : μ[g ^ 2] = ∫ ω, g ω ^ 2 ∂μ := by simp [Pi.pow_apply]
    rw [this, hsqg, hgint]
  have hsf : Real.sqrt (variance f μ) ≤ 1 / 2 := by
    have h1 := toReal_le_one (μ := μ) A
    have h0 : (0:ℝ) ≤ (μ A).toReal := ENNReal.toReal_nonneg
    have hb : variance f μ ≤ (1 / 2) ^ 2 := by
      rw [hvarf]; nlinarith [sq_nonneg ((μ A).toReal - 1 / 2)]
    calc Real.sqrt (variance f μ) ≤ Real.sqrt ((1/2 : ℝ) ^ 2) := Real.sqrt_le_sqrt hb
      _ = 1 / 2 := Real.sqrt_sq (by norm_num)
  have hsg : Real.sqrt (variance g μ) ≤ 1 / 2 := by
    have h1 := toReal_le_one (μ := μ) B
    have h0 : (0:ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
    have hb : variance g μ ≤ (1 / 2) ^ 2 := by
      rw [hvarg]; nlinarith [sq_nonneg ((μ B).toReal - 1 / 2)]
    calc Real.sqrt (variance g μ) ≤ Real.sqrt ((1/2 : ℝ) ^ 2) := Real.sqrt_le_sqrt hb
      _ = 1 / 2 := Real.sqrt_sq (by norm_num)
  set D : ℝ := Real.sqrt (variance f μ) * Real.sqrt (variance g μ) with hD
  have hD0 : 0 ≤ D := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hD4 : D ≤ 1 / 4 := by
    have := mul_le_mul hsf hsg (Real.sqrt_nonneg _) (by norm_num)
    calc D ≤ (1/2 : ℝ) * (1/2) := this
      _ = 1 / 4 := by norm_num
  rcases eq_or_lt_of_le hD0 with hD0' | hDpos
  · -- degenerate: Cauchy–Schwarz forces a vanishing covariance
    have := abs_covariance_le_sqrt_mul hfL hgL
    rw [← hD, ← hD0'] at this
    rw [← hcov]
    linarith [abs_nonneg (cov[f, g; μ])]
  · have hmem : |cov[f, g; μ]| / D ≤ rhoMixCoeff μ m₁ m₂ :=
      le_csSup (rhoMixCoeff_set_bddAbove (mΩ := mΩ)) ⟨f, g, hfmeas, hgmeas, hfL, hgL, rfl⟩
    have hkey : |cov[f, g; μ]| = (|cov[f, g; μ]| / D) * D := by
      field_simp
    rw [← hcov, hkey]
    have h1 : 0 ≤ |cov[f, g; μ]| / D := div_nonneg (abs_nonneg _) hD0
    nlinarith

/-- **DEBT (Bradley/Peligrad; FY §2.6.1 display `¼ρ ≤ ½√φ`)**: the square-root
relation `ρ ≤ 2√φ`. Literature-level; the proof needs the L²-duality description of
`ρ` and a two-sided conditional Cauchy–Schwarz argument. -/
theorem rhoMixCoeff_le_two_mul_sqrt_phiMixCoeff_debt {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    rhoMixCoeff μ m₁ m₂ ≤ 2 * Real.sqrt (phiMixCoeff μ m₁ m₂) := by
  sorry

end TwoAlgebras2

/-! ### Mixing-class implications (FY Definition 2.11 chain) -/

section Process2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The process past σ-algebra sits inside the ambient one once the coordinates are
measurable. -/
private lemma sigmaLE_le_ambient {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (n : ℤ) :
    sigmaLE X n ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

/-- The process future σ-algebra sits inside the ambient one. -/
private lemma sigmaGE_le_ambient {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (n : ℤ) :
    sigmaGE X n ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

/-- ψ-mixing ⇒ φ-mixing.

**Statement repaired 2026-08-05**: needs per-lag finiteness of ψ, for the same reason
as `phiMixCoeff_le_psiMixCoeff` (formally verified counterexample in the proof body:
constant-in-time process on `[0,1]` has junk `ψ ≡ 0` but `φ ≥ 1/2`). -/
theorem IsPsiMixing.isPhiMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsPsiMixing X μ)
    -- USER-INPUT: per-lag finiteness of ψ; Bradley ch. 3 / FY Def 2.11 implicit
    (hψbdd : ∀ n : ℕ, BddAbove {r : ℝ | ∃ A B : Set Ω,
      MeasurableSet[sigmaLE X 0] A ∧ MeasurableSet[sigmaGE X (n : ℤ)] B ∧
      0 < (μ A).toReal ∧ 0 < (μ B).toReal ∧
      r = |1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal|}) :
    IsPhiMixing X μ := by
  -- **FALSE AS FROZEN — unplanned debt (formally verified counterexample).** The process
  -- shadow of `phiMixCoeff_le_psiMixCoeff`'s falsity: with `μ₀ = volume.restrict (Icc 0 1)`
  -- on `Ω = ℝ` and the constant-in-time process `X t ω = ω`, both flanking σ-algebras are
  -- the full Borel σ-algebra (`sigmaLE X c = sigmaGE X c = Borel ℝ`), so
  -- `psiCoeff X μ₀ n = 0` for every `n` (junk value of an unbounded `Real.sSup`) — hence
  -- `IsPsiMixing X μ₀` holds — while `phiCoeff X μ₀ n ≥ 1/2` for every `n`, so
  -- `IsPhiMixing X μ₀` fails. Checked in Lean with 0 sorries.
  -- The repair is the one recorded on `phiMixCoeff_le_psiMixCoeff`: once ψ is finite
  -- (or `ℝ≥0∞`-valued), `φ(n) ≤ ψ(n)` and the squeeze against `0 ≤ φ(n)` closes this.
  sorry

/-- φ-mixing ⇒ β-mixing. -/
theorem IsPhiMixing.isBetaMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsPhiMixing X μ) : IsBetaMixing X μ :=
  squeeze_zero
    (fun n => betaMixCoeff_nonneg (sigmaLE_le_ambient hmeas 0) (sigmaGE_le_ambient hmeas n))
    (fun n => betaMixCoeff_le_phiMixCoeff (sigmaLE_le_ambient hmeas 0)
      (sigmaGE_le_ambient hmeas n)) h

/-- β-mixing ⇒ α-mixing. -/
theorem IsBetaMixing.isAlphaMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsBetaMixing X μ) : IsAlphaMixing X μ := by
  have hg : Tendsto (fun n : ℕ => 1 / 2 * betaCoeff X μ n) atTop (𝓝 0) := by
    have := h.const_mul (1 / 2 : ℝ)
    simpa using this
  refine squeeze_zero (fun n => alphaMixCoeff_nonneg (μ := μ)) (fun n => ?_) hg
  have := two_mul_alphaMixCoeff_le_betaMixCoeff (μ := μ)
    (sigmaLE_le_ambient hmeas 0) (sigmaGE_le_ambient hmeas n)
  unfold alphaCoeff betaCoeff
  linarith

/-- ρ-mixing ⇒ α-mixing. -/
theorem IsRhoMixing.isAlphaMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsRhoMixing X μ) : IsAlphaMixing X μ := by
  have hg : Tendsto (fun n : ℕ => 1 / 4 * rhoCoeff X μ n) atTop (𝓝 0) := by
    have := h.const_mul (1 / 4 : ℝ)
    simpa using this
  refine squeeze_zero (fun n => alphaMixCoeff_nonneg (μ := μ)) (fun n => ?_) hg
  show alphaCoeff X μ n ≤ 1 / 4 * rhoCoeff X μ n
  unfold alphaCoeff rhoCoeff
  exact alphaMixCoeff_le_quarter_mul_rhoMixCoeff (μ := μ)
    (sigmaLE_le_ambient hmeas 0) (sigmaGE_le_ambient hmeas n)

/-! ### Heredity and the shift lemma -/

/-- **Heredity** (FY §2.6.1(iv)): an instantaneous measurable transform
`Y_t = g(X_t)` has smaller past/future σ-algebras, hence smaller α-coefficients; α-mixing
is inherited. (The same argument applies verbatim to β, ρ, φ, ψ via
`alphaMixCoeff_mono`-analogues; α is the one consumed downstream.) -/
theorem IsAlphaMixing.comp [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (h : IsAlphaMixing X μ) {g : ℝ → ℝ} (hg : Measurable g) :
    IsAlphaMixing (fun t ω => g (X t ω)) μ := by
  -- `σ(g ∘ X_s) = comap (X s) (comap g Borel) ≤ σ(X_s)`, so both flanking σ-algebras shrink.
  have hcomap : ∀ s : ℤ,
      MeasurableSpace.comap (fun ω => g (X s ω)) inferInstance
        ≤ MeasurableSpace.comap (X s) inferInstance := by
    intro s
    have he : MeasurableSpace.comap (fun ω => g (X s ω)) (inferInstance : MeasurableSpace ℝ)
        = MeasurableSpace.comap (X s) (MeasurableSpace.comap g inferInstance) :=
      (MeasurableSpace.comap_comp).symm
    rw [he]
    exact MeasurableSpace.comap_mono hg.comap_le
  refine squeeze_zero (fun n => alphaMixCoeff_nonneg (μ := μ)) (fun n => ?_) h
  exact alphaMixCoeff_mono (iSup₂_mono fun s _ => hcomap s) (iSup₂_mono fun s _ => hcomap s)

omit [MeasurableSpace Ω] in
/-- The path map of a shifted process pulls the coordinate σ-algebras back to the process
σ-algebras. -/
private lemma comap_path_cylinderEvents (X : ℤ → Ω → ℝ) (k : ℤ) (S : Set ℤ) :
    MeasurableSpace.comap (fun ω (t : ℤ) => X (t + k) ω) (cylinderEvents S)
      = ⨆ s ∈ S, MeasurableSpace.comap (X (s + k)) inferInstance := by
  unfold cylinderEvents
  rw [MeasurableSpace.comap_iSup]
  refine iSup_congr fun s => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_congr fun _ => ?_
  rw [MeasurableSpace.comap_comp]
  rfl

omit [MeasurableSpace Ω] in
private lemma iSup_Iic_shift (X : ℤ → Ω → ℝ) (c k : ℤ) :
    (⨆ s ∈ Set.Iic c, MeasurableSpace.comap (X (s + k)) inferInstance) = sigmaLE X (c + k) := by
  refine le_antisymm (iSup₂_le fun s hs => ?_) (iSup₂_le fun u hu => ?_)
  · exact le_iSup₂_of_le (s + k) (Set.mem_Iic.mpr (by have : s ≤ c := hs; omega)) le_rfl
  · refine le_iSup₂_of_le (u - k) (Set.mem_Iic.mpr (by have : u ≤ c + k := hu; omega)) ?_
    exact le_of_eq (by rw [sub_add_cancel])

omit [MeasurableSpace Ω] in
private lemma iSup_Ici_shift (X : ℤ → Ω → ℝ) (c k : ℤ) :
    (⨆ s ∈ Set.Ici c, MeasurableSpace.comap (X (s + k)) inferInstance) = sigmaGE X (c + k) := by
  refine le_antisymm (iSup₂_le fun s hs => ?_) (iSup₂_le fun u hu => ?_)
  · exact le_iSup₂_of_le (s + k) (Set.mem_Ici.mpr (by have : c ≤ s := hs; omega)) le_rfl
  · refine le_iSup₂_of_le (u - k) (Set.mem_Ici.mpr (by have : c + k ≤ u := hu; omega)) ?_
    exact le_of_eq (by rw [sub_add_cancel])

omit [MeasurableSpace Ω] in
private lemma cylinderEvents_le (S : Set ℤ) :
    cylinderEvents (X := fun _ : ℤ => ℝ) S ≤ MeasurableSpace.pi :=
  iSup₂_le fun i _ => (measurable_pi_apply i).comap_le

/-- Strict stationarity transported to a finite index set: the law of `(X_{i+k})_{i ∈ s}`
is the law of `(X_i)_{i ∈ s}`. -/
private lemma map_finsetTuple_shift {X : ℤ → Ω → ℝ} (hstat : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) (k : ℤ) (s : Finset ℤ) :
    (μ.map fun ω (i : s) => X ((i : ℤ) + k) ω)
      = μ.map fun ω (i : s) => X (i : ℤ) ω := by
  classical
  set e : s ≃ Fin s.card := s.equivFin with he
  set t : Fin s.card → ℤ := fun j => ((e.symm j : s) : ℤ) with ht
  set Φ : (Fin s.card → ℝ) → (∀ _ : s, ℝ) := fun p i => p (e i) with hΦdef
  have hΦ : Measurable Φ := measurable_pi_lambda _ fun i => measurable_pi_apply (e i)
  have hte : ∀ i : s, t (e i) = (i : ℤ) := by
    intro i; simp [ht]
  have hcomp : ∀ c : ℤ, Measurable fun ω (j : Fin s.card) => X (t j + c) ω :=
    fun c => measurable_pi_lambda _ fun j => hmeas _
  have hpush : ∀ c : ℤ,
      (μ.map fun ω (j : Fin s.card) => X (t j + c) ω).map Φ
        = μ.map fun ω (i : s) => X ((i : ℤ) + c) ω := by
    intro c
    rw [Measure.map_map hΦ (hcomp c)]
    congr 1
    funext ω i
    simp [hΦdef, hte i]
  have h0 : (μ.map fun ω (j : Fin s.card) => X (t j + 0) ω)
      = μ.map fun ω (j : Fin s.card) => X (t j) ω := by simp
  calc (μ.map fun ω (i : s) => X ((i : ℤ) + k) ω)
      = (μ.map fun ω (j : Fin s.card) => X (t j + k) ω).map Φ := (hpush k).symm
    _ = (μ.map fun ω (j : Fin s.card) => X (t j) ω).map Φ := by rw [hstat s.card t k]
    _ = (μ.map fun ω (j : Fin s.card) => X (t j + 0) ω).map Φ := by rw [h0]
    _ = μ.map fun ω (i : s) => X ((i : ℤ) + 0) ω := hpush 0
    _ = μ.map fun ω (i : s) => X (i : ℤ) ω := by simp

/-- **Strict stationarity = shift-invariance of the path law.** -/
private lemma map_path_shift {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t)) (k : ℤ) :
    (μ.map fun ω (u : ℤ) => X (u + k) ω) = μ.map fun ω (u : ℤ) => X u ω := by
  have hTm : Measurable fun ω (u : ℤ) => X (u + k) ω :=
    measurable_pi_lambda _ fun _ => hmeas _
  have hUm : Measurable fun ω (u : ℤ) => X u ω := measurable_pi_lambda _ fun _ => hmeas _
  refine ext_of_generate_finite (measurableCylinders fun _ : ℤ => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro C hC
    obtain ⟨s, S, hSm, rfl⟩ := (mem_measurableCylinders C).mp hC
    have hcyl : MeasurableSet (cylinder s S) := MeasurableSet.cylinder (α := fun _ : ℤ => ℝ) s hSm
    have hT : Measurable fun ω (i : s) => X ((i : ℤ) + k) ω :=
      measurable_pi_lambda _ fun _ => hmeas _
    have hU : Measurable fun ω (i : s) => X (i : ℤ) ω :=
      measurable_pi_lambda _ fun _ => hmeas _
    have eT : (μ.map fun ω (u : ℤ) => X (u + k) ω) (cylinder s S)
        = (μ.map fun ω (i : s) => X ((i : ℤ) + k) ω) S := by
      rw [Measure.map_apply hTm hcyl, Measure.map_apply hT hSm]
      rfl
    have eU : (μ.map fun ω (u : ℤ) => X u ω) (cylinder s S)
        = (μ.map fun ω (i : s) => X (i : ℤ) ω) S := by
      rw [Measure.map_apply hUm hcyl, Measure.map_apply hU hSm]
      rfl
    rw [eT, eU, map_finsetTuple_shift hstat hmeas k s]
  · rw [Measure.map_apply hTm MeasurableSet.univ, Measure.map_apply hUm MeasurableSet.univ]
    simp

/-- The α-coefficient between two pulled-back σ-algebras only depends on the pushforward
law. -/
private lemma alphaMixCoeff_comap {V : Ω → (ℤ → ℝ)} (hV : Measurable V)
    {ν : Measure (ℤ → ℝ)} (hν : μ.map V = ν)
    (m₁ m₂ : MeasurableSpace (ℤ → ℝ)) (h₁ : m₁ ≤ MeasurableSpace.pi)
    (h₂ : m₂ ≤ MeasurableSpace.pi) :
    alphaMixCoeff μ (m₁.comap V) (m₂.comap V)
      = @alphaMixCoeff (ℤ → ℝ) MeasurableSpace.pi ν m₁ m₂ := by
  have hval : ∀ {S : Set (ℤ → ℝ)},
      @MeasurableSet (ℤ → ℝ) MeasurableSpace.pi S → ν S = μ (V ⁻¹' S) := by
    intro S hS
    rw [← hν]
    exact Measure.map_apply hV hS
  unfold alphaMixCoeff
  refine congrArg sSup (Set.ext fun r => ?_)
  constructor
  · rintro ⟨A, B, ⟨A', hA', rfl⟩, ⟨B', hB', rfl⟩, rfl⟩
    refine ⟨A', B', hA', hB', ?_⟩
    have e3 : ν (A' ∩ B') = μ (V ⁻¹' A' ∩ V ⁻¹' B') := by
      rw [hval (@MeasurableSet.inter (ℤ → ℝ) MeasurableSpace.pi _ _ (h₁ _ hA') (h₂ _ hB')),
        Set.preimage_inter]
    rw [hval (h₁ _ hA'), hval (h₂ _ hB'), e3]
  · rintro ⟨A', B', hA', hB', rfl⟩
    refine ⟨V ⁻¹' A', V ⁻¹' B', ⟨A', hA', rfl⟩, ⟨B', hB', rfl⟩, ?_⟩
    have e3 : ν (A' ∩ B') = μ (V ⁻¹' A' ∩ V ⁻¹' B') := by
      rw [hval (@MeasurableSet.inter (ℤ → ℝ) MeasurableSpace.pi _ _ (h₁ _ hA') (h₂ _ hB')),
        Set.preimage_inter]
    rw [hval (h₁ _ hA'), hval (h₂ _ hB'), e3]

/-- **Shift lemma** (used silently by every FY block argument): under strict
stationarity, the α-coefficient between the past up to `k` and the future from `k + n`
does not depend on the anchor `k`. -/
theorem IsStrictlyStationary.alphaMixCoeff_shift [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hstat : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) (k : ℤ) (n : ℕ) :
    alphaMixCoeff μ (sigmaLE X k) (sigmaGE X (k + n)) = alphaCoeff X μ n := by
  have hTm : Measurable fun ω (u : ℤ) => X (u + k) ω := measurable_pi_lambda _ fun _ => hmeas _
  have hUm : Measurable fun ω (u : ℤ) => X u ω := measurable_pi_lambda _ fun _ => hmeas _
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (ℤ → ℝ), (μ.map fun ω (u : ℤ) => X u ω) = ν := ⟨_, rfl⟩
  have hνT : (μ.map fun ω (u : ℤ) => X (u + k) ω) = ν := by
    rw [← hν]; exact map_path_shift hstat hmeas k
  have hLk : MeasurableSpace.comap (fun ω (u : ℤ) => X (u + k) ω) (cylinderEvents (Set.Iic 0))
      = sigmaLE X k := by
    rw [comap_path_cylinderEvents X k (Set.Iic 0), iSup_Iic_shift X 0 k, zero_add]
  have hGk : MeasurableSpace.comap (fun ω (u : ℤ) => X (u + k) ω)
      (cylinderEvents (Set.Ici (n : ℤ))) = sigmaGE X (k + n) := by
    rw [comap_path_cylinderEvents X k (Set.Ici (n : ℤ)), iSup_Ici_shift X (n : ℤ) k, add_comm]
  have hL0 : MeasurableSpace.comap (fun ω (u : ℤ) => X u ω) (cylinderEvents (Set.Iic 0))
      = sigmaLE X 0 := by
    have h := comap_path_cylinderEvents X 0 (Set.Iic 0)
    simp only [add_zero] at h
    exact h
  have hG0 : MeasurableSpace.comap (fun ω (u : ℤ) => X u ω) (cylinderEvents (Set.Ici (n : ℤ)))
      = sigmaGE X (n : ℤ) := by
    have h := comap_path_cylinderEvents X 0 (Set.Ici (n : ℤ))
    simp only [add_zero] at h
    exact h
  calc alphaMixCoeff μ (sigmaLE X k) (sigmaGE X (k + n))
      = alphaMixCoeff μ ((cylinderEvents (Set.Iic 0)).comap fun ω (u : ℤ) => X (u + k) ω)
          ((cylinderEvents (Set.Ici (n : ℤ))).comap fun ω (u : ℤ) => X (u + k) ω) := by
        rw [hLk, hGk]
    _ = @alphaMixCoeff (ℤ → ℝ) MeasurableSpace.pi ν (cylinderEvents (Set.Iic 0))
          (cylinderEvents (Set.Ici (n : ℤ))) :=
        alphaMixCoeff_comap hTm hνT _ _ (cylinderEvents_le _) (cylinderEvents_le _)
    _ = alphaMixCoeff μ ((cylinderEvents (Set.Iic 0)).comap fun ω (u : ℤ) => X u ω)
          ((cylinderEvents (Set.Ici (n : ℤ))).comap fun ω (u : ℤ) => X u ω) :=
        (alphaMixCoeff_comap hUm hν _ _ (cylinderEvents_le _) (cylinderEvents_le _)).symm
    _ = alphaCoeff X μ n := by rw [hL0, hG0]; rfl

/-! ### The deterministic non-example (FY §2.6.1(ix)) -/

/-- **FY §2.6.1(ix), quantitative core**: for a deterministic recursion
`X_{t+1} = m(X_t)` every event of the time-`n` state lies in the past σ-algebra as
well, so `α(n) ≥ P(X_n ∈ C)(1 − P(X_n ∈ C))`. -/
theorem alphaCoeff_ge_of_deterministic [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) {m : ℝ → ℝ} (hm : Measurable m)
    -- USER-INPUT: deterministic recursion; FY §2.6.1(ix)
    (hrec : ∀ t : ℤ, ∀ ω, X (t + 1) ω = m (X t ω))
    {C : Set ℝ} (hC : MeasurableSet C) (n : ℕ) :
    (μ (X n ⁻¹' C)).toReal * (1 - (μ (X n ⁻¹' C)).toReal)
      ≤ alphaCoeff X μ n := by
  -- The recursion solves as `X_n = m^[n] ∘ X_0`, so the time-`n` state is `𝓕_{-∞}^0`-measurable.
  have hiter : ∀ (k : ℕ) (ω : Ω), X (k : ℤ) ω = m^[k] (X 0 ω) := by
    intro k
    induction k with
    | zero => intro ω; simp
    | succ k ih =>
      intro ω
      have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [hcast, hrec (k : ℤ) ω, ih ω]
      exact (Function.iterate_succ_apply' m k (X 0 ω)).symm
  have hDm : MeasurableSet (m^[n] ⁻¹' C) := (hm.iterate n) hC
  have hset : X (n : ℤ) ⁻¹' C = X 0 ⁻¹' (m^[n] ⁻¹' C) := by
    ext ω; simp [Set.mem_preimage, hiter n ω]
  set A : Set Ω := X (n : ℤ) ⁻¹' C with hAdef
  have hA1 : MeasurableSet[sigmaLE X 0] A := by
    have hcomap : MeasurableSpace.comap (X 0) inferInstance ≤ sigmaLE X 0 :=
      le_iSup₂_of_le (0 : ℤ) (Set.mem_Iic.mpr le_rfl) le_rfl
    refine hcomap _ ?_
    exact ⟨m^[n] ⁻¹' C, hDm, hset.symm⟩
  have hA2 : MeasurableSet[sigmaGE X (n : ℤ)] A := by
    have hcomap : MeasurableSpace.comap (X (n : ℤ)) inferInstance ≤ sigmaGE X (n : ℤ) :=
      le_iSup₂_of_le (n : ℤ) (Set.mem_Ici.mpr le_rfl) le_rfl
    exact hcomap _ ⟨C, hC, rfl⟩
  have hp0 : (0 : ℝ) ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have hp1 : (μ A).toReal ≤ 1 := toReal_le_one (μ := μ) A
  have hval : (μ A).toReal * (1 - (μ A).toReal)
      = |(μ (A ∩ A)).toReal - (μ A).toReal * (μ A).toReal| := by
    rw [Set.inter_self]
    rw [abs_of_nonneg (by nlinarith : (0:ℝ) ≤ (μ A).toReal - (μ A).toReal * (μ A).toReal)]
    ring
  rw [hval]
  have hbdd := alphaMixCoeff_set_bddAbove (μ := μ) (m₁ := sigmaLE X 0) (m₂ := sigmaGE X (n : ℤ))
  exact le_csSup hbdd ⟨A, A, hA1, hA2, rfl⟩

/-- **FY §2.6.1(ix)**: a deterministic recursion with uniformly non-degenerate events is
not α-mixing. -/
theorem not_isAlphaMixing_of_deterministic [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) {m : ℝ → ℝ} (hm : Measurable m)
    (hrec : ∀ t : ℤ, ∀ ω, X (t + 1) ω = m (X t ω))
    -- USER-INPUT: uniform non-degeneracy of some tail events; FY §2.6.1(ix)
    {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1 / 2)
    (hC : ∀ n : ℕ, ∃ C : Set ℝ, MeasurableSet C ∧
      c ≤ (μ (X n ⁻¹' C)).toReal ∧ (μ (X n ⁻¹' C)).toReal ≤ 1 - c) :
    ¬ IsAlphaMixing X μ := by
  intro hmix
  have hpos : 0 < c * (1 - c) := by nlinarith
  obtain ⟨n, hn⟩ := (hmix.eventually (gt_mem_nhds hpos)).exists
  obtain ⟨C, hCm, hc1, hc2⟩ := hC n
  have hge := alphaCoeff_ge_of_deterministic (μ := μ) hmeas hm hrec hCm n
  have hprod : 0 ≤ ((μ (X n ⁻¹' C)).toReal - c) * (1 - (μ (X n ⁻¹' C)).toReal - c) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-! ### Literature statement DEBTS (FY §2.6.1(v), (viii), (x)) -/

/-- **DEBT (Pham–Tran 1985; FY §2.6.1(v))**: a stationary causal ARMA process with
iid innovations admitting an (absolutely continuous) density is exponentially
β-mixing. -/
theorem arma_betaCoeff_exponential_debt [IsProbabilityMeasure μ]
    {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hstat : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: iid innovations with a Lebesgue density; Pham–Tran 1985
    (hiid : IsIIDNoise ε σ2 μ)
    (hdens : ∃ g : ℝ → ℝ, Measurable g ∧
      μ.map (ε 0) = MeasureTheory.volume.withDensity fun x => ENNReal.ofReal (g x))
    -- USER-INPUT: no roots of b on the closed unit disc (causality; stated inline —
    -- this concept-layer file must not import `Stationarity/ARMAExistence`); FY §2.1
    (hroot : ∀ z : ℂ, ‖z‖ ≤ 1 → Polynomial.aeval z (arPoly b) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ n : ℕ, betaCoeff X μ n ≤ C * r ^ n := by
  sorry

/-- **DEBT (Basrak–Davis–Mikosch 2002; FY §2.6.1(x))**: a strictly stationary
GARCH(p, q) process with `Σᵢ bᵢ + Σⱼ aⱼ < 1` whose iid innovations have a Lebesgue
density positive in a neighbourhood of `0` is exponentially α-mixing. -/
theorem garch_alphaCoeff_exponential_debt [IsProbabilityMeasure μ]
    {c0 : ℝ} {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: contraction of the GARCH coefficients; BDM 2002 / FY §2.6.1(x)
    (hsum : ∑ i, b i + ∑ j, a j < 1)
    -- USER-INPUT: innovation density positive near zero; BDM 2002
    (hdens : ∃ g : ℝ → ℝ, Measurable g ∧
      μ.map (ε 0) = MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x| < δ → 0 < g x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ n : ℕ, alphaCoeff X μ n ≤ C * r ^ n := by
  sorry

/-- **DEBT (Kolmogorov–Rozanov 1960; FY §2.6.1(viii))**: for a (strictly stationary)
Gaussian process, α-mixing already implies ρ-mixing (the coefficients are comparable:
`ρ(n) ≤ 2π α(n)`). -/
theorem gaussian_rho_le_alpha_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: Gaussian process; Kolmogorov–Rozanov
    (hgauss : ProbabilityTheory.IsGaussianProcess X μ) (n : ℕ) :
    rhoCoeff X μ n ≤ 2 * Real.pi * alphaCoeff X μ n := by
  sorry

end Process2

end StatLean.TimeSeries
