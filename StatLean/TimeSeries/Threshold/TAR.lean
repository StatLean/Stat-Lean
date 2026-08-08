import StatLean.TimeSeries.Models.Defs
import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity
import StatLean.TimeSeries.Process.Stationary
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Threshold autoregression: structure and stationarity (FY §4.1.1, Definition 4.1)

The `k`-regime TAR model is `Models/Defs.lean`'s `IsTAR` (FY eq. (4.1)). This file
carries the §4.1.1 structural facts:

* **SETAR** (`IsSETAR`): the interval-partition special case
  `A_i = (r_{i−1}, r_i]` with `−∞ = r_0 < ⋯ < r_k = +∞`, and the fact that a SETAR
  partition is a legitimate TAR partition;
* the **stationarity claim** of pp. 126–127 ("easy to see from Theorem 2.4"): under
  (a) equal regime scales `σ₁ = ⋯ = σ_k` *(the book prints `σ_p` — typo)* and
  (b) `max_i Σ_j |b_{ij}| < 1`, a strictly stationary solution exists. FY delegates
  this entirely to §2.1.4's Theorem 2.4 + Example 2.1, so we state it as a corollary
  of the Markov-layer debt `nlARKernel_geometricallyErgodic` (whose closure is
  batch F's `ts/f-thm24`): the TAR autoregression function is the `nlARKernel`
  drift function, and the contraction condition (b) is the Lyapunov input;
* the **canonical toy instance** eq. (4.2), `X_t = ∓0.7 X_{t−1} + ε_t` according to the
  sign of `X_{t−1} − r`, exhibited as a two-regime SETAR satisfying (a)+(b).

**Scope.** FY Theorems 4.1 and 4.2 (Chan 1993a: strong consistency; `T(r̂ − r) = O_p(1)`
and the associated asymptotics) and their consumers were **descoped on 2026-08-04** at
the user's direction and are not stated anywhere in this area.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.1.1,
Definition 4.1, eqs. (4.1)–(4.3) and the stationarity discussion pp. 126–127.
(`FY §4.1.1`.)

**Bibliographic comments.** Threshold autoregression is H. Tong (1978; *Non-linear Time
Series: A Dynamical System Approach*, OUP 1990); the drift/ergodicity route for TAR
stationarity is An & Huang (1996) and Chan & Tong (1985).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **SETAR interval partition** determined by ordered thresholds
`r : Fin (k − 1) → ℝ`: regime `i` is `(r_{i−1}, r_i]` with the conventions
`r_{−1} = −∞`, `r_{k−1} = +∞`. -/
def setarPartition {k : ℕ} (r : Fin k → ℝ) : Fin (k + 1) → Set ℝ := fun i =>
  {x : ℝ | (∀ j : Fin k, (j : ℕ) < (i : ℕ) → r j < x) ∧
    ∀ j : Fin k, (i : ℕ) ≤ (j : ℕ) → x ≤ r j}

-- The regime `i` is a finite intersection of half-lines: for each threshold index `j`
-- one of the two guards is vacuous and the other cuts out an `Ioi` resp. an `Iic`.
private lemma setarPartition_eq_iInter {k : ℕ} (r : Fin k → ℝ) (i : Fin (k + 1)) :
    setarPartition r i =
      (⋂ j : Fin k, {x : ℝ | (j : ℕ) < (i : ℕ) → r j < x}) ∩
        ⋂ j : Fin k, {x : ℝ | (i : ℕ) ≤ (j : ℕ) → x ≤ r j} := by
  ext x
  simp only [setarPartition, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]

-- The **regime index of a point**: the number of thresholds strictly below `x`. Under
-- `StrictMono r` the set `{j | r j < x}` is a down-closed initial segment of `Fin k`, so
-- its cardinality is exactly the index of the regime containing `x`.
private noncomputable def setarIndex {k : ℕ} (r : Fin k → ℝ) (x : ℝ) : Fin (k + 1) :=
  ⟨(Finset.univ.filter fun j : Fin k => r j < x).card,
    Nat.lt_succ_of_le (by simpa using Finset.card_filter_le (Finset.univ : Finset (Fin k)) _)⟩

-- Existence: `x` lies in the regime indexed by its threshold count. Both halves are
-- cardinality arguments against the initial segment `Iio j` resp. `Iic j`.
private lemma mem_setarPartition_setarIndex {k : ℕ} {r : Fin k → ℝ} (hr : StrictMono r)
    (x : ℝ) : x ∈ setarPartition r (setarIndex r x) := by
  classical
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · -- `j` is below the count, so `r j < x`: otherwise `{j' | r j' < x} ⊆ Iio j`.
    by_contra hx
    push_neg at hx
    have hsub : (Finset.univ.filter fun j' : Fin k => r j' < x) ⊆ Finset.Iio j := by
      intro j' hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
      simp only [Finset.mem_Iio]
      by_contra hle
      push_neg at hle
      exact absurd (lt_of_lt_of_le (lt_of_lt_of_le hj' hx) (hr.monotone hle)) (lt_irrefl _)
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    simp only [setarIndex] at hj
    omega
  · -- `j` is at or above the count, so `x ≤ r j`: otherwise `Iic j ⊆ {j' | r j' < x}`.
    by_contra hx
    push_neg at hx
    have hsub : Finset.Iic j ⊆ Finset.univ.filter fun j' : Fin k => r j' < x := by
      intro j' hj'
      simp only [Finset.mem_Iic] at hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt (hr.monotone hj') hx
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    simp only [setarIndex] at hj
    omega

-- Uniqueness: a point cannot lie in two regimes. If `i < i'` then `j := i` is a legitimate
-- threshold index, and the two memberships give `r j < x` and `x ≤ r j`.
private lemma setarPartition_not_mem_of_lt {k : ℕ} {r : Fin k → ℝ} {x : ℝ}
    {i i' : Fin (k + 1)} (h : x ∈ setarPartition r i) (h' : x ∈ setarPartition r i')
    (hlt : (i : ℕ) < (i' : ℕ)) : False := by
  have hik : (i : ℕ) < k := lt_of_lt_of_le hlt (Nat.lt_succ_iff.mp i'.isLt)
  have h1 : r ⟨(i : ℕ), hik⟩ < x := h'.1 ⟨(i : ℕ), hik⟩ hlt
  have h2 : x ≤ r ⟨(i : ℕ), hik⟩ := h.2 ⟨(i : ℕ), hik⟩ le_rfl
  linarith

/-- A SETAR partition is a measurable partition of `ℝ` (so `IsTAR` applies to it):
the regimes are measurable, pairwise disjoint, and cover the line. -/
theorem setarPartition_isPartition {k : ℕ} {r : Fin k → ℝ} (hr : StrictMono r) :
    (∀ i, MeasurableSet (setarPartition r i)) ∧
      (Pairwise fun i j => Disjoint (setarPartition r i) (setarPartition r j)) ∧
      (⋃ i, setarPartition r i) = Set.univ := by
  classical
  refine ⟨fun i => ?_, fun i i' hne => ?_, ?_⟩
  · rw [setarPartition_eq_iInter]
    refine MeasurableSet.inter (MeasurableSet.iInter fun j => ?_)
      (MeasurableSet.iInter fun j => ?_)
    · by_cases h : (j : ℕ) < (i : ℕ)
      · have he : {x : ℝ | (j : ℕ) < (i : ℕ) → r j < x} = Set.Ioi (r j) := by
          ext x; simp [h, Set.mem_Ioi]
        rw [he]; exact measurableSet_Ioi
      · have he : {x : ℝ | (j : ℕ) < (i : ℕ) → r j < x} = Set.univ := by
          ext x; simp [h]
        rw [he]; exact MeasurableSet.univ
    · by_cases h : (i : ℕ) ≤ (j : ℕ)
      · have he : {x : ℝ | (i : ℕ) ≤ (j : ℕ) → x ≤ r j} = Set.Iic (r j) := by
          ext x; simp [h, Set.mem_Iic]
        rw [he]; exact measurableSet_Iic
      · have he : {x : ℝ | (i : ℕ) ≤ (j : ℕ) → x ≤ r j} = Set.univ := by
          ext x; simp [h]
        rw [he]; exact MeasurableSet.univ
  · refine Set.disjoint_left.mpr fun x hx hx' => ?_
    rcases lt_or_gt_of_ne (fun hcon : (i : ℕ) = (i' : ℕ) => hne (Fin.ext hcon)) with h | h
    · exact setarPartition_not_mem_of_lt hx hx' h
    · exact setarPartition_not_mem_of_lt hx' hx h
  · exact Set.eq_univ_of_forall fun x =>
      Set.mem_iUnion.mpr ⟨setarIndex r x, mem_setarPartition_setarIndex hr x⟩

/-- **SETAR model** (FY §4.1.1): a TAR whose regimes form an interval partition. -/
def IsSETAR {k P : ℕ} (b0 : Fin (k + 1) → ℝ) (b : Fin (k + 1) → Fin P → ℝ)
    (σ : Fin (k + 1) → ℝ) (r : Fin k → ℝ) (d : ℕ) (X ε : ℤ → Ω → ℝ)
    (μ : Measure Ω) : Prop :=
  StrictMono r ∧ IsTAR b0 b σ (setarPartition r) d X ε μ

/-- The **TAR autoregression function** on the state vector `(x_{t−1}, …, x_{t−P})`
extended with the threshold coordinate: `f(𝐱) = Σᵢ (b_{i0} + Σⱼ b_{ij} x_j)·1_{A_i}(x_d)`
(FY eq. (4.1) without the noise term). Used to instantiate the Markov layer's
`nlARKernel`. -/
noncomputable def tarDrift {k P : ℕ} (b0 : Fin k → ℝ) (b : Fin k → Fin P → ℝ)
    (A : Fin k → Set ℝ) (d : ℕ) (x : Fin (P + 1) → ℝ) : ℝ :=
  ∑ i, (A i).indicator
    (fun _ => b0 i + ∑ j : Fin P, b i j * x (j.castSucc)) (x ⟨min d P, by omega⟩)

/-! ### The TAR state chain

`nlARKernel`'s state at time `s` is `x j = X_{s−j}` (`j : Fin (P + 1)`), so in the
recursion `X_t = f(state at t − 1) + noise` the regressors `X_{t−1−j}` of eq. (4.1) are
the coordinates `x j.castSucc` (`j : Fin P`) and the threshold variable `X_{t−d}` is the
coordinate `d − 1`. `tarStateDrift` is eq. (4.1)'s autoregression function in exactly
those coordinates. (The public `tarDrift` above reads the threshold at `min d P`, which
in these coordinates is `X_{t−1−d}`; the shift by one is why the derivation below uses
its own drift.) -/

/-- The TAR autoregression function in the state-vector coordinates of `nlARKernel`. -/
private noncomputable def tarStateDrift {k P : ℕ} (b0 : Fin k → ℝ) (b : Fin k → Fin P → ℝ)
    (A : Fin k → Set ℝ) (d : ℕ) (x : Fin (P + 1) → ℝ) : ℝ :=
  ∑ i, (A i).indicator
    (fun _ => b0 i + ∑ j : Fin P, b i j * x (j.castSucc)) (x ⟨min (d - 1) P, by omega⟩)

-- On a partition exactly one indicator fires, so an indicator sum collapses to its
-- single active term.
private lemma sum_indicator_of_partition {k : ℕ} {A : Fin k → Set ℝ}
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) {y : ℝ} {i0 : Fin k} (hy : y ∈ A i0)
    (g : Fin k → ℝ) : ∑ i, (A i).indicator (fun _ => g i) y = g i0 := by
  classical
  have hone : (A i0).indicator (fun _ => g i0) y = g i0 := by
    simp only [Set.indicator_apply, if_pos hy]
  rw [← hone]
  refine Finset.sum_eq_single_of_mem i0 (Finset.mem_univ i0) fun i _ hne => ?_
  have hnot : y ∉ A i := fun hmem => Set.disjoint_left.mp (hdisj hne) hmem hy
  simp only [Set.indicator_apply, if_neg hnot]

-- Adding a constant to every branch of a partition indicator sum adds it once.
private lemma sum_indicator_add_const {k : ℕ} {A : Fin k → Set ℝ}
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) (hcov : (⋃ i, A i) = Set.univ)
    (g : Fin k → ℝ) (z y : ℝ) :
    ∑ i, (A i).indicator (fun _ => g i + z) y
      = (∑ i, (A i).indicator (fun _ => g i) y) + z := by
  have hmem : y ∈ ⋃ i, A i := by rw [hcov]; exact Set.mem_univ _
  obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp hmem
  rw [sum_indicator_of_partition hdisj hi0 (fun i => g i + z),
    sum_indicator_of_partition hdisj hi0 g]

private lemma measurable_tarStateDrift {k P : ℕ} (b0 : Fin k → ℝ) (b : Fin k → Fin P → ℝ)
    {A : Fin k → Set ℝ} (hA : ∀ i, MeasurableSet (A i)) (d : ℕ) :
    Measurable (tarStateDrift b0 b A d) := by
  classical
  refine Finset.measurable_sum (Finset.univ : Finset (Fin k)) fun i _ => ?_
  simp only [Set.indicator_apply]
  refine Measurable.ite (measurable_pi_apply _ (hA i)) ?_ measurable_const
  exact measurable_const.add
    (Finset.measurable_sum (Finset.univ : Finset (Fin P)) fun j _ =>
      measurable_const.mul (measurable_pi_apply _))

-- The **contraction bound** (FY p. 126 condition (b)) in the form Theorem 2.4(ii) wants:
-- exactly one regime fires, so the drift is a single affine form whose slope mass is at
-- most `lam` and whose intercept is at most `c`.
private lemma tarStateDrift_bound {k P : ℕ} {b0 : Fin k → ℝ} {b : Fin k → Fin P → ℝ}
    {A : Fin k → Set ℝ} (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hcov : (⋃ i, A i) = Set.univ) (d : ℕ) {lam c : ℝ}
    (hlam : ∀ i, (∑ j, |b i j|) ≤ lam) (hc : ∀ i, |b0 i| ≤ c) (x : Fin (P + 1) → ℝ) :
    |tarStateDrift b0 b A d x| ≤ lam * (⨆ i, |x i|) + c := by
  classical
  have hmem : x ⟨min (d - 1) P, by omega⟩ ∈ ⋃ i, A i := by rw [hcov]; exact Set.mem_univ _
  obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp hmem
  have hval : tarStateDrift b0 b A d x = b0 i0 + ∑ j : Fin P, b i0 j * x (j.castSucc) :=
    sum_indicator_of_partition hdisj hi0 _
  have hxb : ∀ j : Fin (P + 1), |x j| ≤ ⨆ i, |x i| := fun j =>
    le_ciSup (f := fun i : Fin (P + 1) => |x i|) (Finite.bddAbove_range _) j
  have hsup0 : (0 : ℝ) ≤ ⨆ i, |x i| := le_trans (abs_nonneg (x 0)) (hxb 0)
  have hstep : |∑ j : Fin P, b i0 j * x (j.castSucc)| ≤ (∑ j, |b i0 j|) * (⨆ i, |x i|) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hxb _) (abs_nonneg _)
  have hmain : |b0 i0 + ∑ j : Fin P, b i0 j * x (j.castSucc)|
      ≤ c + (∑ j, |b i0 j|) * (⨆ i, |x i|) :=
    le_trans (abs_add_le _ _) (add_le_add (hc i0) hstep)
  have hlast : (∑ j, |b i0 j|) * (⨆ i, |x i|) ≤ lam * (⨆ i, |x i|) :=
    mul_le_mul_of_nonneg_right (hlam i0) hsup0
  rw [hval]
  linarith

/-- **MISSING BRICK (kernel → two-sided process).** From an invariant law of the
vectorized nonlinear-AR kernel, a two-sided strictly stationary realization of the
recursion driven by standardized iid innovations. `ForMathlib/Markov/Chain.lean` closes
the *marginal* core of FY Theorem 2.2 (`invariant_nstep_eq`) but the project has no
path-space construction: Mathlib's pin supplies Ionescu–Tulcea on `ℕ`
(`ProbabilityTheory.Kernel.traj`) and `Measure.infinitePi`, but no Kolmogorov extension
over `ℤ` and no natural extension of a one-sided shift system, so the two-sided
trajectory measure cannot be assembled from what exists. This is the single named debt
of the derivation below (besides the frozen `nlARKernel_geometricallyErgodic`), and its
closure belongs with the batch that builds the path space. -/
private theorem exists_stationary_nlAR_of_invariant {P : ℕ}
    {f : (Fin (P + 1) → ℝ) → ℝ} (hf : Measurable f)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν2 : MemLp id 2 ν) (hνmean : ∫ e, e ∂ν = 0)
    {σ0 : ℝ} (hσ : 0 < σ0) (hνvar : variance id ν = σ0 ^ 2)
    {F : Measure (Fin (P + 1) → ℝ)} [IsProbabilityMeasure F]
    (hinv : (nlARKernel f ν).Invariant F) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' ε' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧ (∀ t, Measurable (X' t)) ∧ IsIIDNoise ε' 1 μ' ∧
        (∀ t : ℤ, Indep (MeasurableSpace.comap (ε' t) inferInstance) (sigmaLT X' t) μ') ∧
        (∀ t : ℤ, X' t =ᵐ[μ']
          fun ω => f (fun j : Fin (P + 1) => X' (t - 1 - (j : ℕ)) ω) + σ0 * ε' t ω) ∧
        IsStrictlyStationary X' μ' := by
  sorry

/-- **FY §4.1.1, pp. 126–127 (delegated to Theorem 2.4)**: under equal regime scales and
the uniform contraction `max_i Σ_j |b_{ij}| < 1`, the TAR state chain is geometrically
ergodic, hence admits a strictly stationary solution. Stated as a corollary of the
Markov-layer statement `nlARKernel_geometricallyErgodic` (FY Thm 2.4(ii)); the closure
of that statement is batch F.

The innovation law fed to Theorem 2.4 is taken to be `N(0, σ₀²)` rather than the
hypothesis' `ν`: the conclusion asks for a TAR in the sense of `IsTAR`, whose innovations
are `IID(0, 1)` and enter as `σ₀ ε_t`, and `ν` is not assumed to have variance `σ₀²`
(only a positive continuous density, mean zero and a finite second moment — exactly the
Theorem 2.4 hypotheses). `N(0, σ₀²)` satisfies those same hypotheses, so the delegation
to Theorem 2.4 is unchanged. -/
theorem exists_stationary_tar [IsProbabilityMeasure μ] {k P : ℕ}
    {b0 : Fin k → ℝ} {b : Fin k → Fin P → ℝ} {σ0 : ℝ} {A : Fin k → Set ℝ} {d : ℕ}
    -- USER-INPUT: measurable partition of ℝ; FY Def 4.1
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hcov : (⋃ i, A i) = Set.univ)
    -- USER-INPUT: equal regime scales (book prints σ_p — typo for σ₁ = ⋯ = σ_k);
    -- FY p. 126 condition (a)
    (hσ : 0 < σ0)
    -- USER-INPUT: uniform contraction; FY p. 126 condition (b)
    (hcontract : ∀ i, (∑ j, |b i j|) < 1)
    -- USER-INPUT: delay within the state window; FY Def 4.1
    (hd : 1 ≤ d) (hdP : d ≤ P)
    -- USER-INPUT: innovation law with a continuous positive density (the Theorem 2.4
    -- hypothesis, in the strengthened form documented in
    -- `ForMathlib/Markov/GeometricErgodicity.lean`); FY §2.1.4 Example 2.1
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, 0 < g x) ∧
      ν = MeasureTheory.volume.withDensity fun x => ENNReal.ofReal (g x))
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν) (hνmean : ∫ x, x ∂ν = 0) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' ε' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧
        IsTAR b0 b (fun _ => σ0) A d X' ε' μ' ∧ IsStrictlyStationary X' μ' := by
  classical
  -- the partition is nonempty (it covers `ℝ`)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · have h0 : (0 : ℝ) ∈ ⋃ i : Fin 0, A i := by rw [hcov]; exact Set.mem_univ _
      simp at h0
    · exact h
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hkpos
  -- the uniform contraction rate and the intercept mass
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = Finset.univ.sup' Finset.univ_nonempty
      fun i : Fin k => ∑ j, |b i j| := ⟨_, rfl⟩
  obtain ⟨cst, hcst⟩ : ∃ c : ℝ, c = Finset.univ.sup' Finset.univ_nonempty
      fun i : Fin k => |b0 i| := ⟨_, rfl⟩
  have hlamle : ∀ i, (∑ j, |b i j|) ≤ lam := fun i => by
    rw [hlam]
    exact Finset.le_sup' (fun i' : Fin k => ∑ j, |b i' j|) (Finset.mem_univ i)
  have hcstle : ∀ i, |b0 i| ≤ cst := fun i => by
    rw [hcst]
    exact Finset.le_sup' (fun i' : Fin k => |b0 i'|) (Finset.mem_univ i)
  have hlam1 : lam < 1 := by
    rw [hlam]; exact Finset.sup'_lt_iff _ |>.mpr fun i _ => hcontract i
  have hlam0 : 0 ≤ lam :=
    le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hlamle (Classical.arbitrary _))
  have hcst0 : 0 ≤ cst := le_trans (abs_nonneg _) (hcstle (Classical.arbitrary _))
  -- the innovation law: `N(0, σ₀²)`, which has a continuous positive density, mean zero
  -- and variance `σ₀²` (see the docstring on the choice)
  obtain ⟨v, hv⟩ : ∃ v : NNReal, v = Real.toNNReal (σ0 ^ 2) := ⟨_, rfl⟩
  have hvne : v ≠ 0 := by
    rw [hv]
    exact ne_of_gt (Real.toNNReal_pos.mpr (by positivity))
  have hvcoe : ((v : NNReal) : ℝ) = σ0 ^ 2 := by
    rw [hv]; exact Real.coe_toNNReal _ (by positivity)
  -- the geometric ergodicity input, from the frozen Theorem 2.4(ii)
  obtain ⟨F, hFprob, hFgeo⟩ :=
    nlARKernel_geometricallyErgodic (f := tarStateDrift b0 b A d)
      (measurable_tarStateDrift b0 b hA d)
      (g := ProbabilityTheory.gaussianPDF 0 v)
      (ProbabilityTheory.measurable_gaussianPDF 0 v)
      (ProbabilityTheory.gaussianPDF_pos 0 hvne)
      (ν := ProbabilityTheory.gaussianReal 0 v)
      (ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hvne)
      (MemLp.integrable le_rfl (ProbabilityTheory.memLp_id_gaussianReal 1))
      ProbabilityTheory.integral_id_gaussianReal
      hlam0 hlam1 hcst0
      (tarStateDrift_bound hdisj hcov d hlamle hcstle)
  haveI := hFprob
  haveI := isMarkovKernel_nlARKernel
    (measurable_tarStateDrift b0 b hA d) (ProbabilityTheory.gaussianReal 0 v)
  -- the attracting law is invariant, and the brick turns it into a two-sided process
  have hinv : (nlARKernel (tarStateDrift b0 b A d)
      (ProbabilityTheory.gaussianReal 0 v)).Invariant F :=
    hFgeo.isErgodicKernel.invariant
  obtain ⟨Ω', mΩ', μ', X', ε', hprob, hXmeas, hiid, hindep, hrec, hstat⟩ :=
    exists_stationary_nlAR_of_invariant (measurable_tarStateDrift b0 b hA d)
      (ProbabilityTheory.memLp_id_gaussianReal 2)
      ProbabilityTheory.integral_id_gaussianReal hσ
      (by rw [ProbabilityTheory.variance_id_gaussianReal, hvcoe]) hinv
  refine ⟨Ω', mΩ', μ', X', ε', hprob, ⟨hd, fun _ => hσ, hA, hdisj, hcov, hXmeas, hiid,
    hindep, fun t => ?_⟩, hstat⟩
  -- the recursion in state coordinates is eq. (4.1): the threshold coordinate `d − 1`
  -- of the state at time `t − 1` is `X_{t−d}`, and the shared noise term factors out of
  -- the partition indicator sum
  filter_upwards [hrec t] with ω hω
  rw [hω]
  have harg : t - 1 - ((min (d - 1) P : ℕ) : ℤ) = t - (d : ℤ) := by
    have h1 : min (d - 1) P = d - 1 := min_eq_left (by omega)
    rw [h1]
    have h2 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
    rw [h2]; ring
  have hthr : (fun j : Fin (P + 1) => X' (t - 1 - (j : ℕ)) ω) ⟨min (d - 1) P, by omega⟩
      = X' (t - (d : ℤ)) ω := by
    simp only []
    rw [harg]
  rw [sum_indicator_add_const hdisj hcov
    (fun i => b0 i + ∑ j : Fin P, b i j * X' (t - 1 - (j : ℕ)) ω) (σ0 * ε' t ω)
    (X' (t - (d : ℤ)) ω)]
  rw [tarStateDrift, ← hthr]
  simp only [Fin.coe_castSucc]

/-- **FY eq. (4.2)** (the canonical toy SETAR): `X_t = −0.7 X_{t−1} + ε_t` when
`X_{t−1} ≤ r` and `X_t = 0.7 X_{t−1} + ε_t` when `X_{t−1} > r` satisfies the two
stationarity conditions of pp. 126–127, so a strictly stationary solution exists. -/
theorem exists_stationary_toy_setar [IsProbabilityMeasure μ] (r : ℝ)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, 0 < g x) ∧
      ν = MeasureTheory.volume.withDensity fun x => ENNReal.ofReal (g x))
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν) (hνmean : ∫ x, x ∂ν = 0) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' ε' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧
        IsTAR (fun _ : Fin 2 => (0 : ℝ))
          (fun i : Fin 2 => fun _ : Fin 1 => if i = 0 then (-0.7 : ℝ) else 0.7)
          (fun _ => (1 : ℝ))
          (fun i : Fin 2 => if i = 0 then {x : ℝ | x ≤ r} else {x : ℝ | r < x})
          1 X' ε' μ' ∧
        IsStrictlyStationary X' μ' := by
  -- the two half-lines are a measurable partition, and `|∓0.7| = 0.7 < 1` is the
  -- contraction condition (b); `d = 1 ≤ P = 1` is the delay condition
  have hd01 : Disjoint {x : ℝ | x ≤ r} {x : ℝ | r < x} := by
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    have h1 : x ≤ r := hx
    have h2 : r < x := hx'
    linarith
  have hfin : ∀ a : Fin 2, a ≠ 0 → a = 1 := by decide
  refine exists_stationary_tar (μ := μ) (b0 := fun _ : Fin 2 => (0 : ℝ))
    (b := fun i : Fin 2 => fun _ : Fin 1 => if i = 0 then (-0.7 : ℝ) else 0.7)
    (σ0 := 1)
    (A := fun i : Fin 2 => if i = 0 then {x : ℝ | x ≤ r} else {x : ℝ | r < x})
    (d := 1) ?_ ?_ ?_ one_pos ?_ le_rfl le_rfl hν hν2 hνmean
  · intro i
    dsimp only
    by_cases h : i = 0
    · rw [if_pos h]; exact measurableSet_Iic
    · rw [if_neg h]; exact measurableSet_Ioi
  · intro i j hij
    dsimp only
    by_cases hi : i = 0
    · have hj : j ≠ 0 := fun h => hij (hi.trans h.symm)
      rw [if_pos hi, if_neg hj]
      exact hd01
    · have hj : j = 0 := by
        by_contra hj0
        exact hij ((hfin i hi).trans (hfin j hj0).symm)
      rw [if_neg hi, if_pos hj]
      exact hd01.symm
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_or_gt x r with h | h
    · exact ⟨0, by rw [if_pos rfl]; exact h⟩
    · exact ⟨1, by rw [if_neg (by decide : ¬((1 : Fin 2) = 0))]; exact h⟩
  · intro i
    dsimp only
    by_cases h : i = 0
    · rw [Fin.sum_univ_one, if_pos h]
      norm_num
    · rw [Fin.sum_univ_one, if_neg h]
      norm_num

end StatLean.TimeSeries
