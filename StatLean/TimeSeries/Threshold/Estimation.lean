import StatLean.TimeSeries.Threshold.TAR
import StatLean.TimeSeries.ARMA.Likelihood
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# TAR estimation with a known partition (FY §4.1.2, eqs. (4.4)–(4.8))

Least-squares fitting of a TAR model when the regime partition (and hence the regime
memberships of the observations) is known:

* `tarRegimeIndices` — the time indices falling in regime `i`, and `tarRegimeCount`
  `T_i = #{t : X_{t−d} ∈ A_i}`;
* `tarLSResidualSS` — the regime-`i` residual sum of squares (FY eq. (4.4)) and
  `tarSigmaHatSq` — the regime variance estimate `σ̂_i²` (eq. (4.6));
* `tarGeneralizedAIC` — the order/delay-selection criterion
  `Σ_i [T_i log σ̂_i²(p_i) + 2(p_i + 1)]` (eq. (4.7); the delay `d` is profiled by
  minimizing over the candidate grid, ties broken by the smallest `d` — recorded as
  the definition's tie-break convention);
* **eq. (4.8)** — the known-partition asymptotic normality
  `T_i^{1/2}(b̃_i − b_i) →d N(0, σ_i² W_i^{-1})`, a literature DEBT (the book says
  "can be shown", pointing at Theorem 3.2). **Caution recorded in the inventory and
  honored here**: the printed `W_i` is built from the moments of the *fictitious global
  regime-`i` AR process*, not from moments conditional on `X_{t−d} ∈ A_i`; we state it
  with the fictitious-process reading, matching Chan (1993a).

**Scope.** FY Theorems 4.1/4.2 (Chan 1993a) and their consumers are **descoped**
(user, 2026-08-04); nothing here estimates the threshold `r` itself.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.1.2,
eqs. (4.4)–(4.8) (pp. 131–134). (`FY §4.1.2`.)

**Bibliographic comments.** Regime-wise least squares for TAR is Tong & Lim (1980);
the known-partition asymptotics are Chan (1993a, Ann. Statist.); the generalized AIC
is Tong (1990) §5.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

open Classical in
/-- Time indices (within the usable window `P + 1 ≤ t < T`) whose threshold variable
falls in regime `i` (FY §4.1.2). -/
noncomputable def tarRegimeIndices {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ) :
    Finset (Fin T) :=
  Finset.univ.filter fun t : Fin T => P < (t : ℕ) ∧ ∃ h : d ≤ (t : ℕ),
    x ⟨(t : ℕ) - d, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ ∈ A

/-- The regime-`i` sample size `T_i` (FY §4.1.2). -/
noncomputable def tarRegimeCount {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ) : ℕ :=
  (tarRegimeIndices x A d P).card

/-- The regime-`i` **residual sum of squares** at coefficients `(β₀, β)`
(FY eq. (4.4)): `Σ_{t ∈ regime i} (x_t − β₀ − Σ_j β_j x_{t−1−j})²`. -/
noncomputable def tarLSResidualSS {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (β0 : ℝ) (β : Fin P → ℝ) : ℝ :=
  ∑ t ∈ tarRegimeIndices x A d P,
    (x t - β0 - ∑ j : Fin P, β j *
      x ⟨(t : ℕ) - 1 - (j : ℕ), Nat.lt_of_le_of_lt (by omega) t.isLt⟩) ^ 2

/-- The regime-`i` variance estimate `σ̂_i² = RSS_i / T_i` (FY eq. (4.6); junk `0` when
the regime is empty). -/
noncomputable def tarSigmaHatSq {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (β0 : ℝ) (β : Fin P → ℝ) : ℝ :=
  tarLSResidualSS x A d β0 β / (tarRegimeCount x A d P : ℝ)

/-- The **generalized AIC** for TAR order selection (FY eq. (4.7)):
`Σ_i [T_i log σ̂_i²(p_i) + 2(p_i + 1)]`, evaluated at given regime fits. -/
noncomputable def tarGeneralizedAIC {k T P : ℕ} (x : Fin T → ℝ) (A : Fin k → Set ℝ)
    (d : ℕ) (β0 : Fin k → ℝ) (β : Fin k → Fin P → ℝ) (porder : Fin k → ℕ) : ℝ :=
  ∑ i, ((tarRegimeCount x (A i) d P : ℝ) *
      Real.log (tarSigmaHatSq x (A i) d (β0 i) (β i))
    + 2 * ((porder i : ℝ) + 1))

/-! ### Existence of a regime-wise least-squares fit

The regime-`i` residual sum of squares is `‖v − Lθ‖²` for the (finite-dimensional) linear
regressor map `L = tarFit` sending the coefficient vector `θ = (β₀, β)` to the fitted
values, extended by zero outside the regime window. Its range is a finite-dimensional —
hence closed — subspace of `Fin T → ℝ` whose elements vanish off the window, so the
sublevel set `{w ∈ range L | ‖v − w‖² ≤ ‖v‖²}` is closed and *bounded*, therefore compact:
the objective attains its minimum there, and that minimum is global on the range. -/

/-- The **regressor map** of the regime-`i` least-squares problem: `(β₀, β)` is sent to the
vector of fitted values `β₀ + Σ_j β_j x_{t−1−j}` on the regime window, extended by `0`
off it. -/
private noncomputable def tarFit {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ) :
    (ℝ × (Fin P → ℝ)) →ₗ[ℝ] (Fin T → ℝ) where
  toFun θ := fun t =>
    if t ∈ tarRegimeIndices x A d P then
      θ.1 + ∑ j : Fin P, θ.2 j *
        x ⟨(t : ℕ) - 1 - (j : ℕ), Nat.lt_of_le_of_lt (by omega) t.isLt⟩
    else 0
  map_add' θ η := by
    funext t
    by_cases h : t ∈ tarRegimeIndices x A d P
    · simp only [h, if_true, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
        Finset.sum_add_distrib]
      ring
    · simp [h]
  map_smul' c θ := by
    funext t
    by_cases h : t ∈ tarRegimeIndices x A d P
    · simp only [h, if_true, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply, Pi.smul_apply]
      simp only [mul_add, Finset.mul_sum, mul_assoc]
    · simp [h]

private lemma tarFit_apply_of_mem {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (θ : ℝ × (Fin P → ℝ)) {t : Fin T} (ht : t ∈ tarRegimeIndices x A d P) :
    tarFit x A d θ t = θ.1 + ∑ j : Fin P, θ.2 j *
      x ⟨(t : ℕ) - 1 - (j : ℕ), Nat.lt_of_le_of_lt (by omega) t.isLt⟩ :=
  if_pos ht

private lemma tarFit_apply_of_not_mem {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (θ : ℝ × (Fin P → ℝ)) {t : Fin T} (ht : t ∉ tarRegimeIndices x A d P) :
    tarFit x A d θ t = 0 :=
  if_neg ht

/-- The least-squares objective as a function of the fitted-value vector. -/
private noncomputable def tarObj {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ)
    (w : Fin T → ℝ) : ℝ :=
  ∑ t ∈ tarRegimeIndices x A d P, (x t - w t) ^ 2

private lemma tarObj_continuous {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ) :
    Continuous (tarObj x A d P) :=
  continuous_finset_sum _ fun t _ => ((continuous_const.sub (continuous_apply t)).pow 2)

private lemma tarObj_nonneg {T : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d P : ℕ)
    (w : Fin T → ℝ) : 0 ≤ tarObj x A d P w :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma tarLSResidualSS_eq_tarObj {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ)
    (β0 : ℝ) (β : Fin P → ℝ) :
    tarLSResidualSS x A d β0 β = tarObj x A d P (tarFit x A d (β0, β)) := by
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [tarFit_apply_of_mem x A d (β0, β) ht]
  ring_nf

/-- The regime-`i` least-squares fit is characterized by its normal equations
(the finite-dimensional projection; no invertibility needed for existence). -/
theorem exists_tarLS_minimizer {T P : ℕ} (x : Fin T → ℝ) (A : Set ℝ) (d : ℕ) :
    ∃ (β0 : ℝ) (β : Fin P → ℝ), ∀ (γ0 : ℝ) (γ : Fin P → ℝ),
      tarLSResidualSS x A d β0 β ≤ tarLSResidualSS x A d γ0 γ := by
  classical
  -- the sublevel set of the objective inside the range of the regressor map
  obtain ⟨C, hC⟩ : ∃ C : Set (Fin T → ℝ),
      C = ((LinearMap.range (tarFit (P := P) x A d) : Submodule ℝ (Fin T → ℝ)) :
            Set (Fin T → ℝ))
          ∩ {w | tarObj x A d P w ≤ tarObj x A d P 0} := ⟨_, rfl⟩
  have h0C : (0 : Fin T → ℝ) ∈ C := by
    rw [hC]
    refine ⟨⟨0, map_zero _⟩, ?_⟩
    simp only [Set.mem_setOf_eq]
    exact le_rfl
  have hCclosed : IsClosed C := by
    rw [hC]
    exact (Submodule.closed_of_finiteDimensional _).inter
      (isClosed_le (tarObj_continuous x A d P) continuous_const)
  -- boundedness: on the window the objective controls each coordinate, off the window
  -- every element of the range vanishes
  have hCbdd : Bornology.IsBounded C := by
    refine isBounded_iff_forall_norm_le.mpr
      ⟨(∑ s : Fin T, |x s|) + Real.sqrt (tarObj x A d P 0), fun w hw => ?_⟩
    have hR : (0 : ℝ) ≤ (∑ s : Fin T, |x s|) + Real.sqrt (tarObj x A d P 0) :=
      add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Real.sqrt_nonneg _)
    rw [pi_norm_le_iff_of_nonneg hR]
    intro t
    rw [hC] at hw
    by_cases ht : t ∈ tarRegimeIndices x A d P
    · have hw2 : tarObj x A d P w ≤ tarObj x A d P 0 := hw.2
      have hterm : (x t - w t) ^ 2 ≤ tarObj x A d P 0 :=
        le_trans (Finset.single_le_sum (f := fun s => (x s - w s) ^ 2)
          (fun s _ => sq_nonneg _) ht) hw2
      have habs : |x t - w t| ≤ Real.sqrt (tarObj x A d P 0) := by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt hterm
      have hxt : |x t| ≤ ∑ s : Fin T, |x s| :=
        Finset.single_le_sum (f := fun s => |x s|) (fun s _ => abs_nonneg _)
          (Finset.mem_univ t)
      have hsplit : |w t| ≤ |x t| + |x t - w t| := by
        rcases abs_cases (w t) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          rcases abs_cases (x t) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
            rcases abs_cases (x t - w t) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> linarith
      calc ‖w t‖ = |w t| := rfl
        _ ≤ |x t| + |x t - w t| := hsplit
        _ ≤ (∑ s : Fin T, |x s|) + Real.sqrt (tarObj x A d P 0) := add_le_add hxt habs
    · obtain ⟨θ, hθ⟩ := hw.1
      have : w t = 0 := by rw [← hθ]; exact tarFit_apply_of_not_mem x A d θ ht
      rw [this]
      simpa using hR
  -- a minimizer on the compact sublevel set is a global minimizer on the range
  obtain ⟨w0, hw0C, hw0min⟩ :=
    (Metric.isCompact_of_isClosed_isBounded hCclosed hCbdd).exists_isMinOn ⟨0, h0C⟩
      (tarObj_continuous x A d P).continuousOn
  rw [hC] at hw0C
  obtain ⟨θ, hθ⟩ := hw0C.1
  refine ⟨θ.1, θ.2, fun γ0 γ => ?_⟩
  rw [tarLSResidualSS_eq_tarObj, tarLSResidualSS_eq_tarObj]
  have hθ' : tarFit x A d (θ.1, θ.2) = w0 := by rw [← hθ]
  rw [hθ']
  by_cases hcase : tarObj x A d P (tarFit x A d (γ0, γ)) ≤ tarObj x A d P 0
  · refine isMinOn_iff.mp hw0min _ ?_
    rw [hC]
    refine ⟨⟨(γ0, γ), rfl⟩, ?_⟩
    simpa only [Set.mem_setOf_eq] using hcase
  · have hw0le : tarObj x A d P w0 ≤ tarObj x A d P 0 := hw0C.2
    exact le_trans hw0le (le_of_not_ge hcase)

/-- **FY eq. (4.8) — DEBT (Chan 1993a; the book's "can be shown", companion to
Thm 3.2)**: with a known partition, under strict stationarity, ergodicity and finite
second moments, the regime-wise LS estimator is `√T_i`-asymptotically normal with
covariance `σ_i² W_i^{-1}`, where `W_i` is the second-moment matrix of the
**fictitious global regime-`i` AR process** (the inventory's documented reading of the
printed `W_i`, per Chan 1993a — *not* the conditional moments given `X_{t−d} ∈ A_i`).
Stated in Cramér–Wold/charFun form over the coefficient vector. -/
theorem tarLS_clt_debt [IsProbabilityMeasure μ] {k P : ℕ}
    {b0 : Fin k → ℝ} {b : Fin k → Fin P → ℝ} {σ : Fin k → ℝ} {A : Fin k → Set ℝ}
    {d : ℕ} {X ε : ℤ → Ω → ℝ}
    (h : IsTAR b0 b σ A d X ε μ)
    -- USER-INPUT: strict stationarity of the fitted process; FY §4.1.2 standing assumption
    (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: finite second moments; FY §4.1.2 standing assumption
    (hL2 : ∀ t, MemLp (X t) 2 μ)
    -- USER-INPUT: the fictitious regime-i AR process' second-moment matrix, assumed
    -- invertible; Chan 1993a
    (i : Fin k) (W : Matrix (Fin P) (Fin P) ℝ) (hW : Matrix.PosDef W)
    -- USER-INPUT: a measurable regime-wise LS estimator sequence; FY eqs. (4.4)-(4.5)
    (bhat : (T : ℕ) → Ω → Fin P → ℝ) (hmeas : ∀ T, Measurable (bhat T))
    (hLS : ∀ (T : ℕ) (ω : Ω), ∀ γ0 : ℝ, ∀ γ : Fin P → ℝ,
      tarLSResidualSS (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d
          (b0 i) (bhat T ω)
        ≤ tarLSResidualSS (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d γ0 γ)
    (c : Fin P → ℝ) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt (tarRegimeCount (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) (A i) d P) *
          ∑ j, c j * (bhat T ω j - b i j)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (σ i ^ 2 * (c ⬝ᵥ (W⁻¹ *ᵥ c))))) u)) := by
  sorry

end StatLean.TimeSeries
