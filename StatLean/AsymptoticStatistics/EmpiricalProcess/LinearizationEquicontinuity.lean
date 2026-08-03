import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformRandomFunctions
import StatLean.AsymptoticStatistics.EmpiricalProcess.ParametricClassDonsker
import StatLean.AsymptoticStatistics.EmpiricalProcess.ZEstimatorNormality
import StatLean.AsymptoticStatistics.ForMathlib.InProbability
import StatLean.AsymptoticStatistics.EmpiricalProcess.LinearizationModulus

/-!
# M-estimator linearization / equicontinuity (vdV Lemma 19.31)

vdV Lemma 19.31 (book p.284): for a criterion `θ ↦ m_θ` that is differentiable
at `θ₀` for `P`-almost every observation, with derivative `ṁ_{θ₀}` (here `mdot`),
and whose local increments are dominated by a square-integrable Lipschitz envelope,
the empirical-process increment along the local reparametrisation
`θ = θ₀ + h/√n` linearises,

    𝔾ₙ[√n(m_{θ₀ + h/√n} − m_{θ₀}) − hᵀṁ_{θ₀}] →ₚ 0

uniformly over bounded `h`. This is the empirical-process half of
`mEstimator_quadratic_expansion`.

The closed Lean proof follows the changing-class route of vdV Theorem 19.28.
It controls the localized increments through the `√n`-scaled shell and its
bracketing modulus, proves fixed-direction convergence from almost-everywhere
differentiability and Lipschitz domination, and combines a finite net with the
shell pair-modulus bound to obtain uniform convergence over bounded `h`.

-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology RealInnerProductSpace

/-- **Localization arithmetic.** For `A ≥ 0` and `ρ > 0`, once
`n ≥ ⌈(A/ρ)²⌉₊` we have `A ≤ ρ·√n`. This discharges the small-`n` guard `‖v‖ ≤ ρ√n`
of the localized Lipschitz bound uniformly over the `A`-ball, for all large `n`. -/
private theorem le_rho_mul_sqrt_of_ceil_le {A ρ : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A)
    {n : ℕ} (hn : ⌈(A / ρ) ^ 2⌉₊ ≤ n) : A ≤ ρ * Real.sqrt n := by
  have hstep : (A / ρ) ^ 2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hsqrt : A / ρ ≤ Real.sqrt n := by
    rw [show A / ρ = Real.sqrt ((A / ρ) ^ 2) from (Real.sqrt_sq (div_nonneg hA hρ.le)).symm]
    exact Real.sqrt_le_sqrt hstep
  rw [div_le_iff₀ hρ, mul_comm] at hsqrt
  exact hsqrt

/-! ### Linearization-residual helpers

The integrand `fhat n h − ψθ₀ h` is, at a sample point `ω` and direction `v = h`,
the residual `√n·(m(θ₀ + v/√n) − m θ₀) − ⟪v, ṁ_{θ₀}⟫`. These `private` helpers
package its Lipschitz domination, continuity in `v`, and (from differentiability
in the Fréchet sense) uniform smallness over a bounded ball, used to drive the
dominated-convergence argument in `linearization_distL2_tendstoZero`. -/

/-- **The linearization residual**
`√n·(m(θ₀ + v/√n) − m θ₀) − ⟪v, ṁ_{θ₀}⟫`. For `v = h.1` this is
`fhat n h ω − ψθ₀ h ω`, the integrand whose `L²(P)` size is controlled below. -/
private noncomputable def linResid {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (n : ℕ) (ω : Ω) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • v) ω - m θ₀ ω)
    - ⟪v, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫

/-- **Continuity of the residual.** `θ ↦ m θ ω` is continuous (Lipschitz with
constant `|menv ω|`), hence the residual `v ↦ linResid … n ω v` is continuous. -/
private theorem continuous_linResid {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (menv : Ω → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (n : ℕ) (ω : Ω) :
    ContinuousOn (fun v => linResid m mdot θ₀ n ω v)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (ρ * Real.sqrt n)) := by
  have hcont_m : ContinuousOn (fun θ => m θ ω) (Metric.closedBall θ₀ ρ) := by
    have hL : LipschitzOnWith (Real.toNNReal |menv ω|) (fun θ => m θ ω)
        (Metric.closedBall θ₀ ρ) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro θ₁ hθ₁ θ₂ hθ₂
      rw [Real.dist_eq, Real.coe_toNNReal _ (abs_nonneg _), dist_eq_norm]
      calc |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖ := hLip θ₁ hθ₁ θ₂ hθ₂ ω
        _ ≤ |menv ω| * ‖θ₁ - θ₂‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    exact hL.continuousOn
  -- `v ↦ θ₀ + (√n)⁻¹ • v` maps `closedBall 0 (ρ√n)` into `closedBall θ₀ ρ`.
  have hmaps : ∀ v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (ρ * Real.sqrt n),
      θ₀ + (Real.sqrt n)⁻¹ • v ∈ Metric.closedBall θ₀ ρ := by
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right] at hv
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa using hρ.le
    · have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
      rw [abs_of_nonneg (inv_nonneg.mpr hs.le)]
      calc (Real.sqrt n)⁻¹ * ‖v‖ ≤ (Real.sqrt n)⁻¹ * (ρ * Real.sqrt n) :=
            mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hs.le)
        _ = ρ := by rw [mul_comm ρ, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  unfold linResid
  have hmv : ContinuousOn (fun v => m (θ₀ + (Real.sqrt n)⁻¹ • v) ω)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (ρ * Real.sqrt n)) :=
    hcont_m.comp (Continuous.continuousOn (by fun_prop)) hmaps
  exact (continuousOn_const.mul (hmv.sub continuousOn_const)).sub
    ((continuous_id.inner continuous_const).continuousOn)

/-- **Lipschitz and Cauchy–Schwarz domination of the residual.**

The bound is uniform in the scale `n`:
`|linResid … n ω v| ≤ (‖menv ω‖ + ‖ṁ_{θ₀}(ω)‖)·‖v‖`. -/
private theorem linResid_abs_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (menv : Ω → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (n : ℕ) (ω : Ω) (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ ≤ ρ * Real.sqrt n) :
    |linResid m mdot θ₀ n ω v|
      ≤ (‖menv ω‖ + ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖) * ‖v‖ := by
  unfold linResid
  set pv := psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω with hpvdef
  have hterm2 : |(⟪v, pv⟫ : ℝ)| ≤ ‖pv‖ * ‖v‖ :=
    (abs_real_inner_le_norm v pv).trans_eq (mul_comm _ _)
  have hterm1 : Real.sqrt n * |m (θ₀ + (Real.sqrt n)⁻¹ • v) ω - m θ₀ ω| ≤ ‖menv ω‖ * ‖v‖ := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [Nat.cast_zero, Real.sqrt_zero, zero_mul]; positivity
    · have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
      have hmem : θ₀ + (Real.sqrt n)⁻¹ • v ∈ Metric.closedBall θ₀ ρ := by
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hs.le)]
        calc (Real.sqrt n)⁻¹ * ‖v‖ ≤ (Real.sqrt n)⁻¹ * (ρ * Real.sqrt n) :=
              mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hs.le)
          _ = ρ := by rw [mul_comm ρ, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
      calc Real.sqrt n * |m (θ₀ + (Real.sqrt n)⁻¹ • v) ω - m θ₀ ω|
          ≤ Real.sqrt n * (menv ω * ‖(θ₀ + (Real.sqrt n)⁻¹ • v) - θ₀‖) :=
            mul_le_mul_of_nonneg_left
              (hLip _ hmem θ₀ (Metric.mem_closedBall_self hρ.le) ω) (Real.sqrt_nonneg _)
        _ = Real.sqrt n * (menv ω * ((Real.sqrt n)⁻¹ * ‖v‖)) := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (inv_nonneg.mpr hs.le)]
        _ = menv ω * ‖v‖ := by
            rw [show Real.sqrt n * (menv ω * ((Real.sqrt n)⁻¹ * ‖v‖))
                = (Real.sqrt n * (Real.sqrt n)⁻¹) * (menv ω * ‖v‖) from by ring,
              mul_inv_cancel₀ hs.ne', one_mul]
        _ ≤ ‖menv ω‖ * ‖v‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  calc |Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • v) ω - m θ₀ ω) - ⟪v, pv⟫|
      ≤ |Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • v) ω - m θ₀ ω)| + |(⟪v, pv⟫ : ℝ)| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ = Real.sqrt n * |m (θ₀ + (Real.sqrt n)⁻¹ • v) ω - m θ₀ ω| + |(⟪v, pv⟫ : ℝ)| := by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ ‖menv ω‖ * ‖v‖ + ‖pv‖ * ‖v‖ := add_le_add hterm1 hterm2
    _ = (‖menv ω‖ + ‖pv‖) * ‖v‖ := by ring

/-- **Uniform smallness from Fréchet differentiability.** From differentiability of
`θ ↦ m θ ω` at `θ₀` with derivative `⟪ṁ_{θ₀}(ω), ·⟫`, the residual is uniformly
small over any bounded ball: for every `ε' > 0` there is `N` with
`|linResid … n ω v| ≤ ε'·‖v‖` for all `n ≥ N` and `‖v‖ ≤ M`. -/
private theorem linResid_abs_le_of_deriv {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (ω : Ω)
    (hω : HasFDerivAt (fun θ => m θ ω)
      (innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) θ₀)
    (M ε' : ℝ) (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n ≥ N, ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≤ M →
      |linResid m mdot θ₀ n ω v| ≤ ε' * ‖v‖ := by
  have hlo : (fun θ => m θ ω - m θ₀ ω
      - (innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) (θ - θ₀))
        =o[𝓝 θ₀] (fun θ => θ - θ₀) := hasFDerivAt_iff_isLittleO.1 hω
  obtain ⟨r, hr, hbound⟩ := Metric.eventually_nhds_iff.1 (Asymptotics.isLittleO_iff.1 hlo hε')
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (M / r)).and
      (eventually_ge_atTop 1))
  refine ⟨N, fun n hn v hv => ?_⟩
  obtain ⟨hn_sqrt, hn_one⟩ := hN n hn
  have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn_one)
  have hdist : dist (θ₀ + (Real.sqrt n)⁻¹ • v) θ₀ < r := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hs.le)]
    have hMsr : M < Real.sqrt n * r := (div_lt_iff₀ hr).1 hn_sqrt
    calc (Real.sqrt n)⁻¹ * ‖v‖ ≤ (Real.sqrt n)⁻¹ * M :=
          mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr hs.le)
      _ < (Real.sqrt n)⁻¹ * (Real.sqrt n * r) := mul_lt_mul_of_pos_left hMsr (inv_pos.mpr hs)
      _ = r := inv_mul_cancel_left₀ hs.ne' r
  have hbnd := hbound hdist
  have hident : linResid m mdot θ₀ n ω v
      = Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • v) ω - m θ₀ ω
          - (innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω))
              ((θ₀ + (Real.sqrt n)⁻¹ • v) - θ₀)) := by
    unfold linResid
    rw [add_sub_cancel_left, innerSL_apply_apply, real_inner_smul_right,
      real_inner_comm v (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)]
    conv_rhs => rw [mul_sub]
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  rw [hident, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), ← Real.norm_eq_abs]
  calc Real.sqrt n * ‖m (θ₀ + (Real.sqrt n)⁻¹ • v) ω - m θ₀ ω
          - (innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω))
              ((θ₀ + (Real.sqrt n)⁻¹ • v) - θ₀)‖
      ≤ Real.sqrt n * (ε' * ‖(θ₀ + (Real.sqrt n)⁻¹ • v) - θ₀‖) :=
        mul_le_mul_of_nonneg_left hbnd (Real.sqrt_nonneg _)
    _ = ε' * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hs.le)]
        rw [show Real.sqrt n * (ε' * ((Real.sqrt n)⁻¹ * ‖v‖))
            = (Real.sqrt n * (Real.sqrt n)⁻¹) * (ε' * ‖v‖) from by ring,
          mul_inv_cancel₀ hs.ne', one_mul]

/-! ### The `L²(P)` marginal -/

/-- **Linearization `L²(P)` distance vanishes** (vdV Lemma 19.31).

For every scale, the `L²(P)`-distance between the localized criterion increment
`fhat n h := √n·(m_{θ₀ + h/√n} − m_{θ₀})` and its linearization
`ψθ₀ h := ⟪h, ṁ_{θ₀}⟫ = ⟪h, psiVec (fun _ => mdot) θ₀⟫` tends to `0` uniformly
over the `M`-ball `{‖h‖ ≤ M}`. This is the `h_tail` input of
the fixed-direction marginal convergence used by the finite-net argument. The
book hypotheses are almost-everywhere differentiability at `θ₀` and local
Lipschitz domination by a square-integrable envelope; dominated convergence
then gives the required `L²` limit. The distance is deterministic in the sample
`ξ`. -/
theorem linearization_distL2_tendstoZero
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d)) (M : ℝ)
    (hm_meas : ∀ θ, Measurable (m θ))
    (hmdot_meas : ∀ i, Measurable (mdot i))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hderiv : ∀ᵐ ω ∂P, HasFDerivAt (fun θ => m θ ω)
      (innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) θ₀)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ] :
    TendstoZeroInOuterProbSup μ
      (fun n _ (h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}) =>
        distL2 P
          (fun ω => Real.sqrt n *
            (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω))
          (fun ω => ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) := by
  intro ε hε
  dsimp only
  rcases lt_or_ge M 0 with hMneg | hM
  · -- `M < 0` ⟹ the index type `{h // ‖h‖ ≤ M}` is empty, so every event is `∅`.
    refine tendsto_const_nhds.congr' ?_
    filter_upwards with n
    symm
    have hset : {ξ : Ξ | ∃ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
        ε < |distL2 P (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω))
              (fun ω => ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ξ ⟨h, -⟩
      have h1 := h.2
      have h2 := norm_nonneg h.1
      linarith
    rw [hset, outerMeasureStar_eq_measure MeasurableSet.empty, measure_empty]
  · -- `0 ≤ M`.  Dominated convergence of the ball-supremum residual.
    have hpv_L2 : MemLp (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) 2 P :=
      MemLp.of_eval_piLp (fun i => hmdot_L2 i)
    -- Small-`n` threshold: for `n ≥ N₀` the whole `M`-ball lands in `closedBall θ₀ ρ`.
    set N₀ : ℕ := ⌈(M / ρ) ^ 2⌉₊ with hN₀def
    have hMρ : ∀ n : ℕ, N₀ ≤ n → M ≤ ρ * Real.sqrt n := fun n hn =>
      le_rho_mul_sqrt_of_ceil_le hρ hM hn
    set D : Ω → ℝ := fun ω =>
      M * (‖menv ω‖ + ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖) with hDdef
    have hD_memLp : MemLp D 2 P := (hmenv.norm.add hpv_L2.norm).const_mul M
    have hD_nonneg : ∀ ω, 0 ≤ D ω := fun ω => by rw [hDdef]; exact mul_nonneg hM (by positivity)
    haveI : Nonempty {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M} := ⟨⟨0, by simpa using hM⟩⟩
    obtain ⟨qseq, hqseq⟩ :=
      TopologicalSpace.exists_dense_seq {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}
    -- Zero the dominating sup below `N₀` (where the local `hLip` bound is unavailable);
    -- the final limit only sees the `n ≥ N₀` tail.
    set Gsqrt : ℕ → Ω → ℝ :=
      fun n ω => if N₀ ≤ n then ⨆ j : ℕ, |linResid m mdot θ₀ n ω (qseq j).1| else 0 with hGdef
    have hG_nonneg : ∀ n ω, 0 ≤ Gsqrt n ω := by
      intro n ω; simp only [hGdef]
      split_ifs with hn
      · exact Real.iSup_nonneg' ⟨0, abs_nonneg _⟩
      · exact le_refl 0
    have hterm_le_D : ∀ n, N₀ ≤ n → ∀ ω (j : ℕ), |linResid m mdot θ₀ n ω (qseq j).1| ≤ D ω := by
      intro n hn ω j
      calc |linResid m mdot θ₀ n ω (qseq j).1|
          ≤ (‖menv ω‖ + ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖) * ‖(qseq j).1‖ :=
            linResid_abs_le m mdot θ₀ menv ρ hρ hLip n ω (qseq j).1 ((qseq j).2.trans (hMρ n hn))
        _ ≤ (‖menv ω‖ + ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖) * M :=
            mul_le_mul_of_nonneg_left (qseq j).2 (by positivity)
        _ = D ω := by rw [hDdef]; ring
    have hG_bdd : ∀ n, N₀ ≤ n → ∀ ω,
        BddAbove (Set.range (fun j => |linResid m mdot θ₀ n ω (qseq j).1|)) :=
      fun n hn ω => ⟨D ω, by rintro _ ⟨j, rfl⟩; exact hterm_le_D n hn ω j⟩
    have hG_le_D : ∀ n ω, Gsqrt n ω ≤ D ω := by
      intro n ω; simp only [hGdef]
      split_ifs with hn
      · exact ciSup_le (fun j => hterm_le_D n hn ω j)
      · exact hD_nonneg ω
    have hlinResid_aesm : ∀ n v, AEStronglyMeasurable (fun ω => linResid m mdot θ₀ n ω v) P := by
      intro n v
      unfold linResid
      exact (aestronglyMeasurable_const.mul
          (((hm_meas _).aestronglyMeasurable).sub (hm_meas _).aestronglyMeasurable)).sub
        (aestronglyMeasurable_const.inner hpv_L2.aestronglyMeasurable)
    have hG_aesm : ∀ n, AEStronglyMeasurable (Gsqrt n) P := by
      intro n
      by_cases hn : N₀ ≤ n
      · simp only [hGdef, if_pos hn]
        exact (AEMeasurable.iSup (fun j => measurable_abs.comp_aemeasurable
          (hlinResid_aesm n (qseq j).1).aemeasurable)).aestronglyMeasurable
      · simp only [hGdef, if_neg hn]; exact aestronglyMeasurable_const
    have hG_memLp : ∀ n, MemLp (Gsqrt n) 2 P := by
      intro n
      refine MemLp.mono' hD_memLp (hG_aesm n) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg n ω)]
      exact hG_le_D n ω
    -- For `n ≥ N₀`, the supremum over a dense sequence dominates every ball direction.
    have hCoreC : ∀ n, N₀ ≤ n → ∀ ω (h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}),
        |linResid m mdot θ₀ n ω h.1| ≤ Gsqrt n ω := by
      intro n hn ω h
      have hGeq : Gsqrt n ω = ⨆ j : ℕ, |linResid m mdot θ₀ n ω (qseq j).1| := by
        simp only [hGdef, if_pos hn]
      rw [hGeq]
      have hcont_on : ContinuousOn (fun v => linResid m mdot θ₀ n ω v)
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M) :=
        (continuous_linResid m mdot θ₀ menv ρ hρ hLip n ω).mono
          (Metric.closedBall_subset_closedBall (hMρ n hn))
      have hFcont : Continuous (fun h' : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M} =>
          |linResid m mdot θ₀ n ω h'.1|) :=
        continuous_abs.comp (hcont_on.comp_continuous continuous_subtype_val
          (fun h' => by rw [Metric.mem_closedBall, dist_zero_right]; exact h'.2))
      have hmem : h ∈ closure (Set.range qseq) := hqseq h
      rw [mem_closure_iff_seq_limit] at hmem
      obtain ⟨y, hy_mem, hy_lim⟩ := hmem
      refine le_of_tendsto ((hFcont.tendsto h).comp hy_lim) (Eventually.of_forall (fun k => ?_))
      obtain ⟨j, hj⟩ := hy_mem k
      simp only [Function.comp_apply, ← hj]
      exact le_ciSup (hG_bdd n hn ω) j
    -- The ball-supremum residual converges pointwise almost everywhere to `0`.
    have hCoreB : ∀ᵐ ω ∂P, Tendsto (fun n => Gsqrt n ω) atTop (𝓝 0) := by
      filter_upwards [hderiv] with ω hω
      rw [Metric.tendsto_atTop]
      intro ε'' hε''
      obtain ⟨N, hN⟩ :=
        linResid_abs_le_of_deriv m mdot θ₀ ω hω M (ε'' / (M + 1)) (div_pos hε'' (by linarith))
      refine ⟨max N N₀, fun n hn => ?_⟩
      have hnN : N ≤ n := le_trans (le_max_left _ _) hn
      have hnN₀ : N₀ ≤ n := le_trans (le_max_right _ _) hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hG_nonneg n ω)]
      have hGeq : Gsqrt n ω = ⨆ j : ℕ, |linResid m mdot θ₀ n ω (qseq j).1| := by
        simp only [hGdef, if_pos hnN₀]
      rw [hGeq]
      have hbound_j : ∀ j, |linResid m mdot θ₀ n ω (qseq j).1| ≤ (ε'' / (M + 1)) * M := by
        intro j
        calc |linResid m mdot θ₀ n ω (qseq j).1|
            ≤ (ε'' / (M + 1)) * ‖(qseq j).1‖ := hN n hnN (qseq j).1 (qseq j).2
          _ ≤ (ε'' / (M + 1)) * M :=
              mul_le_mul_of_nonneg_left (qseq j).2 (le_of_lt (div_pos hε'' (by linarith)))
      refine lt_of_le_of_lt (ciSup_le hbound_j) ?_
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0 : ℝ) < M + 1)]
      have : ε'' * (M + 1) = ε'' * M + ε'' := by ring
      linarith
    -- `‖Gsqrt n‖_{L²} → 0` by dominated convergence in `L²`.
    have hb_tendsto : Tendsto (fun n => (eLpNorm (Gsqrt n) 2 P).toReal) atTop (𝓝 0) := by
      have hUI : UnifIntegrable (fun n => Gsqrt n) 2 P := by
        intro ε₀ hε₀
        obtain ⟨δ, hδpos, hδ⟩ := hD_memLp.eLpNorm_indicator_le one_le_two (by norm_num) hε₀
        refine ⟨δ, hδpos, fun n s hs hμs => le_trans ?_ (hδ s hs hμs)⟩
        refine eLpNorm_mono_real (fun ω => ?_)
        by_cases hω : ω ∈ s
        · simp only [Set.indicator_of_mem hω]
          rw [Real.norm_eq_abs, abs_of_nonneg (hG_nonneg n ω)]
          exact hG_le_D n ω
        · simp only [Set.indicator_of_notMem hω, norm_zero, le_refl]
      have hLp : Tendsto (fun n => eLpNorm (Gsqrt n) 2 P) atTop (𝓝 0) := by
        have h := tendsto_Lp_finite_of_tendsto_ae (μ := P) (p := 2) one_le_two (by norm_num)
          (f := fun n => Gsqrt n) (g := 0) hG_aesm MemLp.zero hUI
          (by filter_upwards [hCoreB] with ω hω using by simpa using hω)
        simpa using h
      have h := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ∞)).comp hLp
      simpa using h
    -- `distL2 (fhat n h) (ψθ₀ h) ≤ ‖Gsqrt n‖_{L²}`, uniformly over the ball (for `n ≥ N₀`).
    have hdistL2_le : ∀ (n : ℕ), N₀ ≤ n → ∀ (h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}),
        distL2 P (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω))
          (fun ω => ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)
          ≤ (eLpNorm (Gsqrt n) 2 P).toReal := by
      intro n hn h
      rw [distL2]
      apply ENNReal.toReal_mono (hG_memLp n).2.ne
      refine eLpNorm_mono_real (fun ω => ?_)
      rw [Pi.sub_apply, Real.norm_eq_abs]
      exact hCoreC n hn ω h
    -- Assembly: eventually the exceedance set is empty.
    have hbε : ∀ᶠ n in atTop, (eLpNorm (Gsqrt n) 2 P).toReal < ε :=
      hb_tendsto.eventually_lt_const hε
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hbε, eventually_ge_atTop N₀] with n hn hnN₀
    symm
    have hset : {ξ : Ξ | ∃ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
        ε < |distL2 P (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω))
              (fun ω => ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ξ ⟨h, hh⟩
      rw [abs_of_nonneg (by rw [distL2]; exact ENNReal.toReal_nonneg)] at hh
      exact absurd ((hdistL2_le n hnN₀ h).trans_lt hn) (not_lt.mpr hh.le)
    rw [hset, outerMeasureStar_eq_measure MeasurableSet.empty, measure_empty]

/-! ### Equicontinuity of the Lipschitz class -/

/-- **The Lipschitz-parametrised class is asymptotically equicontinuous**
(vdV Lemma 19.31, tightness half).

`IsAsymptoticallyEquicontinuous (paramClass ψ Θ) P` for a bounded-index Lipschitz
class, obtained as the `.asymptoticallyEquicontinuous` accessor of
`parametricClass_isPDonsker` (`ParametricClassDonsker.lean`, vdV Example 19.7),
the Donsker⇒equicontinuity bridge. This supplies the `h_equicont` input of
`uniform_donsker_random_function_consistency`. -/
theorem localizedLipschitz_asymptoticallyEquicontinuous
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ : Bornology.IsBounded Θ)
    (m : Ω → ℝ) (hm : MemLp m 2 P) (hm_meas : Measurable m)
    (hLip : ∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ, ∀ (j : Fin k) (x : Ω),
      |ψ θ₁ j x - ψ θ₂ j x| ≤ m x * ‖θ₁ - θ₂‖)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ) (hψ0_L2 : ∀ j, MemLp (ψ θ₀ j) 2 P)
    (hne : (paramClass ψ Θ).Nonempty)
    (hmeas : ∀ g ∈ paramClass ψ Θ, Measurable g) :
    IsAsymptoticallyEquicontinuous (paramClass ψ Θ) P :=
  (parametricClass_isPDonsker P ψ Θ hΘ m hm hm_meas hLip θ₀ hθ₀ hψ0_L2 hne
    hmeas).asymptoticallyEquicontinuous

/-- **O_P ball-collapse.** If the family `D` restricted to every closed `M`-ball is
`→ₚ 0` uniformly (in outer probability, `TendstoZeroInOuterProbSup`), and the random
directions `hₙ` are bounded in probability (`O_P(1)`), then `D` evaluated at the
random point `hₙ` tends to `0` in probability. (Ball-indexed analog of
`tendstoInProbZero_of_tendstoZeroInOuterProbSup_fin`.) -/
theorem tendstoInProbZero_of_ball_outerProbSup
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    {G : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
    (D : ℕ → Ξ → G → ℝ)
    (hₙ : ℕ → Ξ → G) (hₙ_meas : ∀ n, Measurable (hₙ n))
    (hsup : ∀ M : ℝ, 0 ≤ M →
      TendstoZeroInOuterProbSup μ (fun n ξ (h : {h : G // ‖h‖ ≤ M}) => D n ξ h.1))
    (hbdd : IsBoundedInProb (fun _ : ℕ => μ) hₙ) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => D n ξ (hₙ n ξ)) := by
  intro ε hε
  have hμ_tendsto : Tendsto (fun n => μ {ξ | ε ≤ ‖D n ξ (hₙ n ξ)‖}) atTop (𝓝 0) := by
    set u : ℕ → ℝ≥0∞ := fun n => μ {ξ | ε ≤ ‖D n ξ (hₙ n ξ)‖} with hu
    -- Reduce `Tendsto u → 0` to `∀ η > 0, limsup u ≤ ofReal η` (mirror the finite-`H`
    -- collapse skeleton in `UniformRandomFunctions.lean`).
    suffices hlimsup : ∀ η : ℝ, 0 < η → limsup u atTop ≤ ENNReal.ofReal η by
      have hsup0 : limsup u atTop ≤ 0 := by
        refine ENNReal.le_of_forall_pos_le_add fun η hηpos _ => ?_
        rw [zero_add]
        have := hlimsup (η : ℝ) (by exact_mod_cast hηpos)
        rwa [ENNReal.ofReal_coe_nnreal] at this
      have hsup0' : limsup u atTop = 0 := le_antisymm hsup0 bot_le
      refine tendsto_of_le_liminf_of_limsup_le bot_le hsup0'.le ?_ ?_
      · exact isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
      · exact isBoundedUnder_of ⟨0, fun _ => bot_le⟩
    intro η hη
    -- From `O_P(1)` pick a ball radius `M` capturing all but `η` mass of `hₙ`.
    obtain ⟨M₀, hM₀⟩ := hbdd η hη
    set M : ℝ := max M₀ 0 with hM
    have hM_nonneg : 0 ≤ M := le_max_right _ _
    have hM₀M : M₀ ≤ M := le_max_left _ _
    -- The `M`-ball escape event `B` and the `(ε/2)`-ball oscillation event `A`.
    set B : ℕ → Set Ξ := fun n => {ξ | M < ‖hₙ n ξ‖} with hB
    set A : ℕ → Set Ξ :=
      fun n => {ξ | ∃ h : {h : G // ‖h‖ ≤ M}, ε / 2 < |D n ξ h.1|} with hA
    have hB_meas : ∀ n, MeasurableSet (B n) := fun n =>
      measurableSet_lt measurable_const (hₙ_meas n).norm
    -- `M`-ball escape has mass `≤ η` (from `O_P(1)`, enlarging `M₀` to `M`).
    have hMbound : ∀ n, μ.real (B n) ≤ η := by
      intro n
      have hsub : B n ⊆ {ξ | M₀ < ‖hₙ n ξ‖} := by
        simp only [hB]
        intro ξ hξ
        simp only [Set.mem_setOf_eq] at hξ ⊢
        exact lt_of_le_of_lt hM₀M hξ
      exact le_trans (measureReal_mono hsub (measure_ne_top μ _)) (hM₀ n)
    have hBη : ∀ n, μ (B n) ≤ ENNReal.ofReal η := by
      intro n
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ (B n)), ← measureReal_def]
      exact ENNReal.ofReal_le_ofReal (hMbound n)
    -- Ball-collapse inclusion: the `ε`-exceedance at the random point splits into the
    -- oscillation event (when `hₙ` is inside the ball) and the escape event.
    have hsplit : ∀ n, {ξ | ε ≤ ‖D n ξ (hₙ n ξ)‖} ⊆ A n ∪ B n := by
      intro n ξ hξ
      simp only [Set.mem_setOf_eq] at hξ
      rw [Real.norm_eq_abs] at hξ
      simp only [Set.mem_union, hA, hB, Set.mem_setOf_eq]
      by_cases hle : ‖hₙ n ξ‖ ≤ M
      · refine Or.inl ⟨⟨hₙ n ξ, hle⟩, ?_⟩
        show ε / 2 < |D n ξ (hₙ n ξ)|
        linarith [half_lt_self hε]
      · exact Or.inr (not_le.mp hle)
    -- Pointwise `ℝ≥0∞` bound via `P*`-subadditivity (measure `≤ P*`, then union).
    have hbound : ∀ n, u n ≤ μ.outerMeasureStar (A n) + μ (B n) := by
      intro n
      simp only [hu]
      calc μ {ξ | ε ≤ ‖D n ξ (hₙ n ξ)‖}
          ≤ μ.outerMeasureStar {ξ | ε ≤ ‖D n ξ (hₙ n ξ)‖} :=
            measure_le_outerMeasureStar μ _
        _ ≤ μ.outerMeasureStar (A n ∪ B n) := outerMeasureStar_mono μ (hsplit n)
        _ ≤ μ.outerMeasureStar (A n) + μ.outerMeasureStar (B n) :=
            outerMeasureStar_union_le μ _ _
        _ = μ.outerMeasureStar (A n) + μ (B n) := by
            rw [outerMeasureStar_eq_measure (hB_meas n)]
    have hbound2 : ∀ n, u n ≤ ENNReal.ofReal η + μ.outerMeasureStar (A n) := by
      intro n
      calc u n ≤ μ.outerMeasureStar (A n) + μ (B n) := hbound n
        _ ≤ μ.outerMeasureStar (A n) + ENNReal.ofReal η := by gcongr; exact hBη n
        _ = ENNReal.ofReal η + μ.outerMeasureStar (A n) := add_comm _ _
    -- The oscillation event vanishes: it is the `(ε/2)`-slice of the `M`-ball sup.
    have hAtendsto : Tendsto (fun n => μ.outerMeasureStar (A n)) atTop (𝓝 0) := by
      simpa only [hA] using hsup M hM_nonneg (ε / 2) (half_pos hε)
    calc limsup u atTop
        ≤ limsup (fun n => ENNReal.ofReal η + μ.outerMeasureStar (A n)) atTop :=
          limsup_le_limsup (Eventually.of_forall hbound2)
            isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
      _ ≤ ENNReal.ofReal η :=
          limsup_add_tendsto_zero_le (fun _ => ENNReal.ofReal η)
            (fun n => μ.outerMeasureStar (A n)) (ENNReal.ofReal η)
            (le_of_eq (limsup_const _)) hAtendsto
  simp only [measureReal_def]
  have hcomp := (ENNReal.tendsto_toReal (by simp)).comp hμ_tendsto
  rwa [ENNReal.toReal_zero] at hcomp

/-! ### Linearization decomposition (vdV §19.5, Lemma 19.31, Theorem 19.28) -/

/-- **Inner product ↔ empirical process bridge.**

`⟪h, 𝔾ₙṁ_{θ₀}⟫ = 𝔾ₙ(ω ↦ ⟪h, ṁ_{θ₀}(ω)⟫)`, i.e. the Euclidean inner product of a
fixed direction `h` with the vector empirical process
`empiricalProcessVec P (fun _ => mdot) θ₀ n Xs` equals the scalar empirical process
of the pointwise readout `ω ↦ ⟪h, psiVec (fun _ => mdot) θ₀ ω⟫`. Both sides equal
`∑ i, h i · 𝔾ₙ(mdot i)`: the LHS by `PiLp.inner_apply`, the RHS by pushing the finite
inner-product sum through the linearity of `empiricalProcess`
(`empiricalProcess_finset_sum` + `empiricalProcess_smul`). This identity rewrites the
random-direction term `⟪hₙ, 𝔾ₙṁ⟫` in the final M-estimator adapter as the empirical
process of a member of the linearized class. -/
theorem empiricalProcess_inner_empiricalProcessVec
    {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d))
    (Xs : Fin n → Ω) (h : EuclideanSpace ℝ (Fin d))
    (hmdot_int : ∀ i, Integrable (mdot i) P) :
    (⟪h, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n Xs⟫ : ℝ)
      = empiricalProcess P n Xs
          (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) := by
  -- LHS `= ∑ i, h i · 𝔾ₙ(mdot i)` by `PiLp.inner_apply` (coordinatewise defeq).
  have hL : (⟪h, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n Xs⟫ : ℝ)
      = ∑ i, h i * empiricalProcess P n Xs (mdot i) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change (empiricalProcess P n Xs (mdot i) * h i : ℝ)
      = h i * empiricalProcess P n Xs (mdot i)
    ring
  -- RHS integrand `= ∑ i, h i · mdot i ω`.
  have hinner : (fun ω => (⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫ : ℝ))
      = fun ω => ∑ i, h i * mdot i ω := by
    funext ω
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change (mdot i ω * h i : ℝ) = h i * mdot i ω
    ring
  -- Push the sum through the empirical process by linearity.
  have hRHS : empiricalProcess P n Xs (fun ω => ∑ i, h i * mdot i ω)
      = ∑ i, h i * empiricalProcess P n Xs (mdot i) := by
    have h1 := empiricalProcess_finset_sum P n Xs Finset.univ (fun i ω => h i * mdot i ω)
      (fun i _ => (hmdot_int i).const_mul (h i))
    simp only at h1
    rw [h1]
    exact Finset.sum_congr rfl (fun i _ => empiricalProcess_smul P n Xs (h i) (mdot i))
  rw [hL, hinner]
  exact hRHS.symm

/-- **Chebyshev tail for a single empirical-process function.**

For an `L²(P)` function `f` under an iid sample, the empirical process
`𝔾ₙ f = √n·(P_n f − Pf)` is centred (`∫ 𝔾ₙ f ∂μ = 0`), with variance equal to the
`P`-variance of `f`, hence `≤ ∫ f² ∂P`; Chebyshev then bounds its `M`-tail mass by
`(∫ f² ∂P)/M²`. This supplies the fixed-direction marginal bound and the
linear-term `O_P(1)` modulus estimate. -/
private theorem empiricalProcess_chebyshev_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (n : ℕ) (f : Ω → ℝ) (hf_L2 : MemLp f 2 P) {M : ℝ} (hM : 0 < M) :
    μ {ξ | M ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ) f|}
      ≤ ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / M ^ 2) := by
  classical
  -- Centre `f`: `c = Pf`, `g = f − c` (mean-zero under `P`).
  set c : ℝ := ∫ x, f x ∂P with hc
  set g : Ω → ℝ := fun x => f x - c with hg
  have hf_int : Integrable f P := hf_L2.integrable one_le_two
  have hg_L2 : MemLp g 2 P := hf_L2.sub (memLp_const c)
  have hg_aem : AEMeasurable g P := hg_L2.aestronglyMeasurable.aemeasurable
  have hg_int : Integrable g P := hg_L2.integrable one_le_two
  have hg_mean : ∫ x, g x ∂P = 0 := by
    simp only [hg]
    rw [integral_sub hf_int (integrable_const c), integral_const, measureReal_univ_eq_one,
      one_smul, hc, sub_self]
  -- Per-index map facts: `μ.map (X i) = P`, so `g ∘ Xᵢ` is `L²` / mean-zero / iid.
  have hX_aem : ∀ i, AEMeasurable (X i) μ := fun i => (hX_meas i).aemeasurable
  have hmap : ∀ i, μ.map (X i) = P := fun i => (hX_id i).map_eq.trans hX_law
  have hg_aem_map : ∀ i, AEMeasurable g (μ.map (X i)) := by
    intro i; rw [hmap i]; exact hg_aem
  have hgX_L2 : ∀ i, MemLp (g ∘ X i) 2 μ := by
    intro i
    have hgm : MemLp g 2 (μ.map (X i)) := by rw [hmap i]; exact hg_L2
    exact hgm.comp_of_map (hX_aem i)
  have hgX_indep : ProbabilityTheory.iIndepFun (fun i => g ∘ X i) μ :=
    hX_indep.comp₀ (fun _ => g) hX_aem hg_aem_map
  have hgX_idem : ∀ i, ProbabilityTheory.IdentDistrib (g ∘ X i) (g ∘ X 0) μ μ :=
    fun i => (hX_id i).comp_of_aemeasurable (hg_aem_map i)
  have hX0_aem : AEMeasurable (X 0) μ := hX_aem 0
  have hgX0_mean : ∫ ξ, g (X 0 ξ) ∂μ = 0 := by
    have hg_asm_map : AEStronglyMeasurable g (μ.map (X 0)) := by
      rw [hmap 0]; exact hg_L2.aestronglyMeasurable
    have h_int : ∫ ξ, g (X 0 ξ) ∂μ = ∫ x, g x ∂(μ.map (X 0)) :=
      (integral_map hX0_aem hg_asm_map).symm
    rw [h_int, hmap 0, hg_mean]
  have hgX_mean : ∀ i, ∫ ξ, g (X i ξ) ∂μ = 0 := by
    intro i
    have h_eq : ∫ ξ, (g ∘ X i) ξ ∂μ = ∫ ξ, (g ∘ X 0) ξ ∂μ := (hgX_idem i).integral_eq
    simpa [Function.comp_apply] using h_eq.trans hgX0_mean
  -- `V = ∫ g² ∂P`; equals `variance (g ∘ Xᵢ)`, and `≤ ∫ f² ∂P`.
  set V : ℝ := ∫ x, (g x) ^ 2 ∂P with hV
  have hgX0_var : ProbabilityTheory.variance (g ∘ X 0) μ = V := by
    have h_aem : AEMeasurable (g ∘ X 0) μ := (hgX_L2 0).aestronglyMeasurable.aemeasurable
    rw [ProbabilityTheory.variance_eq_integral h_aem,
      show (∫ ω, (g ∘ X 0) ω ∂μ) = 0 from hgX0_mean]
    simp only [sub_zero, Function.comp_apply]
    have hg_sq_asm_map : AEStronglyMeasurable (fun x : Ω => (g x) ^ 2) (μ.map (X 0)) := by
      rw [hmap 0]; exact (hg_aem.pow_const 2).aestronglyMeasurable
    have h_int : ∫ ξ, (g (X 0 ξ)) ^ 2 ∂μ = ∫ x, (g x) ^ 2 ∂(μ.map (X 0)) :=
      (integral_map hX0_aem hg_sq_asm_map).symm
    rw [h_int, hmap 0]
  have hgXi_var : ∀ i, ProbabilityTheory.variance (g ∘ X i) μ = V :=
    fun i => (hgX_idem i).variance_eq.trans hgX0_var
  have hVle : V ≤ ∫ x, (f x) ^ 2 ∂P := by
    have e1 : V = ProbabilityTheory.variance g P := by
      rw [ProbabilityTheory.variance_eq_sub hg_L2, hg_mean, hV]; simp [Pi.pow_apply]
    have e2 : ProbabilityTheory.variance g P = ProbabilityTheory.variance f P :=
      ProbabilityTheory.variance_sub_const hf_L2.aestronglyMeasurable c
    have e3 : ProbabilityTheory.variance f P = (∫ x, (f x) ^ 2 ∂P) - c ^ 2 := by
      rw [ProbabilityTheory.variance_eq_sub hf_L2, ← hc]; simp [Pi.pow_apply]
    rw [e1, e2, e3]; linarith [sq_nonneg c]
  -- `n = 0`: the empirical process is `0`, so the `M`-event is empty.
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hset : {ξ : Ξ | M ≤ |empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) f|} = ∅ := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le,
        empiricalProcess_zero, abs_zero]
      exact hM
    rw [hset, measure_empty]; exact zero_le _
  -- `n > 0`: `EP = (√n)⁻¹ · ∑ᵢ g(Xᵢ)`, mean `0`, variance `V`; apply Chebyshev.
  · have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hsqrt_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := hsqrt_pos.ne'
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    set Y : Ξ → ℝ := fun ξ => ∑ i : Fin n, g (X i.val ξ) with hYdef
    have hY_eq : Y = ∑ i : Fin n, (g ∘ X i.val) := by
      funext ξ; simp only [hYdef, Finset.sum_apply, Function.comp_apply]
    have hY_L2 : ∀ i : Fin n, MemLp (g ∘ X i.val) 2 μ := fun i => hgX_L2 i.val
    have hY_pairwise : Set.Pairwise (↑(Finset.univ : Finset (Fin n)) : Set (Fin n))
        (fun i j => ProbabilityTheory.IndepFun (g ∘ X i.val) (g ∘ X j.val) μ) := by
      intro i _ j _ hij
      exact hgX_indep.indepFun (fun h => hij (Fin.ext h))
    have hY_var : ProbabilityTheory.variance Y μ = (n : ℝ) * V := by
      rw [hY_eq, ProbabilityTheory.IndepFun.variance_sum (fun i _ => hY_L2 i) hY_pairwise,
        Finset.sum_congr rfl (fun i _ => hgXi_var i.val)]
      simp [Finset.sum_const, Finset.card_univ]
    have hY_memLp : MemLp Y 2 μ := by
      rw [hY_eq]; exact memLp_finset_sum' _ (fun i _ => hY_L2 i)
    have hEP_eq : (fun ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)
        = fun ξ => (Real.sqrt n)⁻¹ * Y ξ := by
      funext ξ
      have h_a : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ = (Real.sqrt (n : ℝ))⁻¹ := by
        nth_rewrite 2 [← hsq]
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hsqrt_ne, one_mul]
      have h_b : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) = Real.sqrt (n : ℝ) := by
        nth_rewrite 2 [← hsq]
        rw [← mul_assoc, inv_mul_cancel₀ hsqrt_ne, one_mul]
      simp only [hYdef, hg]
      unfold empiricalProcess empiricalAvg
      rw [← hc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      linear_combination (∑ i : Fin n, f (X i.val ξ)) * h_a + c * h_b
    have hEP_memLp : MemLp (fun ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) 2 μ := by
      rw [hEP_eq]; exact hY_memLp.const_mul _
    have hEP_mean : ∫ ξ, empiricalProcess P n (fun i : Fin n => X i.val ξ) f ∂μ = 0 := by
      rw [show (fun ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)
          = fun ξ => (Real.sqrt n)⁻¹ * Y ξ from hEP_eq, integral_const_mul]
      have hY_int : ∫ ξ, Y ξ ∂μ = 0 := by
        rw [hY_eq]
        simp_rw [Finset.sum_apply]
        rw [integral_finset_sum _ (fun i _ => (hY_L2 i).integrable one_le_two)]
        simp only [Function.comp_apply, hgX_mean, Finset.sum_const_zero]
      rw [hY_int, mul_zero]
    have hEP_var : ProbabilityTheory.variance
        (fun ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) μ = V := by
      rw [hEP_eq, ProbabilityTheory.variance_const_mul, hY_var, inv_pow]
      rw [show (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) from by rw [sq]; exact hsq]
      field_simp
    have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hEP_memLp hM
    simp only [hEP_var, hEP_mean, sub_zero] at hcheb
    refine hcheb.trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr

/-- **Fixed-direction marginal vanishes.**

For each fixed direction `h`, the empirical process of the linearization residual
`R_n(h) ω = √n·(m_{θ₀ + h/√n} − m_{θ₀})(ω) − ⟪h, ṁ_{θ₀}(ω)⟫` tends to `0` in
probability. The `L²(P)` size of `R_n(h)` vanishes by
`linearization_distL2_tendstoZero`) so its second moment `→ 0`, and the empirical
process has vanishing variance (`markov_distL2_tail`, `Donsker.lean`). -/
theorem linearization_marginal_tendstoInProbZero
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (hmdot_meas : ∀ i, Measurable (mdot i))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hderiv : ∀ᵐ ω ∂P, HasFDerivAt (fun θ => m θ ω)
      (innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) θ₀)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (h : EuclideanSpace ℝ (Fin d)) :
    TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω)
          - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) := by
  intro ε hε
  have hpv_L2 : MemLp (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) 2 P :=
    MemLp.of_eval_piLp (fun i => hmdot_L2 i)
  -- Small-`n` threshold: `θ₀ + h/√n ∈ closedBall θ₀ ρ` once `n ≥ N₀`.
  set N₀ : ℕ := ⌈(‖h‖ / ρ) ^ 2⌉₊ with hN₀def
  have hMρ : ∀ n : ℕ, N₀ ≤ n → ‖h‖ ≤ ρ * Real.sqrt n := fun n hn =>
    le_rho_mul_sqrt_of_ceil_le hρ (norm_nonneg h) hn
  -- The marginal integrand is `MemLp 2 P` (Lipschitz + Cauchy–Schwarz domination), for `n ≥ N₀`.
  have hf_L2 : ∀ n : ℕ, N₀ ≤ n →
      MemLp (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω)
      - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) 2 P := by
    intro n hn
    have hdom_L2 : MemLp (fun ω => ‖h‖ *
        (‖menv ω‖ + ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖)) 2 P :=
      (hmenv.norm.add hpv_L2.norm).const_mul ‖h‖
    refine MemLp.mono' hdom_L2 ?_ ?_
    · exact (aestronglyMeasurable_const.mul (((hm_meas _).aestronglyMeasurable).sub
        (hm_meas _).aestronglyMeasurable)).sub
        (aestronglyMeasurable_const.inner hpv_L2.aestronglyMeasurable)
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact (linResid_abs_le m mdot θ₀ menv ρ hρ hLip n ω h (hMρ n hn)).trans_eq (mul_comm _ _)
  -- Apply `linearization_distL2_tendstoZero` at `M := ‖h‖`:
  -- the sample-independent `L²(P)` distance to the linearization tends to zero.
  have hdistL2_tendsto : Tendsto (fun n : ℕ => distL2 P
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
      atTop (𝓝 0) := by
    have hC1 := linearization_distL2_tendstoZero P m mdot θ₀ ‖h‖ hm_meas hmdot_meas hmdot_L2
      menv hmenv ρ hρ hLip hderiv μ
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    intro δ hδ
    have hsup := hC1 (δ / 2) (by positivity)
    filter_upwards [Filter.Tendsto.eventually_lt_const (show (0 : ℝ≥0∞) < 1 by norm_num) hsup]
      with n hn
    have hd_nonneg : (0 : ℝ) ≤ distL2 P
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
        (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) := by
      unfold distL2; exact ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hd_nonneg]
    by_contra hcon
    push_neg at hcon
    refine absurd hn (not_lt.mpr (le_trans ?_
      (outerMeasureStar_mono μ (Set.univ_subset_iff.mpr ?_))))
    · have hle := measure_le_outerMeasureStar μ (Set.univ : Set Ξ)
      rwa [measure_univ] at hle
    · rw [Set.eq_univ_iff_forall]
      exact fun ξ => ⟨⟨h, le_refl _⟩, by rw [abs_of_nonneg hd_nonneg]; linarith⟩
  -- `∫ (marginal)² ≤ (distL2)²` (universal, no `MemLp` needed).
  have hint_le : ∀ n : ℕ, (∫ x, (Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) x - m θ₀ x)
        - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ x⟫) ^ 2 ∂P)
      ≤ (distL2 P (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
          (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) ^ 2 := by
    intro n
    set I : ℝ := ∫ x, (Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) x - m θ₀ x)
      - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ x⟫) ^ 2 ∂P with hI
    have hI_nonneg : 0 ≤ I := by rw [hI]; exact integral_nonneg fun _ => sq_nonneg _
    have hle : Real.sqrt I ≤ distL2 P
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
        (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) := by
      apply le_distL2_of_integral_sq_ge
      rw [Real.sq_sqrt hI_nonneg]
    calc I = Real.sqrt I ^ 2 := (Real.sq_sqrt hI_nonneg).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  -- Squeeze the Chebyshev tail by `(distL2)²/ε² → 0`.
  set gseq : ℕ → ℝ := fun n => (distL2 P
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) ^ 2 / ε ^ 2
    with hgseq
  -- `gseq → 0` (the deterministic `L²`-distance squared, over `ε²`).
  have hgseq_tendsto : Tendsto gseq atTop (𝓝 0) := by
    rw [hgseq]
    have h2 : Tendsto (fun n : ℕ => (distL2 P
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
        (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) ^ 2)
        atTop (𝓝 0) := by
      simpa using hdistL2_tendsto.pow 2
    simpa using h2.div_const (ε ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgseq_tendsto
    (Eventually.of_forall (fun n => measureReal_nonneg)) ?_
  · -- Eventually (`n ≥ N₀`) the Chebyshev tail is bounded by `gseq n`.
    filter_upwards [eventually_ge_atTop N₀] with n hn
    have htail := empiricalProcess_chebyshev_tail P μ X hX_meas hX_indep hX_id hX_law n
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω)
        - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) (hf_L2 n hn) hε
    have hInn : (0 : ℝ) ≤ (∫ x, (Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) x - m θ₀ x)
        - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ x⟫) ^ 2 ∂P) / ε ^ 2 :=
      div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by positivity)
    simp only [Real.norm_eq_abs]
    rw [hgseq]
    calc (μ {ξ | ε ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω)
                - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}).toReal
        ≤ (ENNReal.ofReal ((∫ x, (Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) x - m θ₀ x)
              - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ x⟫) ^ 2 ∂P)
              / ε ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
      _ = (∫ x, (Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) x - m θ₀ x)
              - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ x⟫) ^ 2 ∂P) / ε ^ 2 :=
          ENNReal.toReal_ofReal hInn
      _ ≤ (distL2 P (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
              (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) ^ 2
              / ε ^ 2 := by
          gcongr; exact hint_le n

/-- Fixed-direction variant of `linearization_marginal_tendstoInProbZero` whose
`L²(P)` convergence is supplied directly.  This is the honest adapter for
differentiability in probability: the `MemLp` and Lipschitz guards remain
necessary because `distL2` uses `ENNReal.toReal`. -/
theorem linearization_marginal_tendstoInProbZero_of_distL2
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (h : EuclideanSpace ℝ (Fin d))
    (hd : Tendsto (fun n : ℕ => distL2 P
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
      atTop (𝓝 0)) :
    TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω)
          - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) := by
  intro ε hε
  have hpv_L2 : MemLp (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) 2 P :=
    MemLp.of_eval_piLp (fun i => hmdot_L2 i)
  -- Small-`n` threshold: `θ₀ + h/√n ∈ closedBall θ₀ ρ` once `n ≥ N₀`.
  set N₀ : ℕ := ⌈(‖h‖ / ρ) ^ 2⌉₊ with hN₀def
  have hMρ : ∀ n : ℕ, N₀ ≤ n → ‖h‖ ≤ ρ * Real.sqrt n := fun n hn =>
    le_rho_mul_sqrt_of_ceil_le hρ (norm_nonneg h) hn
  -- The marginal integrand is `MemLp 2 P` (Lipschitz + Cauchy–Schwarz domination), for `n ≥ N₀`.
  have hf_L2 : ∀ n : ℕ, N₀ ≤ n →
      MemLp (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω)
      - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) 2 P := by
    intro n hn
    have hdom_L2 : MemLp (fun ω => ‖h‖ *
        (‖menv ω‖ + ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖)) 2 P :=
      (hmenv.norm.add hpv_L2.norm).const_mul ‖h‖
    refine MemLp.mono' hdom_L2 ?_ ?_
    · exact (aestronglyMeasurable_const.mul (((hm_meas _).aestronglyMeasurable).sub
        (hm_meas _).aestronglyMeasurable)).sub
        (aestronglyMeasurable_const.inner hpv_L2.aestronglyMeasurable)
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact (linResid_abs_le m mdot θ₀ menv ρ hρ hLip n ω h (hMρ n hn)).trans_eq (mul_comm _ _)
  -- `∫ (marginal)² ≤ (distL2)²` (universal, no `MemLp` needed).
  have hint_le : ∀ n : ℕ, (∫ x, (Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) x - m θ₀ x)
        - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ x⟫) ^ 2 ∂P)
      ≤ (distL2 P (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
          (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) ^ 2 := by
    intro n
    set I : ℝ := ∫ x, (Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) x - m θ₀ x)
      - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ x⟫) ^ 2 ∂P with hI
    have hI_nonneg : 0 ≤ I := by rw [hI]; exact integral_nonneg fun _ => sq_nonneg _
    have hle : Real.sqrt I ≤ distL2 P
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
        (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) := by
      apply le_distL2_of_integral_sq_ge
      rw [Real.sq_sqrt hI_nonneg]
    calc I = Real.sqrt I ^ 2 := (Real.sq_sqrt hI_nonneg).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  -- Squeeze the Chebyshev tail by `(distL2)²/ε² → 0`.
  set gseq : ℕ → ℝ := fun n => (distL2 P
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) ^ 2 / ε ^ 2
    with hgseq
  -- `gseq → 0` (the deterministic `L²`-distance squared, over `ε²`).
  have hgseq_tendsto : Tendsto gseq atTop (𝓝 0) := by
    rw [hgseq]
    have h2 : Tendsto (fun n : ℕ => (distL2 P
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
        (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) ^ 2)
        atTop (𝓝 0) := by
      simpa using hd.pow 2
    simpa using h2.div_const (ε ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgseq_tendsto
    (Eventually.of_forall (fun n => measureReal_nonneg)) ?_
  · -- Eventually (`n ≥ N₀`) the Chebyshev tail is bounded by `gseq n`.
    filter_upwards [eventually_ge_atTop N₀] with n hn
    have htail := empiricalProcess_chebyshev_tail P μ X hX_meas hX_indep hX_id hX_law n
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω)
        - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) (hf_L2 n hn) hε
    have hInn : (0 : ℝ) ≤ (∫ x, (Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) x - m θ₀ x)
        - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ x⟫) ^ 2 ∂P) / ε ^ 2 :=
      div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by positivity)
    simp only [Real.norm_eq_abs]
    rw [hgseq]
    calc (μ {ξ | ε ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω)
                - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}).toReal
        ≤ (ENNReal.ofReal ((∫ x, (Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) x - m θ₀ x)
              - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ x⟫) ^ 2 ∂P)
              / ε ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
      _ = (∫ x, (Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) x - m θ₀ x)
              - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ x⟫) ^ 2 ∂P) / ε ^ 2 :=
          ENNReal.toReal_ofReal hInn
      _ ≤ (distL2 P (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
              (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)) ^ 2
              / ε ^ 2 := by
          gcongr; exact hint_le n

/-- **The linear-term modulus vanishes.**

The linear term `h ↦ ⟪h, 𝔾ₙṁ_{θ₀}⟫` is asymptotically equicontinuous over the
`M`-ball: for every oscillation `ε > 0` and mass `η > 0` there is a radius `δ > 0`
so that the `limsupₙ` outer measure of the pair-oscillation event
`{ξ | ∃ h₁ h₂ ∈ ball_M, ‖h₁ − h₂‖ < δ ∧ ε < |⟪h₁ − h₂, 𝔾ₙṁ_{θ₀}⟫|}` is `≤ η`.
Route: `⟪·, 𝔾ₙṁ⟫` is a fixed linear functional of the CLT-tight vector
`𝔾ₙṁ_{θ₀} = empiricalProcessVec …`, so `|⟪h₁ − h₂, 𝔾ₙṁ⟫| ≤ ‖h₁ − h₂‖·‖𝔾ₙṁ‖`
and `O_P(1)` tightness of `‖𝔾ₙṁ‖` gives the modulus. -/
theorem linearTerm_modulus_tendstoZero
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hmdot_meas : ∀ i, Measurable (mdot i))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      limsup (fun n => μ.outerMeasureStar
        {ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
          ‖h₁.1 - h₂.1‖ < δ ∧
          ε < |(⟪h₁.1 - h₂.1, empiricalProcessVec P
                  (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                  (fun i : Fin n => X i.val ξ)⟫ : ℝ)|}) atTop
        ≤ ENNReal.ofReal η := by
  -- Euclidean norm dominated by the `ℓ¹`-sum of coordinates.
  have hnorm_le : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ≤ ∑ i, |v i| := by
    intro v
    rw [EuclideanSpace.norm_eq]
    have hsum_nonneg : (0 : ℝ) ≤ ∑ i, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [← Real.sqrt_sq hsum_nonneg]
    apply Real.sqrt_le_sqrt
    have hcongr : ∀ i, ‖v.ofLp i‖ ^ 2 = |v i| ^ 2 := fun i => by rw [Real.norm_eq_abs]
    rw [Finset.sum_congr rfl (fun i _ => hcongr i)]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)
  -- Coordinate `i` of the vector empirical process is the scalar empirical process of `mdot i`.
  have hcoord : ∀ (n : ℕ) (ξ : Ξ) (i : Fin d),
      (empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
        (fun i : Fin n => X i.val ξ)) i
      = empiricalProcess P n (fun i : Fin n => X i.val ξ) (mdot i) := fun _ _ _ => rfl
  intro ε hε η hη
  -- Uniform `O_P(1)` tail bound on `‖𝔾ₙṁ‖` via per-coordinate Chebyshev.
  set B : ℝ := ∑ i, ∫ x, (mdot i x) ^ 2 ∂P with hB
  have hB_nonneg : 0 ≤ B :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun _ => sq_nonneg _
  set M₀ : ℝ := ((d : ℝ) + 1) * (Real.sqrt (B / η) + 1) with hM₀
  have hM₀_pos : 0 < M₀ := by rw [hM₀]; positivity
  set t : ℝ := M₀ / ((d : ℝ) + 1) with ht
  have ht_pos : 0 < t := by rw [ht]; positivity
  have ht_eq : t = Real.sqrt (B / η) + 1 := by
    rw [ht, hM₀, mul_comm, mul_div_assoc, div_self (by positivity : ((d : ℝ) + 1) ≠ 0), mul_one]
  have hBt : B / t ^ 2 ≤ η := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < t ^ 2)]
    have hge : B / η ≤ t ^ 2 := by
      rw [ht_eq, add_sq, Real.sq_sqrt (div_nonneg hB_nonneg hη.le)]
      nlinarith [Real.sqrt_nonneg (B / η)]
    calc B = η * (B / η) := by field_simp
      _ ≤ η * t ^ 2 := mul_le_mul_of_nonneg_left hge hη.le
  have hcoord_tail : ∀ (n : ℕ) (i : Fin d),
      μ {ξ | t ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ) (mdot i)|}
        ≤ ENNReal.ofReal ((∫ x, (mdot i x) ^ 2 ∂P) / t ^ 2) :=
    fun n i => empiricalProcess_chebyshev_tail P μ X hX_meas hX_indep hX_id hX_law n
      (mdot i) (hmdot_L2 i) ht_pos
  have huniftail : ∀ n : ℕ, μ {ξ | M₀ < ‖empiricalProcessVec P
        (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n (fun i : Fin n => X i.val ξ)‖}
      ≤ ENNReal.ofReal η := by
    intro n
    have hsub : {ξ | M₀ < ‖empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot)
          θ₀ n (fun i : Fin n => X i.val ξ)‖}
        ⊆ ⋃ i : Fin d, {ξ | t ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ) (mdot i)|} := by
      intro ξ hξ
      simp only [Set.mem_setOf_eq] at hξ
      rw [Set.mem_iUnion]
      by_contra hc
      push_neg at hc
      simp only [Set.mem_setOf_eq, not_le] at hc
      have hle1 := hnorm_le (empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot)
        θ₀ n (fun i : Fin n => X i.val ξ))
      have hle2 : ∑ i : Fin d, |(empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot)
            θ₀ n (fun i : Fin n => X i.val ξ)) i| ≤ ∑ _i : Fin d, t := by
        apply Finset.sum_le_sum
        intro i _
        rw [hcoord n ξ i]
        exact (hc i).le
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle2
      have hlt : (d : ℝ) * t < M₀ := by
        rw [ht, ← mul_div_assoc, div_lt_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) + 1)]
        nlinarith [hM₀_pos]
      linarith [hξ, hle1, hle2, hlt]
    calc μ {ξ | M₀ < ‖empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot)
            θ₀ n (fun i : Fin n => X i.val ξ)‖}
        ≤ μ (⋃ i : Fin d, {ξ | t ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ) (mdot i)|}) :=
          measure_mono hsub
      _ ≤ ∑ i : Fin d, μ {ξ | t ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ) (mdot i)|} :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ i : Fin d, ENNReal.ofReal ((∫ x, (mdot i x) ^ 2 ∂P) / t ^ 2) :=
          Finset.sum_le_sum (fun i _ => hcoord_tail n i)
      _ = ENNReal.ofReal (∑ i : Fin d, (∫ x, (mdot i x) ^ 2 ∂P) / t ^ 2) :=
          (ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)).symm
      _ = ENNReal.ofReal (B / t ^ 2) := by rw [hB, Finset.sum_div]
      _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hBt
  -- Cauchy–Schwarz collapse: the pair event lands inside `{M₀ < ‖𝔾ₙṁ‖}`.
  refine ⟨ε / (M₀ + 1), by positivity, ?_⟩
  refine Filter.limsup_le_of_le isCobounded_le_of_bot (Filter.Eventually.of_forall (fun n => ?_))
  have hsub2 : {ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
        ‖h₁.1 - h₂.1‖ < ε / (M₀ + 1) ∧
        ε < |(⟪h₁.1 - h₂.1, empiricalProcessVec P
            (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n (fun i : Fin n => X i.val ξ)⟫ : ℝ)|}
      ⊆ {ξ | M₀ < ‖empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
            (fun i : Fin n => X i.val ξ)‖} := by
    intro ξ hξ
    obtain ⟨h₁, h₂, hnorm, hip⟩ := hξ
    simp only [Set.mem_setOf_eq]
    have hcs : |(⟪h₁.1 - h₂.1, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot)
          θ₀ n (fun i : Fin n => X i.val ξ)⟫ : ℝ)|
        ≤ ‖h₁.1 - h₂.1‖ * ‖empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot)
            θ₀ n (fun i : Fin n => X i.val ξ)‖ := abs_real_inner_le_norm _ _
    have hVnn : (0 : ℝ) ≤ ‖empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot)
        θ₀ n (fun i : Fin n => X i.val ξ)‖ := norm_nonneg _
    have hM1 : (0 : ℝ) < M₀ + 1 := by linarith [hM₀_pos]
    have hchain : ε < ε / (M₀ + 1) * ‖empiricalProcessVec P
        (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n (fun i : Fin n => X i.val ξ)‖ :=
      lt_of_lt_of_le hip (hcs.trans (mul_le_mul_of_nonneg_right hnorm.le hVnn))
    rw [div_mul_eq_mul_div, lt_div_iff₀ hM1] at hchain
    nlinarith [hchain, hε]
  calc μ.outerMeasureStar {ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
          ‖h₁.1 - h₂.1‖ < ε / (M₀ + 1) ∧
          ε < |(⟪h₁.1 - h₂.1, empiricalProcessVec P
              (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n (fun i : Fin n => X i.val ξ)⟫ : ℝ)|}
      ≤ μ.outerMeasureStar {ξ | M₀ < ‖empiricalProcessVec P
          (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n (fun i : Fin n => X i.val ξ)‖} :=
        outerMeasureStar_mono μ hsub2
    _ ≤ μ {ξ | M₀ < ‖empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
          (fun i : Fin n => X i.val ξ)‖} := outerMeasureStar_le_measure μ _
    _ ≤ ENNReal.ofReal η := huniftail n

/-- **The √n-scaled shell / bracketing modulus vanishes** (vdV Lemma 19.34 /
Theorem 19.28).

The empirical process of the localized increment class
`fhat n h := √n·(m_{θ₀ + h/√n} − m_{θ₀})` (`= √n·(m_θ − m_{θ₀})` on the `√n`-shell
`{θ : ‖θ − θ₀‖ ≤ M/√n}` after `θ = θ₀ + h/√n`) is asymptotically equicontinuous
over the `M`-ball: for every `ε, η > 0` a radius `δ > 0` bounds the `limsupₙ` outer
measure of the increment pair-oscillation event by `η`. The proof uses relative
bracketing entropy of the localized increment class, a chaining maximal inequality,
and cancellation of the outer `√n` against the `1/√n` localization scale. -/
theorem sqrtScaled_shell_modulus_tendstoZero
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      limsup (fun n => μ.outerMeasureStar
        {ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
          ‖h₁.1 - h₂.1‖ < δ ∧
          ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω))
                - empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω))|})
        atTop ≤ ENNReal.ofReal η := by
  exact sqrtScaled_shell_modulus_bound P m θ₀ hm_meas menv hmenv hmenv_meas ρ hρ hLip
    μ X hX_meas hX_indep hX_id hX_law M hM

/-- **Empirical-process decomposition of the linearization residual.**

The residual `R_n(h) ω = √n·(m_{θ₀+h/√n} − m_{θ₀})ω − ⟪h, ṁ_{θ₀}(ω)⟫` splits, by
linearity of the empirical process (`empiricalProcess_sub`) and the inner-product
identity `empiricalProcess_inner_empiricalProcessVec`, as the increment
process `𝔾ₙ[√n(m_{θ₀+h/√n} − m_{θ₀})]` minus the inner product `⟪h, 𝔾ₙṁ_{θ₀}⟫`.
Both integrands are `L¹(P)` (Lipschitz / Cauchy–Schwarz domination by the `L²`
envelope and score). -/
private theorem linearizationResidual_process_eq
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (n : ℕ) (Xs : Fin n → Ω) (h : EuclideanSpace ℝ (Fin d)) (hh : ‖h‖ ≤ ρ * Real.sqrt n) :
    empiricalProcess P n Xs
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω)
          - ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)
      = empiricalProcess P n Xs
          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
        - ⟪h, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n Xs⟫ := by
  have hpv_L2 : MemLp (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀) 2 P :=
    MemLp.of_eval_piLp (fun i => hmdot_L2 i)
  -- Increment term `√n(m_{θ₀+h/√n} − m_{θ₀})` is `L¹` (Lipschitz domination by `‖h‖·‖menv‖`).
  have hincr_int : Integrable
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω)) P := by
    have hdom : MemLp (fun ω => ‖h‖ * ‖menv ω‖) 2 P := hmenv.norm.const_mul ‖h‖
    refine (MemLp.mono' hdom ?_ ?_).integrable one_le_two
    · exact aestronglyMeasurable_const.mul
        (((hm_meas _).aestronglyMeasurable).sub (hm_meas _).aestronglyMeasurable)
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; rw [Nat.cast_zero, Real.sqrt_zero, zero_mul]; positivity
      · have hs : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
        have hmem : θ₀ + (Real.sqrt n)⁻¹ • h ∈ Metric.closedBall θ₀ ρ := by
          rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr hs.le)]
          calc (Real.sqrt n)⁻¹ * ‖h‖ ≤ (Real.sqrt n)⁻¹ * (ρ * Real.sqrt n) :=
                mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hs.le)
            _ = ρ := by rw [mul_comm ρ, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
        calc Real.sqrt n * |m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω|
            ≤ Real.sqrt n * (menv ω * ‖(θ₀ + (Real.sqrt n)⁻¹ • h) - θ₀‖) :=
              mul_le_mul_of_nonneg_left
                (hLip _ hmem θ₀ (Metric.mem_closedBall_self hρ.le) ω) (Real.sqrt_nonneg _)
          _ = menv ω * ‖h‖ := by
              rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (inv_nonneg.mpr hs.le)]
              rw [show Real.sqrt n * (menv ω * ((Real.sqrt n)⁻¹ * ‖h‖))
                  = (Real.sqrt n * (Real.sqrt n)⁻¹) * (menv ω * ‖h‖) from by ring,
                mul_inv_cancel₀ hs.ne', one_mul]
          _ ≤ ‖h‖ * ‖menv ω‖ := by
              rw [mul_comm (menv ω) ‖h‖]
              exact mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _)
  -- Linear term `⟪h, ṁ_{θ₀}⟫` is `L¹` (Cauchy–Schwarz domination by `‖h‖·‖ṁ_{θ₀}‖`).
  have hinner_int : Integrable
      (fun ω => (⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫ : ℝ)) P := by
    have hdom : MemLp (fun ω => ‖h‖ *
        ‖psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω‖) 2 P := hpv_L2.norm.const_mul ‖h‖
    refine (MemLp.mono' hdom
      (aestronglyMeasurable_const.inner hpv_L2.aestronglyMeasurable) ?_).integrable one_le_two
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm h _
  have hmdot_int : ∀ i, Integrable (mdot i) P := fun i => (hmdot_L2 i).integrable one_le_two
  have hkey := empiricalProcess_sub P n Xs
    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
    (fun ω => (⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫ : ℝ))
    hincr_int hinner_int
  rw [← empiricalProcess_inner_empiricalProcessVec P mdot θ₀ Xs h hmdot_int] at hkey
  exact hkey

/-- **Subadditivity of `limsup` under `ENNReal.ofReal` bounds.**

For two `ℝ≥0∞` sequences, `ℝ≥0∞` is not an additive group, so
Mathlib's `limsup_add_le` (which needs `AddCommGroup`) does not apply; we prove the
specialization `limsup Uf ≤ ofReal a`, `limsup Vf ≤ ofReal b ⟹
limsup (Uf + Vf) ≤ ofReal a + ofReal b` directly (split the target threshold
`c > a + b` using the finite slack `c − (a + b)`). -/
private theorem limsup_add_le_ofReal (Uf Vf : ℕ → ℝ≥0∞) {a b : ℝ}
    (hU : limsup Uf atTop ≤ ENNReal.ofReal a) (hV : limsup Vf atTop ≤ ENNReal.ofReal b) :
    limsup (fun n => Uf n + Vf n) atTop ≤ ENNReal.ofReal a + ENNReal.ofReal b := by
  rw [limsup_le_iff isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)]
  intro c hc
  have hA : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hB : ENNReal.ofReal b ≠ ⊤ := ENNReal.ofReal_ne_top
  rcases eq_or_ne c ⊤ with rfl | hc_top
  · have hUev := eventually_lt_of_limsup_lt
        (lt_of_le_of_lt hU (ENNReal.lt_add_right hA one_ne_zero))
    have hVev := eventually_lt_of_limsup_lt
        (lt_of_le_of_lt hV (ENNReal.lt_add_right hB one_ne_zero))
    filter_upwards [hUev, hVev] with n hUn hVn
    exact lt_of_lt_of_le (ENNReal.add_lt_add hUn hVn) le_top
  · have hd_pos : 0 < c - (ENNReal.ofReal a + ENNReal.ofReal b) := tsub_pos_of_lt hc
    set dslack : ℝ≥0∞ := c - (ENNReal.ofReal a + ENNReal.ofReal b) with hdslack
    have hhalf_ne : dslack / 2 ≠ 0 := (ENNReal.half_pos hd_pos.ne').ne'
    have hUev := eventually_lt_of_limsup_lt
        (lt_of_le_of_lt hU (ENNReal.lt_add_right hA hhalf_ne))
    have hVev := eventually_lt_of_limsup_lt
        (lt_of_le_of_lt hV (ENNReal.lt_add_right hB hhalf_ne))
    filter_upwards [hUev, hVev] with n hUn hVn
    calc Uf n + Vf n
        < (ENNReal.ofReal a + dslack / 2) + (ENNReal.ofReal b + dslack / 2) :=
          ENNReal.add_lt_add hUn hVn
      _ = (ENNReal.ofReal a + ENNReal.ofReal b) + (dslack / 2 + dslack / 2) :=
          add_add_add_comm _ _ _ _
      _ = (ENNReal.ofReal a + ENNReal.ofReal b) + dslack := by rw [ENNReal.add_halves]
      _ = c := add_tsub_cancel_of_le hc.le

/-- **The residual pair modulus vanishes.**

The pair modulus of `h ↦ 𝔾ₙ(R_n(h))` is controlled: for every `ε, η > 0`
there is `δ > 0` with `limsupₙ` outer
measure of the residual pair-oscillation event `≤ η`. The decomposition
`𝔾ₙ(R_n(h)) = 𝔾ₙ(fhat_h) − ⟪h, 𝔾ₙṁ⟫` from
`linearizationResidual_process_eq` lets the triangle inequality split its modulus
into the increment modulus and the linear-term modulus. -/
theorem linearizationResidual_pairModulus_tendstoZero
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (hmdot_meas : ∀ i, Measurable (mdot i))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      limsup (fun n => μ.outerMeasureStar
        {ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
          ‖h₁.1 - h₂.1‖ < δ ∧
          ε < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                    - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
                - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                    - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|})
        atTop ≤ ENNReal.ofReal η := by
  intro ε hε η hη
  -- Small-`n` threshold: for `n ≥ N₀` the whole `M`-ball lands in `closedBall θ₀ ρ` (after `/√n`).
  set N₀ : ℕ := ⌈(M / ρ) ^ 2⌉₊ with hN₀def
  have hMρ : ∀ n : ℕ, N₀ ≤ n → M ≤ ρ * Real.sqrt n := fun n hn =>
    le_rho_mul_sqrt_of_ceil_le hρ hM hn
  -- The localized-increment modulus at oscillation `ε/2` and mass `η/2` gives `δ₁`.
  obtain ⟨δ₁, hδ₁pos, hN3⟩ := sqrtScaled_shell_modulus_tendstoZero P m mdot θ₀ hm_meas menv hmenv
    hmenv_meas ρ hρ hLip μ X hX_meas hX_indep hX_id hX_law M hM (ε / 2) (by linarith) (η / 2)
    (by linarith)
  -- The linear-term modulus at oscillation `ε/2` and mass `η/2` gives `δ₂`.
  obtain ⟨δ₂, hδ₂pos, hN2⟩ := linearTerm_modulus_tendstoZero P mdot θ₀ hmdot_meas hmdot_L2
    μ X hX_meas hX_indep hX_id hX_law M hM (ε / 2) (by linarith) (η / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  -- The process decomposition holds for `n ≥ N₀`:
  -- `𝔾ₙ(R_n(h)) = 𝔾ₙ[increment] − ⟪h, 𝔾ₙṁ⟫`.
  have hpid : ∀ (n : ℕ), N₀ ≤ n → ∀ (ξ : Ξ) (v : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}),
      empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • v.1) ω - m θ₀ ω)
            - ⟪v.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)
        = empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • v.1) ω - m θ₀ ω))
          - ⟪v.1, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ)⟫ :=
    fun n hn ξ v => linearizationResidual_process_eq P m mdot θ₀ hm_meas hmdot_L2 menv hmenv
      ρ hρ hLip n (fun i : Fin n => X i.val ξ) v.1 ((v.2).trans (hMρ n hn))
  -- Split the residual pair-modulus event into increment- and linear-modulus events.
  have hsub : ∀ n, N₀ ≤ n → {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
        ‖h₁.1 - h₂.1‖ < min δ₁ δ₂ ∧
        ε < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                  - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
              - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                  - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|}
      ⊆ {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ₁ ∧
            ε / 2 < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω))
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω))|}
        ∪ {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ₂ ∧
            ε / 2 < |(⟪h₁.1 - h₂.1, empiricalProcessVec P
                    (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                    (fun i : Fin n => X i.val ξ)⟫ : ℝ)|} := by
    intro n hn ξ hξ
    obtain ⟨h₁, h₂, hnorm, hosc⟩ := hξ
    rw [hpid n hn ξ h₁, hpid n hn ξ h₂] at hosc
    set E₁ := empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)) with hE₁
    set E₂ := empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)) with hE₂
    set 𝔾 := empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
        (fun i : Fin n => X i.val ξ) with h𝔾
    have htri : ε < |E₁ - E₂| + |(⟪h₁.1 - h₂.1, 𝔾⟫ : ℝ)| := by
      refine lt_of_lt_of_le hosc ?_
      have heq : (E₁ - ⟪h₁.1, 𝔾⟫) - (E₂ - ⟪h₂.1, 𝔾⟫)
          = (E₁ - E₂) + (-(⟪h₁.1 - h₂.1, 𝔾⟫ : ℝ)) := by
        rw [inner_sub_left]; ring
      rw [heq]
      exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    by_cases hA : ε / 2 < |E₁ - E₂|
    · exact Or.inl ⟨h₁, h₂, lt_of_lt_of_le hnorm (min_le_left δ₁ δ₂), hA⟩
    · push_neg at hA
      refine Or.inr ⟨h₁, h₂, lt_of_lt_of_le hnorm (min_le_right δ₁ δ₂), ?_⟩
      linarith [htri, hA]
  -- `P*`-subadditivity, then combine the two moduli via `limsup`-subadditivity.
  have hbound : ∀ n, N₀ ≤ n →
      μ.outerMeasureStar {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
        ‖h₁.1 - h₂.1‖ < min δ₁ δ₂ ∧
        ε < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                  - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
              - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                  - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|}
      ≤ μ.outerMeasureStar {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ₁ ∧
            ε / 2 < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω))
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω))|}
        + μ.outerMeasureStar {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ₂ ∧
            ε / 2 < |(⟪h₁.1 - h₂.1, empiricalProcessVec P
                    (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                    (fun i : Fin n => X i.val ξ)⟫ : ℝ)|} :=
    fun n hn => (outerMeasureStar_mono μ (hsub n hn)).trans (outerMeasureStar_union_le μ _ _)
  calc limsup (fun n => μ.outerMeasureStar {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
          ‖h₁.1 - h₂.1‖ < min δ₁ δ₂ ∧
          ε < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                    - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
                - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                    - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|}) atTop
      ≤ limsup (fun n => μ.outerMeasureStar {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ₁ ∧
            ε / 2 < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω))
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω))|}
          + μ.outerMeasureStar {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ₂ ∧
            ε / 2 < |(⟪h₁.1 - h₂.1, empiricalProcessVec P
                    (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                    (fun i : Fin n => X i.val ξ)⟫ : ℝ)|}) atTop :=
        limsup_le_limsup (Filter.eventually_atTop.mpr ⟨N₀, hbound⟩) isCobounded_le_of_bot
          (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := limsup_add_le_ofReal _ _ hN3 hN2
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ η / 2) (by linarith : (0 : ℝ) ≤ η / 2),
          add_halves]

/-- **Sup-over-ball linearization vanishes in outer probability.**

For each `M ≥ 0`, the linearization residual, as a family indexed by the closed
`M`-ball `{h : ‖h‖ ≤ M}`, tends to `0` in outer probability uniformly:
`𝔾ₙ[√n·(m_{θ₀ + h/√n} − m_{θ₀})] − ⟪h, 𝔾ₙṁ_{θ₀}⟫ →ₚ 0` (sup over the ball).
Route: rewrite `⟪h, 𝔾ₙṁ⟫ = 𝔾ₙ(ω ↦ ⟪h, ṁ(ω)⟫)` using
`empiricalProcess_inner_empiricalProcessVec`, then feed the marginal tail and
the residual pair modulus — an `ε/η` split of the exceedance
event into a fixed-net marginal part and an oscillation part — to the
`ℓ∞` collapse argument. It is consumed through
`tendstoInProbZero_of_ball_outerProbSup`. -/
theorem linearizationSup_tendstoZeroInOuterProbSup
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (hmdot_meas : ∀ i, Measurable (mdot i))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hderiv : ∀ᵐ ω ∂P, HasFDerivAt (fun θ => m θ ω)
      (innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) θ₀)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hmenv_meas : Measurable menv)
    (M : ℝ) (hM : 0 ≤ M) :
    TendstoZeroInOuterProbSup μ
      (fun n ξ (h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}) =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω))
          - ⟪h.1, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ)⟫) := by
  simp only [TendstoZeroInOuterProbSup]
  intro ε hε
  -- Small-`n` threshold: for `n ≥ N₀` the whole `M`-ball lands in `closedBall θ₀ ρ` (after `/√n`).
  set N₀ : ℕ := ⌈(M / ρ) ^ 2⌉₊ with hN₀def
  have hMρ : ∀ n : ℕ, N₀ ≤ n → M ≤ ρ * Real.sqrt n := fun n hn =>
    le_rho_mul_sqrt_of_ceil_le hρ hM hn
  -- Apply the process decomposition to each direction `v` once `n ≥ N₀`:
  -- `𝔾ₙ(R_n(v)) = 𝔾ₙ[increment] − ⟪v, 𝔾ₙṁ⟫`.
  have hpid : ∀ (n : ℕ), N₀ ≤ n → ∀ (ξ : Ξ) (v : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}),
      empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • v.1) ω - m θ₀ ω)
            - ⟪v.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)
        = empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • v.1) ω - m θ₀ ω))
          - ⟪v.1, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ)⟫ :=
    fun n hn ξ v => linearizationResidual_process_eq P m mdot θ₀ hm_meas hmdot_L2 menv hmenv
      ρ hρ hLip n (fun i : Fin n => X i.val ξ) v.1 ((v.2).trans (hMρ n hn))
  -- Rewrite the exceedance event in residual form, eventually for `n ≥ N₀`.
  suffices hres : Tendsto (fun n => μ.outerMeasureStar {ξ : Ξ |
      ∃ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω)
              - ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}) atTop (𝓝 0) by
    refine hres.congr' ?_
    filter_upwards [eventually_ge_atTop N₀] with n hn
    congr 1
    ext ξ
    simp only [Set.mem_setOf_eq]
    refine exists_congr (fun hh => ?_)
    rw [hpid n hn ξ hh]
  set u : ℕ → ℝ≥0∞ := fun n => μ.outerMeasureStar {ξ : Ξ |
      ∃ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω)
              - ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|} with hu
  -- Reduce `Tendsto u → 0` to `∀ η > 0, limsup u ≤ ofReal η`.
  suffices hlimsup : ∀ η : ℝ, 0 < η → limsup u atTop ≤ ENNReal.ofReal η by
    have hsup0 : limsup u atTop ≤ 0 := by
      refine ENNReal.le_of_forall_pos_le_add fun η hηpos _ => ?_
      rw [zero_add]
      have := hlimsup (η : ℝ) (by exact_mod_cast hηpos)
      rwa [ENNReal.ofReal_coe_nnreal] at this
    have hsup0' : limsup u atTop = 0 := le_antisymm hsup0 bot_le
    refine tendsto_of_le_liminf_of_limsup_le bot_le hsup0'.le ?_ ?_
    · exact isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
    · exact isBoundedUnder_of ⟨0, fun _ => bot_le⟩
  intro η hη
  -- The residual pair modulus at `(ε/2, η)` gives the radius `δ`.
  obtain ⟨δ, hδpos, hN4⟩ := linearizationResidual_pairModulus_tendstoZero P m mdot θ₀
    hm_meas hmdot_meas hmdot_L2 menv hmenv hmenv_meas ρ hρ hLip μ X hX_meas hX_indep hX_id hX_law
    M hM (ε / 2) (by linarith) η hη
  -- Finite `δ`-net of the compact closed `M`-ball.
  obtain ⟨t, ht_sub, ht_fin, ht_cover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) M) hδpos
  set T : Finset (EuclideanSpace ℝ (Fin d)) := ht_fin.toFinset with hT
  -- Each net-point marginal vanishes by fixed-direction convergence (`μ.real → μ`).
  have hmar_each : ∀ x : EuclideanSpace ℝ (Fin d),
      Tendsto (fun n => μ {ξ : Ξ | ε / 2 ≤
        |empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
            - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}) atTop (𝓝 0) := by
    intro x
    have hN1 := linearization_marginal_tendstoInProbZero P m mdot θ₀ hm_meas hmdot_meas hmdot_L2
      menv hmenv ρ hρ hLip hderiv μ X hX_meas hX_indep hX_id hX_law x (ε / 2) (by linarith)
    simp only [Real.norm_eq_abs] at hN1
    have h1 : Tendsto (fun n => ENNReal.ofReal (μ.real {ξ : Ξ | ε / 2 ≤
        |empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
            - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})) atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp hN1
    refine h1.congr (fun n => ?_)
    rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  -- The finite-net marginal envelope vanishes.
  have hMar0 : Tendsto (fun n => μ.outerMeasureStar
      (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
          - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})) atTop (𝓝 0) := by
    have hsum0 : Tendsto (fun n => ∑ x ∈ T, μ {ξ : Ξ | ε / 2 ≤
        |empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
            - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}) atTop (𝓝 0) := by
      have hts := tendsto_finset_sum T (fun x _ => hmar_each x)
      simpa using hts
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum0
      (Eventually.of_forall fun n => zero_le _) (Eventually.of_forall fun n => ?_)
    calc μ.outerMeasureStar (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
          |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
              - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})
        ≤ μ (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
          |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
              - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}) :=
          outerMeasureStar_le_measure μ _
      _ ≤ ∑ x ∈ T, μ {ξ : Ξ | ε / 2 ≤
          |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
              - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|} :=
          measure_biUnion_finset_le T _
  -- Ball-net split: exceedance ⊆ finite-net marginal event ∪ residual oscillation event.
  have hsplit : ∀ n, {ξ : Ξ | ∃ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
        ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω)
                - ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}
      ⊆ (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
              - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})
        ∪ {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ ∧
            ε / 2 < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                      - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
                  - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                      - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|} := by
    intro n ξ hξ
    obtain ⟨h, hh⟩ := hξ
    have hmem : h.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact h.2
    obtain ⟨x, hx_t, hx_ball⟩ := Set.mem_iUnion₂.mp (ht_cover hmem)
    rw [Metric.mem_ball, dist_eq_norm] at hx_ball
    have hx_M : ‖x‖ ≤ M := by
      have hxc := ht_sub hx_t
      rw [Metric.mem_closedBall, dist_zero_right] at hxc
      exact hxc
    set A := empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω)
          - ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) with hA
    set B := empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
          - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) with hB
    have htri : ε < |B| + |A - B| := by
      have hle : |A| ≤ |B| + |A - B| := by
        have habs := abs_add_le B (A - B)
        have heq : B + (A - B) = A := by ring
        rwa [heq] at habs
      linarith [hh, hle]
    by_cases hx_case : ε / 2 ≤ |B|
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨x, (Set.Finite.mem_toFinset ht_fin).mpr hx_t, hx_case⟩)
    · push_neg at hx_case
      have hosc : ε / 2 < |A - B| := by linarith [htri, hx_case]
      exact Or.inr ⟨h, ⟨x, hx_M⟩, hx_ball, hosc⟩
  -- `P*`-subadditivity, then `limsup`-add with the vanishing marginal envelope.
  have hbound : ∀ n, u n ≤ μ.outerMeasureStar {ξ : Ξ |
        ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
        ‖h₁.1 - h₂.1‖ < δ ∧
        ε / 2 < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                  - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
              - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                  - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|}
      + μ.outerMeasureStar (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
          |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
              - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}) := by
    intro n
    simp only [hu]
    calc μ.outerMeasureStar {ξ : Ξ | ∃ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
          ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω)
                  - ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}
        ≤ μ.outerMeasureStar ((⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
              |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
                - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})
            ∪ {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
              ‖h₁.1 - h₂.1‖ < δ ∧
              ε / 2 < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                        - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
                    - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                        - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|}) :=
          outerMeasureStar_mono μ (hsplit n)
      _ ≤ μ.outerMeasureStar (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
              |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
                - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})
            + μ.outerMeasureStar {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
              ‖h₁.1 - h₂.1‖ < δ ∧
              ε / 2 < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                        - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
                    - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                        - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|} :=
          outerMeasureStar_union_le μ _ _
      _ = _ := add_comm _ _
  calc limsup u atTop
      ≤ limsup (fun n => μ.outerMeasureStar {ξ : Ξ |
            ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ ∧
            ε / 2 < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                      - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
                  - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                      - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|}
          + μ.outerMeasureStar (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
              |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
                  - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})) atTop :=
        limsup_le_limsup (Eventually.of_forall hbound) isCobounded_le_of_bot
          (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ ≤ ENNReal.ofReal η := limsup_add_tendsto_zero_le _ _ _ hN4 hMar0

/-- Sup-over-ball variant of
`linearizationSup_tendstoZeroInOuterProbSup` supplied with fixed-direction
`distL2` convergence.  Pair-modulus regularity is unchanged; in particular
`hmdot_meas` remains required by the residual and linear-term modulus bounds. -/
theorem linearizationSup_tendstoZeroInOuterProbSup_of_distL2
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (hmdot_meas : ∀ i, Measurable (mdot i))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hd : ∀ h : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ => distL2 P
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
      atTop (𝓝 0))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hmenv_meas : Measurable menv)
    (M : ℝ) (hM : 0 ≤ M) :
    TendstoZeroInOuterProbSup μ
      (fun n ξ (h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}) =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω))
          - ⟪h.1, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ)⟫) := by
  simp only [TendstoZeroInOuterProbSup]
  intro ε hε
  set N₀ : ℕ := ⌈(M / ρ) ^ 2⌉₊ with hN₀def
  have hMρ : ∀ n : ℕ, N₀ ≤ n → M ≤ ρ * Real.sqrt n := fun n hn =>
    le_rho_mul_sqrt_of_ceil_le hρ hM hn
  have hpid : ∀ (n : ℕ), N₀ ≤ n → ∀ (ξ : Ξ) (v : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M}),
      empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • v.1) ω - m θ₀ ω)
            - ⟪v.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)
        = empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • v.1) ω - m θ₀ ω))
          - ⟪v.1, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ)⟫ :=
    fun n hn ξ v => linearizationResidual_process_eq P m mdot θ₀ hm_meas hmdot_L2 menv hmenv
      ρ hρ hLip n (fun i : Fin n => X i.val ξ) v.1 ((v.2).trans (hMρ n hn))
  suffices hres : Tendsto (fun n => μ.outerMeasureStar {ξ : Ξ |
      ∃ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω)
              - ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}) atTop (𝓝 0) by
    refine hres.congr' ?_
    filter_upwards [eventually_ge_atTop N₀] with n hn
    congr 1
    ext ξ
    simp only [Set.mem_setOf_eq]
    refine exists_congr (fun hh => ?_)
    rw [hpid n hn ξ hh]
  set u : ℕ → ℝ≥0∞ := fun n => μ.outerMeasureStar {ξ : Ξ |
      ∃ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω)
              - ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|} with hu
  suffices hlimsup : ∀ η : ℝ, 0 < η → limsup u atTop ≤ ENNReal.ofReal η by
    have hsup0 : limsup u atTop ≤ 0 := by
      refine ENNReal.le_of_forall_pos_le_add fun η hηpos _ => ?_
      rw [zero_add]
      have := hlimsup (η : ℝ) (by exact_mod_cast hηpos)
      rwa [ENNReal.ofReal_coe_nnreal] at this
    have hsup0' : limsup u atTop = 0 := le_antisymm hsup0 bot_le
    refine tendsto_of_le_liminf_of_limsup_le bot_le hsup0'.le ?_ ?_
    · exact isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
    · exact isBoundedUnder_of ⟨0, fun _ => bot_le⟩
  intro η hη
  obtain ⟨δ, hδpos, hN4⟩ := linearizationResidual_pairModulus_tendstoZero P m mdot θ₀
    hm_meas hmdot_meas hmdot_L2 menv hmenv hmenv_meas ρ hρ hLip μ X hX_meas hX_indep hX_id hX_law
    M hM (ε / 2) (by linarith) η hη
  obtain ⟨t, ht_sub, ht_fin, ht_cover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) M) hδpos
  set T : Finset (EuclideanSpace ℝ (Fin d)) := ht_fin.toFinset with hT
  have hmar_each : ∀ x : EuclideanSpace ℝ (Fin d),
      Tendsto (fun n => μ {ξ : Ξ | ε / 2 ≤
        |empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
            - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}) atTop (𝓝 0) := by
    intro x
    have hN1 := linearization_marginal_tendstoInProbZero_of_distL2 P m mdot θ₀ hm_meas
      hmdot_L2 menv hmenv ρ hρ hLip μ X hX_meas hX_indep hX_id hX_law x (hd x)
      (ε / 2) (by linarith)
    simp only [Real.norm_eq_abs] at hN1
    have h1 : Tendsto (fun n => ENNReal.ofReal (μ.real {ξ : Ξ | ε / 2 ≤
        |empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
            - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})) atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp hN1
    refine h1.congr (fun n => ?_)
    rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hMar0 : Tendsto (fun n => μ.outerMeasureStar
      (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
          - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})) atTop (𝓝 0) := by
    have hsum0 : Tendsto (fun n => ∑ x ∈ T, μ {ξ : Ξ | ε / 2 ≤
        |empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
            - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}) atTop (𝓝 0) := by
      have hts := tendsto_finset_sum T (fun x _ => hmar_each x)
      simpa using hts
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum0
      (Eventually.of_forall fun n => zero_le _) (Eventually.of_forall fun n => ?_)
    calc μ.outerMeasureStar (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
          |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
              - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})
        ≤ μ (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
          |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
              - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}) :=
          outerMeasureStar_le_measure μ _
      _ ≤ ∑ x ∈ T, μ {ξ : Ξ | ε / 2 ≤
          |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
              - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|} :=
          measure_biUnion_finset_le T _
  have hsplit : ∀ n, {ξ : Ξ | ∃ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
        ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω)
                - ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}
      ⊆ (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
              - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})
        ∪ {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ ∧
            ε / 2 < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                      - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
                  - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                      - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|} := by
    intro n ξ hξ
    obtain ⟨h, hh⟩ := hξ
    have hmem : h.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) M := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact h.2
    obtain ⟨x, hx_t, hx_ball⟩ := Set.mem_iUnion₂.mp (ht_cover hmem)
    rw [Metric.mem_ball, dist_eq_norm] at hx_ball
    have hx_M : ‖x‖ ≤ M := by
      have hxc := ht_sub hx_t
      rw [Metric.mem_closedBall, dist_zero_right] at hxc
      exact hxc
    set A := empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω)
          - ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) with hA
    set B := empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
          - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫) with hB
    have htri : ε < |B| + |A - B| := by
      have hle : |A| ≤ |B| + |A - B| := by
        have habs := abs_add_le B (A - B)
        have heq : B + (A - B) = A := by ring
        rwa [heq] at habs
      linarith [hh, hle]
    by_cases hx_case : ε / 2 ≤ |B|
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨x, (Set.Finite.mem_toFinset ht_fin).mpr hx_t, hx_case⟩)
    · push Not at hx_case
      have hosc : ε / 2 < |A - B| := by linarith [htri, hx_case]
      exact Or.inr ⟨h, ⟨x, hx_M⟩, hx_ball, hosc⟩
  have hbound : ∀ n, u n ≤ μ.outerMeasureStar {ξ : Ξ |
        ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
        ‖h₁.1 - h₂.1‖ < δ ∧
        ε / 2 < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                  - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
              - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                  - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|}
      + μ.outerMeasureStar (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
          |empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
              - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}) := by
    intro n
    simp only [hu]
    calc μ.outerMeasureStar {ξ : Ξ | ∃ h : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
          ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h.1) ω - m θ₀ ω)
                  - ⟪h.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|}
        ≤ μ.outerMeasureStar ((⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
              |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
                - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})
            ∪ {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
              ‖h₁.1 - h₂.1‖ < δ ∧
              ε / 2 < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                        - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
                    - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                        - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|}) :=
          outerMeasureStar_mono μ (hsplit n)
      _ ≤ μ.outerMeasureStar (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
              |empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
                - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})
            + μ.outerMeasureStar {ξ : Ξ | ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
              ‖h₁.1 - h₂.1‖ < δ ∧
              ε / 2 < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                        - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
                    - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                        - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|} :=
          outerMeasureStar_union_le μ _ _
      _ = _ := add_comm _ _
  calc limsup u atTop
      ≤ limsup (fun n => μ.outerMeasureStar {ξ : Ξ |
            ∃ h₁ h₂ : {h : EuclideanSpace ℝ (Fin d) // ‖h‖ ≤ M},
            ‖h₁.1 - h₂.1‖ < δ ∧
            ε / 2 < |(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₁.1) ω - m θ₀ ω)
                      - ⟪h₁.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
                  - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h₂.1) ω - m θ₀ ω)
                      - ⟪h₂.1, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))|}
          + μ.outerMeasureStar (⋃ x ∈ T, {ξ : Ξ | ε / 2 ≤
              |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • x) ω - m θ₀ ω)
                  - ⟪x, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫)|})) atTop :=
        limsup_le_limsup (Eventually.of_forall hbound) isCobounded_le_of_bot
          (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ ≤ ENNReal.ofReal η := limsup_add_tendsto_zero_le _ _ _ hN4 hMar0

/-! ### vdV Lemma 19.31 -/

/-- **M-estimator linearization equicontinuity** (vdV Lemma 19.31).

For a bounded-in-probability random direction `hₙ`, the localized empirical
process increment linearises,

    𝔾ₙ[√n(m_{θ₀ + hₙ/√n} − m_{θ₀})] − ⟪hₙ, 𝔾ₙṁ_{θ₀}⟫ →ₚ 0,

where `𝔾ₙṁ_{θ₀} = empiricalProcessVec P (fun _ => mdot) θ₀ n Xs`. The Lean
implementation uses `linearizationSup_tendstoZeroInOuterProbSup`: its
changing-class argument combines the Theorem 19.28 scaled-shell pair modulus
with fixed-direction convergence on a finite net. Since `hₙ` is `O_P(1)`, it
eventually lies in a closed `M`-ball, so the uniform bound collapses to the
single random value `hₙ n ξ`, yielding this scalar `TendstoInProbZero`. -/
theorem mEstimator_linearization_equicontinuity
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (hmdot_meas : ∀ i, Measurable (mdot i))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hderiv : ∀ᵐ ω ∂P, HasFDerivAt (fun θ => m θ ω)
      (innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) θ₀)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hmenv_meas : Measurable menv)
    (hₙ : ℕ → Ξ → EuclideanSpace ℝ (Fin d))
    (hₙ_meas : ∀ n, Measurable (hₙ n))
    (hₙ_bdd : IsBoundedInProb (fun _ : ℕ => μ) hₙ) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => Real.sqrt n *
            (m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω))
        - ⟪hₙ n ξ, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
              (fun i : Fin n => X i.val ξ)⟫) := by
  -- Collapse the closed `M`-ball supremum onto the `O_P(1)` random direction `hₙ`.
  refine tendstoInProbZero_of_ball_outerProbSup μ
    (fun n ξ h => empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      - ⟪h, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
            (fun i : Fin n => X i.val ξ)⟫)
    hₙ hₙ_meas (fun M hM => ?_) hₙ_bdd
  exact linearizationSup_tendstoZeroInOuterProbSup P m mdot θ₀ hm_meas hmdot_meas hmdot_L2
    menv hmenv ρ hρ hLip hderiv μ X hX_meas hX_indep hX_id hX_law hmenv_meas M hM

/-- Adapter whose fixed-direction `distL2` convergence is supplied directly,
matching the differentiability-in-probability route used by vdV 5.23/5.39. -/
theorem mEstimator_linearization_equicontinuity_of_distL2
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (hmdot_meas : ∀ i, Measurable (mdot i))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hd : ∀ h : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ => distL2 P
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
      atTop (𝓝 0))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hmenv_meas : Measurable menv)
    (hₙ : ℕ → Ξ → EuclideanSpace ℝ (Fin d))
    (hₙ_meas : ∀ n, Measurable (hₙ n))
    (hₙ_bdd : IsBoundedInProb (fun _ : ℕ => μ) hₙ) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun ω => Real.sqrt n *
            (m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω))
        - ⟪hₙ n ξ, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
              (fun i : Fin n => X i.val ξ)⟫) := by
  refine tendstoInProbZero_of_ball_outerProbSup μ
    (fun n ξ h => empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      - ⟪h, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
            (fun i : Fin n => X i.val ξ)⟫)
    hₙ hₙ_meas (fun M hM => ?_) hₙ_bdd
  exact linearizationSup_tendstoZeroInOuterProbSup_of_distL2 P m mdot θ₀ hm_meas
    hmdot_meas hmdot_L2 menv hmenv ρ hρ hLip hd μ X hX_meas hX_indep hX_id hX_law
    hmenv_meas M hM

end AsymptoticStatistics.EmpiricalProcess
