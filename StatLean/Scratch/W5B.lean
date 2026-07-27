import StatLean.HypothesisTesting.GoodnessOfFit.SmoothTest
import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity

/-! Scratch development file for wave-5 lane B.  Not part of the library. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators NNReal InnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧]

/-- The inner product against the per-observation score vector, in coordinates. -/
private lemma inner_psiVec {k : ℕ} (ψ : Fin k → 𝓧 → ℝ) (u : EuclideanSpace ℝ (Fin k))
    (x : 𝓧) : ⟪u, psiVec ψ x⟫_ℝ = ∑ j, u j * ψ j x := by
  rw [inner_euclidean_sum]
  exact Finset.sum_congr rfl fun j _ => rfl

/-! ### Elementary real inequalities -/

/-- `|e^z − (1 + z + z²/2)| ≤ 4 |z|³ e^{|z|}` for every real `z`. -/
private lemma abs_exp_sub_quadratic_le (z : ℝ) :
    |Real.exp z - (1 + z + z ^ 2 / 2)| ≤ 4 * |z| ^ 3 * Real.exp |z| := by
  have hexp1 : (1 : ℝ) ≤ Real.exp |z| := Real.one_le_exp (abs_nonneg z)
  have hcube0 : (0 : ℝ) ≤ |z| ^ 3 := pow_nonneg (abs_nonneg z) 3
  rcases le_or_gt |z| 1 with hle | hgt
  · have h := Real.exp_bound hle (n := 3) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 3, z ^ m / (Nat.factorial m) = 1 + z + z ^ 2 / 2 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    rw [hsum] at h
    have hcoef : ((Nat.succ 3 : ℝ) / ((Nat.factorial 3 : ℝ) * 3)) ≤ 4 := by
      norm_num [Nat.factorial]
    calc |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |z| ^ 3 * ((Nat.succ 3 : ℝ) / ((Nat.factorial 3) * 3)) := h
      _ ≤ |z| ^ 3 * 4 := by nlinarith
      _ ≤ 4 * |z| ^ 3 * Real.exp |z| := by nlinarith
  · -- `|z| > 1`: crude triangle-inequality bound
    have habs0 : (0 : ℝ) ≤ |z| := abs_nonneg z
    have h1 : (1 : ℝ) ≤ |z| ^ 3 := one_le_pow₀ hgt.le
    have hd : 0 ≤ |z| * ((|z| - 1) * (|z| + 1)) :=
      mul_nonneg habs0 (mul_nonneg (by linarith) (by linarith))
    have hz : |z| ≤ |z| ^ 3 := by nlinarith
    have hd2 : 0 ≤ (|z| * |z|) * (|z| - 1) :=
      mul_nonneg (mul_nonneg habs0 habs0) (by linarith)
    have hz2 : z ^ 2 ≤ |z| ^ 3 := by
      have hsq : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
      nlinarith
    have hexpz : Real.exp z ≤ Real.exp |z| := Real.exp_le_exp.mpr (le_abs_self z)
    have htri : |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |Real.exp z| + |1 + z + z ^ 2 / 2| := by
      rw [sub_eq_add_neg]
      refine (abs_add_le _ _).trans_eq ?_
      rw [abs_neg]
    have hterm : |1 + z + z ^ 2 / 2| ≤ 3 * |z| ^ 3 := by
      have hb : |1 + z + z ^ 2 / 2| ≤ 1 + |z| + z ^ 2 / 2 := by
        have h₁ : |1 + z + z ^ 2 / 2| ≤ |1 + z| + |z ^ 2 / 2| := abs_add_le _ _
        have h₂ : |1 + z| ≤ 1 + |z| := by
          calc |1 + z| ≤ |(1 : ℝ)| + |z| := abs_add_le _ _
            _ = 1 + |z| := by norm_num
        have h₃ : |z ^ 2 / 2| = z ^ 2 / 2 := abs_of_nonneg (by positivity)
        linarith
      linarith
    have hexpabs : |Real.exp z| = Real.exp z := abs_of_nonneg (Real.exp_pos z).le
    have hstep : Real.exp |z| ≤ |z| ^ 3 * Real.exp |z| := by nlinarith [Real.exp_pos |z|]
    calc |Real.exp z - (1 + z + z ^ 2 / 2)|
        ≤ |Real.exp z| + |1 + z + z ^ 2 / 2| := htri
      _ ≤ Real.exp |z| + 3 * |z| ^ 3 := by rw [hexpabs]; linarith
      _ ≤ 4 * |z| ^ 3 * Real.exp |z| := by nlinarith

/-- `|log (1 + w) − w| ≤ w²` for `w ≥ 0`. -/
private lemma abs_log_one_add_sub_le (w : ℝ) (hw : 0 ≤ w) :
    |Real.log (1 + w) - w| ≤ w ^ 2 := by
  have hpos : (0 : ℝ) < 1 + w := by linarith
  have hup : Real.log (1 + w) ≤ w := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlow : w - w ^ 2 ≤ Real.log (1 + w) := by
    have h := Real.log_le_sub_one_of_pos (x := (1 + w)⁻¹) (by positivity)
    rw [Real.log_inv] at h
    have hne : (1 : ℝ) + w ≠ 0 := ne_of_gt hpos
    have hkey : 1 - (1 + w)⁻¹ = w / (1 + w) := by field_simp; ring
    have h3 : w - w ^ 2 ≤ 1 - (1 + w)⁻¹ := by
      rw [hkey, le_div_iff₀ hpos]
      nlinarith [pow_nonneg hw 3]
    linarith
  rw [abs_le]
  constructor <;> nlinarith

/-- `u³ ≤ 6 t⁻³ e^{t u}` for `u ≥ 0`, `t > 0`. -/
private lemma cube_le_exp (t : ℝ) (ht : 0 < t) (u : ℝ) (hu : 0 ≤ u) :
    u ^ 3 ≤ 6 / t ^ 3 * Real.exp (t * u) := by
  have h := Real.sum_le_exp_of_nonneg (x := t * u) (by positivity) 4
  have hsum : ∑ m ∈ Finset.range 4, (t * u) ^ m / (Nat.factorial m)
      = 1 + t * u + (t * u) ^ 2 / 2 + (t * u) ^ 3 / 6 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have htu : 0 ≤ t * u := by positivity
  have hcube : (t * u) ^ 3 / 6 ≤ Real.exp (t * u) := by nlinarith [sq_nonneg (t * u)]
  have ht3 : (0 : ℝ) < t ^ 3 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ ht3]
  nlinarith


/-! ### Envelope integrability from the natural parameter set -/

/-- **Sign-vector envelope.** If every exponential tilt `e^{⟪θ, ψ(x)⟫}` is `P₀`-integrable,
then so is `e^{t ∑ⱼ |ψⱼ(x)|}` for every `t ≥ 0`: the `ℓ¹` exponential is dominated by the
sum of the `2^k` sign tilts. -/
private lemma integrable_exp_l1 {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} (hψmeas : ∀ j, Measurable (ψ j))
    (hint : ∀ θ : EuclideanSpace ℝ (Fin k),
      Integrable (fun x => Real.exp ⟪θ, psiVec ψ x⟫_ℝ) P₀)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => Real.exp (t * ∑ j, |ψ j x|)) P₀ := by
  classical
  set Θ : Finset (Fin k) → EuclideanSpace ℝ (Fin k) :=
    fun s => WithLp.toLp 2 (fun j => if j ∈ s then t else -t) with hΘ
  have hmeas : Measurable (fun x => Real.exp (t * ∑ j, |ψ j x|)) :=
    Real.continuous_exp.measurable.comp
      ((Finset.univ.measurable_sum fun j _ => (hψmeas j).abs).const_mul t)
  have hbound : ∀ x, Real.exp (t * ∑ j, |ψ j x|)
      ≤ ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, Real.exp ⟪Θ s, psiVec ψ x⟫_ℝ := by
    intro x
    have hprod : Real.exp (t * ∑ j, |ψ j x|) = ∏ j, Real.exp (t * |ψ j x|) := by
      rw [← Real.exp_sum, Finset.mul_sum]
    have hpt : ∀ j : Fin k,
        Real.exp (t * |ψ j x|) ≤ Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x)) := by
      intro j
      rcases abs_cases (ψ j x) with ⟨h1, -⟩ | ⟨h1, -⟩
      · rw [h1]
        nlinarith [Real.exp_pos (-(t * ψ j x)), le_refl (Real.exp (t * ψ j x))]
      · rw [h1, mul_neg, ← neg_mul]
        nlinarith [Real.exp_pos (t * ψ j x)]
    have hle : ∏ j, Real.exp (t * |ψ j x|)
        ≤ ∏ j, (Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x))) :=
      Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) (fun j _ => hpt j)
    have hexpand : ∏ j, (Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x)))
        = ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset, Real.exp ⟪Θ s, psiVec ψ x⟫_ℝ := by
      rw [Finset.prod_add]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsub : s ⊆ (Finset.univ : Finset (Fin k)) := Finset.subset_univ s
      have hL : (∏ j ∈ s, Real.exp (t * ψ j x))
          * ∏ j ∈ (Finset.univ : Finset (Fin k)) \ s, Real.exp (-(t * ψ j x))
          = Real.exp ((∑ j ∈ s, t * ψ j x)
              + ∑ j ∈ (Finset.univ : Finset (Fin k)) \ s, -(t * ψ j x)) := by
        rw [Real.exp_add, Real.exp_sum, Real.exp_sum]
      rw [hL]
      congr 1
      rw [inner_psiVec]
      rw [← Finset.sum_sdiff hsub]
      have h1 : ∑ j ∈ (Finset.univ : Finset (Fin k)) \ s, (Θ s) j * ψ j x
          = ∑ j ∈ (Finset.univ : Finset (Fin k)) \ s, -(t * ψ j x) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjs : j ∉ s := (Finset.mem_sdiff.mp hj).2
        show (if j ∈ s then t else -t) * ψ j x = -(t * ψ j x)
        rw [if_neg hjs]; ring
      have h2 : ∑ j ∈ s, (Θ s) j * ψ j x = ∑ j ∈ s, t * ψ j x := by
        refine Finset.sum_congr rfl fun j hj => ?_
        show (if j ∈ s then t else -t) * ψ j x = t * ψ j x
        rw [if_pos hj]
      rw [h1, h2, add_comm]
    calc Real.exp (t * ∑ j, |ψ j x|) = ∏ j, Real.exp (t * |ψ j x|) := hprod
      _ ≤ ∏ j, (Real.exp (t * ψ j x) + Real.exp (-(t * ψ j x))) := hle
      _ = _ := hexpand
  have hsumint : Integrable (fun x => ∑ s ∈ (Finset.univ : Finset (Fin k)).powerset,
      Real.exp ⟪Θ s, psiVec ψ x⟫_ℝ) P₀ :=
    integrable_finset_sum (Finset.univ : Finset (Fin k)).powerset (fun s _ => hint (Θ s))
  refine Integrable.mono' hsumint hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact hbound x


/-! ### The quadratic expansion of the log-partition function -/

/-- `|θ j| ≤ ‖θ‖` in `EuclideanSpace`. -/
private lemma abs_coord_le_norm {k : ℕ} (θ : EuclideanSpace ℝ (Fin k)) (j : Fin k) :
    |θ j| ≤ ‖θ‖ := by
  have hle : (θ j) ^ 2 ≤ ‖θ‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (f := fun i => (θ i) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  nlinarith [sq_abs (θ j), abs_nonneg (θ j), norm_nonneg θ]

/-- Integrability facts for an orthonormal centred score system. -/
private lemma score_L2_facts {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0) :
    (∀ i, Integrable (ψ i) P₀) ∧ (∀ i j, Integrable (fun x => ψ i x * ψ j x) P₀) := by
  have hsqint : ∀ i, Integrable (fun x => ψ i x ^ 2) P₀ := by
    intro i
    have h1 : (∫ x, ψ i x * ψ i x ∂P₀) = 1 := by rw [hortho i i]; simp
    simpa [sq] using integrable_of_integral_eq_one h1
  have hψL2 : ∀ i, MemLp (ψ i) 2 P₀ := fun i =>
    (memLp_two_iff_integrable_sq (hψmeas i).aestronglyMeasurable).2 (hsqint i)
  exact ⟨fun i => (hψL2 i).integrable one_le_two,
    fun i j => by simpa using (hψL2 i).integrable_mul (hψL2 j)⟩

/-- **Quadratic expansion of the log-partition function of the smooth model.**  For a centred
orthonormal score system whose exponential tilts are all integrable, the log-partition
function `A(θ) = log ∫ e^{⟪θ,ψ⟫} dP₀` satisfies `|A(θ) − ‖θ‖²/2| ≤ C‖θ‖³` on the ball of
radius `r`.  Purely elementary: a third-order Taylor bound on `e^z`, the moment identities
`∫⟪θ,ψ⟫ = 0` and `∫⟪θ,ψ⟫² = ‖θ‖²`, and `|log(1+w) − w| ≤ w²`. -/
private lemma logPartition_quadratic_bound {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    (hint : ∀ θ : EuclideanSpace ℝ (Fin k),
      Integrable (fun x => Real.exp ⟪θ, psiVec ψ x⟫_ℝ) P₀)
    {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ‖ ≤ r →
      |Real.log (∫ x, Real.exp ⟪θ, psiVec ψ x⟫_ℝ ∂P₀) - ‖θ‖ ^ 2 / 2| ≤ C * ‖θ‖ ^ 3 := by
  classical
  obtain ⟨hψint, hψψint⟩ := score_L2_facts hψmeas hortho
  set W : 𝓧 → ℝ := fun x => ∑ j, |ψ j x| with hW
  have hWnn : ∀ x, 0 ≤ W x := fun x => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hWmeas : Measurable W := Finset.univ.measurable_sum fun j _ => (hψmeas j).abs
  -- the cubic envelope `G` and its integral `K`
  set G : 𝓧 → ℝ := fun x => (W x) ^ 3 * Real.exp (r * W x) with hG
  have hGnn : ∀ x, 0 ≤ G x := fun x => by positivity
  have hGmeas : Measurable G :=
    (hWmeas.pow_const 3).mul (Real.continuous_exp.measurable.comp (hWmeas.const_mul r))
  have hGint : Integrable G P₀ := by
    have hdom : Integrable (fun x => 6 / r ^ 3 * Real.exp (2 * r * W x)) P₀ := by
      have h2 := integrable_exp_l1 (P₀ := P₀) hψmeas hint (t := 2 * r) (by positivity)
      exact h2.const_mul _
    refine hdom.mono' hGmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (hGnn x)]
    have hcube := cube_le_exp r hr (W x) (hWnn x)
    have hexp : Real.exp (r * W x) * Real.exp (r * W x) = Real.exp (2 * r * W x) := by
      rw [← Real.exp_add]; ring_nf
    calc (W x) ^ 3 * Real.exp (r * W x)
        ≤ (6 / r ^ 3 * Real.exp (r * W x)) * Real.exp (r * W x) := by
          exact mul_le_mul_of_nonneg_right hcube (Real.exp_pos _).le
      _ = 6 / r ^ 3 * Real.exp (2 * r * W x) := by rw [mul_assoc, hexp]
  set K : ℝ := ∫ x, G x ∂P₀ with hK
  have hKnn : 0 ≤ K := integral_nonneg hGnn
  refine ⟨4 * K + r * (1 / 2 + 4 * K * r) ^ 2, by positivity, ?_⟩
  intro θ hθ
  have hθ0 : 0 ≤ ‖θ‖ := norm_nonneg θ
  set z : 𝓧 → ℝ := fun x => ⟪θ, psiVec ψ x⟫_ℝ with hz
  have hzval : ∀ x, z x = ∑ j, θ j * ψ j x := fun x => inner_psiVec ψ θ x
  have hzmeas : Measurable z := by
    have : z = fun x => ∑ j, θ j * ψ j x := funext hzval
    rw [this]
    exact Finset.univ.measurable_sum fun j _ => (hψmeas j).const_mul _
  have hzint : Integrable z P₀ := by
    have : z = fun x => ∑ j, θ j * ψ j x := funext hzval
    rw [this]
    exact integrable_finset_sum _ fun j _ => (hψint j).const_mul _
  have hzsqint : Integrable (fun x => z x ^ 2) P₀ := by
    have hpt : (fun x => z x ^ 2) = fun x => ∑ i, ∑ j, (θ i * θ j) * (ψ i x * ψ j x) := by
      funext x
      rw [hzval x, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hpt]
    exact integrable_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => (hψψint i j).const_mul _
  -- the two moment identities
  have hmom1 : ∫ x, z x ∂P₀ = 0 := by
    have : z = fun x => ∑ j, θ j * ψ j x := funext hzval
    rw [this, integral_finset_sum _ fun j _ => (hψint j).const_mul _]
    simp_rw [integral_const_mul, hcentred, mul_zero, Finset.sum_const_zero]
  have hmom2 : ∫ x, z x ^ 2 ∂P₀ = ‖θ‖ ^ 2 := by
    have hpt : (fun x => z x ^ 2) = fun x => ∑ i, ∑ j, (θ i * θ j) * (ψ i x * ψ j x) := by
      funext x
      rw [hzval x, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hpt, integral_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => (hψψint i j).const_mul _,
      EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => (hψψint i j).const_mul _]
    simp_rw [integral_const_mul, hortho i]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [if_neg (Ne.symm hji), mul_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [if_pos rfl, mul_one, sq]
  -- the pointwise third-order bound
  have hzbd : ∀ x, |z x| ≤ ‖θ‖ * W x := by
    intro x
    rw [hzval x]
    calc |∑ j, θ j * ψ j x| ≤ ∑ j, |θ j * ψ j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ‖θ‖ * |ψ j x| := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (abs_coord_le_norm θ j) (abs_nonneg _)
      _ = ‖θ‖ * W x := by rw [hW, Finset.mul_sum]
  have hptbd : ∀ x, |Real.exp (z x) - (1 + z x + (z x) ^ 2 / 2)| ≤ 4 * ‖θ‖ ^ 3 * G x := by
    intro x
    refine (abs_exp_sub_quadratic_le (z x)).trans ?_
    have h1 : |z x| ^ 3 ≤ ‖θ‖ ^ 3 * (W x) ^ 3 := by
      have := hzbd x
      have hpow : |z x| ^ 3 ≤ (‖θ‖ * W x) ^ 3 :=
        pow_le_pow_left₀ (abs_nonneg _) this 3
      calc |z x| ^ 3 ≤ (‖θ‖ * W x) ^ 3 := hpow
        _ = ‖θ‖ ^ 3 * (W x) ^ 3 := by ring
    have h2 : Real.exp |z x| ≤ Real.exp (r * W x) := by
      refine Real.exp_le_exp.mpr ((hzbd x).trans ?_)
      exact mul_le_mul_of_nonneg_right hθ (hWnn x)
    calc 4 * |z x| ^ 3 * Real.exp |z x|
        ≤ 4 * (‖θ‖ ^ 3 * (W x) ^ 3) * Real.exp (r * W x) := by
          have hc : (0 : ℝ) ≤ 4 * |z x| ^ 3 := by positivity
          have := mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
          nlinarith [Real.exp_pos (r * W x), pow_nonneg (abs_nonneg (z x)) 3]
      _ = 4 * ‖θ‖ ^ 3 * G x := by rw [hG]; ring
  -- the integral of the exponential
  set M : ℝ := ∫ x, Real.exp (z x) ∂P₀ with hM
  have hMint : Integrable (fun x => Real.exp (z x)) P₀ := hint θ
  have hquadint : Integrable (fun x => 1 + z x + (z x) ^ 2 / 2) P₀ :=
    ((integrable_const 1).add hzint).add (hzsqint.div_const 2)
  have hlinint : Integrable (fun x : 𝓧 => (1 : ℝ) + z x) P₀ := (integrable_const 1).add hzint
  have hquadval : ∫ x, (1 + z x + (z x) ^ 2 / 2) ∂P₀ = 1 + ‖θ‖ ^ 2 / 2 := by
    rw [show (∫ x, (1 + z x + (z x) ^ 2 / 2) ∂P₀)
          = (∫ x, ((1 : ℝ) + z x) ∂P₀) + ∫ x, (z x) ^ 2 / 2 ∂P₀ from
        integral_add hlinint (hzsqint.div_const 2),
      show (∫ x, ((1 : ℝ) + z x) ∂P₀) = (∫ _x : 𝓧, (1 : ℝ) ∂P₀) + ∫ x, z x ∂P₀ from
        integral_add (integrable_const 1) hzint,
      integral_div, hmom1, hmom2]
    simp
  have hMbd : |M - (1 + ‖θ‖ ^ 2 / 2)| ≤ 4 * ‖θ‖ ^ 3 * K := by
    have hdiff : M - (1 + ‖θ‖ ^ 2 / 2)
        = ∫ x, (Real.exp (z x) - (1 + z x + (z x) ^ 2 / 2)) ∂P₀ := by
      rw [integral_sub hMint hquadint, hquadval]
    rw [hdiff]
    refine (abs_integral_le_integral_abs).trans ?_
    have hb : ∫ x, |Real.exp (z x) - (1 + z x + (z x) ^ 2 / 2)| ∂P₀
        ≤ ∫ x, 4 * ‖θ‖ ^ 3 * G x ∂P₀ := by
      refine integral_mono ((hMint.sub hquadint).abs) (hGint.const_mul _) ?_
      intro x; exact hptbd x
    rw [integral_const_mul] at hb
    calc _ ≤ 4 * ‖θ‖ ^ 3 * K := hb
      _ = 4 * ‖θ‖ ^ 3 * K := rfl
  -- `M ≥ 1`
  have hM1 : 1 ≤ M := by
    have hmono : ∫ x, ((1 : ℝ) + z x) ∂P₀ ≤ M := by
      refine integral_mono hlinint hMint fun x => ?_
      have := Real.add_one_le_exp (z x)
      linarith
    rw [show (∫ x, ((1 : ℝ) + z x) ∂P₀) = (∫ _x : 𝓧, (1 : ℝ) ∂P₀) + ∫ x, z x ∂P₀ from
      integral_add (integrable_const 1) hzint, hmom1] at hmono
    simpa using hmono
  set w : ℝ := M - 1 with hw
  have hwnn : 0 ≤ w := by simp [hw]; linarith
  have hwbd : |w - ‖θ‖ ^ 2 / 2| ≤ 4 * K * ‖θ‖ ^ 3 := by
    have : w - ‖θ‖ ^ 2 / 2 = M - (1 + ‖θ‖ ^ 2 / 2) := by rw [hw]; ring
    rw [this]
    calc |M - (1 + ‖θ‖ ^ 2 / 2)| ≤ 4 * ‖θ‖ ^ 3 * K := hMbd
      _ = 4 * K * ‖θ‖ ^ 3 := by ring
  have hlog : |Real.log M - ‖θ‖ ^ 2 / 2| ≤ w ^ 2 + 4 * K * ‖θ‖ ^ 3 := by
    have hMw : M = 1 + w := by rw [hw]; ring
    have h1 := abs_log_one_add_sub_le w hwnn
    rw [hMw]
    calc |Real.log (1 + w) - ‖θ‖ ^ 2 / 2|
        ≤ |Real.log (1 + w) - w| + |w - ‖θ‖ ^ 2 / 2| := by
          have hsum : (Real.log (1 + w) - w) + (w - ‖θ‖ ^ 2 / 2)
              = Real.log (1 + w) - ‖θ‖ ^ 2 / 2 := by ring
          rw [← hsum]
          exact abs_add_le _ _
      _ ≤ w ^ 2 + 4 * K * ‖θ‖ ^ 3 := add_le_add h1 hwbd
  have hwle : w ≤ (1 / 2 + 4 * K * r) * ‖θ‖ ^ 2 := by
    have h1 : w ≤ ‖θ‖ ^ 2 / 2 + 4 * K * ‖θ‖ ^ 3 := by
      have := (abs_le.mp hwbd).2; linarith
    have h2 : 4 * K * ‖θ‖ ^ 3 ≤ 4 * K * r * ‖θ‖ ^ 2 := by
      have : ‖θ‖ ^ 3 = ‖θ‖ ^ 2 * ‖θ‖ := by ring
      rw [this]
      have hkk : (0 : ℝ) ≤ 4 * K * ‖θ‖ ^ 2 := by positivity
      nlinarith [sq_nonneg ‖θ‖]
    linarith
  have hwsq : w ^ 2 ≤ r * (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 := by
    have hc : (0 : ℝ) ≤ 1 / 2 + 4 * K * r := by positivity
    have h1 : w ^ 2 ≤ ((1 / 2 + 4 * K * r) * ‖θ‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ hwnn hwle 2
    have h2 : ((1 / 2 + 4 * K * r) * ‖θ‖ ^ 2) ^ 2
        = (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * ‖θ‖ := by ring
    have h3 : (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * ‖θ‖
        ≤ (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * r := by
      have hnn : (0 : ℝ) ≤ (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 := by positivity
      exact mul_le_mul_of_nonneg_left hθ hnn
    calc w ^ 2 ≤ ((1 / 2 + 4 * K * r) * ‖θ‖ ^ 2) ^ 2 := h1
      _ = (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * ‖θ‖ := h2
      _ ≤ (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 * r := h3
      _ = r * (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 := by ring
  calc |Real.log M - ‖θ‖ ^ 2 / 2| ≤ w ^ 2 + 4 * K * ‖θ‖ ^ 3 := hlog
    _ ≤ r * (1 / 2 + 4 * K * r) ^ 2 * ‖θ‖ ^ 3 + 4 * K * ‖θ‖ ^ 3 := by linarith
    _ = (4 * K + r * (1 / 2 + 4 * K * r) ^ 2) * ‖θ‖ ^ 3 := by ring


/-! ### The canonical experiment -/

/-- `N(0, Iₖ)` is the standard Gaussian of `EuclideanSpace`. -/
private lemma mvGaussian_zero_one_eq_stdGaussian {k : ℕ} :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (1 : Matrix (Fin k) (Fin k) ℝ)
      = stdGaussian (EuclideanSpace ℝ (Fin k)) := by
  rw [multivariateGaussian]
  simp only [CFC.sqrt_one, map_one, ContinuousLinearMap.one_apply, zero_add]
  exact Measure.map_id

/-- The stage-`n` law of the score vector is the standardised product law. -/
private lemma law_scoreVec_pi {n k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {X : Fin n → Ω → 𝓧}
    (hψmeas : ∀ j, Measurable (ψ j)) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = P₀) :
    P.map (scoreVec ψ X)
      = (Measure.pi fun _ : Fin n => P₀).map
          (fun d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i)) := by
  classical
  have hgmeas : Measurable (psiVec ψ) :=
    (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp (measurable_pi_lambda _ hψmeas)
  set F : (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k) :=
    fun d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i) with hF
  have hFmeas : Measurable F :=
    measurable_const.smul
      (Finset.univ.measurable_sum fun i _ => hgmeas.comp (measurable_pi_apply i))
  have hXmeas : Measurable (fun ω (i : Fin n) => X i ω) := measurable_pi_lambda _ hX
  have hpiX : P.map (fun ω (i : Fin n) => X i ω) = Measure.pi (fun _ : Fin n => P₀) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).1 hindep]
    congr 1; funext i; exact hlaw i
  have hcomp : scoreVec ψ X = F ∘ (fun ω (i : Fin n) => X i ω) := by
    funext ω
    rw [scoreVec_eq_smul_sum ψ X ω]
    rfl
  rw [hcomp, ← Measure.map_map hFmeas hXmeas, hpiX]

/-- **The canonical score law converges to the standard Gaussian.** -/
private lemma pi_scoreLaw_weakConverges {k : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {ψ : Fin k → 𝓧 → ℝ} (hψmeas : ∀ j, Measurable (ψ j))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0) :
    WeakConverges (fun n => (Measure.pi fun _ : Fin n => P₀).map
        (fun d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i)))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  classical
  obtain ⟨Ω₀, mΩ₀, P₀c, Z, hZmeas, hZlaw, hZindep, hP₀cprob⟩ :=
    ProbabilityTheory.exists_iid ℕ P₀
  letI : MeasurableSpace Ω₀ := mΩ₀
  haveI : IsProbabilityMeasure P₀c := hP₀cprob
  have hbrick := scoreVec_weakConverges_gaussian (P₀ := P₀) (ψ := ψ)
    (P := fun _ : ℕ => P₀c) (X := fun n (i : Fin n) ω => Z (i : ℕ) ω)
    hψmeas hortho hcentred
    (fun n i => hZmeas i) (fun n => hZindep.precomp Fin.val_injective)
    (fun n i => (hZlaw (i : ℕ)).map_eq)
  have heq : ∀ n : ℕ, P₀c.map (scoreVec ψ (fun (i : Fin n) ω => Z (i : ℕ) ω))
      = (Measure.pi fun _ : Fin n => P₀).map
          (fun d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i)) :=
    fun n => law_scoreVec_pi hψmeas (fun i => hZmeas i)
      (hZindep.precomp Fin.val_injective) (fun i => (hZlaw (i : ℕ)).map_eq)
  simp only [heq] at hbrick
  rwa [mvGaussian_zero_one_eq_stdGaussian] at hbrick


/-! ### The smooth model as an explicit exponential tilt -/

private lemma smoothModel_base {k : ℕ} (P₀ : Measure 𝓧) (ψ : Fin k → 𝓧 → ℝ)
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k))) :
    (smoothModel P₀ ψ hψ).base = P₀ := by
  show P₀.withDensity (fun _ => 1) = P₀
  simp

private lemma smoothModel_P_eq {k : ℕ} (P₀ : Measure 𝓧) (ψ : Fin k → 𝓧 → ℝ)
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k)))
    (θ : EuclideanSpace ℝ (Fin k)) :
    (smoothModel P₀ ψ hψ).P θ = P₀.tilted (fun x => ⟪θ, psiVec ψ x⟫_ℝ) := by
  have h : (smoothModel P₀ ψ hψ).P θ
      = ((smoothModel P₀ ψ hψ).base).tilted (fun x => ⟪θ, psiVec ψ x⟫_ℝ) := rfl
  rw [h, smoothModel_base]

/-- A tilt that is a probability measure has an integrable exponential. -/
private lemma integrable_exp_of_isProbabilityMeasure_tilted {P₀ : Measure 𝓧} {f : 𝓧 → ℝ}
    (h : IsProbabilityMeasure (P₀.tilted f)) :
    Integrable (fun x => Real.exp (f x)) P₀ := by
  by_contra hcon
  rw [tilted_of_not_integrable hcon] at h
  have h1 : (0 : Measure 𝓧) Set.univ = 1 := h.measure_univ
  simp only [Measure.coe_zero, Pi.zero_apply] at h1
  exact zero_ne_one h1

/-- The tilt written with the log-partition normalisation. -/
private lemma tilted_eq_withDensity_log (μ : Measure 𝓧) (f : 𝓧 → ℝ)
    (hpos : 0 < ∫ x, Real.exp (f x) ∂μ) :
    μ.tilted f = μ.withDensity (fun x =>
      ENNReal.ofReal (Real.exp (f x - Real.log (∫ y, Real.exp (f y) ∂μ)))) := by
  rw [Measure.tilted]
  congr 1
  funext x
  rw [Real.exp_sub, Real.exp_log hpos]

/-- The `n`-fold product of an exponential tilt is the tilt of the product by the sum. -/
private lemma pi_withDensity_exp {n : ℕ} {P₀ : Measure 𝓧} [IsProbabilityMeasure P₀]
    {u : 𝓧 → ℝ} (hu : Measurable u)
    [hprob : IsProbabilityMeasure
      (P₀.withDensity (fun x => ENNReal.ofReal (Real.exp (u x))))] :
    Measure.pi (fun _ : Fin n => P₀.withDensity (fun x => ENNReal.ofReal (Real.exp (u x))))
      = (Measure.pi fun _ : Fin n => P₀).withDensity
          (fun d => ENNReal.ofReal (Real.exp (∑ i, u (d i)))) := by
  classical
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (u x))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp hu)
  have hprod : (fun d : Fin n → 𝓧 => ENNReal.ofReal (Real.exp (∑ i, u (d i))))
      = fun d => ∏ i, ENNReal.ofReal (Real.exp (u (d i))) := by
    funext d
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _)]
  rw [hprod, pi_withDensity_prod (μ := fun _ : Fin n => P₀)
    (f := fun _ : Fin n => fun x => ENNReal.ofReal (Real.exp (u x))) (fun _ => hmeas)]


/-! ### The upper bound -/

theorem smoothTest_maximin_upper_bound' {k : ℕ} {α b B c : ℝ} {P₀ : Measure 𝓧}
    [IsProbabilityMeasure P₀] {ψ : Fin k → 𝓧 → ℝ}
    {Q : ℕ → EuclideanSpace ℝ (Fin k) → Measure Ω} [∀ n h, IsProbabilityMeasure (Q n h)]
    {X : (n : ℕ) → Fin n → Ω → 𝓧} {φ : ℕ → Ω → ℝ}
    (hk : 0 < k) (hb : 0 < b) (hbB : b < B) (hα : 0 < α) (hα1 : α < 1)
    (hc : chiSquared k (Set.Ioi c) = ENNReal.ofReal α)
    (hψ : Measurable fun x => (WithLp.toLp 2 fun j => ψ j x : EuclideanSpace ℝ (Fin k)))
    (hortho : ∀ i j, (∫ x, ψ i x * ψ j x ∂P₀) = if i = j then 1 else 0)
    (hcentred : ∀ j, (∫ x, ψ j x ∂P₀) = 0)
    (hX : ∀ n, ∀ i, Measurable (X n i))
    (hindep : ∀ n h, iIndepFun (X n) (Q n h))
    (hlaw : ∀ n h, ∀ i, (Q n h).map (X n i)
      = (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h))
    (hφ : ∀ n, IsCriticalFn (φ n))
    (hφX : ∀ n, ∃ ρ : (Fin n → 𝓧) → ℝ,
      Measurable ρ ∧ ∀ ω, φ n ω = ρ (fun i => X n i ω))
    (hlevel : Tendsto (fun n => power (Q n) (φ n) 0) atTop (nhds α)) :
    limsup (fun n => sInf ((fun h => power (Q n) (φ n) h) ''
        {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B})) atTop
      ≤ ((noncentralChiSquared k (b ^ 2).toNNReal) (Set.Ioi c)).toReal := by
  classical
  have hψmeas : ∀ j, Measurable (ψ j) := fun j =>
    ((measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin k → ℝ))).comp hψ
  have hgmeas : Measurable (psiVec ψ) :=
    (WithLp.measurable_toLp 2 (Fin k → ℝ)).comp (measurable_pi_lambda _ hψmeas)
  -- ### The log-partition function
  set A : EuclideanSpace ℝ (Fin k) → ℝ :=
    fun θ => Real.log (∫ x, Real.exp ⟪θ, psiVec ψ x⟫_ℝ ∂P₀) with hAdef
  -- every member of the smooth family is a probability measure, hence every tilt is
  -- integrable: the natural parameter set is all of the space
  have hEprob : ∀ θ : EuclideanSpace ℝ (Fin k),
      IsProbabilityMeasure ((smoothModel P₀ ψ hψ).P θ) := by
    intro θ
    have h1 := hlaw 1 θ (0 : Fin 1)
    have hs : (Real.sqrt ((1 : ℕ) : ℝ))⁻¹ • θ = θ := by
      norm_num
    rw [hs] at h1
    rw [← h1]
    exact Measure.isProbabilityMeasure_map (hX 1 (0 : Fin 1)).aemeasurable
  haveI hEprobI : ∀ θ, IsProbabilityMeasure ((smoothModel P₀ ψ hψ).P θ) := hEprob
  have hEint : ∀ θ, Integrable (fun x => Real.exp ⟪θ, psiVec ψ x⟫_ℝ) P₀ := by
    intro θ
    refine integrable_exp_of_isProbabilityMeasure_tilted (P₀ := P₀) ?_
    rw [← smoothModel_P_eq P₀ ψ hψ θ]
    exact hEprob θ
  have hMpos : ∀ θ, 0 < ∫ x, Real.exp ⟪θ, psiVec ψ x⟫_ℝ ∂P₀ :=
    fun θ => integral_exp_pos (hEint θ)
  -- the explicit density of each member with respect to `P₀`
  have hEdens : ∀ θ, (smoothModel P₀ ψ hψ).P θ
      = P₀.withDensity (fun x => ENNReal.ofReal (Real.exp (⟪θ, psiVec ψ x⟫_ℝ - A θ))) := by
    intro θ
    rw [smoothModel_P_eq P₀ ψ hψ θ]
    exact tilted_eq_withDensity_log P₀ _ (hMpos θ)
  have hEP0 : (smoothModel P₀ ψ hψ).P 0 = P₀ := by
    rw [smoothModel_P_eq]
    have hz : (fun x => ⟪(0 : EuclideanSpace ℝ (Fin k)), psiVec ψ x⟫_ℝ) = fun _ => (0 : ℝ) := by
      funext x; simp
    rw [hz, tilted_const]
  -- measurability of the log-partition function
  have hAmeas : Measurable A := by
    have hjoint : Measurable
        (fun p : EuclideanSpace ℝ (Fin k) × 𝓧 => Real.exp ⟪p.1, psiVec ψ p.2⟫_ℝ) := by
      refine Real.continuous_exp.measurable.comp ?_
      exact (continuous_inner.measurable).comp
        (measurable_fst.prodMk (hgmeas.comp measurable_snd))
    have := (hjoint.stronglyMeasurable).integral_prod_right' (ν := P₀)
    exact Real.measurable_log.comp this.measurable
  -- ### The quadratic expansion, on the ball of radius `b`
  obtain ⟨Cst, hCst0, hCstbd⟩ :=
    logPartition_quadratic_bound (P₀ := P₀) hψmeas hortho hcentred hEint hb
  -- ### The canonical experiment
  choose ρ0 hρ0meas hρ0val using hφX
  set ρ : (n : ℕ) → (Fin n → 𝓧) → ℝ := fun n d => min 1 (max 0 (ρ0 n d)) with hρdef
  have hρmeas : ∀ n, Measurable (ρ n) := fun n =>
    measurable_const.min (measurable_const.max (hρ0meas n))
  have hρcrit : ∀ n, IsCriticalFn (ρ n) := by
    intro n
    refine ⟨hρmeas n, fun d => ⟨?_, ?_⟩⟩
    · exact le_min zero_le_one (le_max_left _ _)
    · exact min_le_left _ _
  have hρval : ∀ n ω, φ n ω = ρ n (fun i => X n i ω) := by
    intro n ω
    obtain ⟨h0, h1⟩ := (hφ n).2 ω
    rw [hρdef]
    simp only
    rw [← hρ0val n ω, max_eq_right h0, min_eq_right h1]
  set QC : (n : ℕ) → EuclideanSpace ℝ (Fin k) → Measure (Fin n → 𝓧) :=
    fun n h => Measure.pi (fun _ : Fin n =>
      (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h)) with hQCdef
  haveI : ∀ n h, IsProbabilityMeasure (QC n h) := by
    intro n h
    rw [hQCdef]
    infer_instance
  have hQC0 : ∀ n : ℕ, QC n 0 = Measure.pi (fun _ : Fin n => P₀) := by
    intro n
    rw [hQCdef]
    simp only [smul_zero, hEP0]
  -- the sample map transports the power function
  have hsample : ∀ n h, (Q n h).map (fun ω (i : Fin n) => X n i ω) = QC n h := by
    intro n h
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX n i).aemeasurable)).1 (hindep n h),
      hQCdef]
    congr 1
    funext i
    exact hlaw n h i
  have hpower : ∀ n h, power (Q n) (φ n) h = power (QC n) (ρ n) h := by
    intro n h
    simp only [power]
    rw [show (∫ ω, φ n ω ∂(Q n h)) = ∫ ω, ρ n (fun i => X n i ω) ∂(Q n h) from
      integral_congr_ae (Filter.Eventually.of_forall (fun ω => hρval n ω))]
    rw [← hsample n h,
      integral_map (measurable_pi_lambda _ (fun i => hX n i)).aemeasurable
        (hρmeas n).aestronglyMeasurable]
  have hQCval : ∀ n h, QC n h = Measure.pi (fun _ : Fin n =>
      (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h)) := fun n h => rfl
  -- ### The centring statistics and the log-likelihood field
  set ZC : (n : ℕ) → (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k) :=
    fun n d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i) with hZCdef
  have hZCval : ∀ n (d : Fin n → 𝓧),
      ZC n d = (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i) := fun n d => rfl
  have hZCmeas : ∀ n, Measurable (ZC n) := fun n =>
    measurable_const.smul (Finset.univ.measurable_sum
      fun i _ => hgmeas.comp (measurable_pi_apply i))
  have hZ : WeakConverges (fun n => (QC n 0).map (ZC n))
      (stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    have hbrick := pi_scoreLaw_weakConverges (P₀ := P₀) hψmeas hortho hcentred
    have heq : ∀ n : ℕ, (QC n 0).map (ZC n)
        = (Measure.pi fun _ : Fin n => P₀).map
            (fun d => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, psiVec ψ (d i)) := by
      intro n; rw [hQC0 n]
    simp only [heq]
    exact hbrick
  set LC : (n : ℕ) → EuclideanSpace ℝ (Fin k) → (Fin n → 𝓧) → ℝ :=
    fun n h d => ∑ i, (⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ
      - A ((Real.sqrt (n : ℝ))⁻¹ • h)) with hLCdef
  have hLCval : ∀ n h (d : Fin n → 𝓧), LC n h d
      = ∑ i, (⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ
        - A ((Real.sqrt (n : ℝ))⁻¹ • h)) := fun n h d => rfl
  have hsmulmeas : ∀ n : ℕ, Measurable
      (fun h : EuclideanSpace ℝ (Fin k) => (Real.sqrt (n : ℝ))⁻¹ • h) :=
    fun n => (continuous_const_smul ((Real.sqrt (n : ℝ))⁻¹)).measurable
  have hLCmeas : ∀ n, Measurable
      fun p : EuclideanSpace ℝ (Fin k) × (Fin n → 𝓧) => LC n p.1 p.2 := by
    intro n
    simp only [hLCval]
    refine Finset.univ.measurable_sum fun i _ => Measurable.sub ?_ ?_
    · exact continuous_inner.measurable.comp
        (((hsmulmeas n).comp measurable_fst).prodMk
          (hgmeas.comp ((measurable_pi_apply i).comp measurable_snd)))
    · exact (hAmeas.comp (hsmulmeas n)).comp measurable_fst
  -- ### The (deterministic) LAN envelope
  set DC : (n : ℕ) → (Fin n → 𝓧) → ℝ :=
    fun n _ => if n = 0 then b ^ 2 else Cst * b ^ 3 / Real.sqrt (n : ℝ) with hDCdef
  have hDCval : ∀ n (d : Fin n → 𝓧),
      DC n d = if n = 0 then b ^ 2 else Cst * b ^ 3 / Real.sqrt (n : ℝ) := fun n d => rfl
  have hLAN : ∀ n h (d : Fin n → 𝓧), ‖h‖ = b →
      |LC n h d - (⟪h, ZC n d⟫_ℝ - b ^ 2 / 2)| ≤ DC n d := by
    intro n h d hh
    have hinner : ⟪h, ZC n d⟫_ℝ
        = ∑ i, ⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ := by
      rw [hZCval n d, real_inner_smul_right, inner_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (real_inner_smul_left _ _ _).symm
    have hL : LC n h d
        = (∑ i, ⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ)
          - (n : ℝ) * A ((Real.sqrt (n : ℝ))⁻¹ • h) := by
      rw [hLCval n h d, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hL, hinner, hDCval n d]
    have hgoal : (∑ i, ⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ)
          - (n : ℝ) * A ((Real.sqrt (n : ℝ))⁻¹ • h)
          - ((∑ i, ⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ (d i)⟫_ℝ) - b ^ 2 / 2)
        = -((n : ℝ) * A ((Real.sqrt (n : ℝ))⁻¹ • h) - b ^ 2 / 2) := by ring
    rw [hgoal, abs_neg]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, zero_mul, zero_sub, abs_neg, if_true]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ b ^ 2 / 2)]
      nlinarith [sq_nonneg b]
    · rw [if_neg hn.ne']
      have hCstbd' : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ‖ ≤ b →
          |A θ - ‖θ‖ ^ 2 / 2| ≤ Cst * ‖θ‖ ^ 3 := hCstbd
      set t : ℝ := Real.sqrt (n : ℝ) with htdef
      have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have htpos : 0 < t := by rw [htdef]; exact Real.sqrt_pos.mpr hnn
      have ht2 : t ^ 2 = (n : ℝ) := by rw [htdef]; exact Real.sq_sqrt hnn.le
      have ht1 : (1 : ℝ) ≤ t := by
        rw [htdef, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
      have hnorm : ‖t⁻¹ • h‖ = t⁻¹ * b := by
        rw [norm_smul, hh, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hinvle : t⁻¹ ≤ 1 := by
        rw [inv_le_one₀ htpos]; exact ht1
      have hle : t⁻¹ * b ≤ b := by nlinarith
      have h1 := hCstbd' (t⁻¹ • h) (by rw [hnorm]; exact hle)
      rw [hnorm] at h1
      have hq : (n : ℝ) * ((t⁻¹ * b) ^ 2 / 2) = b ^ 2 / 2 := by
        rw [← ht2]; field_simp
      calc |(n : ℝ) * A (t⁻¹ • h) - b ^ 2 / 2|
          = (n : ℝ) * |A (t⁻¹ • h) - (t⁻¹ * b) ^ 2 / 2| := by
            rw [← hq, ← mul_sub, abs_mul, abs_of_nonneg hnn.le]
        _ ≤ (n : ℝ) * (Cst * (t⁻¹ * b) ^ 3) := mul_le_mul_of_nonneg_left h1 hnn.le
        _ = Cst * b ^ 3 / t := by rw [← ht2]; field_simp
  -- ### The envelope is `o_P(1)`
  have hD0 : ∀ ε > 0, Tendsto (fun n => ((QC n 0) {d | ε ≤ DC n d}).toReal) atTop (nhds 0) := by
    intro ε hε
    have htend : Tendsto (fun n : ℕ => Cst * b ^ 3 / Real.sqrt (n : ℝ)) atTop (nhds 0) := by
      refine Filter.Tendsto.div_atTop tendsto_const_nhds ?_
      exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hsmall : ∀ᶠ n : ℕ in atTop, Cst * b ^ 3 / Real.sqrt (n : ℝ) < ε :=
      htend.eventually (gt_mem_nhds hε)
    have hev : ∀ᶠ n : ℕ in atTop, ((QC n 0) {d | ε ≤ DC n d}).toReal = 0 := by
      filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hn0
      have hset : {d : Fin n → 𝓧 | ε ≤ DC n d} = (∅ : Set (Fin n → 𝓧)) := by
        ext d
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le, hDCval,
          if_neg hn0.ne']
        exact hn
      rw [hset]
      simp
    have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
    refine Filter.Tendsto.congr' ?_ hconst
    filter_upwards [hev] with n hn
    exact hn.symm
  -- ### The likelihood-ratio representation
  have hdens : ∀ n h, QC n h
      = (QC n 0).withDensity (fun d => ENNReal.ofReal (Real.exp (LC n h d))) := by
    intro n h
    simp only [hLCval]
    rw [hQCval n h, hQC0 n]
    have hu : Measurable (fun x => ⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ x⟫_ℝ
        - A ((Real.sqrt (n : ℝ))⁻¹ • h)) :=
      ((continuous_const.inner continuous_id).measurable.comp hgmeas).sub measurable_const
    haveI hpm : IsProbabilityMeasure (P₀.withDensity (fun x => ENNReal.ofReal
        (Real.exp (⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ x⟫_ℝ
          - A ((Real.sqrt (n : ℝ))⁻¹ • h))))) := by
      rw [← hEdens ((Real.sqrt (n : ℝ))⁻¹ • h)]
      exact hEprob _
    rw [show (fun _ : Fin n => (smoothModel P₀ ψ hψ).P ((Real.sqrt (n : ℝ))⁻¹ • h))
        = (fun _ : Fin n => P₀.withDensity (fun x => ENNReal.ofReal
            (Real.exp (⟪(Real.sqrt (n : ℝ))⁻¹ • h, psiVec ψ x⟫_ℝ
              - A ((Real.sqrt (n : ℝ))⁻¹ • h))))) from funext fun _ => hEdens _,
      pi_withDensity_exp (n := n) (P₀ := P₀) hu]
  -- ### Assembly
  have hlevel' : Tendsto (fun n => power (QC n) (ρ n) 0) atTop (nhds α) :=
    hlevel.congr fun n => hpower n 0
  have hS : ∀ᶠ n : ℕ in atTop, {h : EuclideanSpace ℝ (Fin k) | ‖h‖ = b} ⊆
      {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B} :=
    Filter.Eventually.of_forall fun _ h hh => ⟨le_of_eq hh.symm, by rw [hh]; exact hbB.le⟩
  have hmain := asymptotic_maximin_upper_bound (Ω := fun n => (Fin n → 𝓧)) (Q := QC)
    (φ := ρ) (Z := ZC) (L := LC) (D := DC)
    (S := fun _ : ℕ => {h : EuclideanSpace ℝ (Fin k) | b ≤ ‖h‖ ∧ ‖h‖ ≤ B})
    hk hb hα hα1 hc hρcrit hlevel' hZCmeas hZ hLCmeas hdens hLAN hD0 hS
  have hfun : ∀ n, (fun h => power (Q n) (φ n) h) = fun h => power (QC n) (ρ n) h :=
    fun n => funext (hpower n)
  simp only [hfun]
  exact hmain



#print axioms smoothTest_maximin_upper_bound'

end StatLean.HypothesisTesting
