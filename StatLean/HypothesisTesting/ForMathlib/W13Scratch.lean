import StatLean.HypothesisTesting.ForMathlib.MultivariateBerryEsseen

/-!
# Scratch development for wave-13 BENT (to be merged into `MultivariateBerryEsseen`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators InnerProductSpace Real

namespace StatLean.HypothesisTesting

section GaussianTilt

/-- Third-order Taylor bound for the real exponential, valid on **all** of `ℝ`
(Mathlib's `Real.exp_bound` needs `|x| ≤ 1`). The constant is `1/2` rather than the sharp
`1/6` because the remainder integral is bounded by its sup times the length of the
interval. -/
private lemma abs_exp_sub_taylor_two_le (x : ℝ) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 * Real.exp |x| / 2 := by
  set G : ℝ → ℝ := fun u => ((x - u) ^ 2 / 2 + (x - u) + 1) * Real.exp u with hG
  have hderiv : ∀ u : ℝ, HasDerivAt G ((x - u) ^ 2 / 2 * Real.exp u) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => (x - u) ^ 2 / 2 + (x - u) + 1)
        (-(x - u) - 1) u := by
      have hsub : HasDerivAt (fun u : ℝ => x - u) (-1) u := by
        simpa using (hasDerivAt_id u).const_sub x
      have hsq : HasDerivAt (fun u : ℝ => (x - u) ^ 2) (2 * (x - u) * (-1)) u := by
        simpa using hsub.pow 2
      have := ((hsq.div_const 2).add hsub).add_const (1 : ℝ)
      convert this using 1
      ring
    have h2 : HasDerivAt (fun u : ℝ => Real.exp u) (Real.exp u) u := Real.hasDerivAt_exp u
    have := h1.mul h2
    convert this using 1
    ring
  have hint : ∫ u in (0 : ℝ)..x, (x - u) ^ 2 / 2 * Real.exp u = G x - G 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hGx : G x = Real.exp x := by simp [hG]
  have hG0 : G 0 = 1 + x + x ^ 2 / 2 := by simp [hG]; ring
  have hbound : ∀ u ∈ Set.uIoc (0 : ℝ) x,
      ‖(x - u) ^ 2 / 2 * Real.exp u‖ ≤ x ^ 2 / 2 * Real.exp |x| := by
    intro u hu
    have hu' : |u| ≤ |x| := by
      rcases le_total (0 : ℝ) x with hx | hx
      · rw [Set.uIoc_of_le hx] at hu
        rw [abs_of_nonneg hu.1.le, abs_of_nonneg hx]
        exact hu.2
      · rw [Set.uIoc_of_ge hx] at hu
        rw [abs_of_nonpos hu.2, abs_of_nonpos hx]
        linarith [hu.1]
    have hxu : |x - u| ≤ |x| := by
      rcases le_total (0 : ℝ) x with hx | hx
      · rw [Set.uIoc_of_le hx] at hu
        rw [abs_of_nonneg (by linarith [hu.2] : (0:ℝ) ≤ x - u), abs_of_nonneg hx]
        linarith [hu.1]
      · rw [Set.uIoc_of_ge hx] at hu
        rw [abs_of_nonpos (by linarith [hu.1] : x - u ≤ 0), abs_of_nonpos hx]
        linarith [hu.2]
    have hsq : (x - u) ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs (x - u), ← sq_abs x]
      exact pow_le_pow_left₀ (abs_nonneg _) hxu 2
    have hexp : Real.exp u ≤ Real.exp |x| := Real.exp_le_exp.2 (le_trans (le_abs_self u) hu')
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (x - u) ^ 2 / 2),
      abs_of_pos (Real.exp_pos u)]
    exact mul_le_mul (by linarith) hexp (Real.exp_pos u).le (by positivity)
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hint, hGx, hG0, Real.norm_eq_abs] at hle
  refine hle.trans ?_
  have hz : |x - 0| = |x| := by ring_nf
  rw [hz, show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
  nlinarith [abs_nonneg x, Real.exp_pos |x|]

/-! ### Elementary envelopes -/

/-- `y ≤ exp y`. -/
private lemma self_le_exp (y : ℝ) : y ≤ Real.exp y := by
  have := Real.add_one_le_exp y
  linarith

/-- `|t| ≤ exp t + exp (-t)`. -/
private lemma abs_le_exp_add_exp (t : ℝ) : |t| ≤ Real.exp t + Real.exp (-t) := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith [self_le_exp t, Real.exp_pos (-t)]
  · rw [h]; linarith [self_le_exp (-t), Real.exp_pos t]

/-- `exp |t| ≤ exp t + exp (-t)`. -/
private lemma exp_abs_le_exp_add_exp (t : ℝ) :
    Real.exp |t| ≤ Real.exp t + Real.exp (-t) := by
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith [Real.exp_pos (-t)]
  · rw [h]; linarith [Real.exp_pos t]

/-- `t² ≤ 4 (exp t + exp (-t))`. -/
private lemma sq_le_exp_add_exp (t : ℝ) : t ^ 2 ≤ 4 * (Real.exp t + Real.exp (-t)) := by
  have hkey : ∀ y : ℝ, 0 ≤ y → y ^ 2 ≤ 4 * Real.exp y := by
    intro y hy
    have h1 : y / 2 + 1 ≤ Real.exp (y / 2) := Real.add_one_le_exp _
    have h2 : (0 : ℝ) ≤ y / 2 + 1 := by linarith
    have h3 : (y / 2 + 1) ^ 2 ≤ Real.exp (y / 2) ^ 2 := pow_le_pow_left₀ h2 h1 2
    have h4 : Real.exp (y / 2) ^ 2 = Real.exp y := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    nlinarith
  have habs : |t| ^ 2 ≤ 4 * Real.exp |t| := hkey _ (abs_nonneg t)
  have hex := exp_abs_le_exp_add_exp t
  nlinarith [sq_abs t]

/-- `y³ ≤ 27 exp y` for `y ≥ 0`. -/
private lemma cube_le_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 3 ≤ 27 * Real.exp y := by
  have h1 : y / 3 + 1 ≤ Real.exp (y / 3) := Real.add_one_le_exp _
  have h2 : (0 : ℝ) ≤ y / 3 + 1 := by linarith
  have h3 : (y / 3 + 1) ^ 3 ≤ Real.exp (y / 3) ^ 3 := pow_le_pow_left₀ h2 h1 3
  have h4 : Real.exp (y / 3) ^ 3 = Real.exp y := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  nlinarith

/-! ### Gaussian moments used by the tilt bound -/

private lemma integrable_exp_mul_gauss (a : ℝ) :
    Integrable (fun t : ℝ => Real.exp (a * t)) (gaussianReal 0 1) :=
  integrable_exp_mul_gaussianReal a

private lemma integral_exp_mul_gauss (a : ℝ) :
    (∫ t, Real.exp (a * t) ∂(gaussianReal 0 1)) = Real.exp (a ^ 2 / 2) := by
  rw [integral_exp_mul_gaussianReal 0 1 a]
  norm_num

private lemma exp_neg_mul_eq (a : ℝ) :
    (fun t : ℝ => Real.exp (-a * t)) = fun t : ℝ => Real.exp (-(a * t)) := by
  funext t; congr 1; ring

private lemma integrable_cosh (a : ℝ) :
    Integrable (fun t : ℝ => Real.exp (a * t) + Real.exp (-(a * t))) (gaussianReal 0 1) := by
  have h2 := integrable_exp_mul_gauss (-a)
  rw [exp_neg_mul_eq a] at h2
  exact (integrable_exp_mul_gauss a).add h2

private lemma integral_cosh (a : ℝ) :
    (∫ t, (Real.exp (a * t) + Real.exp (-(a * t))) ∂(gaussianReal 0 1))
      = 2 * Real.exp (a ^ 2 / 2) := by
  have h2 := integrable_exp_mul_gauss (-a)
  rw [exp_neg_mul_eq a] at h2
  rw [integral_add (integrable_exp_mul_gauss a) h2, ← exp_neg_mul_eq a,
    integral_exp_mul_gauss a, integral_exp_mul_gauss (-a), show (-a) ^ 2 = a ^ 2 by ring]
  ring

private lemma integrable_cosh_one :
    Integrable (fun t : ℝ => Real.exp t + Real.exp (-t)) (gaussianReal 0 1) := by
  have h := integrable_cosh 1
  simp only [one_mul] at h
  exact h

private lemma integral_cosh_one :
    (∫ t, (Real.exp t + Real.exp (-t)) ∂(gaussianReal 0 1)) = 2 * Real.exp (1 / 2) := by
  have h := integral_cosh 1
  simp only [one_mul] at h
  rw [h]
  norm_num

private lemma integral_cosh_two :
    (∫ t, (Real.exp (2 * t) + Real.exp (-(2 * t))) ∂(gaussianReal 0 1)) = 2 * Real.exp 2 := by
  rw [integral_cosh 2]
  norm_num

private lemma integrable_id_gauss : Integrable (fun t : ℝ => t) (gaussianReal 0 1) := by
  refine Integrable.mono' integrable_cosh_one (by fun_prop) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs]
  exact abs_le_exp_add_exp t

private lemma integrable_sq_gauss : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_cosh_one.const_mul 4) (by fun_prop) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
  exact sq_le_exp_add_exp t

/-! ### The scalar tilt remainder -/

/-- The **scalar tilt remainder**: the error in the second-order expansion, in the tilt
parameter `s`, of the Cameron–Martin density `exp (s t − s²/2)` of the standard Gaussian
shifted by `s`. Its first three coefficients are the Hermite polynomials `1`, `t`, `t² − 1`. -/
private noncomputable def tiltRemainder (s t : ℝ) : ℝ :=
  Real.exp (s * t - s ^ 2 / 2) - (1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2)

private lemma integrable_exp_tilt (s : ℝ) :
    Integrable (fun t : ℝ => Real.exp (s * t - s ^ 2 / 2)) (gaussianReal 0 1) := by
  have hre : (fun t : ℝ => Real.exp (s * t - s ^ 2 / 2))
      = fun t : ℝ => Real.exp (-(s ^ 2 / 2)) * Real.exp (s * t) := by
    funext t; rw [← Real.exp_add]; congr 1; ring
  rw [hre]
  exact (integrable_exp_mul_gauss s).const_mul _

private lemma integral_exp_tilt (s : ℝ) :
    (∫ t, Real.exp (s * t - s ^ 2 / 2) ∂(gaussianReal 0 1)) = 1 := by
  have hre : (fun t : ℝ => Real.exp (s * t - s ^ 2 / 2))
      = fun t : ℝ => Real.exp (-(s ^ 2 / 2)) * Real.exp (s * t) := by
    funext t; rw [← Real.exp_add]; congr 1; ring
  rw [hre, integral_const_mul, integral_exp_mul_gauss s, ← Real.exp_add]
  norm_num

private lemma integrable_tiltRemainder (s : ℝ) :
    Integrable (fun t => tiltRemainder s t) (gaussianReal 0 1) :=
  (integrable_exp_tilt s).sub
    (((integrable_const (1 : ℝ)).add (integrable_id_gauss.const_mul s)).add
      (((integrable_sq_gauss.sub (integrable_const (1 : ℝ))).const_mul (s ^ 2)).div_const 2))

/-- The (parameter-free) envelope controlling the tilt remainder for small tilts. -/
private noncomputable def tiltEnvSmall (t : ℝ) : ℝ :=
  27 / 2 * Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t)))
    + ((Real.exp t + Real.exp (-t)) / 2 + 1 / 8)

private lemma integrable_tiltEnvSmall : Integrable tiltEnvSmall (gaussianReal 0 1) :=
  ((integrable_cosh 2).const_mul _).add
    ((integrable_cosh_one.div_const 2).add (integrable_const _))

private lemma integral_tiltEnvSmall_le :
    (∫ t, tiltEnvSmall t ∂(gaussianReal 0 1)) ≤ 30 * Real.exp 3 + 3 := by
  have hA : Integrable (fun t : ℝ =>
      27 / 2 * Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t)))) (gaussianReal 0 1) :=
    (integrable_cosh 2).const_mul _
  have hB : Integrable (fun t : ℝ => (Real.exp t + Real.exp (-t)) / 2) (gaussianReal 0 1) :=
    integrable_cosh_one.div_const 2
  have hC : Integrable (fun _ : ℝ => (1 / 8 : ℝ)) (gaussianReal 0 1) := integrable_const _
  have hBC : Integrable (fun t : ℝ => (Real.exp t + Real.exp (-t)) / 2 + 1 / 8)
      (gaussianReal 0 1) := hB.add hC
  have hval : (∫ t, tiltEnvSmall t ∂(gaussianReal 0 1))
      = 27 / 2 * Real.exp 1 * (2 * Real.exp 2) + ((2 * Real.exp (1 / 2)) / 2 + 1 / 8) := by
    simp only [tiltEnvSmall]
    rw [integral_add hA hBC, integral_add hB hC, integral_const_mul, integral_div,
      integral_cosh_two, integral_cosh_one, integral_const]
    simp
  rw [hval]
  have he3 : Real.exp 1 * Real.exp 2 = Real.exp 3 := by rw [← Real.exp_add]; norm_num
  have hhalf : Real.exp (1 / 2) ≤ Real.exp 3 := Real.exp_le_exp.2 (by norm_num)
  have hE31 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  nlinarith [Real.exp_pos (1:ℝ), Real.exp_pos (2:ℝ)]

/-- The (parameter-free) envelope controlling the tilt remainder for large tilts, apart from
the tilt-dependent exponential term. -/
private noncomputable def tiltEnvLarge (t : ℝ) : ℝ :=
  4 * (Real.exp t + Real.exp (-t)) + 1

private lemma integrable_tiltEnvLarge : Integrable tiltEnvLarge (gaussianReal 0 1) :=
  (integrable_cosh_one.const_mul 4).add (integrable_const _)

private lemma integral_tiltEnvLarge :
    (∫ t, tiltEnvLarge t ∂(gaussianReal 0 1)) = 4 * (2 * Real.exp (1 / 2)) + 1 := by
  simp only [tiltEnvLarge]
  rw [integral_add (integrable_cosh_one.const_mul 4) (integrable_const _), integral_const_mul,
    integral_cosh_one, integral_const]
  simp

/-- The `L¹(γ)` bound on the tilt remainder for **small** tilts: the third-order Taylor
expansion of `exp` with an exponential envelope. -/
private lemma integral_abs_tiltRemainder_le_of_le_one {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ (30 * Real.exp 3 + 3) * s ^ 3 := by
  have hpt : ∀ t : ℝ, |tiltRemainder s t| ≤ s ^ 3 * tiltEnvSmall t := by
    intro t
    set x : ℝ := s * t - s ^ 2 / 2 with hx
    have hsplit : tiltRemainder s t
        = (Real.exp x - (1 + x + x ^ 2 / 2)) + (-(s ^ 3 * t / 2) + s ^ 4 / 8) := by
      simp only [tiltRemainder, hx]; ring
    have hxabs : |x| ≤ s * (|t| + 1 / 2) := by
      have h1 : |x| ≤ s * |t| + s ^ 2 / 2 := by
        rw [hx]
        calc |s * t - s ^ 2 / 2| ≤ |s * t| + |s ^ 2 / 2| := abs_sub _ _
          _ = s * |t| + s ^ 2 / 2 := by
              rw [abs_mul, abs_of_nonneg hs,
                abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 2 / 2)]
      nlinarith
    have hcube : |x| ^ 3 ≤ s ^ 3 * (|t| + 1 / 2) ^ 3 := by
      have h := pow_le_pow_left₀ (abs_nonneg x) hxabs 3
      calc |x| ^ 3 ≤ (s * (|t| + 1 / 2)) ^ 3 := h
        _ = s ^ 3 * (|t| + 1 / 2) ^ 3 := by ring
    have hexpx : Real.exp |x| ≤ Real.exp (|t| + 1 / 2) := by
      refine Real.exp_le_exp.2 (hxabs.trans ?_)
      nlinarith [abs_nonneg t]
    have hbig : (|t| + 1 / 2) ^ 3 ≤ 27 * Real.exp (|t| + 1 / 2) := cube_le_exp (by positivity)
    have hexpabs : Real.exp (|t| + 1 / 2) * Real.exp (|t| + 1 / 2)
        = Real.exp 1 * Real.exp (2 * |t|) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hcosh2 : Real.exp (2 * |t|) ≤ Real.exp (2 * t) + Real.exp (-(2 * t)) := by
      rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]; linarith [Real.exp_pos (-(2 * t))]
      · rw [h]
        have he : Real.exp (2 * -t) = Real.exp (-(2 * t)) := by congr 1; ring
        rw [he]; linarith [Real.exp_pos (2 * t)]
    have hT := abs_exp_sub_taylor_two_le x
    have hterm1 : |x| ^ 3 * Real.exp |x| / 2
        ≤ s ^ 3 * (27 / 2 * Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t)))) := by
      have e1 : |x| ^ 3 * Real.exp |x|
          ≤ (s ^ 3 * (|t| + 1 / 2) ^ 3) * Real.exp (|t| + 1 / 2) :=
        mul_le_mul hcube hexpx (Real.exp_pos _).le (by positivity)
      have e2 : (s ^ 3 * (|t| + 1 / 2) ^ 3) * Real.exp (|t| + 1 / 2)
          ≤ (s ^ 3 * (27 * Real.exp (|t| + 1 / 2))) * Real.exp (|t| + 1 / 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbig (by positivity : (0:ℝ) ≤ s ^ 3))
          (Real.exp_pos _).le
      have e3 : (s ^ 3 * (27 * Real.exp (|t| + 1 / 2))) * Real.exp (|t| + 1 / 2)
          = s ^ 3 * 27 * (Real.exp 1 * Real.exp (2 * |t|)) := by
        rw [mul_assoc (s ^ 3) _ _, mul_assoc, hexpabs]; ring
      have e5 : s ^ 3 * 27 * (Real.exp 1 * Real.exp (2 * |t|))
          ≤ s ^ 3 * 27 * (Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcosh2 (Real.exp_pos 1).le) (by positivity)
      have e6 : s ^ 3 * 27 * (Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t))))
          = 2 * (s ^ 3 * (27 / 2 * Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t))))) := by
        ring
      have hnn : (0:ℝ) ≤ s ^ 3 * (27 / 2 * Real.exp 1
          * (Real.exp (2 * t) + Real.exp (-(2 * t)))) := by positivity
      linarith [e1, e2, e5]
    have hterm2 : |(-(s ^ 3 * t / 2) + s ^ 4 / 8)|
        ≤ s ^ 3 * ((Real.exp t + Real.exp (-t)) / 2) + s ^ 3 * (1 / 8 : ℝ) := by
      have hAdd := abs_add_le (-(s ^ 3 * t / 2)) (s ^ 4 / 8)
      have e1 : |(-(s ^ 3 * t / 2))| = s ^ 3 / 2 * |t| := by
        rw [abs_neg, show s ^ 3 * t / 2 = s ^ 3 / 2 * t by ring, abs_mul,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 3 / 2)]
      have e2 : |s ^ 4 / 8| = s ^ 4 / 8 := abs_of_nonneg (by positivity)
      rw [e1, e2] at hAdd
      have h2 : s ^ 4 ≤ s ^ 3 := by nlinarith [pow_nonneg hs 3]
      nlinarith [abs_le_exp_add_exp t, pow_nonneg hs 3]
    have hexpand : s ^ 3 * tiltEnvSmall t
        = s ^ 3 * (27 / 2 * Real.exp 1 * (Real.exp (2 * t) + Real.exp (-(2 * t))))
          + (s ^ 3 * ((Real.exp t + Real.exp (-t)) / 2) + s ^ 3 * (1 / 8 : ℝ)) := by
      simp only [tiltEnvSmall]; ring
    rw [hsplit, hexpand]
    calc |(Real.exp x - (1 + x + x ^ 2 / 2)) + (-(s ^ 3 * t / 2) + s ^ 4 / 8)|
        ≤ |Real.exp x - (1 + x + x ^ 2 / 2)| + |(-(s ^ 3 * t / 2) + s ^ 4 / 8)| :=
          abs_add_le _ _
      _ ≤ _ := by linarith [hT, hterm1, hterm2]
  refine (integral_mono (integrable_tiltRemainder s).abs
    (integrable_tiltEnvSmall.const_mul (s ^ 3)) hpt).trans ?_
  rw [integral_const_mul]
  nlinarith [integral_tiltEnvSmall_le, pow_nonneg hs 3]

/-- The `L¹(γ)` bound on the tilt remainder for **large** tilts, where the trivial termwise
bound already beats `s³`. -/
private lemma integral_abs_tiltRemainder_le_of_one_le {s : ℝ} (hs1 : 1 ≤ s) :
    (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ (30 * Real.exp 3 + 3) * s ^ 3 := by
  have hs : (0 : ℝ) ≤ s := by linarith
  have hA : Integrable (fun t : ℝ => Real.exp (s * t - s ^ 2 / 2)) (gaussianReal 0 1) :=
    integrable_exp_tilt s
  have hW : Integrable
      (fun t : ℝ => 1 + s * (Real.exp t + Real.exp (-t)) + s ^ 2 * tiltEnvLarge t / 2)
      (gaussianReal 0 1) :=
    ((integrable_const (1 : ℝ)).add (integrable_cosh_one.const_mul s)).add
      ((integrable_tiltEnvLarge.const_mul (s ^ 2)).div_const 2)
  have hpt : ∀ t : ℝ, |tiltRemainder s t|
      ≤ Real.exp (s * t - s ^ 2 / 2)
        + (1 + s * (Real.exp t + Real.exp (-t)) + s ^ 2 * tiltEnvLarge t / 2) := by
    intro t
    have ha := abs_le_exp_add_exp t
    have hb := sq_le_exp_add_exp t
    have hc : |1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2|
        ≤ 1 + s * |t| + s ^ 2 * (t ^ 2 + 1) / 2 := by
      have e1 : |1 + s * t| ≤ 1 + s * |t| := by
        calc |1 + s * t| ≤ |(1:ℝ)| + |s * t| := abs_add_le _ _
          _ = 1 + s * |t| := by rw [abs_one, abs_mul, abs_of_nonneg hs]
      have e2 : |s ^ 2 * (t ^ 2 - 1) / 2| ≤ s ^ 2 * (t ^ 2 + 1) / 2 := by
        rw [show s ^ 2 * (t ^ 2 - 1) / 2 = s ^ 2 / 2 * (t ^ 2 - 1) by ring, abs_mul,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 2 / 2)]
        have habs : |t ^ 2 - 1| ≤ t ^ 2 + 1 := by
          rcases abs_cases (t ^ 2 - 1) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith [sq_nonneg t]
        nlinarith [sq_nonneg s]
      calc |1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2|
          ≤ |1 + s * t| + |s ^ 2 * (t ^ 2 - 1) / 2| := abs_add_le _ _
        _ ≤ (1 + s * |t|) + s ^ 2 * (t ^ 2 + 1) / 2 := by linarith
        _ = 1 + s * |t| + s ^ 2 * (t ^ 2 + 1) / 2 := by ring
    have h0 : |tiltRemainder s t|
        ≤ Real.exp (s * t - s ^ 2 / 2) + |1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2| := by
      simp only [tiltRemainder]
      calc |Real.exp (s * t - s ^ 2 / 2) - (1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2)|
          ≤ |Real.exp (s * t - s ^ 2 / 2)| + |1 + s * t + s ^ 2 * (t ^ 2 - 1) / 2| :=
            abs_sub _ _
        _ = _ := by rw [abs_of_pos (Real.exp_pos _)]
    simp only [tiltEnvLarge]
    nlinarith [sq_nonneg s, Real.exp_pos t, Real.exp_pos (-t)]
  have h1s : Integrable (fun t : ℝ => 1 + s * (Real.exp t + Real.exp (-t)))
      (gaussianReal 0 1) := (integrable_const (1 : ℝ)).add (integrable_cosh_one.const_mul s)
  have h2s : Integrable (fun t : ℝ => s ^ 2 * tiltEnvLarge t / 2) (gaussianReal 0 1) :=
    (integrable_tiltEnvLarge.const_mul (s ^ 2)).div_const 2
  have hWval : (∫ t, (1 + s * (Real.exp t + Real.exp (-t)) + s ^ 2 * tiltEnvLarge t / 2)
      ∂(gaussianReal 0 1))
      = 1 + s * (2 * Real.exp (1 / 2)) + s ^ 2 * (4 * (2 * Real.exp (1 / 2)) + 1) / 2 := by
    rw [integral_add h1s h2s,
      integral_add (integrable_const (1 : ℝ)) (integrable_cosh_one.const_mul s),
      integral_const, integral_const_mul, integral_cosh_one, integral_div, integral_const_mul,
      integral_tiltEnvLarge]
    simp
  refine (integral_mono (integrable_tiltRemainder s).abs (hA.add hW)
    (fun t => by simpa using hpt t)).trans ?_
  simp only [Pi.add_apply]
  rw [integral_add hA hW, integral_exp_tilt s, hWval]
  have hhalf : Real.exp (1 / 2) ≤ Real.exp 3 := Real.exp_le_exp.2 (by norm_num)
  have hE31 : (1 : ℝ) ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hcube1 : s ≤ s ^ 3 := by nlinarith
  have hsq1 : s ^ 2 ≤ s ^ 3 := by nlinarith
  have hone : (1 : ℝ) ≤ s ^ 3 := by nlinarith
  nlinarith [Real.exp_pos ((1:ℝ) / 2)]

/-- **The tilt remainder is cubically small in the tilt parameter, in `L¹` of the Gaussian.**
This is the analytic heart of the improved bound: the third-order Taylor error of the
Cameron–Martin density is `O(s³)` *after integration against the Gaussian*, with an absolute
constant. (Pointwise it is *not* `O(s³)`: `exp (s t)` is unbounded in `t`.) -/
private lemma exists_tiltRemainder_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s →
      (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ C * s ^ 3 := by
  refine ⟨30 * Real.exp 3 + 3, by positivity, fun s hs => ?_⟩
  rcases le_total s 1 with h | h
  · exact integral_abs_tiltRemainder_le_of_le_one hs h
  · exact integral_abs_tiltRemainder_le_of_one_le h


/-! ### The multivariate Cameron–Martin tilt -/

section MultivariateTilt

variable {k : ℕ}

private lemma continuous_tiltRemainder (s : ℝ) : Continuous (fun t => tiltRemainder s t) := by
  unfold tiltRemainder
  fun_prop

/-- The **vector tilt remainder**: the second-order Taylor error, in the shift `w`, of the
Cameron–Martin density `exp (⟪w,z⟫ − ‖w‖²/2)` of `N(0,I_k)` translated by `w`. -/
private noncomputable def vecTiltRemainder (w z : EuclideanSpace ℝ (Fin k)) : ℝ :=
  Real.exp (⟪w, z⟫_ℝ - ‖w‖ ^ 2 / 2)
    - (1 + ⟪w, z⟫_ℝ + (⟪w, z⟫_ℝ ^ 2 - ‖w‖ ^ 2) / 2)

/-- **The vector tilt remainder is cubically small in the shift, in `L¹(N(0,I_k))`.**
Reduction to the scalar statement `exists_tiltRemainder_bound` by the one-dimensional marginal
`⟪ŵ, ·⟫ ∼ N(0,1)` (`stdGaussian_map_inner_unit`): the whole expression depends on `z` only
through that marginal. The constant is **dimension-free**. -/
private lemma integral_abs_vecTiltRemainder_le {C : ℝ}
    (hC : ∀ s : ℝ, 0 ≤ s → (∫ t, |tiltRemainder s t| ∂(gaussianReal 0 1)) ≤ C * s ^ 3)
    (w : EuclideanSpace ℝ (Fin k)) :
    (∫ z, |vecTiltRemainder w z| ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      ≤ C * ‖w‖ ^ 3 := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [vecTiltRemainder]
  · have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
    obtain ⟨u, hunit, hwu⟩ : ∃ u : EuclideanSpace ℝ (Fin k), ‖u‖ = 1 ∧ w = ‖w‖ • u :=
      ⟨‖w‖⁻¹ • w, by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnw)]
        field_simp, by rw [smul_smul, mul_inv_cancel₀ hnw.ne', one_smul]⟩
    have hinner : ∀ z : EuclideanSpace ℝ (Fin k), ⟪w, z⟫_ℝ = ‖w‖ * ⟪u, z⟫_ℝ := by
      intro z
      conv_lhs => rw [hwu]
      rw [real_inner_smul_left]
    have hrw : ∀ z : EuclideanSpace ℝ (Fin k),
        vecTiltRemainder w z = tiltRemainder ‖w‖ (⟪u, z⟫_ℝ) := by
      intro z
      simp only [vecTiltRemainder, tiltRemainder, hinner z]
      ring
    simp_rw [hrw]
    have hmap : Measure.map (fun y : EuclideanSpace ℝ (Fin k) => ⟪u, y⟫_ℝ)
        (stdGaussian (EuclideanSpace ℝ (Fin k))) = gaussianReal 0 1 := by
      have h := stdGaussian_map_inner_unit u hunit
      rwa [multivariateGaussian_zero_one] at h
    have hpush : (∫ z, |tiltRemainder ‖w‖ (⟪u, z⟫_ℝ)|
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
        = ∫ t, |tiltRemainder ‖w‖ t| ∂(gaussianReal 0 1) := by
      rw [← hmap, integral_map (by fun_prop)
        ((continuous_tiltRemainder ‖w‖).abs.aestronglyMeasurable)]
    rw [hpush]
    exact hC ‖w‖ hnw.le

/-- **Cameron–Martin: a Gaussian shift is an exponential tilt.** For a bounded continuous `g`,
`∫ g(z + a) dγ = ∫ g(z) exp(⟪a,z⟫ − ‖a‖²/2) dγ`. This is
`stdGaussian_withDensity_exp_shift` read as an integral identity; it is what replaces the
third derivative of `g` by a factor `σ⁻³` in the Lindeberg swap. -/
private lemma integral_gaussian_shift_eq_tilt {g : EuclideanSpace ℝ (Fin k) → ℝ}
    (hg : Continuous g) (a : EuclideanSpace ℝ (Fin k)) :
    (∫ z, g (z + a) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = ∫ z, g z * Real.exp (⟪a, z⟫_ℝ - ‖a‖ ^ 2 / 2)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  have hmapint : (∫ z, g (z + a) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))))
      = ∫ z, g z ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun y => y + a)) := by
    rw [integral_map (by fun_prop) hg.aestronglyMeasurable]
  rw [hmapint, ← stdGaussian_withDensity_exp_shift a,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, mul_comm]

end MultivariateTilt

end GaussianTilt

end StatLean.HypothesisTesting
