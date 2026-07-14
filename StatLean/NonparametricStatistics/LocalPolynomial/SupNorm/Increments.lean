import StatLean.NonparametricStatistics.LocalPolynomial.WeightBounds

/-!
# Lipschitz control of local polynomial weights in the evaluation point

For a Lipschitz boxed kernel, the total variation of the weight vector between two evaluation
points is controlled:
$$ \sum_i \bigl|W^*_i(t) - W^*_i(t')\bigr| \;\le\; C_L\,\frac{|t - t'|}{h^3},
   \qquad t, t' \in [0,1], $$
with `C_L = C_L(ℓ, K_max, λ₀, a₀, L_K)`. This is the grid-to-continuum step of the sup-norm
analysis: on a grid of mesh `n^{-4}` the increment is `O(n^{-4}/h³) = O(n^{-1})`.

**Proof formalization notes.** Write the weight difference through the resolvent identity
`B_t⁻¹ − B_{t'}⁻¹ = B_t⁻¹(B_{t'} − B_t)B_{t'}⁻¹`. Each ingredient is Lipschitz in `t` with
constants polynomial in `1/h`: `‖U(zᵢ)K(zᵢ) − U(z'ᵢ)K(z'ᵢ)‖ ≤ C·|t−t'|/h` (Lipschitz kernel,
bounded basis on the support), `‖B_t − B_{t'}‖ ≤ C·|t−t'|/h` (design density bound controls
the number of active summands), and `‖B⁻¹‖ ≤ 1/λ₀`. Both `t, t'` count on the union of the
two bandwidth windows, of cardinality `≤ 4a₀nh`. The generous `h⁻³` absorbs all bookkeeping
(only upper bounds are needed; `h ≤ 1`).

**Bibliographic comments.** Standard chaining/discretization bookkeeping; folklore.
-/

open Matrix

namespace StatLean.NonparametricStatistics

/-- Basis-vector norm bound on `|z| ≤ 2`: `∑ k, (lpBasis ℓ z k)² ≤ (ℓ+1)·4^ℓ`. -/
private lemma lpBasis_normSq_le_two {ℓ : ℕ} {z : ℝ} (hz : |z| ≤ 2) :
    ∑ k, (lpBasis ℓ z k) ^ 2 ≤ ((ℓ : ℝ) + 1) * 4 ^ ℓ := by
  have hterm : ∀ k : Fin (ℓ + 1), (lpBasis ℓ z k) ^ 2 ≤ (4 : ℝ) ^ ℓ := by
    intro k
    rw [lpBasis, div_pow]
    have hzk : |z ^ (k : ℕ)| ≤ 2 ^ (k : ℕ) := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg z) hz _
    have hk1 : (z ^ (k : ℕ)) ^ 2 ≤ 4 ^ ℓ := by
      have h2k : (2 : ℝ) ^ (k : ℕ) ≤ 2 ^ ℓ :=
        pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp k.isLt)
      have : (z ^ (k : ℕ)) ^ 2 ≤ (2 ^ (k : ℕ)) ^ 2 := by
        nlinarith [hzk, sq_abs (z ^ (k : ℕ)), abs_nonneg (z ^ (k : ℕ)),
          pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) (k:ℕ)]
      calc (z ^ (k : ℕ)) ^ 2 ≤ (2 ^ (k : ℕ)) ^ 2 := this
        _ = (4 : ℝ) ^ (k : ℕ) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ (4 : ℝ) ^ ℓ := pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp k.isLt)

    have hfac : (1 : ℝ) ≤ (Nat.factorial (k : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [div_le_iff₀ (by positivity)]
    have hfsq : (1 : ℝ) ≤ ((Nat.factorial (k : ℕ) : ℝ)) ^ 2 := by nlinarith [hfac]
    nlinarith [hk1, hfsq, pow_nonneg (show (0:ℝ) ≤ 4 by norm_num) ℓ]
  calc ∑ k, (lpBasis ℓ z k) ^ 2
      ≤ ∑ _k : Fin (ℓ + 1), (4 : ℝ) ^ ℓ := Finset.sum_le_sum (fun k _ => hterm k)
    _ = ((ℓ : ℝ) + 1) * 4 ^ ℓ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring

/-- Per-coordinate Lipschitz bound of the basis difference on `|z|,|z'| ≤ 2`:
`|z^k - z'^k| ≤ k·2^(k-1)·|z - z'|`, hence `≤ 2^ℓ·|z-z'|`. -/
private lemma abs_pow_sub_le {z z' : ℝ} (hz : |z| ≤ 2) (hz' : |z'| ≤ 2) (k : ℕ) :
    |z ^ k - z' ^ k| ≤ (k : ℝ) * 2 ^ k * |z - z'| := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hstep : z ^ (m + 1) - z' ^ (m + 1)
        = z * (z ^ m - z' ^ m) + z' ^ m * (z - z') := by ring
    have hzm : |z ^ m| ≤ 2 ^ m := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg z) hz _
    have hz'm : |z' ^ m| ≤ 2 ^ m := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg z') hz' _
    calc |z ^ (m + 1) - z' ^ (m + 1)|
        = |z * (z ^ m - z' ^ m) + z' ^ m * (z - z')| := by rw [hstep]
      _ ≤ |z * (z ^ m - z' ^ m)| + |z' ^ m * (z - z')| := abs_add_le _ _
      _ = |z| * |z ^ m - z' ^ m| + |z' ^ m| * |z - z'| := by rw [abs_mul, abs_mul]
      _ ≤ 2 * ((m : ℝ) * 2 ^ m * |z - z'|) + 2 ^ m * |z - z'| := by
          gcongr
      _ ≤ ((m : ℝ) + 1) * 2 ^ (m + 1) * |z - z'| := by
          have := abs_nonneg (z - z'); rw [pow_succ]; nlinarith [this,
            pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) m]
      _ = ((m : ℕ) + 1 : ℝ) * 2 ^ (m + 1) * |z - z'| := by push_cast; ring
      _ = (↑(m + 1) : ℝ) * 2 ^ (m + 1) * |z - z'| := by push_cast; ring

/-- ℓ¹→ℓ² helper: from `∑_k (v k)² ≤ M²` and `M ≥ 0`, `|v 0| ≤ M`. -/
private lemma abs_zero_le_of_sq_sum_le {ℓ : ℕ} (v : Fin (ℓ + 1) → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hsum : ∑ k, (v k) ^ 2 ≤ M ^ 2) : |v 0| ≤ M := by
  have h0 : (v 0) ^ 2 ≤ M ^ 2 :=
    le_trans (Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ 0)) hsum
  calc |v 0| = Real.sqrt ((v 0) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt h0
    _ = M := Real.sqrt_sq hM

/-- Uniform bound on a basis coordinate for `|z| ≤ 2`: `|U_k(z)| ≤ (ℓ+1)·2^ℓ`. -/
private lemma lpBasis_abs_le_two {ℓ : ℕ} {z : ℝ} (hz : |z| ≤ 2) (k : Fin (ℓ + 1)) :
    |lpBasis ℓ z k| ≤ ((ℓ : ℝ) + 1) * 2 ^ ℓ := by
  rw [lpBasis, abs_div]
  have hnum : |z ^ (k : ℕ)| ≤ 2 ^ ℓ := by
    rw [abs_pow]
    calc |z| ^ (k : ℕ) ≤ 2 ^ (k : ℕ) := pow_le_pow_left₀ (abs_nonneg z) hz _
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp k.isLt)
  have hden : (1 : ℝ) ≤ |(Nat.factorial (k : ℕ) : ℝ)| := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [div_le_iff₀ (by positivity)]
  have h1 : |z ^ (k : ℕ)| ≤ 2 ^ ℓ := hnum
  have hle1 : (1:ℝ) ≤ (ℓ:ℝ) + 1 := by have := (Nat.cast_nonneg ℓ : (0:ℝ) ≤ (ℓ:ℝ)); linarith
  have hp : (0:ℝ) ≤ (2:ℝ) ^ ℓ := pow_nonneg (by norm_num) ℓ
  calc |z ^ (k:ℕ)| ≤ 2 ^ ℓ := h1
    _ = 1 * 2 ^ ℓ * 1 := by ring
    _ ≤ ((ℓ:ℝ) + 1) * 2 ^ ℓ * |(Nat.factorial (k : ℕ) : ℝ)| := by
        gcongr

/-- Lipschitz bound on a basis coordinate difference for `|z|,|z'| ≤ 2`:
`|U_k(z) − U_k(z')| ≤ (ℓ+1)·2^ℓ·|z − z'|`. -/
private lemma lpBasis_sub_abs_le_two {ℓ : ℕ} {z z' : ℝ} (hz : |z| ≤ 2) (hz' : |z'| ≤ 2)
    (k : Fin (ℓ + 1)) :
    |lpBasis ℓ z k - lpBasis ℓ z' k| ≤ ((ℓ : ℝ) + 1) * 2 ^ ℓ * |z - z'| := by
  rw [lpBasis, lpBasis, div_sub_div_same, abs_div]
  have hnum := abs_pow_sub_le hz hz' (k : ℕ)
  have hden : (1 : ℝ) ≤ |(Nat.factorial (k : ℕ) : ℝ)| := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hk2 : (k : ℝ) * 2 ^ (k : ℕ) ≤ ((ℓ : ℝ) + 1) * 2 ^ ℓ := by
    have h1 : (k : ℝ) ≤ (ℓ : ℝ) + 1 := by
      have := Nat.lt_succ_iff.mp k.isLt; exact_mod_cast Nat.le_succ_of_le this
    have h2 : (2 : ℝ) ^ (k : ℕ) ≤ 2 ^ ℓ :=
      pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.mp k.isLt)
    have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
    nlinarith [h1, h2, pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) (k:ℕ), (Nat.cast_nonneg ℓ : (0:ℝ) ≤ (ℓ:ℝ))]
  rw [div_le_iff₀ (by positivity)]
  have hle : |z ^ (k:ℕ) - z' ^ (k:ℕ)| ≤ ((ℓ:ℝ) + 1) * 2 ^ ℓ * |z - z'| :=
    le_trans hnum (by nlinarith [hk2, abs_nonneg (z - z')])
  nlinarith [hle, hden, abs_nonneg (z ^ (k:ℕ) - z' ^ (k:ℕ)), abs_nonneg (z - z'),
    mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ (ℓ:ℝ)+1)
      (pow_nonneg (show (0:ℝ)≤2 by norm_num) ℓ)) (abs_nonneg (z - z'))]

/-- Entry expansion of the local design matrix. -/
private lemma lpMatrix_apply {n : ℕ} (xdat : Fin n → ℝ) (K : ℝ → ℝ) (h : ℝ) (ℓ : ℕ) (t : ℝ)
    (k j : Fin (ℓ + 1)) :
    lpMatrix xdat K h ℓ t k j = ((n : ℝ) * h)⁻¹ * ∑ i, K ((xdat i - t) / h)
      * (lpBasis ℓ ((xdat i - t) / h) k * lpBasis ℓ ((xdat i - t) / h) j) := by
  simp only [lpMatrix, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Per-summand triple-telescope Lipschitz bound with the union-window indicator. -/
private lemma lpMatrix_summand_le {n : ℕ} {xdat : Fin n → ℝ} {K : ℝ → ℝ}
    {Kmax LK h : ℝ} {ℓ : ℕ} (hh : 0 < h) (hbox : KernelBoxed K Kmax)
    (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|)
    {t t' : ℝ} (hd : |t - t'| < h) (k j : Fin (ℓ + 1)) (i : Fin n) :
    |K ((xdat i - t') / h) * (lpBasis ℓ ((xdat i - t') / h) k
        * lpBasis ℓ ((xdat i - t') / h) j)
      - K ((xdat i - t) / h) * (lpBasis ℓ ((xdat i - t) / h) k
        * lpBasis ℓ ((xdat i - t) / h) j)|
      ≤ (LK + 2 * Kmax) * (((ℓ : ℝ) + 1) * 2 ^ ℓ) ^ 2 * (|t - t'| / h)
        * (Set.Icc (t - 2 * h) (t + 2 * h)).indicator (fun _ => (1 : ℝ)) (xdat i) := by
  set B := ((ℓ : ℝ) + 1) * 2 ^ ℓ with hBdef
  have hBpos : (0 : ℝ) ≤ B := by positivity
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hLK : 0 ≤ LK := by
    have hk := hKlip 1 0
    have : |(1:ℝ) - 0| = 1 := by norm_num
    rw [this, mul_one] at hk
    exact le_trans (abs_nonneg _) hk
  set z := (xdat i - t) / h with hz
  set z' := (xdat i - t') / h with hz'
  have hzz' : |z - z'| = |t - t'| / h := by
    rw [hz, hz', div_sub_div_same, abs_div, abs_of_pos hh]
    congr 1; rw [show xdat i - t - (xdat i - t') = t' - t by ring, abs_sub_comm]
  -- if the summand is nonzero, both |z|,|z'| ≤ 2 and x_i in the union window
  by_cases hact : xdat i ∈ Set.Icc (t - 2 * h) (t + 2 * h)
  · rw [Set.indicator_of_mem hact, mul_one]
    -- We bound in all cases assuming |z|,|z'| ≤ 2. Show that.
    -- At least one K ≠ 0 forces both ≤ 2; else summand = 0.
    by_cases hboth : (z ∈ Set.Icc (-1:ℝ) 1) ∨ (z' ∈ Set.Icc (-1:ℝ) 1)
    · have hz2 : |z| ≤ 2 ∧ |z'| ≤ 2 := by
        have hdz : |z - z'| < 1 := by rw [hzz', div_lt_one hh]; exact hd
        rcases hboth with hin | hin
        · have h1 : |z| ≤ 1 := abs_le.mpr (Set.mem_Icc.mp hin)
          refine ⟨le_trans h1 (by norm_num), ?_⟩
          have hdz' : |z' - z| < 1 := by rw [abs_sub_comm]; exact hdz
          calc |z'| = |z' - z + z| := by ring_nf
            _ ≤ |z' - z| + |z| := abs_add_le _ _
            _ ≤ 2 := by linarith [hdz', h1]
        · have h1 : |z'| ≤ 1 := abs_le.mpr (Set.mem_Icc.mp hin)
          refine ⟨?_, le_trans h1 (by norm_num)⟩
          calc |z| = |z - z' + z'| := by ring_nf
            _ ≤ |z - z'| + |z'| := abs_add_le _ _
            _ ≤ 2 := by linarith [hdz, h1]
      obtain ⟨hz2, hz'2⟩ := hz2
      -- triple telescope
      have hUk := lpBasis_abs_le_two hz2 k
      have hUj := lpBasis_abs_le_two hz2 j
      have hUk' := lpBasis_abs_le_two hz'2 k
      have hUj' := lpBasis_abs_le_two hz'2 j
      have hdUk : |lpBasis ℓ z' k - lpBasis ℓ z k| ≤ B * (|t - t'| / h) := by
        have := lpBasis_sub_abs_le_two hz'2 hz2 k; rwa [hzz'] at this
      have hdUj : |lpBasis ℓ z' j - lpBasis ℓ z j| ≤ B * (|t - t'| / h) := by
        have := lpBasis_sub_abs_le_two hz'2 hz2 j; rwa [hzz'] at this
      have hdK : |K z' - K z| ≤ LK * (|t - t'| / h) := by
        have hkl := hKlip z' z
        rw [abs_sub_comm z' z, hzz'] at hkl; exact hkl
      -- telescoping identity
      set uk := lpBasis ℓ z k; set uj := lpBasis ℓ z j
      set uk' := lpBasis ℓ z' k; set uj' := lpBasis ℓ z' j
      have htel : K z' * (uk' * uj') - K z * (uk * uj)
          = (K z' - K z) * (uk' * uj') + K z * (uk' - uk) * uj'
            + K z * uk * (uj' - uj) := by ring
      calc |K z' * (uk' * uj') - K z * (uk * uj)|
          = |(K z' - K z) * (uk' * uj') + K z * (uk' - uk) * uj'
              + K z * uk * (uj' - uj)| := by rw [htel]
        _ ≤ |(K z' - K z) * (uk' * uj')| + |K z * (uk' - uk) * uj'|
              + |K z * uk * (uj' - uj)| := by
            refine le_trans (abs_add_le _ _) ?_; gcongr; exact abs_add_le _ _
        _ = |K z' - K z| * (|uk'| * |uj'|) + |K z| * |uk' - uk| * |uj'|
              + |K z| * |uk| * |uj' - uj| := by
            rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
        _ ≤ (LK * (|t-t'|/h)) * (B * B) + Kmax * (B * (|t-t'|/h)) * B
              + Kmax * B * (B * (|t-t'|/h)) := by
            have hnn : (0:ℝ) ≤ |t-t'|/h := div_nonneg (abs_nonneg _) hh.le
            gcongr <;> first
              | exact hdK | exact hbox.1 z | exact hUk' | exact hUj' | exact hUk
              | exact hdUk | exact hdUj
        _ = (LK + 2 * Kmax) * B ^ 2 * (|t - t'| / h) := by ring
    · push_neg at hboth
      have hK1 : K z = 0 := hbox.2 z hboth.1
      have hK2 : K z' = 0 := hbox.2 z' hboth.2
      simp only [hK1, hK2, zero_mul, mul_zero, sub_zero, abs_zero]
      positivity
  · -- summand = 0 since both K vanish (x_i not in window)
    rw [Set.indicator_of_notMem hact, mul_zero]
    have hz1 : z ∉ Set.Icc (-1:ℝ) 1 := by
      intro hin
      apply hact
      have : |z| ≤ 1 := abs_le.mpr (Set.mem_Icc.mp hin)
      rw [hz, abs_div, abs_of_pos hh, div_le_one hh] at this
      rw [Set.mem_Icc]; rw [abs_le] at this
      constructor <;> nlinarith [this.1, this.2, hh]
    have hz'1 : z' ∉ Set.Icc (-1:ℝ) 1 := by
      intro hin
      apply hact
      have hb : |z'| ≤ 1 := abs_le.mpr (Set.mem_Icc.mp hin)
      rw [hz', abs_div, abs_of_pos hh, div_le_one hh] at hb
      rw [abs_le] at hb
      have hd' : |t - t'| < h := hd
      rw [Set.mem_Icc]; rw [abs_le] at hd'
      constructor <;> nlinarith [hb.1, hb.2, hd'.1, hd'.2, hh]
    have hK1 : K z = 0 := hbox.2 z hz1
    have hK2 : K z' = 0 := hbox.2 z' hz'1
    simp only [hK1, hK2, zero_mul, mul_zero, sub_zero, abs_zero, le_refl]

/-- **ℓ¹-Lipschitz bound of the weight vector in the evaluation point**: there is
`C_L = C_L(ℓ, K_max, λ₀, a₀, L_K)` with
`∑ i, |W*ᵢ(t) − W*ᵢ(t')| ≤ C_L·|t − t'|/h³` for all `t, t' ∈ [0,1]` under the standing
assumptions. -/
theorem lp_weight_lipschitz_sum {ℓ : ℕ} {K : ℝ → ℝ} {Kmax lam0 a₀ LK : ℝ}
    -- USER-INPUT: positive eigenvalue floor and nonnegative density constant; standing
    -- design assumptions
    (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: Lipschitz kernel; the sup-norm analysis input
    (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|) :
    ∃ CL : ℝ, 0 < CL ∧
      ∀ {n : ℕ}, 0 < n → ∀ {h : ℝ}, 1 / (2 * (n : ℝ)) ≤ h → h ≤ 1 →
      ∀ {xdat : Fin n → ℝ}, (∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1) →
        DesignEigenvalueLB xdat K h ℓ lam0 → DesignDensityBound xdat a₀ →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
        ∑ i, |lpWeight xdat K h ℓ t i - lpWeight xdat K h ℓ t' i|
          ≤ CL * |t - t'| / h ^ 3 := by
  sorry

end StatLean.NonparametricStatistics
