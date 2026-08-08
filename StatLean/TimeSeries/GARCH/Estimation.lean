import StatLean.TimeSeries.GARCH.GARCHBasic
import StatLean.TimeSeries.Spectral.Periodogram
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# GARCH estimation: QMLE, general-density MLE, Whittle, LAD (FY §4.2.3)

Definitions only, plus the two cited asymptotic statements as literature debts:

* **eq. (4.35)/(4.36)**: the ARCH(∞) expansion of the GARCH volatility and its
  **truncated** version `σ̃_t²(θ)` (started from a fixed presample constant), the object
  every practical criterion uses *(the printed `𝐛 = (b₁ … b_p)²` in (4.36) is a typo for
  the coefficient vector — we take the intended reading)*;
* **eq. (4.37)**: the Gaussian quasi-likelihood criterion
  `l_ν(θ) = Σ_{t=ν}^{T}(log σ̃_t² + X_t²/σ̃_t²)`, minimized to give the QMLE;
* **eq. (4.38)**: the general-density criterion `Σ_t (log σ̃_t − log f(X_t/σ̃_t))`, with
  the standardized-`t` and generalized-Gaussian densities recorded as instances;
* **eqs. (4.39)–(4.40)**: AIC/BIC for GARCH order selection;
* **eq. (4.41)**: the Whittle criterion on the squared process, built from the
  periodogram of `Y_t = X_t²` against the model spectral density — its asymptotics are
  a DEBT (Giraitis & Robinson 2001);
* **eq. (4.42)**: the LAD criterion in the median-1 reparametrization — `√T`-normality
  is a DEBT (Peng & Yao 2002).

**Scope.** §4.2.4 (Hall–Yao Theorems 4.5/4.6) and §4.2.5 (bootstrap CIs) were
**descoped on 2026-08-04** at the user's direction, together with the stable-law /
domain-of-attraction scaffolding that existed only to state them. The QMLE definitions
stay because §4.2.6's tests consume them.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.3,
eqs. (4.35)–(4.42) (pp. 156–161). (`FY §4.2.3`.)

**Bibliographic comments.** Gaussian QMLE for GARCH is Bollerslev & Wooldridge (1992);
the Whittle estimator for squared GARCH is Giraitis & Robinson, *Whittle estimation of
ARCH models* (Econometric Theory 17 (2001), 608–631); the LAD estimator is Peng & Yao,
*Least absolute deviations estimation for ARCH and GARCH models* (Biometrika 90 (2003),
967–975).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology Real

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **FY eq. (4.36)**: the **truncated conditional variance** of a GARCH(p, q) at
parameter `(c₀, b, a)`, computed from the data by running the volatility recursion
forward from a presample constant `v₀ ≥ 0` (the recursion is over the ARCH(∞) form, so
only past data enter). -/
noncomputable def garchTruncVol {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) : ℕ → ℝ
  | 0 => v0
  | (n + 1) =>
      c0 + (∑ i : Fin p, b i * (if h : n - (i : ℕ) < T then x ⟨n - (i : ℕ), h⟩ else 0) ^ 2)
        + ∑ j : Fin q, a j * garchTruncVol c0 b a v0 x (n - (j : ℕ))
  decreasing_by all_goals omega

/-- **FY eq. (4.37)**: the Gaussian **quasi-likelihood criterion**
`l_ν(θ) = Σ_{t=ν}^{T−1} (log σ̃_t² + X_t²/σ̃_t²)`; the QMLE minimizes it over the
admissible parameter set. -/
noncomputable def garchQuasiLik {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico ν T,
    (Real.log (garchTruncVol c0 b a v0 x t)
      + (if h : t < T then x ⟨t, h⟩ else 0) ^ 2 / garchTruncVol c0 b a v0 x t)

/-- **FY eq. (4.38)**: the **general-density criterion**
`Σ_t (log σ̃_t − log f(X_t/σ̃_t))` for a known standardized innovation density `f`. -/
noncomputable def garchDensityLik {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) (f : ℝ → ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico ν T,
    (Real.log (Real.sqrt (garchTruncVol c0 b a v0 x t))
      - Real.log (f ((if h : t < T then x ⟨t, h⟩ else 0)
          / Real.sqrt (garchTruncVol c0 b a v0 x t))))

/-- **FY eq. (4.39)**: AIC for GARCH order selection (`2(p + q + 1)` parameters). -/
noncomputable def garchAIC {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  garchQuasiLik c0 b a v0 x ν + 2 * ((p : ℝ) + (q : ℝ) + 1)

/-- **FY eq. (4.40)**: BIC for GARCH order selection. -/
noncomputable def garchBIC {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  garchQuasiLik c0 b a v0 x ν + ((p : ℝ) + (q : ℝ) + 1) * Real.log T

/-- **FY eq. (4.41)**: the **Whittle criterion** for the squared process — the
periodogram of `Y_t = X_t²` integrated against the reciprocal model spectral density,
in the discrete Fourier-frequency form. `gmodel` is the model spectral density of the
squared process at the candidate parameter. -/
noncomputable def garchWhittle {T : ℕ} (x : Fin T → ℝ) (gmodel : ℝ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 T,
    (Real.log (gmodel (fourierFreq T k))
      + periodogram (fun t => x t ^ 2) k / gmodel (fourierFreq T k))

/-- **FY eq. (4.42)**: the **LAD criterion** in the median-1 reparametrization:
`Σ_t |log X_t² − log σ̃_t²|`, minimized over the admissible set. -/
noncomputable def garchLAD {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico ν T,
    |Real.log ((if h : t < T then x ⟨t, h⟩ else 0) ^ 2)
      - Real.log (garchTruncVol c0 b a v0 x t)|

/-- The truncated conditional variance is nonnegative under nonnegative parameters and
presample value — the sanity fact every criterion needs for its logarithms. -/
theorem garchTruncVol_nonneg {p q : ℕ} {c0 : ℝ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    {v0 : ℝ} (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j) (hv0 : 0 ≤ v0)
    {T : ℕ} (x : Fin T → ℝ) (n : ℕ) :
    0 ≤ garchTruncVol c0 b a v0 x n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa [garchTruncVol] using hv0
    | (m + 1) =>
      rw [garchTruncVol]
      have h1 : 0 ≤ ∑ i : Fin p,
          b i * (if h : m - (i : ℕ) < T then x ⟨m - (i : ℕ), h⟩ else 0) ^ 2 :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (sq_nonneg _)
      have h2 : 0 ≤ ∑ j : Fin q, a j * garchTruncVol c0 b a v0 x (m - (j : ℕ)) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (ih _ (by omega))
      linarith

/-! ### A counterexample to the frozen rate in `garchTruncVol_presample_stable`

The recursion (4.36) contracts the presample discrepancy at the rate of the dominant
root `ρ` of `ρ^q = ∑_j a_j ρ^{q-1-j}`, NOT at the rate `A := ∑_j a_j`. For `q = 1` the
two agree (`ρ = a₀`), but for `q ≥ 2` with mass on the higher lags `ρ > A`, and the
frozen conclusion `≤ C · A^n` is then false for every constant `C`. The witness below is
the smallest such instance: `p = 0`, `q = 2`, `c₀ = 0`, `a = (0, 9/10)`, so
`A = 9/10` but the discrepancy only halves its index each step and decays like `A^{n/2}`.
-/

private noncomputable def presampleWitnessB : Fin 0 → ℝ := fun _ => 0

private noncomputable def presampleWitnessA : Fin 2 → ℝ := ![0, 9 / 10]

private noncomputable def presampleWitnessX : Fin 0 → ℝ := fun _ => 0

/-- The witness volatility path started from presample value `w`. -/
private noncomputable def presampleWitnessV (w : ℝ) (n : ℕ) : ℝ :=
  garchTruncVol (0 : ℝ) presampleWitnessB presampleWitnessA w presampleWitnessX n

private lemma presampleWitnessA_sum : (∑ j, presampleWitnessA j) = (9 / 10 : ℝ) := by
  simp [presampleWitnessA, Fin.sum_univ_two]

private lemma presampleWitnessV_zero (w : ℝ) : presampleWitnessV w 0 = w := by
  simp [presampleWitnessV, garchTruncVol]

/-- Only the lag-2 coefficient is nonzero, so the recursion drops the index by two. -/
private lemma presampleWitnessV_succ (w : ℝ) (n : ℕ) :
    presampleWitnessV w (n + 1) = (9 / 10) * presampleWitnessV w (n - 1) := by
  rw [presampleWitnessV, garchTruncVol]
  simp [presampleWitnessV, presampleWitnessB, presampleWitnessA, Fin.sum_univ_two]

private lemma presampleWitnessV_even (w : ℝ) (k : ℕ) :
    presampleWitnessV w (2 * k) = (9 / 10 : ℝ) ^ k * w := by
  induction k with
  | zero => simpa using presampleWitnessV_zero w
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, presampleWitnessV_succ,
      show 2 * k + 1 - 1 = 2 * k by omega, ih]
    ring

/-- **The conclusion of `garchTruncVol_presample_stable` is FALSE as frozen.** All of its
hypotheses hold for the witness (`c₀ = 0 ≥ 0`, `b` vacuous, `a = (0, 9/10) ≥ 0`,
`∑ a_j = 9/10 < 1`, `v₀ = 1 ≥ 0`, `v₁ = 0 ≥ 0`), yet the discrepancy at even times is
`(9/10)^k` while the claimed bound at time `2k` is `C · (9/10)^{2k}`; no constant absorbs
the missing factor `(10/9)^k`. -/
private theorem presample_stable_rate_false :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |garchTruncVol (0 : ℝ) presampleWitnessB presampleWitnessA 1 presampleWitnessX n
          - garchTruncVol (0 : ℝ) presampleWitnessB presampleWitnessA 0 presampleWitnessX n|
        ≤ C * (∑ j, presampleWitnessA j) ^ n := by
  rintro ⟨C, -, hC⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 10 / 9)
  have h := hC (2 * k)
  rw [presampleWitnessA_sum] at h
  have e1 : garchTruncVol (0 : ℝ) presampleWitnessB presampleWitnessA 1 presampleWitnessX
      (2 * k) = (9 / 10 : ℝ) ^ k := by
    simpa [presampleWitnessV] using presampleWitnessV_even 1 k
  have e2 : garchTruncVol (0 : ℝ) presampleWitnessB presampleWitnessA 0 presampleWitnessX
      (2 * k) = 0 := by
    simpa [presampleWitnessV] using presampleWitnessV_even 0 k
  have hpos : (0 : ℝ) < (9 / 10 : ℝ) ^ k := by positivity
  rw [e1, e2, sub_zero, abs_of_pos hpos, two_mul, pow_add] at h
  have h1 : (1 : ℝ) * ((9 / 10 : ℝ) ^ k) ≤ (C * (9 / 10 : ℝ) ^ k) * ((9 / 10 : ℝ) ^ k) := by
    rw [one_mul, mul_assoc]; exact h
  have h2 : (1 : ℝ) ≤ C * (9 / 10 : ℝ) ^ k := le_of_mul_le_mul_right h1 hpos
  have h3 : C * (9 / 10 : ℝ) ^ k < ((10 : ℝ) / 9) ^ k * (9 / 10 : ℝ) ^ k :=
    mul_lt_mul_of_pos_right hk hpos
  rw [show ((10 : ℝ) / 9) ^ k * (9 / 10 : ℝ) ^ k = 1 by rw [← mul_pow]; norm_num] at h3
  linarith

/-! ### The repaired rate

The discrepancy `D n := |σ̃²_n(v₀) − σ̃²_n(v₁)|` obeys `D 0 = |v₀ − v₁|` (the `c₀` and data
terms are common to both runs and cancel) and `D (n+1) ≤ Σⱼ aⱼ · D (n − j)`. Since each
lag index `n − j` with `j < q` is at least `n + 1 − q`, one factor `A := Σⱼ aⱼ` is gained
every `q` steps: `D n ≤ |v₀ − v₁| · A ^ ⌊n/q⌋`. Choosing any `ρ ∈ (0, 1)` with `A ≤ ρ^q`
— e.g. `ρ = max (A ^ (1/q)) (1/2)`, the `max` only to keep `ρ > 0` when `A = 0` — turns
that into the geometric bound `D n ≤ (|v₀ − v₁| / ρ^{q−1}) · ρ^n`. No characteristic-root
analysis is needed: `ρ` is *some* admissible rate, not the dominant root. -/

/-- One factor `A = Σⱼ aⱼ` is gained every `q` steps of the recursion (4.36). -/
private lemma garchTruncVol_diff_le {p q : ℕ} {c0 : ℝ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (ha : ∀ j, 0 ≤ a j) (ha1 : (∑ j, a j) ≤ 1) {v0 v1 : ℝ} {T : ℕ} (x : Fin T → ℝ) (n : ℕ) :
    |garchTruncVol c0 b a v0 x n - garchTruncVol c0 b a v1 x n|
      ≤ |v0 - v1| * (∑ j, a j) ^ (n / q) := by
  have hA0 : (0 : ℝ) ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha j
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [garchTruncVol]
    | (m + 1) =>
      rw [garchTruncVol, garchTruncVol]
      -- the constant and the data terms are common to both runs
      have hcancel : ∀ u v : ℝ,
          (c0 + (∑ i : Fin p, b i * (if h : m - (i : ℕ) < T then x ⟨m - (i : ℕ), h⟩ else 0) ^ 2)
              + u)
            - (c0 + (∑ i : Fin p,
                b i * (if h : m - (i : ℕ) < T then x ⟨m - (i : ℕ), h⟩ else 0) ^ 2) + v)
            = u - v := by intro u v; ring
      rw [hcancel, ← Finset.sum_sub_distrib]
      -- every lag index `m − j` (`j < q`) has quotient at least `e`
      set e : ℕ := (m + 1 - q) / q with he
      have hstep : ∀ j : Fin q,
          |a j * garchTruncVol c0 b a v0 x (m - (j : ℕ))
              - a j * garchTruncVol c0 b a v1 x (m - (j : ℕ))|
            ≤ a j * (|v0 - v1| * (∑ j, a j) ^ e) := by
        intro j
        rw [← mul_sub, abs_mul, abs_of_nonneg (ha j)]
        refine mul_le_mul_of_nonneg_left ?_ (ha j)
        refine (ih _ (by omega)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine pow_le_pow_of_le_one hA0 ha1 ?_
        have hj := j.isLt
        exact Nat.div_le_div_right (by omega)
      calc |∑ j : Fin q, (a j * garchTruncVol c0 b a v0 x (m - (j : ℕ))
                - a j * garchTruncVol c0 b a v1 x (m - (j : ℕ)))|
          ≤ ∑ j : Fin q, |a j * garchTruncVol c0 b a v0 x (m - (j : ℕ))
              - a j * garchTruncVol c0 b a v1 x (m - (j : ℕ))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin q, a j * (|v0 - v1| * (∑ j, a j) ^ e) :=
            Finset.sum_le_sum fun j _ => hstep j
        _ = |v0 - v1| * (∑ j, a j) ^ (e + 1) := by
            rw [← Finset.sum_mul, pow_succ]; ring
        _ ≤ |v0 - v1| * (∑ j, a j) ^ ((m + 1) / q) := by
            refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hA0 ha1 ?_) (abs_nonneg _)
            rcases Nat.eq_zero_or_pos q with hq | hq
            · subst hq; simp
            · rcases lt_or_ge (m + 1) q with h | h
              · rw [Nat.div_eq_of_lt h]; exact Nat.zero_le _
              · rw [he]
                have : (m + 1 - q) / q + 1 = (m + 1) / q := by
                  rw [← Nat.add_div_right _ hq]
                  congr 1
                  omega
                omega

/-- **The truncation is asymptotically negligible** (the fact that makes (4.36) usable):
under `Σ a_j < 1` the effect of the presample value decays geometrically, so two
presample choices give criteria differing by `O(ρ^ν)` for **some** rate `ρ < 1`.

**Rate repaired 2026-08-09.** The statement previously claimed the rate `Σ a_j`; that is
false for `q ≥ 2` with mass on the higher lags, since the recursion contracts at the
dominant root `ρ` of `ρ^q = Σ_j a_j ρ^{q−1−j}`, which exceeds `Σ a_j`. The witness
`a = (0, 9/10)` is formalized just above (`presample_stable_rate_false`). Only the
existence of *a* geometric rate is used downstream, so the rate is now existentially
quantified. -/
theorem garchTruncVol_presample_stable {p q : ℕ} {c0 : ℝ} {b : Fin p → ℝ}
    {a : Fin q → ℝ} (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j)
    (hsum : (∑ j, a j) < 1) {v0 v1 : ℝ} (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1)
    {T : ℕ} (x : Fin T → ℝ) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ n : ℕ,
      |garchTruncVol c0 b a v0 x n - garchTruncVol c0 b a v1 x n| ≤ C * ρ ^ n := by
  have hA0 : (0 : ℝ) ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha j
  rcases Nat.eq_zero_or_pos q with hq | hq
  · -- with no lag terms the discrepancy is annihilated after a single step
    subst hq
    refine ⟨|v0 - v1|, 0, abs_nonneg _, le_rfl, by norm_num, ?_⟩
    intro n
    match n with
    | 0 => simp [garchTruncVol]
    | (m + 1) => rw [garchTruncVol, garchTruncVol]; simp
  · have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    set A : ℝ := ∑ j, a j with hAdef
    -- any `ρ < 1` with `A ≤ ρ^q` will do; the `max` only keeps `ρ > 0` when `A = 0`
    set ρ : ℝ := max (A ^ ((q : ℝ)⁻¹)) (1 / 2) with hρdef
    have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hρ1 : ρ < 1 := max_lt (Real.rpow_lt_one hA0 hsum (inv_pos.2 hqR)) (by norm_num)
    have hAρ : A ≤ ρ ^ q := by
      have h1 : (A ^ ((q : ℝ)⁻¹)) ^ q = A := by
        rw [← Real.rpow_natCast (A ^ ((q : ℝ)⁻¹)) q, ← Real.rpow_mul hA0,
          inv_mul_cancel₀ hqR.ne', Real.rpow_one]
      calc A = (A ^ ((q : ℝ)⁻¹)) ^ q := h1.symm
        _ ≤ ρ ^ q := pow_le_pow_left₀ (Real.rpow_nonneg hA0 _) (le_max_left _ _) q
    refine ⟨|v0 - v1| / ρ ^ (q - 1), ρ, by positivity, hρ0.le, hρ1, fun n => ?_⟩
    refine (garchTruncVol_diff_le ha hsum.le x n).trans ?_
    calc |v0 - v1| * A ^ (n / q)
        ≤ |v0 - v1| * (ρ ^ q) ^ (n / q) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hAρ _) (abs_nonneg _)
      _ = |v0 - v1| * ρ ^ (q * (n / q)) := by rw [← pow_mul]
      _ ≤ |v0 - v1| * ρ ^ (n - (q - 1)) := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ0.le hρ1.le ?_) (abs_nonneg _)
          have h1 : q * (n / q) + n % q = n := Nat.div_add_mod n q
          have h2 : n % q < q := Nat.mod_lt _ hq
          omega
      _ ≤ |v0 - v1| / ρ ^ (q - 1) * ρ ^ n := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hρ0 (q - 1)), mul_assoc, ← pow_add]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hρ0.le hρ1.le (by omega)) (abs_nonneg _)

/-- **DEBT (Giraitis & Robinson 2001; FY §4.2.3)**: `√T`-asymptotic normality of the
Whittle estimator of a GARCH model under fourth-order stationarity. Recorded at the
granularity FY cites (Cramér–Wold/charFun form against an assumed limiting covariance
matrix). -/
theorem whittle_clt_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: fourth-order stationarity; FY §4.2.3 / GR 2001
    (hL4 : ∀ t, MemLp (X t) 4 μ)
    -- USER-INPUT: the limiting covariance matrix of the Whittle estimator; GR 2001
    (W : Matrix (Fin (p + q + 1)) (Fin (p + q + 1)) ℝ) (hW : Matrix.PosDef W)
    -- USER-INPUT: a measurable Whittle-minimizing estimator sequence; FY eq. (4.41)
    (θhat : (T : ℕ) → Ω → Fin (p + q + 1) → ℝ) (hmeas : ∀ T, Measurable (θhat T))
    (θ0 : Fin (p + q + 1) → ℝ)
    (c : Fin (p + q + 1) → ℝ) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (∑ i, ∑ j, c i * c j * W i j))) u)) := by
  sorry

/-- **DEBT (Peng & Yao 2002/2003; FY §4.2.3)**: `√T`-asymptotic normality of the LAD
estimator, which unlike the QMLE needs no moment condition beyond the model's own —
the heavy-tail-robust alternative FY highlights. -/
theorem lad_clt_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: median-1 normalization of the squared innovations; Peng & Yao
    (hmed : μ {ω | ε 0 ω ^ 2 ≤ 1} = μ {ω | 1 ≤ ε 0 ω ^ 2})
    (W : Matrix (Fin (p + q + 1)) (Fin (p + q + 1)) ℝ) (hW : Matrix.PosDef W)
    (θhat : (T : ℕ) → Ω → Fin (p + q + 1) → ℝ) (hmeas : ∀ T, Measurable (θhat T))
    (θ0 : Fin (p + q + 1) → ℝ)
    (c : Fin (p + q + 1) → ℝ) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * ∑ i, c i * (θhat T ω i - θ0 i)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (∑ i, ∑ j, c i * c j * W i j))) u)) := by
  sorry

/-! ### Sanity checks on the criteria

Cheap facts pinning down the degenerate corners and the AIC/BIC penalties, so that the
definitions above are exercised rather than merely stated. -/

/-- Strict positivity of the truncated volatility — what the `log σ̃_t²` in (4.37) and the
division in (4.38) actually need. -/
private lemma garchTruncVol_pos {p q : ℕ} {c0 : ℝ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    {v0 : ℝ} (hc0 : 0 < c0) (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j) (hv0 : 0 < v0)
    {T : ℕ} (x : Fin T → ℝ) (n : ℕ) :
    0 < garchTruncVol c0 b a v0 x n := by
  match n with
  | 0 => simpa [garchTruncVol] using hv0
  | (m + 1) =>
    rw [garchTruncVol]
    have h1 : 0 ≤ ∑ i : Fin p,
        b i * (if h : m - (i : ℕ) < T then x ⟨m - (i : ℕ), h⟩ else 0) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (sq_nonneg _)
    have h2 : 0 ≤ ∑ j : Fin q, a j * garchTruncVol c0 b a v0 x (m - (j : ℕ)) :=
      Finset.sum_nonneg fun j _ =>
        mul_nonneg (ha j) (garchTruncVol_nonneg hc0.le hb ha hv0.le x _)
    linarith

/-- The quasi-likelihood (4.37) over an empty time range is `0` (in particular at `T = 0`). -/
private lemma garchQuasiLik_of_le {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) {ν : ℕ} (h : T ≤ ν) :
    garchQuasiLik c0 b a v0 x ν = 0 := by
  simp [garchQuasiLik, Finset.Ico_eq_empty_of_le h]

/-- The general-density criterion (4.38) over an empty time range is `0`. -/
private lemma garchDensityLik_of_le {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) (f : ℝ → ℝ) {T : ℕ} (x : Fin T → ℝ) {ν : ℕ} (h : T ≤ ν) :
    garchDensityLik c0 b a v0 f x ν = 0 := by
  simp [garchDensityLik, Finset.Ico_eq_empty_of_le h]

/-- The LAD criterion (4.42) over an empty time range is `0`. -/
private lemma garchLAD_of_le {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) {ν : ℕ} (h : T ≤ ν) :
    garchLAD c0 b a v0 x ν = 0 := by
  simp [garchLAD, Finset.Ico_eq_empty_of_le h]

/-- The Whittle criterion (4.41) is well defined on an empty frequency range, where it
vanishes; the Fourier frequencies `k = 1, …, T − 1` are none for `T ≤ 1`. -/
private lemma garchWhittle_of_le_one {T : ℕ} (x : Fin T → ℝ) (gmodel : ℝ → ℝ)
    (h : T ≤ 1) : garchWhittle x gmodel = 0 := by
  simp [garchWhittle, Finset.Ico_eq_empty_of_le h]

/-- AIC (4.39) is the quasi-likelihood plus its stated `2(p + q + 1)` penalty. -/
private lemma garchAIC_sub_quasiLik {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) :
    garchAIC c0 b a v0 x ν - garchQuasiLik c0 b a v0 x ν = 2 * ((p : ℝ) + (q : ℝ) + 1) := by
  simp [garchAIC]

/-- BIC (4.40) is the quasi-likelihood plus its stated `(p + q + 1) log T` penalty. -/
private lemma garchBIC_sub_quasiLik {p q : ℕ} (c0 : ℝ) (b : Fin p → ℝ) (a : Fin q → ℝ)
    (v0 : ℝ) {T : ℕ} (x : Fin T → ℝ) (ν : ℕ) :
    garchBIC c0 b a v0 x ν - garchQuasiLik c0 b a v0 x ν
      = ((p : ℝ) + (q : ℝ) + 1) * Real.log T := by
  simp [garchBIC]

end StatLean.TimeSeries
