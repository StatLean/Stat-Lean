import StatLean.TimeSeries.GARCH.ARCHBasic
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.ConditionalExpectation

/-!
# Basic properties of GARCH(p, q) (FY §4.2.2, Theorem 4.4, Proposition 4.2)

* **ARCH(∞) reduction** (FY p. 148): inverting `1 − Σ_j a_j B^j` turns the GARCH
  volatility recursion into an ARCH(∞) one with nonnegative coefficients `d_i`
  (recursion as in eq. (2.20)) — this is how Theorem 2.5 applies.
* **Theorem 4.4** (sufficiency half): `Σ b_i + Σ a_j < 1` ⇒ a unique strictly
  stationary solution with `E X_t² < ∞`; then `E X_t = 0`,
  `Var X_t = c₀/(1 − Σb − Σa)`, and `X` is white noise. Finite fourth moments hold
  under eq. (4.28). The **necessity** half is Bollerslev (1986) — literature DEBT.
* **eqs. (4.25)–(4.26)**: `X_t²` follows an ARMA(p∨q, q) with martingale-difference
  noise `e_t = (ε_t² − 1)σ_t²`.
* **Proposition 4.2**: stationary GARCH is white noise, `σ_t²` is the conditional
  variance given the **infinite** past, and (under (4.28)) `{X_t²}` is a causal
  invertible ARMA with `κ_x ≥ κ_ε`.
* **Example 4.2**, eqs. (4.29)–(4.30): the GARCH(1,1) ARCH(∞) form and the closed-form
  squared-process ACF
  `Corr(X_t², X_{t+k}²) = ((1 − a₁² − a₁b₁)b₁ / (1 − a₁² − 2a₁b₁))·(b₁ + a₁)^{k−1}`.
* **Nelson (1990) sufficiency — a COMMISSIONED PROOF TARGET** (user, 2026-08-04):
  `E log(b₁ε² + a₁) < 0` ⇒ GARCH(1,1) has a unique strictly stationary solution, via
  the a.s. convergence of the random-product series `Σ_k ∏_{i<k}(b₁ε²_{t−i} + a₁)`
  (iid SLLN on the logs), *without* any moment condition; and the **IGARCH(1,1)**
  corollary: `b₁ + a₁ = 1` with nondegenerate `ε²` still gives strict stationarity,
  because strict Jensen makes `E log(b₁ε² + a₁) < log E(b₁ε² + a₁) = 0`.

**Scope.** Descoped 2026-08-04 (user), with all consumers: Nelson **necessity**,
Bougerol–Picard (1992b) Lyapunov-exponent iff and the general-`(p,q)` IGARCH
eq. (4.33), Kesten (1973) tail index eqs. (4.31)–(4.32). None is stated here.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.2,
Definition 4.3, Theorem 4.4, Proposition 4.2, eqs. (4.24)–(4.30) (pp. 147–156).
(`FY §4.2.2`.)

**Bibliographic comments.** GARCH is T. Bollerslev, *Generalized autoregressive
conditional heteroskedasticity* (J. Econometrics 31 (1986), 307–327); the strict
stationarity criterion for GARCH(1,1) is D. B. Nelson, *Stationarity and persistence in
the GARCH(1,1) model* (Econometric Theory 6 (1990), 318–334).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Shared second-moment bricks -/

/-- The strict past is a sub-σ-algebra, and (over a probability measure) trimming to it
keeps the measure σ-finite — the standing side conditions of the conditional-expectation
API. -/
private lemma sigmaLT_le_of_measurable {X : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaLT X t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hm s).comap_le

omit [MeasurableSpace Ω] in
private lemma comapLE_sigmaLT {X : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    MeasurableSpace.comap (X s) inferInstance ≤ sigmaLT X t :=
  le_iSup₂ (f := fun s (_ : s ∈ Set.Iio t) => MeasurableSpace.comap (X s) inferInstance) s hst

omit [MeasurableSpace Ω] in
private lemma measurable_of_lt_sigmaLT {X : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    Measurable[sigmaLT X t] (X s) :=
  (Measurable.of_comap_le (le_refl (MeasurableSpace.comap (X s) inferInstance))).mono
    (comapLE_sigmaLT hst) le_rfl

/-- `E ε_t² = 1` for unit-variance centred i.i.d. innovations, at every time. -/
private lemma iidNoise_integral_sq [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε 1 μ) (t : ℤ) : (∫ ω, ε t ω ^ 2 ∂μ) = 1 := by
  have h0 : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1 := by
    have hv := variance_eq_sub (μ := μ) hε.memLp
    rw [hε.variance_eq, hε.integral_eq_zero] at hv
    simpa using hv.symm
  rw [← h0]
  exact ((hε.identDistrib t 0).comp
    (measurable_id.pow_const 2 : Measurable fun x : ℝ => x ^ 2)).integral_eq

/-- `σ_t²` is the conditional variance of `X_t` given the strict past (FY Prop 4.2(i)).
Private form, so that the second-moment identities below can use it. -/
private lemma garch_condexp_sq [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hL2 : ∀ t, MemLp (X t) 2 μ) (t : ℤ) :
    μ[fun ω => X t ω ^ 2 | sigmaLT X t] =ᵐ[μ] fun ω => σvol t ω ^ 2 := by
  have hFle : sigmaLT X t ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup₂_le fun s _ => (h.measurableX s).comap_le
  haveI : SigmaFinite (μ.trim hFle) := by
    haveI : IsFiniteMeasure (μ.trim hFle) := MeasureTheory.isFiniteMeasure_trim hFle
    infer_instance
  -- `E ε_t² = 1`
  have hEeps : (∫ ω, ε t ω ^ 2 ∂μ) = 1 := iidNoise_integral_sq h.iid t
  have hεL2 : MemLp (ε t) 2 μ := (h.iid.identDistrib 0 t).memLp_snd h.iid.memLp
  have hεsq : Integrable (fun ω => ε t ω ^ 2) μ := hεL2.integrable_sq
  have hXsq : Integrable (fun ω => X t ω ^ 2) μ := (hL2 t).integrable_sq
  -- `X_t² = σ_t² ε_t²`
  have hprod : (fun ω => X t ω ^ 2) =ᵐ[μ] fun ω => σvol t ω ^ 2 * ε t ω ^ 2 := by
    filter_upwards [h.recX t] with ω hω
    rw [hω, mul_pow]
  have hprodint : Integrable (fun ω => σvol t ω ^ 2 * ε t ω ^ 2) μ := hXsq.congr hprod
  -- the volatility is measurable for the strict past, so it pulls out
  have hσm : StronglyMeasurable[sigmaLT X t] fun ω => σvol t ω ^ 2 :=
    ((h.adapted t).pow_const 2).stronglyMeasurable
  have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := sigmaLT X t)
    hσm hprodint hεsq
  -- and the innovation is independent of the strict past
  have hεm : StronglyMeasurable[MeasurableSpace.comap (ε t) inferInstance]
      fun ω => ε t ω ^ 2 :=
    ((Measurable.of_comap_le (le_refl (MeasurableSpace.comap (ε t) inferInstance))).pow_const
      2).stronglyMeasurable
  have hcondε : μ[fun ω => ε t ω ^ 2 | sigmaLT X t] =ᵐ[μ] fun _ => (1 : ℝ) := by
    have := condExp_indep_eq (h.iid.measurable t).comap_le hFle hεm (h.indep_past t)
    filter_upwards [this] with ω hω
    rw [hω, hEeps]
  calc μ[fun ω => X t ω ^ 2 | sigmaLT X t]
      =ᵐ[μ] μ[fun ω => σvol t ω ^ 2 * ε t ω ^ 2 | sigmaLT X t] := condExp_congr_ae hprod
    _ =ᵐ[μ] (fun ω => σvol t ω ^ 2) * μ[fun ω => ε t ω ^ 2 | sigmaLT X t] := hpull
    _ =ᵐ[μ] fun ω => σvol t ω ^ 2 := by
        filter_upwards [hcondε] with ω hω
        simp only [Pi.mul_apply, hω, mul_one]

/-- The GARCH process is a martingale difference: `E[X_t | past] = 0` (FY Prop 4.2(i)). -/
private lemma garch_condexp_zero [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hL2 : ∀ t, MemLp (X t) 2 μ) (t : ℤ) :
    μ[X t | sigmaLT X t] =ᵐ[μ] fun _ => (0 : ℝ) := by
  have hFle := sigmaLT_le_of_measurable h.measurableX t
  haveI : SigmaFinite (μ.trim hFle) := by
    haveI : IsFiniteMeasure (μ.trim hFle) := MeasureTheory.isFiniteMeasure_trim hFle
    infer_instance
  have hEeps0 : (∫ ω, ε t ω ∂μ) = 0 :=
    (h.iid.identDistrib t 0).integral_eq.trans h.iid.integral_eq_zero
  have hXint : Integrable (X t) μ := (hL2 t).integrable one_le_two
  have hεint : Integrable (ε t) μ :=
    ((h.iid.identDistrib 0 t).memLp_snd h.iid.memLp).integrable one_le_two
  have hprodint : Integrable (fun ω => σvol t ω * ε t ω) μ := hXint.congr (h.recX t)
  have hpull : μ[fun ω => σvol t ω * ε t ω | sigmaLT X t]
      =ᵐ[μ] fun ω => σvol t ω * (μ[ε t | sigmaLT X t]) ω :=
    condExp_mul_of_stronglyMeasurable_left (h.adapted t).stronglyMeasurable hprodint hεint
  have hcondε : μ[ε t | sigmaLT X t] =ᵐ[μ] fun _ => (0 : ℝ) := by
    have := condExp_indep_eq (h.iid.measurable t).comap_le hFle
      (Measurable.of_comap_le
        (le_refl (MeasurableSpace.comap (ε t) inferInstance))).stronglyMeasurable
      (h.indep_past t)
    filter_upwards [this] with ω hω
    rw [hω, hEeps0]
  refine ((condExp_congr_ae (h.recX t)).trans hpull).trans ?_
  filter_upwards [hcondε] with ω hω
  rw [hω, mul_zero]

/-- The martingale-difference property kills the cross moments: `E[X_s X_t] = 0` for
`s < t`. -/
private lemma garch_integral_mul_eq_zero [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hL2 : ∀ t, MemLp (X t) 2 μ) {s t : ℤ} (hst : s < t) :
    (∫ ω, X s ω * X t ω ∂μ) = 0 := by
  have hFle := sigmaLT_le_of_measurable h.measurableX t
  haveI : SigmaFinite (μ.trim hFle) := by
    haveI : IsFiniteMeasure (μ.trim hFle) := MeasureTheory.isFiniteMeasure_trim hFle
    infer_instance
  have hmulint : Integrable (fun ω => X s ω * X t ω) μ :=
    MemLp.integrable_mul (p := 2) (q := 2) (hL2 s) (hL2 t)
  have hXtint : Integrable (X t) μ := (hL2 t).integrable one_le_two
  have hpull : μ[fun ω => X s ω * X t ω | sigmaLT X t]
      =ᵐ[μ] fun ω => X s ω * (μ[X t | sigmaLT X t]) ω :=
    condExp_mul_of_stronglyMeasurable_left
      (measurable_of_lt_sigmaLT hst).stronglyMeasurable hmulint hXtint
  have hz : μ[fun ω => X s ω * X t ω | sigmaLT X t] =ᵐ[μ] fun _ => (0 : ℝ) := by
    refine hpull.trans ?_
    filter_upwards [garch_condexp_zero h hL2 t] with ω hω
    rw [hω, mul_zero]
  rw [← integral_condExp hFle (f := fun ω => X s ω * X t ω), integral_congr_ae hz]
  simp

/-- `σ_t²` is integrable with the same mean as `X_t²`: it *is* the conditional expectation
of `X_t²` given the strict past (FY Prop 4.2(i)). -/
private lemma garch_integral_vol_sq [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hL2 : ∀ t, MemLp (X t) 2 μ) (t : ℤ) :
    Integrable (fun ω => σvol t ω ^ 2) μ ∧
      (∫ ω, σvol t ω ^ 2 ∂μ) = ∫ ω, X t ω ^ 2 ∂μ := by
  have hFle := sigmaLT_le_of_measurable h.measurableX t
  haveI : SigmaFinite (μ.trim hFle) := by
    haveI : IsFiniteMeasure (μ.trim hFle) := MeasureTheory.isFiniteMeasure_trim hFle
    infer_instance
  have hce := garch_condexp_sq h hL2 t
  exact ⟨integrable_condExp.congr hce, by rw [← integral_congr_ae hce, integral_condExp hFle]⟩

/-- The **ARCH(∞) coefficients of a GARCH(p, q)** (FY p. 148): the coefficients `d_i` of
`(Σ_i b_i z^i)/(1 − Σ_j a_j z^j)`, obtained as formal power-series coefficients. -/
noncomputable def garchInfCoeffs {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (i : ℕ) :
    ℝ :=
  PowerSeries.coeff i
    (((∑ i : Fin p, Polynomial.C (b i) * Polynomial.X ^ ((i : ℕ) + 1) :
        Polynomial ℝ) : PowerSeries ℝ) *
      (((arPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)

/-- The GARCH ARCH(∞) coefficients are nonnegative under nonnegative GARCH
coefficients (FY p. 148: "the recursion has nonnegative solutions like (2.20)"). -/
private lemma coeffArPoly {p : ℕ} (b : Fin p → ℝ) (m : ℕ) :
    (arPoly b).coeff m
      = (if m = 0 then (1 : ℝ) else 0) - ∑ i : Fin p, if m = (i : ℕ) + 1 then b i else 0 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

private lemma coeffGarchNum {p : ℕ} (b : Fin p → ℝ) (m : ℕ) :
    (∑ i : Fin p, Polynomial.C (b i) * Polynomial.X ^ ((i : ℕ) + 1) : Polynomial ℝ).coeff m
      = ∑ i : Fin p, if m = (i : ℕ) + 1 then b i else 0 := by
  simp [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite]

private lemma constantCoeffArPoly_ne_zero {p : ℕ} (b : Fin p → ℝ) :
    PowerSeries.constantCoeff (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
  rw [Polynomial.constantCoeff_coe]
  have h : (arPoly b).coeff 0 = 1 := by rw [coeffArPoly]; simp
  rw [h]
  exact one_ne_zero

/-- The defining convolution identity `a ∗ d = b` (FY p. 148: the `d_i` solve a recursion
like eq. (2.20)). -/
private lemma arPoly_conv_garchInfCoeffs {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (arPoly a).coeff k * garchInfCoeffs b a (n - k)
      = (∑ i : Fin p, Polynomial.C (b i) * Polynomial.X ^ ((i : ℕ) + 1) :
          Polynomial ℝ).coeff n := by
  have key : (((arPoly a : Polynomial ℝ) : PowerSeries ℝ))
      * ((((∑ i : Fin p, Polynomial.C (b i) * Polynomial.X ^ ((i : ℕ) + 1) :
              Polynomial ℝ) : PowerSeries ℝ))
        * (((arPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = (((∑ i : Fin p, Polynomial.C (b i) * Polynomial.X ^ ((i : ℕ) + 1) :
            Polynomial ℝ) : PowerSeries ℝ)) := by
    rw [← mul_assoc, mul_comm (((arPoly a : Polynomial ℝ) : PowerSeries ℝ)),
      mul_assoc, PowerSeries.mul_inv_cancel _ (constantCoeffArPoly_ne_zero a), mul_one]
  have hcoeff := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_coe] at hcoeff
  rw [← hcoeff]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_coe]; rfl

/-- The ARCH(∞) coefficients solve `d_n = b_n + Σ_j a_j d_{n−1−j}` (FY p. 148). -/
private lemma garchInfCoeffs_rec {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    garchInfCoeffs b a n
      = (∑ i : Fin p, if n = (i : ℕ) + 1 then b i else 0)
        + ∑ j : Fin q, a j *
            (if (j : ℕ) < n then garchInfCoeffs b a (n - ((j : ℕ) + 1)) else 0) := by
  have hconv := arPoly_conv_garchInfCoeffs b a n
  rw [Finset.sum_range_succ', coeffGarchNum] at hconv
  have h0 : (arPoly a).coeff 0 = 1 := by rw [coeffArPoly]; simp
  rw [h0, one_mul, Nat.sub_zero] at hconv
  have hk : ∀ k : ℕ, (arPoly a).coeff (k + 1)
      = - ∑ j : Fin q, if k + 1 = (j : ℕ) + 1 then a j else 0 := by
    intro k; rw [coeffArPoly]; simp
  simp only [hk, neg_mul] at hconv
  rw [Finset.sum_neg_distrib] at hconv
  have hswap : (∑ k ∈ Finset.range n,
        (∑ j : Fin q, if k + 1 = (j : ℕ) + 1 then a j else 0) * garchInfCoeffs b a (n - (k + 1)))
      = ∑ j : Fin q, a j *
          (if (j : ℕ) < n then garchInfCoeffs b a (n - ((j : ℕ) + 1)) else 0) := by
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : (j : ℕ) < n
    · rw [if_pos hj]
      rw [Finset.sum_eq_single ((j : ℕ))]
      · rw [if_pos rfl]
      · intro k _ hkj
        rw [if_neg (by omega)]
      · intro hmem
        exact absurd (Finset.mem_range.2 hj) hmem
    · rw [if_neg hj, mul_zero]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [if_neg (by omega)]
  linarith [hconv, hswap]

theorem garchInfCoeffs_nonneg {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) < 1) (i : ℕ) :
    0 ≤ garchInfCoeffs b a i := by
  induction i using Nat.strong_induction_on with
  | _ n ih =>
    rw [garchInfCoeffs_rec]
    refine add_nonneg (Finset.sum_nonneg fun i _ => ?_) (Finset.sum_nonneg fun j _ => ?_)
    · split
      · exact hb i
      · exact le_rfl
    · refine mul_nonneg (ha j) ?_
      split
      · rename_i hj
        exact ih _ (by omega)
      · exact le_rfl

/-- Their total mass: `Σ_i d_i = (Σ b_i)/(1 − Σ a_j)`, which is `< 1` exactly when
`Σ b + Σ a < 1` — the bridge from FY Theorem 4.4's hypothesis to Theorem 2.5's. -/
theorem tsum_garchInfCoeffs {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) < 1) :
    HasSum (garchInfCoeffs b a) ((∑ i, b i) / (1 - ∑ j, a j)) := by
  have hd := garchInfCoeffs_nonneg hb ha hsum
  have hsa0 : 0 ≤ ∑ j : Fin q, a j := Finset.sum_nonneg fun j _ => ha j
  -- shifting the index in a partial sum
  have hshift : ∀ (j : ℕ) (N : ℕ),
      (∑ n ∈ Finset.range N, if j < n then garchInfCoeffs b a (n - (j + 1)) else 0)
        = ∑ m ∈ Finset.range (N - (j + 1)), garchInfCoeffs b a m := by
    intro j N
    induction N with
    | zero => simp
    | succ N ihN =>
      rw [Finset.sum_range_succ, ihN]
      by_cases hjN : j < N
      · have h1 : N + 1 - (j + 1) = (N - (j + 1)) + 1 := by omega
        rw [if_pos hjN, h1, Finset.sum_range_succ]
      · have h1 : N + 1 - (j + 1) = 0 := by omega
        have h2 : N - (j + 1) = 0 := by omega
        rw [if_neg hjN, h1, h2]
        simp
  -- the recursion, summed over `range N`
  have hpart : ∀ N : ℕ, (∑ n ∈ Finset.range N, garchInfCoeffs b a n)
      = (∑ i : Fin p, if (i : ℕ) + 1 < N then b i else 0)
        + ∑ j : Fin q, a j * ∑ m ∈ Finset.range (N - ((j : ℕ) + 1)), garchInfCoeffs b a m := by
    intro N
    rw [Finset.sum_congr rfl fun n (_ : n ∈ Finset.range N) => garchInfCoeffs_rec b a n,
      Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : (i : ℕ) + 1 < N
      · rw [if_pos hi, Finset.sum_eq_single ((i : ℕ) + 1)]
        · rw [if_pos rfl]
        · intro n _ hn
          rw [if_neg hn]
        · intro hmem
          exact absurd (Finset.mem_range.2 hi) hmem
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun n hn => ?_
        rw [Finset.mem_range] at hn
        rw [if_neg (by omega)]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.mul_sum, hshift]
  -- the partial sums are bounded, hence the family is summable
  have hmono : ∀ M N : ℕ, M ≤ N → (∑ m ∈ Finset.range M, garchInfCoeffs b a m)
      ≤ ∑ m ∈ Finset.range N, garchInfCoeffs b a m := by
    intro M N hMN
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => hd m
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hbnd : ∀ N : ℕ, (∑ n ∈ Finset.range N, garchInfCoeffs b a n)
      ≤ (∑ i, b i) / (1 - ∑ j, a j) := by
    intro N
    have h1 := hpart N
    have h2 : (∑ j : Fin q, a j * ∑ m ∈ Finset.range (N - ((j : ℕ) + 1)), garchInfCoeffs b a m)
        ≤ (∑ j : Fin q, a j) * ∑ m ∈ Finset.range N, garchInfCoeffs b a m := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hmono _ _ (by omega)) (ha j)
    have h3 : (∑ i : Fin p, if (i : ℕ) + 1 < N then b i else 0) ≤ ∑ i, b i :=
      Finset.sum_le_sum fun i _ => by
        split
        · exact le_rfl
        · exact hb i
    rw [le_div_iff₀ (by linarith)]
    nlinarith [h1, h2, h3]
  have hsummable : Summable (garchInfCoeffs b a) := summable_of_sum_range_le hd hbnd
  -- pass to the limit in the summed recursion
  have hTlim : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, garchInfCoeffs b a n)
      Filter.atTop (nhds (∑' n, garchInfCoeffs b a n)) := hsummable.hasSum.tendsto_sum_nat
  have hshiftlim : ∀ j : ℕ, Filter.Tendsto
      (fun N => ∑ m ∈ Finset.range (N - (j + 1)), garchInfCoeffs b a m) Filter.atTop
      (nhds (∑' n, garchInfCoeffs b a n)) :=
    fun j => hTlim.comp (Filter.tendsto_sub_atTop_nat (j + 1))
  have hblim : Filter.Tendsto (fun N : ℕ => ∑ i : Fin p, if (i : ℕ) + 1 < N then b i else 0)
      Filter.atTop (nhds (∑ i, b i)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop (p + 1)] with N hN
    refine (Finset.sum_congr rfl fun i _ => ?_).symm
    have := i.isLt
    rw [if_pos (by omega)]
  have hRlim : Filter.Tendsto (fun N : ℕ => (∑ i : Fin p, if (i : ℕ) + 1 < N then b i else 0)
      + ∑ j : Fin q, a j * ∑ m ∈ Finset.range (N - ((j : ℕ) + 1)), garchInfCoeffs b a m)
      Filter.atTop (nhds ((∑ i, b i) + ∑ j : Fin q, a j * ∑' n, garchInfCoeffs b a n)) :=
    hblim.add (tendsto_finset_sum _ fun j _ => (hshiftlim (j : ℕ)).const_mul (a j))
  have heq : (∑' n, garchInfCoeffs b a n)
      = (∑ i, b i) + ∑ j : Fin q, a j * ∑' n, garchInfCoeffs b a n :=
    tendsto_nhds_unique (hTlim.congr fun N => hpart N) hRlim
  rw [← Finset.sum_mul] at heq
  have hne : (1 : ℝ) - ∑ j, a j ≠ 0 := by linarith
  have hval : (∑' n, garchInfCoeffs b a n) = (∑ i, b i) / (1 - ∑ j, a j) := by
    rw [eq_div_iff hne]
    linarith [heq]
  rw [← hval]
  exact hsummable.hasSum

/-- **FY Theorem 4.4, existence**: under `Σ b + Σ a < 1` a strictly stationary
square-integrable GARCH(p, q) solution exists. -/
theorem exists_stationary_garch [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: nonnegative coefficients; FY Def 4.3
    (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j)
    -- USER-INPUT: contraction; FY Thm 4.4
    (hsum : (∑ i, b i) + (∑ j, a j) < 1)
    -- USER-INPUT: iid(0,1) innovations; FY Def 4.3
    (hε : IsIIDNoise ε 1 μ) :
    ∃ X σvol : ℤ → Ω → ℝ, IsGARCH c0 b a X σvol ε μ ∧ IsStrictlyStationary X μ ∧
      (∀ t, MemLp (X t) 2 μ) := by
  sorry

/-- **FY Theorem 4.4, moments**: a stationary square-integrable GARCH process is
centered with variance `c₀/(1 − Σb − Σa)`. -/
theorem IsGARCH.integral_and_variance [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    (hL2 : ∀ t, MemLp (X t) 2 μ)
    (hsum : (∑ i, b i) + (∑ j, a j) < 1) (t : ℤ) :
    (∫ ω, X t ω ∂μ) = 0 ∧
      variance (X t) μ = c0 / (1 - (∑ i, b i) - ∑ j, a j) := by
  have hFle := sigmaLT_le_of_measurable h.measurableX t
  haveI : SigmaFinite (μ.trim hFle) := by
    haveI : IsFiniteMeasure (μ.trim hFle) := MeasureTheory.isFiniteMeasure_trim hFle
    infer_instance
  -- (i) `E X_t = E σ_t · E ε_t = 0`, via the conditional expectation given the strict past
  have hcondX : μ[X t | sigmaLT X t] =ᵐ[μ] fun _ => (0 : ℝ) := garch_condexp_zero h hL2 t
  have hmean : (∫ ω, X t ω ∂μ) = 0 := by
    rw [← integral_condExp hFle (f := X t), integral_congr_ae hcondX]
    simp
  refine ⟨hmean, ?_⟩
  -- (ii) the second moment solves `v = c₀ + (Σb + Σa) v`
  have hXsq_eq : ∀ s : ℤ, (∫ ω, X s ω ^ 2 ∂μ) = ∫ ω, X t ω ^ 2 ∂μ := fun s =>
    ((hstat.identDistrib h.measurableX s t).comp
      (measurable_id.pow_const 2 : Measurable fun x : ℝ => x ^ 2)).integral_eq
  have hIb : Integrable (fun ω => ∑ i : Fin p, b i * X (t - 1 - (i : ℕ)) ω ^ 2) μ :=
    integrable_finset_sum _ fun i _ => (hL2 _).integrable_sq.const_mul (b i)
  have hIa : Integrable (fun ω => ∑ j : Fin q, a j * σvol (t - 1 - (j : ℕ)) ω ^ 2) μ :=
    integrable_finset_sum _ fun j _ => (garch_integral_vol_sq h hL2 _).1.const_mul (a j)
  have hc : Integrable (fun _ : Ω => c0) μ := integrable_const c0
  have e1 : (∫ ω, (c0 + (∑ i : Fin p, b i * X (t - 1 - (i : ℕ)) ω ^ 2)
        + ∑ j : Fin q, a j * σvol (t - 1 - (j : ℕ)) ω ^ 2) ∂μ)
      = (∫ ω, (c0 + ∑ i : Fin p, b i * X (t - 1 - (i : ℕ)) ω ^ 2) ∂μ)
        + ∫ ω, (∑ j : Fin q, a j * σvol (t - 1 - (j : ℕ)) ω ^ 2) ∂μ :=
    integral_add (hc.add hIb) hIa
  have e2 : (∫ ω, (c0 + ∑ i : Fin p, b i * X (t - 1 - (i : ℕ)) ω ^ 2) ∂μ)
      = (∫ _ω : Ω, c0 ∂μ) + ∫ ω, (∑ i : Fin p, b i * X (t - 1 - (i : ℕ)) ω ^ 2) ∂μ :=
    integral_add hc hIb
  have e3 : (∫ ω, (∑ i : Fin p, b i * X (t - 1 - (i : ℕ)) ω ^ 2) ∂μ)
      = (∑ i : Fin p, b i) * ∫ ω, X t ω ^ 2 ∂μ := by
    rw [integral_finset_sum (Finset.univ : Finset (Fin p)) fun i _ =>
      (hL2 (t - 1 - (i : ℕ))).integrable_sq.const_mul (b i), Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul, hXsq_eq]
  have e4 : (∫ ω, (∑ j : Fin q, a j * σvol (t - 1 - (j : ℕ)) ω ^ 2) ∂μ)
      = (∑ j : Fin q, a j) * ∫ ω, X t ω ^ 2 ∂μ := by
    rw [integral_finset_sum (Finset.univ : Finset (Fin q)) fun j _ =>
      (garch_integral_vol_sq h hL2 (t - 1 - (j : ℕ))).1.const_mul (a j), Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, (garch_integral_vol_sq h hL2 (t - 1 - (j : ℕ))).2, hXsq_eq]
  have hcv : (∫ _ω : Ω, c0 ∂μ) = c0 := by simp
  have hfix0 : (∫ ω, σvol t ω ^ 2 ∂μ)
      = c0 + ((∑ i : Fin p, b i) + ∑ j : Fin q, a j) * ∫ ω, X t ω ^ 2 ∂μ := by
    rw [integral_congr_ae (h.recVol t), e1, e2, e3, e4, hcv]
    ring
  have hfix : (∫ ω, X t ω ^ 2 ∂μ)
      = c0 + ((∑ i : Fin p, b i) + ∑ j : Fin q, a j) * ∫ ω, X t ω ^ 2 ∂μ :=
    (garch_integral_vol_sq h hL2 t).2.symm.trans hfix0
  have hne : (1 : ℝ) - (∑ i : Fin p, b i) - ∑ j : Fin q, a j ≠ 0 := by linarith
  have hval : (∫ ω, X t ω ^ 2 ∂μ) = c0 / (1 - (∑ i : Fin p, b i) - ∑ j : Fin q, a j) := by
    rw [eq_div_iff hne]
    linarith [hfix]
  have hvar := variance_eq_sub (μ := μ) (hL2 t)
  simp only [Pi.pow_apply] at hvar
  rw [hvar, hmean, hval]
  norm_num

/-- **FY Proposition 4.2(i)**: a stationary GARCH process is white noise. -/
theorem IsGARCH.isWhiteNoise [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    (hL2 : ∀ t, MemLp (X t) 2 μ) (hsum : (∑ i, b i) + (∑ j, a j) < 1) :
    IsWhiteNoise X (c0 / (1 - (∑ i, b i) - ∑ j, a j)) μ := by
  refine
    { measurable := h.measurableX
      memLp := hL2
      integral_eq_zero := fun t => (h.integral_and_variance hstat hL2 hsum t).1
      variance_eq := fun t => (h.integral_and_variance hstat hL2 hsum t).2
      uncorrelated := fun s t hst => ?_ }
  have hkey : ∀ u v : ℤ, u < v → cov[X u, X v; μ] = 0 := by
    intro u v huv
    rw [covariance_eq_sub (hL2 u) (hL2 v),
      (h.integral_and_variance hstat hL2 hsum u).1, zero_mul, sub_zero]
    have : μ[X u * X v] = ∫ ω, X u ω * X v ω ∂μ := by
      simp only [Pi.mul_apply]
    rw [this]
    exact garch_integral_mul_eq_zero h hL2 huv
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · exact hkey s t hlt
  · rw [covariance_comm]
    exact hkey t s hgt

/-- **FY Proposition 4.2(i)**: `σ_t²` is the conditional variance of `X_t` given the
strict past. -/
theorem IsGARCH.condexp_sq [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hL2 : ∀ t, MemLp (X t) 2 μ) (t : ℤ) :
    μ[fun ω => X t ω ^ 2 | sigmaLT X t] =ᵐ[μ] fun ω => σvol t ω ^ 2 :=
  garch_condexp_sq h hL2 t

/-- **FY eqs. (4.25)–(4.26)**: the squared process satisfies the ARMA(p∨q, q) recursion
`X_t² = c₀ + Σ_{i ≤ p∨q}(b_i + a_i) X_{t−i}² + e_t − Σ_j a_j e_{t−j}` with the
martingale-difference noise `e_t = (ε_t² − 1)σ_t²` (coefficients zero-padded to the
common order). -/
private lemma sum_range_pad_two {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (g : ℕ → ℝ) :
    (∑ i ∈ Finset.range (max p q),
        ((if hi : i < p then b ⟨i, hi⟩ else 0) + (if hi : i < q then a ⟨i, hi⟩ else 0)) * g i)
      = (∑ i : Fin p, b i * g (i : ℕ)) + ∑ j : Fin q, a j * g (j : ℕ) := by
  have key : ∀ (m : ℕ) (f : Fin m → ℝ), m ≤ max p q →
      (∑ i ∈ Finset.range (max p q), (if hi : i < m then f ⟨i, hi⟩ else 0) * g i)
        = ∑ i : Fin m, f i * g (i : ℕ) := by
    intro m f hm
    have hsub : Finset.range m ⊆ Finset.range (max p q) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hzero : ∀ x ∈ Finset.range (max p q), x ∉ Finset.range m →
        (if hi : x < m then f ⟨x, hi⟩ else 0) * g x = 0 := by
      intro x _ hx
      rw [dif_neg (by simpa using hx)]
      ring
    rw [← Finset.sum_subset hsub hzero]
    rw [← Fin.sum_univ_eq_sum_range (fun i => (if hi : i < m then f ⟨i, hi⟩ else 0) * g i) m]
    exact Finset.sum_congr rfl fun i _ => by simp
  simp only [add_mul]
  rw [Finset.sum_add_distrib, key p b (le_max_left p q), key q a (le_max_right p q)]

theorem IsGARCH.sq_arma_recursion [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (t : ℤ) :
    (fun ω => X t ω ^ 2) =ᵐ[μ] fun ω =>
      c0 + (∑ i ∈ Finset.range (max p q),
          ((if hi : i < p then b ⟨i, hi⟩ else 0) + (if hi : i < q then a ⟨i, hi⟩ else 0))
            * X (t - 1 - (i : ℕ)) ω ^ 2)
        + ((ε t ω ^ 2 - 1) * σvol t ω ^ 2)
        - ∑ j : Fin q, a j * ((ε (t - 1 - (j : ℕ)) ω ^ 2 - 1)
            * σvol (t - 1 - (j : ℕ)) ω ^ 2) := by
  filter_upwards [h.recX t, h.recVol t,
    ae_all_iff.2 fun j : Fin q => h.recX (t - 1 - (j : ℕ))] with ω h1 h2 h3
  -- `X_t² = σ_t² + e_t` with `e_t = (ε_t² − 1)σ_t²`
  have hL : X t ω ^ 2 = σvol t ω ^ 2 + (ε t ω ^ 2 - 1) * σvol t ω ^ 2 := by
    rw [h1, mul_pow]; ring
  -- and `σ²_{t−1−j} = X²_{t−1−j} − e_{t−1−j}`
  have hsig : ∀ j : Fin q, a j * σvol (t - 1 - (j : ℕ)) ω ^ 2
      = a j * X (t - 1 - (j : ℕ)) ω ^ 2
        - a j * ((ε (t - 1 - (j : ℕ)) ω ^ 2 - 1) * σvol (t - 1 - (j : ℕ)) ω ^ 2) := by
    intro j
    rw [h3 j, mul_pow]
    ring
  rw [hL, h2, sum_range_pad_two b a fun i : ℕ => X (t - 1 - (i : ℕ)) ω ^ 2,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hsig j, Finset.sum_sub_distrib]
  ring

/-- **DEBT (Bollerslev 1986; FY Theorem 4.4, necessity half)**: a strictly stationary
GARCH solution with finite variance and `c₀ > 0` forces `Σ b + Σ a < 1`. -/
theorem IsGARCH.sum_lt_one_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    (hL2 : ∀ t, MemLp (X t) 2 μ) (hc0 : 0 < c0) :
    (∑ i, b i) + (∑ j, a j) < 1 := by
  sorry

/-- **FY Example 4.2, eq. (4.30)**: the squared-process ACF of a stationary GARCH(1,1)
with finite fourth moment is
`Corr(X_t², X_{t+k}²) = ((1 − a₁² − a₁b₁)b₁/(1 − a₁² − 2a₁b₁))·(b₁ + a₁)^{k−1}`
for `k ≥ 1`. -/
theorem IsGARCH.acf_sq_garch_one_one [IsProbabilityMeasure μ] {c0 b1 a1 : ℝ}
    {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 (fun _ : Fin 1 => b1) (fun _ : Fin 1 => a1) X σvol ε μ)
    (hstat : IsStrictlyStationary X μ) (hL4 : ∀ t, MemLp (X t) 4 μ)
    (hb1 : 0 < b1) (ha1 : 0 ≤ a1) (hsum : b1 + a1 < 1)
    -- USER-INPUT: nondegenerate denominator; FY eq. (4.30)
    (hden : 1 - a1 ^ 2 - 2 * a1 * b1 ≠ 0)
    (hvar : 0 < variance (fun ω => X 0 ω ^ 2) μ) {k : ℕ} (hk : 1 ≤ k) :
    acf (fun t ω => X t ω ^ 2) μ (k : ℤ)
      = ((1 - a1 ^ 2 - a1 * b1) * b1 / (1 - a1 ^ 2 - 2 * a1 * b1))
        * (b1 + a1) ^ (k - 1) := by
  sorry

/-! ### Nelson's strict-stationarity criterion (commissioned proof target) -/

/-! #### The random-product volatility series

The construction is packaged as a fixed measurable functional of the *innovation path*, so
that strict stationarity is a transport along the shift-invariance of the path law — the
pattern of `Stationarity/ARCH.lean`. Everything is nonnegative, so the series lives in
`ℝ≥0∞` and no summability side condition is carried through the definitions. -/

/-- The innovation path seen from time `t`. -/
private def nelPath (ε : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℤ → ℝ := fun s => ε (s + t) ω

/-- The random product `∏_{i<k}(b₁ p(−1−i)² + a₁)` read off a path `p`, in `ℝ≥0∞`. -/
private noncomputable def nelProd (b1 a1 : ℝ) (k : ℕ) (p : ℤ → ℝ) : ENNReal :=
  ∏ i ∈ Finset.range k, ENNReal.ofReal (b1 * p (-1 - (i : ℤ)) ^ 2 + a1)

/-- Nelson's random-product series `Σ_{k ≥ 0} ∏_{i<k}(b₁ p(−1−i)² + a₁)`. -/
private noncomputable def nelW (b1 a1 : ℝ) (p : ℤ → ℝ) : ENNReal :=
  ∑' k : ℕ, nelProd b1 a1 k p

/-- The squared volatility `σ² = c₀ Σ_k ∏_{i<k}(b₁ε² + a₁)` as a path functional. -/
private noncomputable def nelV (c0 b1 a1 : ℝ) (p : ℤ → ℝ) : ℝ :=
  (ENNReal.ofReal c0 * nelW b1 a1 p).toReal

/-- The solution `X_t = σ_t ε_t` as a functional of the innovation path. -/
private noncomputable def nelXf (c0 b1 a1 : ℝ) (p : ℤ → ℝ) : ℝ :=
  Real.sqrt (nelV c0 b1 a1 p) * p 0

omit [MeasurableSpace Ω] in
private lemma nelPath_sub (ε : ℤ → Ω → ℝ) (t c : ℤ) (ω : Ω) :
    (fun s => nelPath ε t ω (s - c)) = nelPath ε (t - c) ω := by
  funext s; simp only [nelPath]; congr 1; ring

omit [MeasurableSpace Ω] in
private lemma nelPath_add (ε : ℤ → Ω → ℝ) (t c : ℤ) (ω : Ω) :
    (fun s => nelPath ε t ω (s + c)) = nelPath ε (t + c) ω := by
  funext s; simp only [nelPath]; congr 1; ring

private lemma measurable_nelProd (b1 a1 : ℝ) (k : ℕ) : Measurable (nelProd b1 a1 k) := by
  refine Finset.measurable_prod _ fun i _ => Measurable.ennreal_ofReal ?_
  fun_prop

private lemma measurable_nelW (b1 a1 : ℝ) : Measurable (nelW b1 a1) :=
  Measurable.ennreal_tsum fun k => measurable_nelProd b1 a1 k

private lemma measurable_nelV (c0 b1 a1 : ℝ) : Measurable (nelV c0 b1 a1) :=
  (measurable_const.mul (measurable_nelW b1 a1)).ennreal_toReal

private lemma measurable_nelXf (c0 b1 a1 : ℝ) : Measurable (nelXf c0 b1 a1) :=
  (measurable_nelV c0 b1 a1).sqrt.mul (measurable_pi_apply 0)

private lemma measurable_nelPath {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t)) (t : ℤ) :
    Measurable (nelPath ε t) :=
  measurable_pi_lambda _ fun s => hm (s + t)

private lemma nelProd_ne_top (b1 a1 : ℝ) (k : ℕ) (p : ℤ → ℝ) : nelProd b1 a1 k p ≠ ⊤ := by
  refine (ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top).ne

/-- Peeling the first factor off the random product. -/
private lemma nelProd_succ (b1 a1 : ℝ) (k : ℕ) (p : ℤ → ℝ) :
    nelProd b1 a1 (k + 1) p
      = ENNReal.ofReal (b1 * p (-1) ^ 2 + a1) * nelProd b1 a1 k (fun s => p (s - 1)) := by
  simp only [nelProd]
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast
  ring_nf

/-- Peeling the empty product off the series: one step of Nelson's recursion. -/
private lemma nelW_succ (b1 a1 : ℝ) (p : ℤ → ℝ) :
    nelW b1 a1 p
      = 1 + ENNReal.ofReal (b1 * p (-1) ^ 2 + a1) * nelW b1 a1 (fun s => p (s - 1)) := by
  have h0 : nelProd b1 a1 0 p = 1 := by simp [nelProd]
  rw [nelW, tsum_eq_zero_add' ENNReal.summable, h0]
  congr 1
  simp only [nelProd_succ, nelW]
  exact ENNReal.tsum_mul_left

private lemma ennreal_tsum_split (f : ℕ → ENNReal) (N : ℕ) :
    ∑' i : ℕ, f i = (∑ i ∈ Finset.range N, f i) + ∑' i : ℕ, f (i + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ,
      tsum_eq_zero_add' (f := fun i : ℕ => f (i + N)) ENNReal.summable, ← add_assoc]
    simp only [Nat.zero_add]
    congr 1
    exact tsum_congr fun i => congrArg f (by omega)

private lemma self_le_exp_log {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.exp (Real.log x) := by
  rcases hx.lt_or_eq with h | h
  · rw [Real.exp_log h]
  · rw [← h]; positivity

/-- **Pathwise convergence criterion.** Let `g` dominate the multipliers in the sense
`b₁x² + a₁ ≤ exp (g x)`. If the running `g`-averages along the path converge to a negative
limit, Nelson's random-product series converges: the partial products are dominated by a
geometric sequence. Taking `g x = log (b₁x² + a₁)` gives Nelson's own criterion (the
junk value `Real.log 0 = 0` only weakens the domination, so vanishing multipliers are
harmless); a `g` that is more negative on the zero set covers the degenerate case where
`E log(b₁ε² + a₁)` is not negative. -/
private lemma nelW_ne_top_of_tendsto {b1 a1 c : ℝ} {p : ℤ → ℝ} {g : ℝ → ℝ}
    (hb1 : 0 ≤ b1) (ha1 : 0 ≤ a1) (hdom : ∀ x : ℝ, b1 * x ^ 2 + a1 ≤ Real.exp (g x))
    (hc : c < 0)
    (h : Filter.Tendsto
      (fun k : ℕ => (∑ i ∈ Finset.range k, g (p (-1 - (i : ℤ)))) / k)
      Filter.atTop (nhds c)) :
    nelW b1 a1 p ≠ ⊤ := by
  have hmnn : ∀ i : ℕ, 0 ≤ b1 * p (-1 - (i : ℤ)) ^ 2 + a1 :=
    fun i => add_nonneg (mul_nonneg hb1 (sq_nonneg _)) ha1
  have hr0 : (0 : ℝ) < Real.exp (c / 2) := Real.exp_pos _
  have hr1 : Real.exp (c / 2) < 1 := by
    have : Real.exp (c / 2) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
    simpa using this
  -- the partial products are bounded by the exponential of the log-partial-sums
  have hbound : ∀ k : ℕ, nelProd b1 a1 k p
      ≤ ENNReal.ofReal
          (Real.exp (∑ i ∈ Finset.range k, g (p (-1 - (i : ℤ))))) := by
    intro k
    have h1 : nelProd b1 a1 k p
        = ENNReal.ofReal (∏ i ∈ Finset.range k, (b1 * p (-1 - (i : ℤ)) ^ 2 + a1)) := by
      rw [nelProd, ENNReal.ofReal_prod_of_nonneg fun i _ => hmnn i]
    rw [h1]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => hmnn i) fun i _ => hdom (p (-1 - (i : ℤ)))
  -- past a threshold, the log-partial-sums drop below `k · c/2`
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
    (Filter.Tendsto.eventually_lt_const (show c < c / 2 by linarith) h)
  have hgeom : ∀ k : ℕ, max K 1 ≤ k →
      nelProd b1 a1 k p ≤ ENNReal.ofReal (Real.exp (c / 2)) ^ k := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans (le_max_right K 1) hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hlt := hK k (le_trans (le_max_left K 1) hk)
    rw [div_lt_iff₀ hkpos] at hlt
    have hS : (∑ i ∈ Finset.range k, g (p (-1 - (i : ℤ))))
        ≤ (k : ℝ) * (c / 2) := by
      have := mul_comm (c / 2) ((k : ℕ) : ℝ)
      linarith
    calc nelProd b1 a1 k p ≤ _ := hbound k
      _ ≤ ENNReal.ofReal (Real.exp (c / 2) ^ k) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Real.exp_nat_mul]
          exact Real.exp_le_exp.2 hS
      _ = ENNReal.ofReal (Real.exp (c / 2)) ^ k := by rw [ENNReal.ofReal_pow hr0.le]
  -- split off the finitely many initial terms and dominate the rest geometrically
  have hsplit : nelW b1 a1 p
      = (∑ i ∈ Finset.range (max K 1), nelProd b1 a1 i p)
        + ∑' i : ℕ, nelProd b1 a1 (i + max K 1) p :=
    ennreal_tsum_split (fun k => nelProd b1 a1 k p) (max K 1)
  rw [hsplit]
  have hfin1 : (∑ i ∈ Finset.range (max K 1), nelProd b1 a1 i p) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun i _ => nelProd_ne_top b1 a1 i p
  have hgeo : (∑' i : ℕ, ENNReal.ofReal (Real.exp (c / 2)) ^ (i + max K 1))
      = (1 - ENNReal.ofReal (Real.exp (c / 2)))⁻¹
        * ENNReal.ofReal (Real.exp (c / 2)) ^ max K 1 := by
    simp only [pow_add]
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  have hfin2 : (∑' i : ℕ, ENNReal.ofReal (Real.exp (c / 2)) ^ (i + max K 1)) ≠ ⊤ := by
    rw [hgeo]
    exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.2 (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hr1)).ne')
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have htail : (∑' i : ℕ, nelProd b1 a1 (i + max K 1) p)
      ≤ ∑' i : ℕ, ENNReal.ofReal (Real.exp (c / 2)) ^ (i + max K 1) :=
    ENNReal.tsum_le_tsum fun i => hgeom _ (Nat.le_add_left _ _)
  exact ENNReal.add_ne_top.2 ⟨hfin1, ne_top_of_le_ne_top hfin2 htail⟩

/-- **The engine of Nelson's theorem**: by the i.i.d. strong law of large numbers the
`g`-averages of the innovations converge to `E g(ε₀) < 0`, so the random-product series
converges almost surely — with *no* moment condition on the innovations. -/
private lemma nelW_ae_ne_top [IsProbabilityMeasure μ] {b1 a1 : ℝ} {ε : ℤ → Ω → ℝ}
    {g : ℝ → ℝ} (hb1 : 0 ≤ b1) (ha1 : 0 ≤ a1) (hgm : Measurable g)
    (hdom : ∀ x : ℝ, b1 * x ^ 2 + a1 ≤ Real.exp (g x)) (hε : IsIIDNoise ε 1 μ)
    (hgint : Integrable (fun ω => g (ε 0 ω)) μ)
    (hneg : (∫ ω, g (ε 0 ω) ∂μ) < 0) (t : ℤ) :
    ∀ᵐ ω ∂μ, nelW b1 a1 (nelPath ε t ω) ≠ ⊤ := by
  have hid : ∀ i : ℕ,
      IdentDistrib (fun ω => g (ε (t - 1 - (i : ℕ)) ω))
        (fun ω => g (ε (t - 1 - ((0 : ℕ) : ℤ)) ω)) μ μ :=
    fun i => (hε.identDistrib (t - 1 - (i : ℕ)) (t - 1 - ((0 : ℕ) : ℤ))).comp hgm
  have hindep : ∀ i j : ℕ, i ≠ j →
      IndepFun (fun ω => g (ε (t - 1 - (i : ℕ)) ω))
        (fun ω => g (ε (t - 1 - (j : ℕ)) ω)) μ := by
    intro i j hij
    have hne : t - 1 - (i : ℕ) ≠ t - 1 - (j : ℕ) := by
      intro hEq
      rw [sub_right_inj, Nat.cast_inj] at hEq
      exact hij hEq
    exact (hε.iIndep.indepFun hne).comp hgm hgm
  have hid0 : IdentDistrib (fun ω => g (ε 0 ω))
      (fun ω => g (ε (t - 1 - ((0 : ℕ) : ℤ)) ω)) μ μ :=
    (hε.identDistrib 0 (t - 1 - ((0 : ℕ) : ℤ))).comp hgm
  have hint0 : Integrable (fun ω => g (ε (t - 1 - ((0 : ℕ) : ℤ)) ω)) μ :=
    hid0.integrable_snd hgint
  have hmean0 : (∫ ω, g (ε (t - 1 - ((0 : ℕ) : ℤ)) ω) ∂μ) < 0 := by
    rw [← hid0.integral_eq]; exact hneg
  have hslln := ProbabilityTheory.strong_law_ae_real
    (fun (i : ℕ) ω => g (ε (t - 1 - (i : ℕ)) ω)) hint0
    (fun i j hij => hindep i j hij) hid
  filter_upwards [hslln] with ω hω
  have hp : ∀ i : ℕ, nelPath ε t ω (-1 - (i : ℤ)) = ε (t - 1 - (i : ℕ)) ω := by
    intro i; simp only [nelPath]; congr 1; ring
  refine nelW_ne_top_of_tendsto hb1 ha1 hdom hmean0 ?_
  simpa only [hp] using hω

private lemma nelV_nonneg (c0 b1 a1 : ℝ) (p : ℤ → ℝ) : 0 ≤ nelV c0 b1 a1 p :=
  ENNReal.toReal_nonneg

/-- Nelson's one-step recursion `σ_t² = c₀ + (b₁ε_{t−1}² + a₁)σ_{t−1}²`, valid pointwise
wherever the series converges. -/
private lemma nelV_rec {c0 b1 a1 : ℝ} (hc0 : 0 ≤ c0) (hb1 : 0 ≤ b1) (ha1 : 0 ≤ a1)
    {p : ℤ → ℝ} (h2 : nelW b1 a1 (fun s => p (s - 1)) ≠ ⊤) :
    nelV c0 b1 a1 p = c0 + (b1 * p (-1) ^ 2 + a1) * nelV c0 b1 a1 (fun s => p (s - 1)) := by
  have hm : 0 ≤ b1 * p (-1) ^ 2 + a1 := add_nonneg (mul_nonneg hb1 (sq_nonneg _)) ha1
  have hfin : ENNReal.ofReal (b1 * p (-1) ^ 2 + a1)
      * (ENNReal.ofReal c0 * nelW b1 a1 (fun s => p (s - 1))) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2)
  have hkey : ENNReal.ofReal c0 * nelW b1 a1 p
      = ENNReal.ofReal c0
        + ENNReal.ofReal (b1 * p (-1) ^ 2 + a1)
          * (ENNReal.ofReal c0 * nelW b1 a1 (fun s => p (s - 1))) := by
    rw [nelW_succ]; ring
  simp only [nelV]
  rw [hkey, ENNReal.toReal_add ENNReal.ofReal_ne_top hfin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc0, ENNReal.toReal_ofReal hm]

/-- Splitting the random product at depth `N`. -/
private lemma nelProd_add (b1 a1 : ℝ) (N j : ℕ) (p : ℤ → ℝ) :
    nelProd b1 a1 (N + j) p
      = nelProd b1 a1 N p * nelProd b1 a1 j (fun s => p (s - (N : ℤ))) := by
  simp only [nelProd]
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have h : ((-1 : ℤ) - ((N + i : ℕ) : ℤ)) = -1 - (i : ℤ) - (N : ℤ) := by push_cast; ring
  rw [h]

/-- `∏_{i<N} M_{t−1−i} · Σ_k ∏_{i<k} M_{t−N−1−i} = Σ_{k ≥ N} ∏_{i<k} M_{t−1−i}` — the
identity behind the pointwise decay of the remainder `a₁^N σ²_{t−N}`. -/
private lemma nelProd_mul_nelW (b1 a1 : ℝ) (N : ℕ) (p : ℤ → ℝ) :
    nelProd b1 a1 N p * nelW b1 a1 (fun s => p (s - (N : ℤ)))
      = ∑' j : ℕ, nelProd b1 a1 (N + j) p := by
  rw [nelW, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun j => (nelProd_add b1 a1 N j p).symm

/-- Each multiplier dominates `a₁`, so the random product dominates `a₁^N`. -/
private lemma ofReal_pow_le_nelProd {b1 a1 : ℝ} (hb1 : 0 ≤ b1) (ha1 : 0 ≤ a1) (N : ℕ)
    (p : ℤ → ℝ) : ENNReal.ofReal (a1 ^ N) ≤ nelProd b1 a1 N p := by
  have h1 : ENNReal.ofReal a1 ^ N = ∏ _i ∈ Finset.range N, ENNReal.ofReal a1 := by
    rw [Finset.prod_const, Finset.card_range]
  rw [ENNReal.ofReal_pow ha1, h1, nelProd]
  refine Finset.prod_le_prod' fun i _ => ENNReal.ofReal_le_ofReal ?_
  have := mul_nonneg hb1 (sq_nonneg (p (-1 - (i : ℤ))))
  linarith

/-! #### σ-algebra bookkeeping (local copies of the `Stationarity/ARCH.lean` bricks) -/

private lemma indep_last_sigmaLT {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t))
    (hi : iIndepFun ε μ) (t : ℤ) :
    Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT ε t) μ := by
  have hdisj : Disjoint ({t} : Set ℤ) (Set.Iio t) :=
    Set.disjoint_singleton_left.2 (by simp)
  have := indep_iSup_of_disjoint
    (m := fun s : ℤ => MeasurableSpace.comap (ε s) inferInstance)
    (fun s => (hm s).comap_le) hi hdisj
  simpa using this

omit [MeasurableSpace Ω] in
/-- The random product at time `s ≤ t`, as a function of the strict past of time `t`. -/
private lemma measurable_nelProd_sigmaLT {ε : ℤ → Ω → ℝ} (b1 a1 : ℝ) (k : ℕ) {s t : ℤ}
    (hst : s ≤ t) : Measurable[sigmaLT ε t] fun ω => nelProd b1 a1 k (nelPath ε s ω) := by
  simp only [nelProd]
  refine Finset.measurable_prod _ fun i _ => Measurable.ennreal_ofReal ?_
  have hlt : s - 1 - (i : ℕ) < t := by
    have : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    omega
  have hfun : (fun ω => b1 * nelPath ε s ω (-1 - (i : ℤ)) ^ 2 + a1)
      = fun ω => b1 * ε (s - 1 - (i : ℕ)) ω ^ 2 + a1 := by
    funext ω
    have h : nelPath ε s ω (-1 - (i : ℤ)) = ε (s - 1 - (i : ℕ)) ω := by
      simp only [nelPath]; congr 1; ring
    rw [h]
  rw [hfun]
  exact (((measurable_of_lt_sigmaLT hlt).pow_const 2).const_mul b1).add_const a1

omit [MeasurableSpace Ω] in
private lemma measurable_nelV_sigmaLT {ε : ℤ → Ω → ℝ} (c0 b1 a1 : ℝ) {s t : ℤ} (hst : s ≤ t) :
    Measurable[sigmaLT ε t] fun ω => nelV c0 b1 a1 (nelPath ε s ω) := by
  simp only [nelV, nelW]
  exact Measurable.ennreal_toReal (measurable_const.mul
    (Measurable.ennreal_tsum fun k => measurable_nelProd_sigmaLT b1 a1 k hst))

omit [MeasurableSpace Ω] in
private lemma measurable_nelXf_sigmaLT {ε : ℤ → Ω → ℝ} (c0 b1 a1 : ℝ) {s t : ℤ} (hst : s < t) :
    Measurable[sigmaLT ε t] fun ω => nelXf c0 b1 a1 (nelPath ε s ω) := by
  simp only [nelXf]
  have h0 : (fun ω => nelPath ε s ω 0) = ε s := by
    funext ω; simp only [nelPath]; congr 1; ring
  refine Measurable.mul ((measurable_nelV_sigmaLT c0 b1 a1 hst.le).sqrt) ?_
  rw [h0]
  exact measurable_of_lt_sigmaLT hst

/-! #### Shift-invariance of the innovation path law -/

private lemma map_nelPath [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hi : iIndepFun ε μ)
    (hid : ∀ s t, IdentDistrib (ε s) (ε t) μ μ) (t t' : ℤ) :
    μ.map (nelPath ε t) = μ.map (nelPath ε t') := by
  have hinj : ∀ c : ℤ, Function.Injective fun s : ℤ => s + c :=
    fun c x y h => by simpa using h
  have h1 : iIndepFun (fun s : ℤ => ε (s + t)) μ := hi.precomp (hinj t)
  have h2 : iIndepFun (fun s : ℤ => ε (s + t')) μ := hi.precomp (hinj t')
  have e1 : (nelPath ε t) = fun ω (s : ℤ) => ε (s + t) ω := rfl
  have e2 : (nelPath ε t') = fun ω (s : ℤ) => ε (s + t') ω := rfl
  rw [e1, e2, (iIndepFun_iff_map_fun_eq_infinitePi_map fun s => hm (s + t)).1 h1,
    (iIndepFun_iff_map_fun_eq_infinitePi_map fun s => hm (s + t')).1 h2]
  exact congrArg Measure.infinitePi (funext fun s => (hid (s + t) (s + t')).map_eq)

private lemma map_comp_nelPath [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {β : Type*}
    [MeasurableSpace β] (hm : ∀ t, Measurable (ε t)) (hi : iIndepFun ε μ)
    (hid : ∀ s t, IdentDistrib (ε s) (ε t) μ μ) {F : (ℤ → ℝ) → β} (hF : Measurable F)
    (t t' : ℤ) :
    (μ.map fun ω => F (nelPath ε t ω)) = μ.map fun ω => F (nelPath ε t' ω) := by
  have e1 : (fun ω => F (nelPath ε t ω)) = F ∘ nelPath ε t := rfl
  have e2 : (fun ω => F (nelPath ε t' ω)) = F ∘ nelPath ε t' := rfl
  rw [e1, e2, ← Measure.map_map hF (measurable_nelPath hm t),
    ← Measure.map_map hF (measurable_nelPath hm t'), map_nelPath hm hi hid t t']

/-- **Strict stationarity of the constructed process**: it is a fixed measurable
functional of the shifted innovation path. -/
private lemma isStrictlyStationary_nelX [IsProbabilityMeasure μ] {c0 b1 a1 : ℝ}
    {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t)) (hi : iIndepFun ε μ)
    (hid : ∀ s t, IdentDistrib (ε s) (ε t) μ μ) :
    IsStrictlyStationary (fun t ω => nelXf c0 b1 a1 (nelPath ε t ω)) μ := by
  intro n tt k
  set Ψ : (ℤ → ℝ) → (Fin n → ℝ) :=
    fun p i => nelXf c0 b1 a1 fun s => p (s + tt i) with hΨ
  have hΨm : Measurable Ψ :=
    measurable_pi_lambda _ fun i => (measurable_nelXf c0 b1 a1).comp
      (measurable_pi_lambda _ fun s => measurable_pi_apply (s + tt i))
  have hfac : ∀ c : ℤ, (fun ω (i : Fin n) => nelXf c0 b1 a1 (nelPath ε (tt i + c) ω))
      = fun ω => Ψ (nelPath ε c ω) := by
    intro c
    funext ω i
    simp only [hΨ]
    congr 1
    funext s
    simp only [nelPath]
    congr 1
    ring
  have hz : (fun ω (i : Fin n) => nelXf c0 b1 a1 (nelPath ε (tt i) ω))
      = fun ω => Ψ (nelPath ε 0 ω) := by
    have := hfac 0
    simpa using this
  rw [hfac k, hz]
  exact map_comp_nelPath hm hi hid hΨm k 0

/-! #### The ARCH(∞) form of the volatility, read off the *observation* path -/

private noncomputable def nelT (b1 a1 : ℝ) (q : ℤ → ℝ) : ENNReal :=
  ∑' k : ℕ, ENNReal.ofReal (b1 * a1 ^ k * q (-1 - (k : ℤ)) ^ 2)

/-- FY eq. (4.29): `σ_t² = c₀/(1−a₁) + b₁ Σ_{k≥0} a₁^k X_{t−1−k}²`. Reading the volatility
off the *observation* path is what makes it measurable for the strict past of `X` — the
`adapted` field of `IsGARCH`. -/
private noncomputable def nelU (c0 b1 a1 : ℝ) (q : ℤ → ℝ) : ℝ :=
  (ENNReal.ofReal (c0 / (1 - a1)) + nelT b1 a1 q).toReal

private lemma measurable_nelT (b1 a1 : ℝ) : Measurable (nelT b1 a1) := by
  refine Measurable.ennreal_tsum fun k => Measurable.ennreal_ofReal ?_
  fun_prop

private lemma measurable_nelU (c0 b1 a1 : ℝ) : Measurable (nelU c0 b1 a1) :=
  (measurable_const.add (measurable_nelT b1 a1)).ennreal_toReal

private lemma nelU_nonneg (c0 b1 a1 : ℝ) (q : ℤ → ℝ) : 0 ≤ nelU c0 b1 a1 q :=
  ENNReal.toReal_nonneg

omit [MeasurableSpace Ω] in
private lemma measurable_nelT_sigmaLT {X : ℤ → Ω → ℝ} (b1 a1 : ℝ) (t : ℤ) :
    Measurable[sigmaLT X t] fun ω => nelT b1 a1 (nelPath X t ω) := by
  simp only [nelT]
  refine Measurable.ennreal_tsum fun k => Measurable.ennreal_ofReal ?_
  have hlt : t - 1 - (k : ℕ) < t := by
    have : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    omega
  have hfun : (fun ω => b1 * a1 ^ k * nelPath X t ω (-1 - (k : ℤ)) ^ 2)
      = fun ω => b1 * a1 ^ k * X (t - 1 - (k : ℕ)) ω ^ 2 := by
    funext ω
    have h : nelPath X t ω (-1 - (k : ℤ)) = X (t - 1 - (k : ℕ)) ω := by
      simp only [nelPath]; congr 1; ring
    rw [h]
  rw [hfun]
  exact ((measurable_of_lt_sigmaLT hlt).pow_const 2).const_mul (b1 * a1 ^ k)

omit [MeasurableSpace Ω] in
private lemma measurable_nelU_sigmaLT {X : ℤ → Ω → ℝ} (c0 b1 a1 : ℝ) (t : ℤ) :
    Measurable[sigmaLT X t] fun ω => nelU c0 b1 a1 (nelPath X t ω) :=
  Measurable.ennreal_toReal (measurable_const.add (measurable_nelT_sigmaLT b1 a1 t))

omit [MeasurableSpace Ω] in
/-- The GARCH(1,1) volatility recursion `σ_t² = c₀ + b₁X_{t−1}² + a₁σ_{t−1}²` for the
constructed pair, pointwise wherever the random-product series converges. -/
private lemma nelV_rec_proc {c0 b1 a1 : ℝ} (hc0 : 0 ≤ c0) (hb1 : 0 ≤ b1) (ha1 : 0 ≤ a1)
    {ε X : ℤ → Ω → ℝ} {ω : Ω}
    (hX : ∀ s : ℤ, X s ω = nelXf c0 b1 a1 (nelPath ε s ω))
    (hfin : ∀ s : ℤ, nelW b1 a1 (nelPath ε s ω) ≠ ⊤) (s : ℤ) :
    nelV c0 b1 a1 (nelPath ε s ω)
      = c0 + b1 * X (s - 1) ω ^ 2 + a1 * nelV c0 b1 a1 (nelPath ε (s - 1) ω) := by
  have hX2 : X (s - 1) ω ^ 2
      = nelV c0 b1 a1 (nelPath ε (s - 1) ω) * ε (s - 1) ω ^ 2 := by
    rw [hX (s - 1)]
    simp only [nelXf]
    have h0 : nelPath ε (s - 1) ω 0 = ε (s - 1) ω := by
      simp only [nelPath]; congr 1; ring
    rw [h0, mul_pow, Real.sq_sqrt (nelV_nonneg c0 b1 a1 _)]
  have hp1 : (fun u => nelPath ε s ω (u - 1)) = nelPath ε (s - 1) ω := nelPath_sub ε s 1 ω
  have h2 : nelW b1 a1 (fun u => nelPath ε s ω (u - 1)) ≠ ⊤ := by
    rw [hp1]; exact hfin (s - 1)
  have hnv := nelV_rec (c0 := c0) hc0 hb1 ha1 h2
  rw [hp1] at hnv
  have hm1 : nelPath ε s ω (-1) = ε (s - 1) ω := by
    simp only [nelPath]; congr 1; ring
  rw [hm1] at hnv
  rw [hnv, hX2]
  ring

omit [MeasurableSpace Ω] in
/-- **The ARCH(∞) form recovers Nelson's series** (FY eq. (4.29)). The proof is entirely
pathwise: iterating the volatility recursion `N` times leaves the remainder
`a₁^N σ²_{t−N}`, which is dominated by `c₀ Σ_{k ≥ N} ∏_{i<k} M_{t−1−i}` — the depth-`N`
tail of the (convergent) random-product series — because every multiplier dominates `a₁`.
So no moment condition and no identical-distribution argument is needed. -/
private lemma nelU_eq_nelV {c0 b1 a1 : ℝ} (hc0 : 0 ≤ c0) (hb1 : 0 ≤ b1) (ha1 : 0 ≤ a1)
    (ha1' : a1 < 1) {ε X : ℤ → Ω → ℝ} {ω : Ω}
    (hX : ∀ s : ℤ, X s ω = nelXf c0 b1 a1 (nelPath ε s ω))
    (hfin : ∀ s : ℤ, nelW b1 a1 (nelPath ε s ω) ≠ ⊤) (t : ℤ) :
    nelU c0 b1 a1 (nelPath X t ω) = nelV c0 b1 a1 (nelPath ε t ω) := by
  obtain ⟨V, hVdef⟩ : ∃ V : ℤ → ℝ, ∀ s, V s = nelV c0 b1 a1 (nelPath ε s ω) :=
    ⟨_, fun _ => rfl⟩
  have hVnn : ∀ s, 0 ≤ V s := fun s => by rw [hVdef]; exact nelV_nonneg _ _ _ _
  -- the one-step recursion
  have hrec : ∀ s : ℤ, V s = c0 + b1 * X (s - 1) ω ^ 2 + a1 * V (s - 1) := by
    intro s
    rw [hVdef s, hVdef (s - 1)]
    exact nelV_rec_proc hc0 hb1 ha1 hX hfin s
  -- iterating the recursion `N` times
  have hiter : ∀ (N : ℕ) (s : ℤ), V s = c0 * (∑ k ∈ Finset.range N, a1 ^ k)
      + (∑ k ∈ Finset.range N, b1 * a1 ^ k * X (s - 1 - (k : ℕ)) ω ^ 2)
      + a1 ^ N * V (s - (N : ℕ)) := by
    intro N
    induction N with
    | zero => intro s; simp
    | succ N ih =>
      intro s
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h1 := ih s
      have h2 := hrec (s - (N : ℕ))
      have hcast1 : s - (N : ℕ) - 1 = s - 1 - (N : ℕ) := by ring
      have hcast2 : s - ((N + 1 : ℕ) : ℤ) = s - (N : ℕ) - 1 := by push_cast; ring
      rw [hcast1] at h2
      rw [hcast2, h1, h2]
      ring_nf
  -- the remainder is dominated by the tail of the random-product series
  have htail : ∀ N : ℕ, a1 ^ N * V (t - (N : ℕ))
      ≤ c0 * ∑' j : ℕ, (nelProd b1 a1 (j + N) (nelPath ε t ω)).toReal := by
    intro N
    have hpN : (fun u => nelPath ε t ω (u - (N : ℤ))) = nelPath ε (t - (N : ℕ)) ω :=
      nelPath_sub ε t (N : ℤ) ω
    have hsplit : (∑' j : ℕ, nelProd b1 a1 (N + j) (nelPath ε t ω))
        = nelProd b1 a1 N (nelPath ε t ω) * nelW b1 a1 (nelPath ε (t - (N : ℕ)) ω) := by
      rw [← nelProd_mul_nelW b1 a1 N (nelPath ε t ω), hpN]
    have htne : (∑' j : ℕ, nelProd b1 a1 (N + j) (nelPath ε t ω)) ≠ ⊤ := by
      rw [hsplit]
      exact ENNReal.mul_ne_top (nelProd_ne_top _ _ _ _) (hfin _)
    have hfin2 : ENNReal.ofReal c0 * ∑' j : ℕ, nelProd b1 a1 (N + j) (nelPath ε t ω) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top htne
    have hle : ENNReal.ofReal (a1 ^ N)
          * (ENNReal.ofReal c0 * nelW b1 a1 (nelPath ε (t - (N : ℕ)) ω))
        ≤ ENNReal.ofReal c0 * ∑' j : ℕ, nelProd b1 a1 (N + j) (nelPath ε t ω) := by
      rw [hsplit]
      calc ENNReal.ofReal (a1 ^ N)
            * (ENNReal.ofReal c0 * nelW b1 a1 (nelPath ε (t - (N : ℕ)) ω))
          = ENNReal.ofReal c0 * (ENNReal.ofReal (a1 ^ N)
              * nelW b1 a1 (nelPath ε (t - (N : ℕ)) ω)) := by ring
        _ ≤ ENNReal.ofReal c0 * (nelProd b1 a1 N (nelPath ε t ω)
              * nelW b1 a1 (nelPath ε (t - (N : ℕ)) ω)) := by
            gcongr
            exact ofReal_pow_le_nelProd hb1 ha1 N (nelPath ε t ω)
    have hmono := ENNReal.toReal_mono hfin2 hle
    have hLHS : (ENNReal.ofReal (a1 ^ N)
        * (ENNReal.ofReal c0 * nelW b1 a1 (nelPath ε (t - (N : ℕ)) ω))).toReal
        = a1 ^ N * nelV c0 b1 a1 (nelPath ε (t - (N : ℕ)) ω) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ha1 N)]
      rfl
    have hRHS : (ENNReal.ofReal c0 * ∑' j : ℕ, nelProd b1 a1 (N + j) (nelPath ε t ω)).toReal
        = c0 * ∑' j : ℕ, (nelProd b1 a1 (j + N) (nelPath ε t ω)).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0,
        ENNReal.tsum_toReal_eq fun j => nelProd_ne_top b1 a1 (N + j) (nelPath ε t ω)]
      exact congrArg (fun z => c0 * z)
        (tsum_congr fun j => congrArg (fun m => (nelProd b1 a1 m (nelPath ε t ω)).toReal)
          (Nat.add_comm N j))
    rw [hVdef, ← hLHS, ← hRHS]
    exact hmono
  -- hence the remainder vanishes
  have hzero : Filter.Tendsto (fun N : ℕ => a1 ^ N * V (t - (N : ℕ))) Filter.atTop (nhds 0) := by
    have h1 := tendsto_sum_nat_add fun k : ℕ => (nelProd b1 a1 k (nelPath ε t ω)).toReal
    have h2 := h1.const_mul c0
    rw [mul_zero] at h2
    exact squeeze_zero (fun N => mul_nonneg (pow_nonneg ha1 N) (hVnn _)) htail h2
  -- the geometric part
  have hgeo : Filter.Tendsto (fun N : ℕ => c0 * ∑ k ∈ Finset.range N, a1 ^ k) Filter.atTop
      (nhds (c0 / (1 - a1))) := by
    have hg := (hasSum_geometric_of_lt_one ha1 ha1').tendsto_sum_nat
    have := hg.const_mul c0
    rwa [← div_eq_mul_inv] at this
  -- so the ARCH(∞) partial sums converge
  have hfnn : ∀ k : ℕ, 0 ≤ b1 * a1 ^ k * X (t - 1 - (k : ℕ)) ω ^ 2 :=
    fun k => mul_nonneg (mul_nonneg hb1 (pow_nonneg ha1 k)) (sq_nonneg _)
  have hEq : ∀ N : ℕ, (∑ k ∈ Finset.range N, b1 * a1 ^ k * X (t - 1 - (k : ℕ)) ω ^ 2)
      = V t - c0 * (∑ k ∈ Finset.range N, a1 ^ k) - a1 ^ N * V (t - (N : ℕ)) := by
    intro N
    have := hiter N t
    linarith
  have hS : Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N, b1 * a1 ^ k * X (t - 1 - (k : ℕ)) ω ^ 2)
      Filter.atTop (nhds (V t - c0 / (1 - a1))) := by
    simp only [hEq]
    have h3 := ((tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => V t) Filter.atTop (nhds (V t))).sub hgeo).sub hzero
    rwa [sub_zero] at h3
  have hsummable : Summable fun k : ℕ => b1 * a1 ^ k * X (t - 1 - (k : ℕ)) ω ^ 2 := by
    refine summable_of_sum_range_le (c := V t) hfnn fun N => ?_
    have h1 : 0 ≤ c0 * (∑ k ∈ Finset.range N, a1 ^ k) :=
      mul_nonneg hc0 (Finset.sum_nonneg fun k _ => pow_nonneg ha1 k)
    have h2 : 0 ≤ a1 ^ N * V (t - (N : ℕ)) := mul_nonneg (pow_nonneg ha1 N) (hVnn _)
    have := hEq N
    linarith
  have hhas : HasSum (fun k : ℕ => b1 * a1 ^ k * X (t - 1 - (k : ℕ)) ω ^ 2)
      (V t - c0 / (1 - a1)) := hsummable.hasSum_iff_tendsto_nat.2 hS
  have hL : 0 ≤ V t - c0 / (1 - a1) :=
    ge_of_tendsto hS (Filter.Eventually.of_forall fun N =>
      Finset.sum_nonneg fun k _ => hfnn k)
  -- assemble
  have hq : ∀ k : ℕ, nelPath X t ω (-1 - (k : ℤ)) = X (t - 1 - (k : ℕ)) ω := by
    intro k; simp only [nelPath]; congr 1; ring
  have hnelT : nelT b1 a1 (nelPath X t ω) = ENNReal.ofReal (V t - c0 / (1 - a1)) := by
    simp only [nelT, hq]
    rw [← ENNReal.ofReal_tsum_of_nonneg hfnn hsummable, hhas.tsum_eq]
  have hc0d : 0 ≤ c0 / (1 - a1) := div_nonneg hc0 (by linarith)
  rw [← hVdef t]
  simp only [nelU, hnelT]
  rw [← ENNReal.ofReal_add hc0d hL, ENNReal.toReal_ofReal (by linarith [hVnn t])]
  ring

/-- **The construction.** Given only the almost-sure convergence of the random-product
series, the pair `X_t = σ_t ε_t` with `σ_t² = c₀/(1−a₁) + b₁ Σ_k a₁^k X_{t−1−k}²` solves
the GARCH(1,1) equations and is strictly stationary. -/
private lemma exists_garch_of_nelW_ae [IsProbabilityMeasure μ] {c0 b1 a1 : ℝ}
    {ε : ℤ → Ω → ℝ} (hc0 : 0 ≤ c0) (hb1 : 0 ≤ b1) (ha1 : 0 ≤ a1) (ha1' : a1 < 1)
    (hε : IsIIDNoise ε 1 μ)
    (hconv : ∀ t : ℤ, ∀ᵐ ω ∂μ, nelW b1 a1 (nelPath ε t ω) ≠ ⊤) :
    ∃ X σvol : ℤ → Ω → ℝ,
      IsGARCH c0 (fun _ : Fin 1 => b1) (fun _ : Fin 1 => a1) X σvol ε μ ∧
        IsStrictlyStationary X μ := by
  obtain ⟨X, hX⟩ : ∃ X : ℤ → Ω → ℝ, ∀ t, X t = fun ω => nelXf c0 b1 a1 (nelPath ε t ω) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨σv, hσ⟩ : ∃ σv : ℤ → Ω → ℝ,
      ∀ t, σv t = fun ω => Real.sqrt (nelU c0 b1 a1 (nelPath X t ω)) := ⟨_, fun _ => rfl⟩
  have hXfun : X = fun t ω => nelXf c0 b1 a1 (nelPath ε t ω) := funext hX
  have hXpt : ∀ (s : ℤ) (ω : Ω), X s ω = nelXf c0 b1 a1 (nelPath ε s ω) :=
    fun s ω => congrFun (hX s) ω
  have hgood : ∀ᵐ ω ∂μ, ∀ s : ℤ, nelW b1 a1 (nelPath ε s ω) ≠ ⊤ := ae_all_iff.2 hconv
  have hmX : ∀ t, Measurable (X t) := fun t => by
    rw [hX t]; exact (measurable_nelXf c0 b1 a1).comp (measurable_nelPath hε.measurable t)
  have hmσ : ∀ t, Measurable (σv t) := fun t => by
    rw [hσ t]
    exact ((measurable_nelU c0 b1 a1).comp (measurable_nelPath hmX t)).sqrt
  have hUV : ∀ᵐ ω ∂μ, ∀ t : ℤ,
      nelU c0 b1 a1 (nelPath X t ω) = nelV c0 b1 a1 (nelPath ε t ω) := by
    filter_upwards [hgood] with ω hω t
    exact nelU_eq_nelV hc0 hb1 ha1 ha1' (fun s => hXpt s ω) hω t
  have hvolnn : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ σv t ω := fun t =>
    Filter.Eventually.of_forall fun ω => by simp only [hσ]; exact Real.sqrt_nonneg _
  have hadapt : ∀ t, Measurable[sigmaLT X t] (σv t) := fun t => by
    rw [hσ t]; exact (measurable_nelU_sigmaLT c0 b1 a1 t).sqrt
  have hpast : ∀ t : ℤ, Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT X t) μ := by
    intro t
    refine indep_of_indep_of_le_right (indep_last_sigmaLT hε.measurable hε.iIndep t) ?_
    refine iSup₂_le fun s hs => ?_
    have hms : Measurable[sigmaLT ε t] (X s) := by
      rw [hX s]; exact measurable_nelXf_sigmaLT c0 b1 a1 hs
    exact hms.comap_le
  have hrecX : ∀ t : ℤ, X t =ᵐ[μ] fun ω => σv t ω * ε t ω := by
    intro t
    filter_upwards [hUV] with ω hω
    simp only [hσ, hX, nelXf]
    have h0 : nelPath ε t ω 0 = ε t ω := by simp only [nelPath]; congr 1; ring
    rw [h0, hω t]
  have hrecVol : ∀ t : ℤ, (fun ω => σv t ω ^ 2) =ᵐ[μ] fun ω =>
      c0 + (∑ i : Fin 1, b1 * X (t - 1 - (i : ℕ)) ω ^ 2)
        + ∑ j : Fin 1, a1 * σv (t - 1 - (j : ℕ)) ω ^ 2 := by
    intro t
    filter_upwards [hgood, hUV] with ω hg hω
    have hsq : ∀ s : ℤ, σv s ω ^ 2 = nelV c0 b1 a1 (nelPath ε s ω) := by
      intro s
      simp only [hσ]
      rw [Real.sq_sqrt (nelU_nonneg _ _ _ _), hω s]
    simp only [Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, sub_zero, hsq]
    exact nelV_rec_proc hc0 hb1 ha1 (fun s => hXpt s ω) hg t
  refine ⟨X, σv, ⟨hc0, fun _ => hb1, fun _ => ha1, hmX, hmσ, hvolnn, hadapt, hε, hpast,
    hrecX, hrecVol⟩, ?_⟩
  rw [hXfun]
  exact isStrictlyStationary_nelX hε.measurable hε.iIndep hε.identDistrib

/-- **Nelson (1990), sufficiency — COMMISSIONED PROOF TARGET** (user, 2026-08-04):
if `E log(b₁ ε₀² + a₁) < 0` then the GARCH(1,1) equations admit a strictly stationary
solution, *with no moment condition on `ε`*. The volatility is the a.s.-convergent
random-product series `σ_t² = c₀ Σ_{k ≥ 0} ∏_{i < k} (b₁ ε_{t−1−i}² + a₁)`, whose
convergence comes from the iid strong law applied to the logs. -/
theorem exists_strictlyStationary_garch_one_one_nelson [IsProbabilityMeasure μ]
    {c0 b1 a1 : ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: nonnegative coefficients; FY Def 4.3
    (hc0 : 0 < c0) (hb1 : 0 < b1) (ha1 : 0 ≤ a1)
    -- USER-INPUT: iid(0,1) innovations; FY Def 4.3
    (hε : IsIIDNoise ε 1 μ)
    -- LEAN-ONLY: integrability of the log-multiplier (implicit in Nelson's E log < 0)
    (hlogint : Integrable (fun ω => Real.log (b1 * ε 0 ω ^ 2 + a1)) μ)
    -- USER-INPUT: Nelson's condition; Nelson 1990 Thm 2
    (hnelson : (∫ ω, Real.log (b1 * ε 0 ω ^ 2 + a1) ∂μ) < 0) :
    ∃ X σvol : ℤ → Ω → ℝ,
      IsGARCH c0 (fun _ : Fin 1 => b1) (fun _ : Fin 1 => a1) X σvol ε μ ∧
        IsStrictlyStationary X μ := by
  have hMnn : ∀ x : ℝ, 0 ≤ b1 * x ^ 2 + a1 := fun x =>
    add_nonneg (mul_nonneg hb1.le (sq_nonneg x)) ha1
  -- Nelson's condition already forces `a₁ < 1`: otherwise every multiplier is `≥ 1`.
  have ha1' : a1 < 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hnn : ∀ ω, 0 ≤ Real.log (b1 * ε 0 ω ^ 2 + a1) := by
      intro ω
      refine Real.log_nonneg ?_
      have := mul_nonneg hb1.le (sq_nonneg (ε 0 ω))
      linarith
    have := integral_nonneg (μ := μ)
      (f := fun ω => Real.log (b1 * ε 0 ω ^ 2 + a1)) hnn
    linarith
  refine exists_garch_of_nelW_ae hc0.le hb1.le ha1 ha1' hε fun t => ?_
  exact nelW_ae_ne_top (g := fun x => Real.log (b1 * x ^ 2 + a1)) hb1.le ha1 (by fun_prop)
    (fun x => self_le_exp_log (hMnn x)) hε hlogint hnelson t

/-- **IGARCH(1,1)** (the `(p,q) = (1,1)` case of FY eq. (4.33), the only case in scope):
when `b₁ + a₁ = 1` and `ε²` is nondegenerate, strict Jensen gives
`E log(b₁ε² + a₁) < log E(b₁ε² + a₁) = log 1 = 0`, so Nelson's criterion applies and a
strictly stationary IGARCH(1,1) solution exists — even though no stationary solution
with finite variance does (FY Theorem 4.4). -/
theorem exists_strictlyStationary_igarch_one_one [IsProbabilityMeasure μ]
    {c0 b1 a1 : ℝ} {ε : ℤ → Ω → ℝ}
    (hc0 : 0 < c0) (hb1 : 0 < b1) (ha1 : 0 ≤ a1)
    -- USER-INPUT: the integrated-GARCH boundary; FY eq. (4.33) at (p,q) = (1,1)
    (hunit : b1 + a1 = 1)
    (hε : IsIIDNoise ε 1 μ)
    (hlogint : Integrable (fun ω => Real.log (b1 * ε 0 ω ^ 2 + a1)) μ)
    -- USER-INPUT: nondegenerate innovations (needed for STRICT Jensen); Nelson 1990
    (hnondeg : ¬ (fun ω => ε 0 ω ^ 2) =ᵐ[μ] fun _ => (1 : ℝ)) :
    ∃ X σvol : ℤ → Ω → ℝ,
      IsGARCH c0 (fun _ : Fin 1 => b1) (fun _ : Fin 1 => a1) X σvol ε μ ∧
        IsStrictlyStationary X μ := by
  have ha1' : a1 < 1 := by linarith
  have hMnn : ∀ x : ℝ, 0 ≤ b1 * x ^ 2 + a1 := fun x =>
    add_nonneg (mul_nonneg hb1.le (sq_nonneg x)) ha1
  have hmM : Measurable fun ω => b1 * ε 0 ω ^ 2 + a1 :=
    (((hε.measurable 0).pow_const 2).const_mul b1).add_const a1
  by_cases hdeg : μ {ω | b1 * ε 0 ω ^ 2 + a1 = 0} = 0
  · -- **Nondegenerate case**: the multiplier is a.e. positive, so strict Jensen applies:
    -- `E log M < log E M = log 1 = 0`, i.e. exactly Nelson's condition.
    refine exists_strictlyStationary_garch_one_one_nelson hc0 hb1 ha1 hε hlogint ?_
    have hsqint : Integrable (fun ω => ε 0 ω ^ 2) μ := hε.memLp.integrable_sq
    have hEsq : (∫ ω, ε 0 ω ^ 2 ∂μ) = 1 := by
      have hv := variance_eq_sub (μ := μ) hε.memLp
      rw [hε.variance_eq, hε.integral_eq_zero] at hv
      simpa using hv.symm
    have hMint : Integrable (fun ω => b1 * ε 0 ω ^ 2 + a1) μ :=
      (hsqint.const_mul b1).add (integrable_const a1)
    have hEM : (∫ ω, (b1 * ε 0 ω ^ 2 + a1) ∂μ) = 1 := by
      rw [integral_add (hsqint.const_mul b1) (integrable_const a1), integral_const_mul, hEsq]
      simp [hunit]
    have hMpos : ∀ᵐ ω ∂μ, 0 < b1 * ε 0 ω ^ 2 + a1 := by
      have hne : ∀ᵐ ω ∂μ, ¬ (b1 * ε 0 ω ^ 2 + a1 = 0) := by
        rw [ae_iff]; simpa using hdeg
      filter_upwards [hne] with ω hω
      exact lt_of_le_of_ne (hMnn (ε 0 ω)) (Ne.symm hω)
    -- the Jensen gap `(M − 1) − log M` is nonnegative, and strictly positive off `{M = 1}`
    have hgapint : Integrable (fun ω =>
        (b1 * ε 0 ω ^ 2 + a1 - 1) - Real.log (b1 * ε 0 ω ^ 2 + a1)) μ :=
      (hMint.sub (integrable_const 1)).sub hlogint
    have hgap : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω =>
        (b1 * ε 0 ω ^ 2 + a1 - 1) - Real.log (b1 * ε 0 ω ^ 2 + a1) := by
      filter_upwards [hMpos] with ω hω
      have := Real.log_le_sub_one_of_pos hω
      simp only [Pi.zero_apply]
      linarith
    have hgapval : (∫ ω, ((b1 * ε 0 ω ^ 2 + a1 - 1)
          - Real.log (b1 * ε 0 ω ^ 2 + a1)) ∂μ)
        = - ∫ ω, Real.log (b1 * ε 0 ω ^ 2 + a1) ∂μ := by
      have h1 : (∫ ω, ((b1 * ε 0 ω ^ 2 + a1 - 1)
            - Real.log (b1 * ε 0 ω ^ 2 + a1)) ∂μ)
          = (∫ ω, (b1 * ε 0 ω ^ 2 + a1 - 1) ∂μ)
            - ∫ ω, Real.log (b1 * ε 0 ω ^ 2 + a1) ∂μ :=
        integral_sub (hMint.sub (integrable_const 1)) hlogint
      have h2 : (∫ ω, (b1 * ε 0 ω ^ 2 + a1 - 1) ∂μ)
          = (∫ ω, (b1 * ε 0 ω ^ 2 + a1) ∂μ) - ∫ _ω : Ω, (1 : ℝ) ∂μ :=
        integral_sub hMint (integrable_const 1)
      rw [h1, h2, hEM, integral_const]
      simp
    by_contra hcon
    rw [not_lt] at hcon
    have hz : (∫ ω, ((b1 * ε 0 ω ^ 2 + a1 - 1)
        - Real.log (b1 * ε 0 ω ^ 2 + a1)) ∂μ) = 0 := by
      have h1 := integral_nonneg_of_ae hgap
      rw [hgapval] at h1 ⊢
      linarith
    have hae := (integral_eq_zero_iff_of_nonneg_ae hgap hgapint).1 hz
    refine hnondeg ?_
    filter_upwards [hae, hMpos] with ω h1 h2
    by_contra hne
    have hMne : b1 * ε 0 ω ^ 2 + a1 ≠ 1 := by
      intro h
      exact hne (mul_left_cancel₀ hb1.ne' (by linarith : b1 * (ε 0 ω ^ 2) = b1 * 1))
    have hstrict := Real.log_lt_sub_one_of_pos h2 hMne
    simp only [Pi.zero_apply] at h1
    linarith
  · -- **Degenerate case**: `μ{b₁ε² + a₁ = 0} > 0`. Nelson's own condition may fail here
    -- (`Real.log`'s junk value at `0` is `0`, not `−∞`), but the generalized criterion
    -- applies with `g x = log (max (b₁x² + a₁) δ)` for a small enough floor `δ`.
    have hSm : MeasurableSet {ω | b1 * ε 0 ω ^ 2 + a1 = 0} := hmM (measurableSet_singleton 0)
    obtain ⟨ind, hind⟩ : ∃ ind : Ω → ℝ,
        ind = Set.indicator {ω | b1 * ε 0 ω ^ 2 + a1 = 0} fun _ => (1 : ℝ) := ⟨_, rfl⟩
    have hindint : Integrable ind μ := by
      rw [hind]; exact (integrable_const (1 : ℝ)).indicator hSm
    have hindval : (∫ ω, ind ω ∂μ) = (μ {ω | b1 * ε 0 ω ^ 2 + a1 = 0}).toReal := by
      rw [hind, integral_indicator_const (1 : ℝ) hSm]
      simp [measureReal_def]
    have hIpos : 0 < ∫ ω, ind ω ∂μ := by
      rw [hindval]; exact ENNReal.toReal_pos hdeg (measure_ne_top μ _)
    obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ∫ ω, |Real.log (b1 * ε 0 ω ^ 2 + a1)| ∂μ := ⟨_, rfl⟩
    have hCnn : 0 ≤ C := by
      rw [hC]
      exact integral_nonneg (μ := μ) (f := fun ω => |Real.log (b1 * ε 0 ω ^ 2 + a1)|)
        fun ω => abs_nonneg _
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = Real.exp (-((C + 1) / ∫ ω, ind ω ∂μ)) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by rw [hδ]; exact Real.exp_pos _
    have hlogδ : Real.log δ = -((C + 1) / ∫ ω, ind ω ∂μ) := by rw [hδ, Real.log_exp]
    have hδle : δ ≤ 1 := by
      rw [hδ]
      have : -((C + 1) / ∫ ω, ind ω ∂μ) ≤ 0 := by
        have : 0 ≤ (C + 1) / ∫ ω, ind ω ∂μ := div_nonneg (by linarith) hIpos.le
        linarith
      calc Real.exp (-((C + 1) / ∫ ω, ind ω ∂μ)) ≤ Real.exp 0 := Real.exp_le_exp.2 this
        _ = 1 := Real.exp_zero
    -- the floored log dominates the multiplier
    have hdom : ∀ x : ℝ, b1 * x ^ 2 + a1 ≤ Real.exp (Real.log (max (b1 * x ^ 2 + a1) δ)) := by
      intro x
      have hmax : 0 < max (b1 * x ^ 2 + a1) δ := lt_of_lt_of_le hδpos (le_max_right _ _)
      rw [Real.exp_log hmax]
      exact le_max_left _ _
    have hgm : Measurable fun x : ℝ => Real.log (max (b1 * x ^ 2 + a1) δ) := by fun_prop
    -- pointwise control of the floored log
    have hbdd : ∀ ω, Real.log (max (b1 * ε 0 ω ^ 2 + a1) δ)
        ≤ |Real.log (b1 * ε 0 ω ^ 2 + a1)| + Real.log δ * ind ω := by
      intro ω
      by_cases hz : b1 * ε 0 ω ^ 2 + a1 = 0
      · have hmem : ω ∈ {ω | b1 * ε 0 ω ^ 2 + a1 = 0} := hz
        have hi : ind ω = 1 := by rw [hind]; exact Set.indicator_of_mem hmem _
        rw [hz, hi, Real.log_zero]
        simp only [abs_zero, zero_add, mul_one]
        rw [max_eq_right hδpos.le]
      · have hnmem : ω ∉ {ω | b1 * ε 0 ω ^ 2 + a1 = 0} := hz
        have hi : ind ω = 0 := by
          rw [hind]; exact Set.indicator_of_notMem hnmem _
        rw [hi, mul_zero, add_zero]
        rcases le_total (b1 * ε 0 ω ^ 2 + a1) δ with h | h
        · rw [max_eq_right h]
          calc Real.log δ ≤ Real.log 1 := Real.log_le_log hδpos hδle
            _ = 0 := Real.log_one
            _ ≤ |Real.log (b1 * ε 0 ω ^ 2 + a1)| := abs_nonneg _
        · rw [max_eq_left h]
          exact le_abs_self _
    have habs : ∀ ω, |Real.log (max (b1 * ε 0 ω ^ 2 + a1) δ)|
        ≤ |Real.log (b1 * ε 0 ω ^ 2 + a1)| + |Real.log δ| := by
      intro ω
      rcases le_total (b1 * ε 0 ω ^ 2 + a1) δ with h | h
      · rw [max_eq_right h]
        have := abs_nonneg (Real.log (b1 * ε 0 ω ^ 2 + a1))
        linarith
      · rw [max_eq_left h]
        have := abs_nonneg (Real.log δ)
        linarith
    have hbound_int : Integrable
        (fun ω => |Real.log (b1 * ε 0 ω ^ 2 + a1)| + |Real.log δ|) μ :=
      hlogint.abs.add (integrable_const _)
    have hgint : Integrable (fun ω => Real.log (max (b1 * ε 0 ω ^ 2 + a1) δ)) μ := by
      refine hbound_int.mono' ((hgm.comp (hε.measurable 0)).aestronglyMeasurable) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs]
      exact habs ω
    have hneg : (∫ ω, Real.log (max (b1 * ε 0 ω ^ 2 + a1) δ) ∂μ) < 0 := by
      have hmono : (∫ ω, Real.log (max (b1 * ε 0 ω ^ 2 + a1) δ) ∂μ)
          ≤ ∫ ω, (|Real.log (b1 * ε 0 ω ^ 2 + a1)| + Real.log δ * ind ω) ∂μ := by
        refine integral_mono hgint (hlogint.abs.add (hindint.const_mul _)) ?_
        exact hbdd
      have hval : (∫ ω, (|Real.log (b1 * ε 0 ω ^ 2 + a1)| + Real.log δ * ind ω) ∂μ)
          = C + Real.log δ * ∫ ω, ind ω ∂μ := by
        rw [integral_add hlogint.abs (hindint.const_mul _), integral_const_mul, hC]
      have hIne : (∫ ω, ind ω ∂μ) ≠ 0 := hIpos.ne'
      have hkey : Real.log δ * ∫ ω, ind ω ∂μ = -(C + 1) := by
        rw [hlogδ, neg_mul, div_mul_cancel₀ _ hIne]
      rw [hval, hkey] at hmono
      linarith
    refine exists_garch_of_nelW_ae hc0.le hb1.le ha1 ha1' hε fun t => ?_
    exact nelW_ae_ne_top (g := fun x => Real.log (max (b1 * x ^ 2 + a1) δ)) hb1.le ha1 hgm
      hdom hε hgint hneg t

end StatLean.TimeSeries
