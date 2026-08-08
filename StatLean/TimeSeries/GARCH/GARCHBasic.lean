import StatLean.TimeSeries.GARCH.ARCHBasic
import Mathlib.Probability.StrongLaw

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
theorem garchInfCoeffs_nonneg {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) < 1) (i : ℕ) :
    0 ≤ garchInfCoeffs b a i := by
  sorry

/-- Their total mass: `Σ_i d_i = (Σ b_i)/(1 − Σ a_j)`, which is `< 1` exactly when
`Σ b + Σ a < 1` — the bridge from FY Theorem 4.4's hypothesis to Theorem 2.5's. -/
theorem tsum_garchInfCoeffs {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hb : ∀ i, 0 ≤ b i) (ha : ∀ j, 0 ≤ a j) (hsum : (∑ j, a j) < 1) :
    HasSum (garchInfCoeffs b a) ((∑ i, b i) / (1 - ∑ j, a j)) := by
  sorry

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
  sorry

/-- **FY Proposition 4.2(i)**: a stationary GARCH process is white noise. -/
theorem IsGARCH.isWhiteNoise [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hstat : IsStrictlyStationary X μ)
    (hL2 : ∀ t, MemLp (X t) 2 μ) (hsum : (∑ i, b i) + (∑ j, a j) < 1) :
    IsWhiteNoise X (c0 / (1 - (∑ i, b i) - ∑ j, a j)) μ := by
  sorry

/-- **FY Proposition 4.2(i)**: `σ_t²` is the conditional variance of `X_t` given the
strict past. -/
theorem IsGARCH.condexp_sq [IsProbabilityMeasure μ] {c0 : ℝ} {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X σvol ε : ℤ → Ω → ℝ}
    (h : IsGARCH c0 b a X σvol ε μ) (hL2 : ∀ t, MemLp (X t) 2 μ) (t : ℤ) :
    μ[fun ω => X t ω ^ 2 | sigmaLT X t] =ᵐ[μ] fun ω => σvol t ω ^ 2 := by
  sorry

/-- **FY eqs. (4.25)–(4.26)**: the squared process satisfies the ARMA(p∨q, q) recursion
`X_t² = c₀ + Σ_{i ≤ p∨q}(b_i + a_i) X_{t−i}² + e_t − Σ_j a_j e_{t−j}` with the
martingale-difference noise `e_t = (ε_t² − 1)σ_t²` (coefficients zero-padded to the
common order). -/
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
  sorry

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

/-- **Pathwise convergence criterion.** If the running log-averages of the multipliers
`M_i = b₁ p(−1−i)² + a₁` converge to a negative limit, Nelson's random-product series
converges: the partial products are dominated by a geometric sequence. (The multipliers
may vanish, in which case `Real.log`'s junk value `0` only makes the bound weaker.) -/
private lemma nelW_ne_top_of_tendsto {b1 a1 c : ℝ} {p : ℤ → ℝ}
    (hb1 : 0 ≤ b1) (ha1 : 0 ≤ a1) (hc : c < 0)
    (h : Filter.Tendsto
      (fun k : ℕ => (∑ i ∈ Finset.range k, Real.log (b1 * p (-1 - (i : ℤ)) ^ 2 + a1)) / k)
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
          (Real.exp (∑ i ∈ Finset.range k, Real.log (b1 * p (-1 - (i : ℤ)) ^ 2 + a1))) := by
    intro k
    have h1 : nelProd b1 a1 k p
        = ENNReal.ofReal (∏ i ∈ Finset.range k, (b1 * p (-1 - (i : ℤ)) ^ 2 + a1)) := by
      rw [nelProd, ENNReal.ofReal_prod_of_nonneg fun i _ => hmnn i]
    rw [h1]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => hmnn i) fun i _ => self_le_exp_log (hmnn i)
  -- past a threshold, the log-partial-sums drop below `k · c/2`
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
    (Filter.Tendsto.eventually_lt_const (show c < c / 2 by linarith) h)
  have hgeom : ∀ k : ℕ, max K 1 ≤ k → nelProd b1 a1 k p ≤ ENNReal.ofReal (Real.exp (c / 2)) ^ k := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans (le_max_right K 1) hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hlt := hK k (le_trans (le_max_left K 1) hk)
    rw [div_lt_iff₀ hkpos] at hlt
    have hS : (∑ i ∈ Finset.range k, Real.log (b1 * p (-1 - (i : ℤ)) ^ 2 + a1))
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
log-multipliers have negative running averages, so the random-product series converges
almost surely — with *no* moment condition on the innovations. -/
private lemma nelW_ae_ne_top [IsProbabilityMeasure μ] {b1 a1 : ℝ} {ε : ℤ → Ω → ℝ}
    (hb1 : 0 ≤ b1) (ha1 : 0 ≤ a1) (hε : IsIIDNoise ε 1 μ)
    (hlogint : Integrable (fun ω => Real.log (b1 * ε 0 ω ^ 2 + a1)) μ)
    (hneg : (∫ ω, Real.log (b1 * ε 0 ω ^ 2 + a1) ∂μ) < 0) (t : ℤ) :
    ∀ᵐ ω ∂μ, nelW b1 a1 (nelPath ε t ω) ≠ ⊤ := by
  have hg : Measurable fun x : ℝ => Real.log (b1 * x ^ 2 + a1) := by fun_prop
  have hid : ∀ i : ℕ,
      IdentDistrib (fun ω => Real.log (b1 * ε (t - 1 - (i : ℕ)) ω ^ 2 + a1))
        (fun ω => Real.log (b1 * ε (t - 1 - ((0 : ℕ) : ℤ)) ω ^ 2 + a1)) μ μ :=
    fun i => (hε.identDistrib (t - 1 - (i : ℕ)) (t - 1 - ((0 : ℕ) : ℤ))).comp hg
  have hindep : ∀ i j : ℕ, i ≠ j →
      IndepFun (fun ω => Real.log (b1 * ε (t - 1 - (i : ℕ)) ω ^ 2 + a1))
        (fun ω => Real.log (b1 * ε (t - 1 - (j : ℕ)) ω ^ 2 + a1)) μ := by
    intro i j hij
    have hne : t - 1 - (i : ℕ) ≠ t - 1 - (j : ℕ) := by
      intro hEq
      rw [sub_right_inj, Nat.cast_inj] at hEq
      exact hij hEq
    exact (hε.iIndep.indepFun hne).comp hg hg
  have hid0 : IdentDistrib (fun ω => Real.log (b1 * ε 0 ω ^ 2 + a1))
      (fun ω => Real.log (b1 * ε (t - 1 - ((0 : ℕ) : ℤ)) ω ^ 2 + a1)) μ μ :=
    (hε.identDistrib 0 (t - 1 - ((0 : ℕ) : ℤ))).comp hg
  have hint0 : Integrable
      (fun ω => Real.log (b1 * ε (t - 1 - ((0 : ℕ) : ℤ)) ω ^ 2 + a1)) μ :=
    hid0.integrable_snd hlogint
  have hmean0 : (∫ ω, Real.log (b1 * ε (t - 1 - ((0 : ℕ) : ℤ)) ω ^ 2 + a1) ∂μ) < 0 := by
    rw [← hid0.integral_eq]; exact hneg
  have hslln := ProbabilityTheory.strong_law_ae_real
    (fun (i : ℕ) ω => Real.log (b1 * ε (t - 1 - (i : ℕ)) ω ^ 2 + a1)) hint0
    (fun i j hij => hindep i j hij) hid
  filter_upwards [hslln] with ω hω
  have hp : ∀ i : ℕ, nelPath ε t ω (-1 - (i : ℤ)) = ε (t - 1 - (i : ℕ)) ω := by
    intro i; simp only [nelPath]; congr 1; ring
  refine nelW_ne_top_of_tendsto hb1 ha1 hmean0 ?_
  simpa only [hp] using hω

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
  sorry

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
  sorry

end StatLean.TimeSeries
