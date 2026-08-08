import StatLean.TimeSeries.Stationarity.ARCH
import StatLean.TimeSeries.Stationarity.ARMAExistence
import StatLean.TimeSeries.Models.Linear
import StatLean.TimeSeries.Process.LinearProcess
import Mathlib.Probability.ConditionalExpectation

/-!
# Basic properties of ARCH(p) (FY §4.2.1, Theorem 4.3, Proposition 4.1)

The finite-order ARCH theory, all of it routed through the ARCH(∞) Volterra machinery
of `Stationarity/ARCH.lean` (FY Theorem 2.5) — §2.1.4's Markov apparatus is never used
in §4.2:

* **Theorem 4.3(i)** (sufficiency half): `Σ_j b_j < 1` ⇒ a unique strictly stationary
  ARCH(p) solution with `E X_t² < ∞`, and then `E X_t = 0`,
  `E X_t² = c₀/(1 − Σ b_j)`; `c₀ = 0` forces `X ≡ 0`. Proof: apply Theorem 2.5 with
  `Y_t = X_t²`, `ξ_t = ε_t²`, then read off the moments by stationarity. The
  **necessity** half is Bollerslev (1986) Thm 1 — a literature DEBT.
* **Theorem 4.3(ii)**: `E ε⁴ < ∞` and eq. (4.16) `max{1, (Eε⁴)^{1/2}} Σ b_j < 1`
  ⇒ `E X_t⁴ < ∞`.
* **eqs. (4.17)–(4.20)**: `X_t²` satisfies an AR(p) recursion whose noise
  `e_t = (ε_t² − 1)σ_t²` is a **martingale difference** (eq. (4.18)); under (4.16) it
  is white noise, and since `Σ b_j < 1` forces `1 − Σ b_j z^j ≠ 0` on `|z| ≤ 1`, the
  squared process is a **causal AR(p)** — so its ACF is the ARMA machinery's, and it
  is strictly positive at every lag when `Σ b_j > 0`.
* **eq. (4.21)**: kurtosis dominance `κ_x ≥ κ_ε` (tower + Jensen).
* **Proposition 4.1**: the packaging of the three previous items.
* **Example 4.1 (ARCH(1))**, eqs. (4.22)–(4.23): the geometric `k`-step conditional
  variance, `Corr(X_t², X_{t+τ}²) = b₁^{|τ|}`, and — for normal errors —
  `(4.16) ⇔ 3b₁² < 1` with `κ_x = 3(1 − b₁²)/(1 − 3b₁²)`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.1,
Definition 4.2, Theorem 4.3, Proposition 4.1, eqs. (4.15)–(4.23) (pp. 143–147).
(`FY §4.2.1`.)

**Bibliographic comments.** ARCH is R. F. Engle, *Autoregressive conditional
heteroscedasticity with estimates of the variance of United Kingdom inflation*
(Econometrica 50 (1982), 987–1007); the stationarity characterization is Bollerslev
(1986) Thm 1; the Volterra route used here is Giraitis, Kokoszka & Leipus (2000).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The ARCH(p) coefficient sequence read as an ARCH(∞) sequence (zero-padded), so the
§2.1.5 theory applies verbatim to `Y_t = X_t²`, `ξ_t = ε_t²`. -/
noncomputable def archInfCoeffs {p : ℕ} (b : Fin p → ℝ) : ℕ → ℝ := fun j =>
  if h : j < p then b ⟨j, h⟩ else 0

/-! ### Elementary bricks

The `σ`-algebra bookkeeping of `Stationarity/ARCH.lean` (whose copies there are `private`),
the closed form of `archVol²`, and the two moment identities of a unit-variance i.i.d.
noise. -/

omit [MeasurableSpace Ω] in
private lemma comap_le_sigmaLT {X : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    MeasurableSpace.comap (X s) inferInstance ≤ sigmaLT X t :=
  le_iSup₂ (f := fun s (_ : s ∈ Set.Iio t) => MeasurableSpace.comap (X s) inferInstance) s hst

omit [MeasurableSpace Ω] in
private lemma measurable_sigmaLT {X : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    Measurable[sigmaLT X t] (X s) :=
  (Measurable.of_comap_le (le_refl (MeasurableSpace.comap (X s) inferInstance))).mono
    (comap_le_sigmaLT hst) le_rfl

private lemma sigmaLT_le {X : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaLT X t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun _ _ => (hm _).comap_le

omit [MeasurableSpace Ω] in
/-- The lag indices of an ARCH(p) recursion are strictly in the past. -/
private lemma sub_one_sub_lt (t : ℤ) (i : ℕ) : t - 1 - (i : ℕ) < t := by
  have : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
  omega

omit [MeasurableSpace Ω] in
/-- **The closed form of `σ_t²`** (FY eq. (4.15)): the radicand of `archVol` is nonnegative
under the model's sign conditions, so squaring undoes the square root everywhere. -/
private lemma archVol_sq {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ} {X : ℤ → Ω → ℝ}
    (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (t : ℤ) (ω : Ω) :
    archVol c0 b X t ω ^ 2 = c0 + ∑ i, b i * X (t - 1 - (i : ℕ)) ω ^ 2 :=
  Real.sq_sqrt
    (add_nonneg hc0 (Finset.sum_nonneg fun i _ => mul_nonneg (hb i) (sq_nonneg _)))

omit [MeasurableSpace Ω] in
private lemma archVol_nonneg (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (X : ℤ → Ω → ℝ) (t : ℤ)
    (ω : Ω) : 0 ≤ archVol c0 b X t ω := Real.sqrt_nonneg _

omit [MeasurableSpace Ω] in
/-- The volatility is a function of the strict past of the process. -/
private lemma measurable_archVol_sigmaLT {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ} {X : ℤ → Ω → ℝ}
    (t : ℤ) : Measurable[sigmaLT X t] (archVol c0 b X t) :=
  Measurable.sqrt (measurable_const.add (Finset.measurable_sum _ fun i _ =>
    (((measurable_sigmaLT (X := X) (sub_one_sub_lt t (i : ℕ)))).pow_const 2).const_mul _))

/-- `E ε² = 1` for `IID(0,1)` noise. -/
private lemma integral_sq_iid [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε 1 μ) (t : ℤ) : ∫ ω, ε t ω ^ 2 ∂μ = 1 := by
  have h0 : ∫ ω, ε 0 ω ^ 2 ∂μ = 1 := by
    have := variance_eq_sub hε.memLp
    rw [hε.variance_eq, hε.integral_eq_zero] at this
    simpa using this.symm
  have := ((hε.identDistrib t 0).comp (measurable_id.pow_const 2)).integral_eq
  simpa [Function.comp_def] using this.trans h0

/-- `ε_t²` is integrable for `IID(0,1)` noise. -/
private lemma integrable_sq_iid [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε 1 μ) (t : ℤ) : Integrable (fun ω => ε t ω ^ 2) μ :=
  ((hε.identDistrib 0 t).memLp_snd hε.memLp).integrable_sq

/-- Every past-measurable functional is independent of the current innovation — the
working form of the model's `indep_past` field. -/
private lemma indepFun_of_sigmaLT {X ε : ℤ → Ω → ℝ} {t : ℤ}
    (hindep : Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT X t) μ)
    {f : Ω → ℝ} (hf : Measurable[sigmaLT X t] f) : IndepFun f (ε t) μ :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right hindep hf.comap_le).symm

/-- `σ_t²` is integrable as soon as the process is square-integrable. -/
private lemma integrable_archVol_sq [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hL2 : ∀ t, MemLp (X t) 2 μ) (t : ℤ) :
    Integrable (fun ω => archVol c0 b X t ω ^ 2) μ := by
  have hvolsq : (fun ω => archVol c0 b X t ω ^ 2)
      = fun ω => c0 + ∑ i, b i * X (t - 1 - (i : ℕ)) ω ^ 2 :=
    funext fun ω => archVol_sq h.c0_nonneg h.b_nonneg t ω
  rw [hvolsq]
  exact (integrable_const c0).add (integrable_finset_sum _ fun i _ =>
    ((hL2 _).integrable_sq).const_mul _)

/-- A fourth `L`-power is integrable, in the `x ↦ x⁴` form the file uses. -/
private lemma integrable_pow_four [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 4 μ) :
    Integrable (fun ω => f ω ^ 4) μ := by
  have h := hf.integrable_norm_rpow'
  have he : ∀ ω, ‖f ω‖ ^ (ENNReal.toReal 4) = f ω ^ 4 := fun ω => by
    have h4 : (ENNReal.toReal 4) = ((4 : ℕ) : ℝ) := by norm_num
    rw [h4, Real.rpow_natCast, ← norm_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [he] using h

/-- The square of an `L⁴` variable lies in `L²`. -/
private lemma memLp_sq_of_memLp_four [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hm : Measurable f) (hf : MemLp f 4 μ) : MemLp (fun ω => f ω ^ 2) 2 μ := by
  refine (memLp_two_iff_integrable_sq (hm.pow_const 2).aestronglyMeasurable).2 ?_
  have h := integrable_pow_four hf
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  change f ω ^ 4 = (f ω ^ 2) ^ 2
  ring

/-- **`E X_t² = E σ_t²`**: the innovation is independent of the volatility and has unit
second moment. -/
private lemma integral_sq_eq_archVol [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ) (t : ℤ) :
    ∫ ω, X t ω ^ 2 ∂μ = ∫ ω, archVol c0 b X t ω ^ 2 ∂μ := by
  have hle : sigmaLT X t ≤ (inferInstance : MeasurableSpace Ω) := sigmaLT_le h.measurableX t
  have hvolM : Measurable (archVol c0 b X t) :=
    (measurable_archVol_sigmaLT (c0 := c0) (b := b) (X := X) t).mono hle le_rfl
  have hIF2 : IndepFun (fun ω => archVol c0 b X t ω ^ 2) (fun ω => ε t ω ^ 2) μ :=
    (indepFun_of_sigmaLT (h.indep_past t) (measurable_archVol_sigmaLT t)).comp
      (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hae : (fun ω => X t ω ^ 2) =ᵐ[μ] fun ω => archVol c0 b X t ω ^ 2 * ε t ω ^ 2 := by
    filter_upwards [h.recurrence t] with ω hω
    rw [hω]; ring
  rw [integral_congr_ae hae, hIF2.integral_fun_mul_eq_mul_integral
    (hvolM.pow_const 2).aestronglyMeasurable
    ((h.iid.measurable t).pow_const 2).aestronglyMeasurable, integral_sq_iid h.iid t, mul_one]

/-- The squared ARCH(p) process is an ARCH(∞) process in the sense of `IsARCHInf`
(FY §4.2.1's reduction to Theorem 2.5). -/
theorem IsARCH.isARCHInf_sq [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ) :
    IsARCHInf c0 (archInfCoeffs b) (fun t ω => X t ω ^ 2) (fun t ω => ε t ω ^ 2) μ := by
  have hsq : Measurable fun x : ℝ => x ^ 2 := measurable_id.pow_const 2
  have hcoe : ∀ i : Fin p, archInfCoeffs b (i : ℕ) = b i := fun i => by
    simp [archInfCoeffs, i.isLt]
  refine
    { a_nonneg := h.c0_nonneg
      bc_nonneg := fun j => ?_
      measurableY := fun s => (h.measurableX s).pow_const 2
      measurableXi := fun s => (h.iid.measurable s).pow_const 2
      xi_nonneg := fun s => Filter.Eventually.of_forall fun ω => sq_nonneg _
      iIndep := h.iid.iIndep.comp (fun _ x => x ^ 2) fun _ => hsq
      identDistrib := fun s s' => (h.iid.identDistrib s s').comp hsq
      integrable_xi := integrable_sq_iid h.iid 0
      integral_xi := integral_sq_iid h.iid 0
      indep_past := fun s => ?_
      Y_nonneg := fun s => Filter.Eventually.of_forall fun ω => sq_nonneg _
      recurrence := fun s => ?_ }
  · simp only [archInfCoeffs]
    split
    · exact h.b_nonneg _
    · exact le_rfl
  · -- `σ(ε_s²) ⊆ σ(ε_s)` and `σ(X_u² : u < s) ⊆ σ(X_u : u < s)`
    have h1 : MeasurableSpace.comap (fun ω => ε s ω ^ 2) inferInstance
        ≤ MeasurableSpace.comap (ε s) inferInstance :=
      (hsq.comp (Measurable.of_comap_le
        (le_refl (MeasurableSpace.comap (ε s) inferInstance)))).comap_le
    have h2 : sigmaLT (fun u ω => X u ω ^ 2) s ≤ sigmaLT X s :=
      iSup₂_le fun u hu =>
        ((measurable_sigmaLT (X := X) (t := s) hu).pow_const 2).comap_le
    exact indep_of_indep_of_le_left
      (indep_of_indep_of_le_right (h.indep_past s) h2) h1
  · filter_upwards [h.recurrence s] with ω hω
    have htsum : (∑' j : ℕ, archInfCoeffs b j * X (s - 1 - (j : ℕ)) ω ^ 2)
        = ∑ i, b i * X (s - 1 - (i : ℕ)) ω ^ 2 := by
      rw [tsum_eq_sum (s := Finset.range p) (fun j hj => by
        have hj' : ¬ j < p := by simpa using hj
        simp [archInfCoeffs, hj'])]
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => archInfCoeffs b j * X (s - 1 - (j : ℕ)) ω ^ 2) p]
      exact Finset.sum_congr rfl fun i _ => by rw [hcoe i]
    change X s ω ^ 2 = _
    rw [hω, mul_pow, htsum, archVol_sq h.c0_nonneg h.b_nonneg]

/-- **FY Theorem 4.3(i), existence + moments**: under `Σ_j b_j < 1` there is a strictly
stationary ARCH(p) solution with finite variance, and every such solution has
`E X_t = 0` and `E X_t² = c₀/(1 − Σ b_j)`. -/
theorem exists_stationary_arch [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: nonnegative coefficients; FY Def 4.2
    (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i)
    -- USER-INPUT: contraction; FY Thm 4.3(i)
    (hsum : (∑ i, b i) < 1)
    -- USER-INPUT: iid(0,1) innovations; FY Def 4.2
    (hε : IsIIDNoise ε 1 μ) :
    ∃ X : ℤ → Ω → ℝ, IsARCH c0 b X ε μ ∧ IsStrictlyStationary X μ ∧
      (∀ t, MemLp (X t) 2 μ) := by
  sorry

/-- **FY Theorem 4.3(i), moment identities**: a stationary square-integrable ARCH(p)
process is centered with variance `c₀/(1 − Σ b_j)`. -/
theorem IsARCH.integral_and_variance [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL2 : ∀ t, MemLp (X t) 2 μ)
    (hsum : (∑ i, b i) < 1) (t : ℤ) :
    (∫ ω, X t ω ∂μ) = 0 ∧ variance (X t) μ = c0 / (1 - ∑ i, b i) := by
  have hsq : Measurable fun x : ℝ => x ^ 2 := measurable_id.pow_const 2
  have hle : sigmaLT X t ≤ (inferInstance : MeasurableSpace Ω) := sigmaLT_le h.measurableX t
  have hvolM : Measurable (archVol c0 b X t) :=
    (measurable_archVol_sigmaLT (c0 := c0) (b := b) (X := X) t).mono hle le_rfl
  have hIF : IndepFun (archVol c0 b X t) (ε t) μ :=
    indepFun_of_sigmaLT (h.indep_past t) (measurable_archVol_sigmaLT t)
  -- (i) `E X_t = E σ_t · E ε_t = 0`.
  have hmean : (∫ ω, X t ω ∂μ) = 0 := by
    have e1 : ∫ ω, X t ω ∂μ = ∫ ω, archVol c0 b X t ω * ε t ω ∂μ :=
      integral_congr_ae (h.recurrence t)
    have he : ∫ ω, ε t ω ∂μ = 0 := by
      rw [(h.iid.identDistrib t 0).integral_eq, h.iid.integral_eq_zero]
    rw [e1, hIF.integral_fun_mul_eq_mul_integral hvolM.aestronglyMeasurable
      (h.iid.measurable t).aestronglyMeasurable, he, mul_zero]
  -- (ii) `E X_t² = E σ_t² = c₀ + (Σ b) E X_t²`.
  have e2 : ∫ ω, X t ω ^ 2 ∂μ = ∫ ω, archVol c0 b X t ω ^ 2 ∂μ := by
    have hae : (fun ω => X t ω ^ 2)
        =ᵐ[μ] fun ω => archVol c0 b X t ω ^ 2 * ε t ω ^ 2 := by
      filter_upwards [h.recurrence t] with ω hω
      rw [hω]; ring
    have hIF2 : IndepFun (fun ω => archVol c0 b X t ω ^ 2) (fun ω => ε t ω ^ 2) μ :=
      hIF.comp hsq hsq
    rw [integral_congr_ae hae,
      hIF2.integral_fun_mul_eq_mul_integral
        (hvolM.pow_const 2).aestronglyMeasurable
        ((h.iid.measurable t).pow_const 2).aestronglyMeasurable,
      integral_sq_iid h.iid t, mul_one]
  have hstatsq : ∀ s : ℤ, ∫ ω, X s ω ^ 2 ∂μ = ∫ ω, X t ω ^ 2 ∂μ := fun s => by
    simpa [Function.comp_def] using
      ((hstat.identDistrib h.measurableX s t).comp hsq).integral_eq
  have e3 : ∫ ω, archVol c0 b X t ω ^ 2 ∂μ = c0 + (∑ i, b i) * ∫ ω, X t ω ^ 2 ∂μ := by
    have hvolsq : (fun ω => archVol c0 b X t ω ^ 2)
        = fun ω => c0 + ∑ i, b i * X (t - 1 - (i : ℕ)) ω ^ 2 :=
      funext fun ω => archVol_sq h.c0_nonneg h.b_nonneg t ω
    have hterm : ∀ i : Fin p, ∫ ω, b i * X (t - 1 - (i : ℕ)) ω ^ 2 ∂μ
        = b i * ∫ ω, X t ω ^ 2 ∂μ := fun i => by
      rw [integral_const_mul, hstatsq]
    have hc : ∫ _ω : Ω, c0 ∂μ = c0 := by simp
    rw [hvolsq, integral_add (integrable_const c0)
      (integrable_finset_sum _ fun i _ => ((hL2 _).integrable_sq).const_mul _),
      integral_finset_sum _ fun i _ => ((hL2 _).integrable_sq).const_mul _, hc,
      Finset.sum_mul]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => hterm i)
  have hne : (1 : ℝ) - ∑ i, b i ≠ 0 := by linarith
  have hfix : ∫ ω, X t ω ^ 2 ∂μ = c0 / (1 - ∑ i, b i) := by
    have hkey := e2.trans e3
    rw [eq_div_iff hne]
    nlinarith [hkey]
  refine ⟨hmean, ?_⟩
  rw [variance_eq_sub (hL2 t)]
  have hpow : ∫ ω, ((X t) ^ 2) ω ∂μ = ∫ ω, X t ω ^ 2 ∂μ := rfl
  rw [hpow, hmean, hfix]
  ring

/-- **FY Theorem 4.3(i), degenerate case**: `c₀ = 0` forces the stationary solution to
vanish. -/
theorem IsARCH.eq_zero_of_c0_eq_zero [IsProbabilityMeasure μ] {p : ℕ} {b : Fin p → ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH 0 b X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL2 : ∀ t, MemLp (X t) 2 μ)
    (hsum : (∑ i, b i) < 1) (t : ℤ) :
    X t =ᵐ[μ] 0 := by
  obtain ⟨hm, hv⟩ := h.integral_and_variance hstat hL2 hsum t
  have h2 : ∫ ω, X t ω ^ 2 ∂μ = 0 := by
    have hvs := variance_eq_sub (hL2 t)
    rw [hv, hm] at hvs
    have hpow : ∫ ω, ((X t) ^ 2) ω ∂μ = ∫ ω, X t ω ^ 2 ∂μ := rfl
    rw [hpow] at hvs
    simp at hvs
    linarith [hvs]
  have hint : Integrable (fun ω => X t ω ^ 2) μ := (hL2 t).integrable_sq
  have hnn : 0 ≤ᵐ[μ] fun ω => X t ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h2] with ω hω
  have hz : X t ω ^ 2 = 0 := hω
  exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).1 hz

/-- **DEBT (Bollerslev 1986 Thm 1; FY Theorem 4.3(i), necessity half)**: conversely, a
strictly stationary ARCH(p) solution with finite variance forces `Σ_j b_j < 1`. -/
theorem IsARCH.sum_lt_one_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL2 : ∀ t, MemLp (X t) 2 μ)
    -- USER-INPUT: nondegeneracy (c₀ > 0 rules out the trivial solution); FY Thm 4.3(i)
    (hc0 : 0 < c0) :
    (∑ i, b i) < 1 := by
  sorry

/-- **FY Theorem 4.3(ii)** (eq. (4.16)): a finite fourth innovation moment together with
`max{1, (Eε⁴)^{1/2}}·Σ b_j < 1` gives a finite fourth moment for the process. -/
theorem IsARCH.memLp_four [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: finite fourth innovation moment; FY Thm 4.3(ii)
    (hε4 : MemLp (ε 0) 4 μ)
    -- USER-INPUT: eq. (4.16); FY Thm 4.3(ii)
    (h416 : max 1 (Real.sqrt (∫ ω, ε 0 ω ^ 4 ∂μ)) * (∑ i, b i) < 1)
    (t : ℤ) :
    MemLp (X t) 4 μ := by
  sorry

/-- **FY eq. (4.18)**: the squared-process innovations `e_t = (ε_t² − 1)σ_t²` are a
martingale difference with respect to the strict past of `X`. -/
theorem IsARCH.condexp_sq_innovation [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hL2 : ∀ t, MemLp (X t) 2 μ) (t : ℤ) :
    μ[fun ω => (ε t ω ^ 2 - 1) * archVol c0 b X t ω ^ 2 | sigmaLT X t] =ᵐ[μ] 0 := by
  have hle : sigmaLT X t ≤ (inferInstance : MeasurableSpace Ω) := sigmaLT_le h.measurableX t
  have hvolm : Measurable[sigmaLT X t] fun ω => archVol c0 b X t ω ^ 2 :=
    (measurable_archVol_sigmaLT (c0 := c0) (b := b) (X := X) t).pow_const 2
  have hvolint : Integrable (fun ω => archVol c0 b X t ω ^ 2) μ :=
    integrable_archVol_sq h hL2 t
  have hεint : Integrable (fun ω => ε t ω ^ 2 - 1) μ :=
    (integrable_sq_iid h.iid t).sub (integrable_const 1)
  -- The innovation `ε_t² − 1` is independent of the past and centered.
  have hIF : IndepFun (fun ω => archVol c0 b X t ω ^ 2) (fun ω => ε t ω ^ 2 - 1) μ :=
    (indepFun_of_sigmaLT (h.indep_past t) hvolm).comp measurable_id
      ((measurable_id.pow_const 2).sub_const 1)
  have hprod : Integrable
      ((fun ω => ε t ω ^ 2 - 1) * fun ω => archVol c0 b X t ω ^ 2) μ :=
    (hIF.symm).integrable_mul hεint hvolint
  have hmean : ∫ ω, (ε t ω ^ 2 - 1) ∂μ = 0 := by
    rw [integral_sub (integrable_sq_iid h.iid t) (integrable_const 1),
      integral_sq_iid h.iid t]
    simp
  have hcond : μ[fun ω => ε t ω ^ 2 - 1 | sigmaLT X t] =ᵐ[μ] fun _ => (0 : ℝ) := by
    have := condExp_indep_eq (μ := μ) (h.iid.measurable t).comap_le hle
      (f := fun ω => ε t ω ^ 2 - 1)
      (((Measurable.of_comap_le
          (le_refl (MeasurableSpace.comap (ε t) inferInstance))).pow_const 2).sub_const
        1).stronglyMeasurable (h.indep_past t)
    filter_upwards [this] with ω hω
    rw [hω, hmean]
  have hpull := condExp_mul_of_stronglyMeasurable_right (μ := μ) (m := sigmaLT X t)
    (f := fun ω => ε t ω ^ 2 - 1) (g := fun ω => archVol c0 b X t ω ^ 2)
    hvolm.stronglyMeasurable hprod hεint
  filter_upwards [hpull, hcond] with ω h1 h2
  change μ[fun ω => (ε t ω ^ 2 - 1) * archVol c0 b X t ω ^ 2 | sigmaLT X t] ω = 0
  rw [show (fun ω => (ε t ω ^ 2 - 1) * archVol c0 b X t ω ^ 2)
      = ((fun ω => ε t ω ^ 2 - 1) * fun ω => archVol c0 b X t ω ^ 2) from rfl, h1]
  simp [h2]

/-- **FY eq. (4.17)**: the squared process satisfies the AR(p) recursion
`X_t² = c₀ + Σᵢ bᵢ X_{t−i}² + e_t` with `e_t = (ε_t² − 1)σ_t²`. -/
theorem IsARCH.sq_ar_recursion [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ) (t : ℤ) :
    (fun ω => X t ω ^ 2) =ᵐ[μ] fun ω =>
      c0 + (∑ i, b i * X (t - 1 - (i : ℕ)) ω ^ 2)
        + (ε t ω ^ 2 - 1) * archVol c0 b X t ω ^ 2 := by
  filter_upwards [h.recurrence t] with ω hω
  have hv : archVol c0 b X t ω ^ 2 = c0 + ∑ i, b i * X (t - 1 - (i : ℕ)) ω ^ 2 :=
    archVol_sq h.c0_nonneg h.b_nonneg t ω
  change X t ω ^ 2 = _
  rw [hω, mul_pow]
  linear_combination hv

/-- **FY §4.2.1**: `Σ b_j < 1` with nonnegative coefficients forces the AR polynomial of
the squared process to be root-free on the closed unit disc — hence `{X_t²}` is a
*causal* AR(p) (FY eq. (4.20)). -/
theorem noRootClosedDisc_of_sum_lt_one {p : ℕ} {b : Fin p → ℝ}
    (hb : ∀ i, 0 ≤ b i) (hsum : (∑ i, b i) < 1) :
    NoRootClosedDisc b := by
  intro z hz h0
  have hev : Polynomial.aeval z (arPoly b) = 1 - ∑ i, (b i : ℂ) * z ^ ((i : ℕ) + 1) := by
    simp [arPoly]
  rw [hev, sub_eq_zero] at h0
  have hle : ‖∑ i, (b i : ℂ) * z ^ ((i : ℕ) + 1)‖ ≤ ∑ i, b i := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have h1 : ‖z‖ ^ ((i : ℕ) + 1) ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
    calc ‖(b i : ℂ) * z ^ ((i : ℕ) + 1)‖ = b i * ‖z‖ ^ ((i : ℕ) + 1) := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hb i)]
      _ ≤ b i * 1 := mul_le_mul_of_nonneg_left h1 (hb i)
      _ = b i := mul_one _
  rw [← h0, norm_one] at hle
  linarith

/-- **FY eq. (4.21) / Proposition 4.1(iii)**: an ARCH process is at least as leptokurtic
as its innovations, `κ_x ≥ κ_ε` (equivalently `E X⁴ · (E ε²)² ≥ E ε⁴ · (E X²)²`; stated
in the product form to avoid division). -/
theorem IsARCH.kurtosis_le [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL4 : ∀ t, MemLp (X t) 4 μ)
    (hε4 : MemLp (ε 0) 4 μ) :
    (∫ ω, ε 0 ω ^ 4 ∂μ) * (∫ ω, X 0 ω ^ 2 ∂μ) ^ 2
      ≤ (∫ ω, X 0 ω ^ 4 ∂μ) * (∫ ω, ε 0 ω ^ 2 ∂μ) ^ 2 := by
  have hle : sigmaLT X 0 ≤ (inferInstance : MeasurableSpace Ω) := sigmaLT_le h.measurableX 0
  have hvolM : Measurable (archVol c0 b X 0) :=
    (measurable_archVol_sigmaLT (c0 := c0) (b := b) (X := X) 0).mono hle le_rfl
  -- `σ_0² ∈ L²`, i.e. `E σ_0⁴ < ∞`, because `X ∈ L⁴`.
  have hvolL2 : MemLp (fun ω => archVol c0 b X 0 ω ^ 2) 2 μ := by
    have he : (fun ω => archVol c0 b X 0 ω ^ 2)
        = fun ω => c0 + ∑ i, b i * X (0 - 1 - (i : ℕ)) ω ^ 2 :=
      funext fun ω => archVol_sq h.c0_nonneg h.b_nonneg 0 ω
    rw [he]
    exact (memLp_const c0).add (memLp_finset_sum _ fun i _ =>
      (memLp_sq_of_memLp_four (h.measurableX _) (hL4 _)).const_mul _)
  have hvol4 : Integrable (fun ω => archVol c0 b X 0 ω ^ 4) μ := by
    have h4 := (memLp_two_iff_integrable_sq
      (hvolM.pow_const 2).aestronglyMeasurable).1 hvolL2
    refine h4.congr (Filter.Eventually.of_forall fun ω => ?_)
    change (archVol c0 b X 0 ω ^ 2) ^ 2 = archVol c0 b X 0 ω ^ 4
    ring
  have hε4int : Integrable (fun ω => ε 0 ω ^ 4) μ := integrable_pow_four hε4
  have hIF : IndepFun (archVol c0 b X 0) (ε 0) μ :=
    indepFun_of_sigmaLT (h.indep_past 0) (measurable_archVol_sigmaLT 0)
  have hIF4 : IndepFun (fun ω => archVol c0 b X 0 ω ^ 4) (fun ω => ε 0 ω ^ 4) μ :=
    hIF.comp (measurable_id.pow_const 4) (measurable_id.pow_const 4)
  -- `E X⁴ = E σ⁴ · E ε⁴`.
  have hE4 : ∫ ω, X 0 ω ^ 4 ∂μ
      = (∫ ω, archVol c0 b X 0 ω ^ 4 ∂μ) * ∫ ω, ε 0 ω ^ 4 ∂μ := by
    have hae : (fun ω => X 0 ω ^ 4)
        =ᵐ[μ] fun ω => archVol c0 b X 0 ω ^ 4 * ε 0 ω ^ 4 := by
      filter_upwards [h.recurrence 0] with ω hω
      rw [hω]; ring
    rw [integral_congr_ae hae, hIF4.integral_fun_mul_eq_mul_integral
      hvol4.aestronglyMeasurable hε4int.aestronglyMeasurable]
  -- Jensen: `(E σ²)² ≤ E σ⁴`.
  have hJensen : (∫ ω, archVol c0 b X 0 ω ^ 2 ∂μ) ^ 2
      ≤ ∫ ω, archVol c0 b X 0 ω ^ 4 ∂μ := by
    have hv := variance_nonneg (fun ω => archVol c0 b X 0 ω ^ 2) μ
    rw [variance_eq_sub hvolL2] at hv
    have hp : ∫ ω, ((fun ω => archVol c0 b X 0 ω ^ 2) ^ 2) ω ∂μ
        = ∫ ω, archVol c0 b X 0 ω ^ 4 ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      change (archVol c0 b X 0 ω ^ 2) ^ 2 = archVol c0 b X 0 ω ^ 4
      ring
    rw [hp] at hv
    linarith
  have he4nn : 0 ≤ ∫ ω, ε 0 ω ^ 4 ∂μ := integral_nonneg fun ω => by positivity
  rw [integral_sq_eq_archVol h 0, hE4, integral_sq_iid h.iid 0]
  nlinarith [hJensen, he4nn]

/-- **FY Proposition 4.1(i)**: a stationary ARCH(p) process is white noise with variance
`c₀/(1 − Σ b_j)`. -/
theorem IsARCH.isWhiteNoise [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL2 : ∀ t, MemLp (X t) 2 μ)
    (hsum : (∑ i, b i) < 1) :
    IsWhiteNoise X (c0 / (1 - ∑ i, b i)) μ := by
  -- The martingale-difference property kills every nonzero-lag covariance.
  have key : ∀ s t : ℤ, s < t → cov[X s, X t; μ] = 0 := by
    intro s t hst
    have hle : sigmaLT X t ≤ (inferInstance : MeasurableSpace Ω) := sigmaLT_le h.measurableX t
    have hvolM : Measurable (archVol c0 b X t) :=
      (measurable_archVol_sigmaLT (c0 := c0) (b := b) (X := X) t).mono hle le_rfl
    have hvolL2 : MemLp (archVol c0 b X t) 2 μ :=
      (memLp_two_iff_integrable_sq hvolM.aestronglyMeasurable).2
        (integrable_archVol_sq h hL2 t)
    have hfm : Measurable[sigmaLT X t] fun ω => X s ω * archVol c0 b X t ω :=
      (measurable_sigmaLT hst).mul (measurable_archVol_sigmaLT t)
    have hIF : IndepFun (fun ω => X s ω * archVol c0 b X t ω) (ε t) μ :=
      indepFun_of_sigmaLT (h.indep_past t) hfm
    have hprod : Integrable (fun ω => X s ω * archVol c0 b X t ω) μ :=
      (hL2 s).integrable_mul hvolL2
    have he : ∫ ω, ε t ω ∂μ = 0 := by
      rw [(h.iid.identDistrib t 0).integral_eq, h.iid.integral_eq_zero]
    have hxy : ∫ ω, X s ω * X t ω ∂μ = 0 := by
      have hae : (fun ω => X s ω * X t ω)
          =ᵐ[μ] fun ω => (X s ω * archVol c0 b X t ω) * ε t ω := by
        filter_upwards [h.recurrence t] with ω hω
        rw [hω]; ring
      rw [integral_congr_ae hae, hIF.integral_fun_mul_eq_mul_integral
        hprod.aestronglyMeasurable (h.iid.measurable t).aestronglyMeasurable, he, mul_zero]
    rw [covariance_eq_sub (hL2 s) (hL2 t), (h.integral_and_variance hstat hL2 hsum s).1,
      (h.integral_and_variance hstat hL2 hsum t).1]
    simp only [Pi.mul_apply]
    rw [hxy]
    ring
  exact
    { measurable := h.measurableX
      memLp := hL2
      integral_eq_zero := fun t => (h.integral_and_variance hstat hL2 hsum t).1
      variance_eq := fun t => (h.integral_and_variance hstat hL2 hsum t).2
      uncorrelated := fun s t hne => by
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact key s t hlt
        · rw [covariance_comm]; exact key t s hlt }

/-- **FY Example 4.1, eq. (4.23)**: for a stationary ARCH(1) with finite fourth moment,
the squared process has autocorrelation `Corr(X_t², X_{t+τ}²) = b₁^{|τ|}`. -/
theorem IsARCH.acf_sq_arch_one [IsProbabilityMeasure μ] {c0 b1 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 (fun _ : Fin 1 => b1) X ε μ)
    (hstat : IsStrictlyStationary X μ) (hL4 : ∀ t, MemLp (X t) 4 μ)
    (hb1 : 0 < b1) (hb1' : b1 < 1)
    -- USER-INPUT: nondegenerate squared process; FY Example 4.1
    (hvar : 0 < variance (fun ω => X 0 ω ^ 2) μ) (τ : ℤ) :
    acf (fun t ω => X t ω ^ 2) μ τ = b1 ^ τ.natAbs := by
  sorry

/-- **FY Example 4.1**, normal-error specialization: for `ε ∼ N(0,1)`, condition (4.16)
reads `3b₁² < 1`, and then the kurtosis is `κ_x = 3(1 − b₁²)/(1 − 3b₁²)`. -/
theorem IsARCH.kurtosis_arch_one_gaussian [IsProbabilityMeasure μ] {c0 b1 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 (fun _ : Fin 1 => b1) X ε μ)
    (hstat : IsStrictlyStationary X μ)
    -- USER-INPUT: standard normal innovations; FY Example 4.1
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    (hb1 : 0 < b1) (h3b : 3 * b1 ^ 2 < 1) (hc0 : 0 < c0) :
    MemLp (X 0) 4 μ ∧
      (∫ ω, X 0 ω ^ 4 ∂μ) * (1 - 3 * b1 ^ 2)
        = 3 * (1 - b1 ^ 2) * (∫ ω, X 0 ω ^ 2 ∂μ) ^ 2 := by
  sorry

end StatLean.TimeSeries
