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
open scoped ProbabilityTheory Topology ENNReal

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

omit [MeasurableSpace Ω] in
private lemma norm_rpow_four {f : Ω → ℝ} (ω : Ω) :
    ‖f ω‖ ^ (ENNReal.toReal 4) = f ω ^ 4 := by
  have h4 : (ENNReal.toReal 4) = ((4 : ℕ) : ℝ) := by norm_num
  rw [h4, Real.rpow_natCast, ← norm_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- `L⁴` membership in the `x ↦ x⁴` form the file uses. -/
private lemma memLp_four_iff_integrable {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    MemLp f 4 μ ↔ Integrable (fun ω => f ω ^ 4) μ := by
  rw [← integrable_norm_rpow_iff hf (by norm_num) (by norm_num)]
  exact ⟨fun hi => hi.congr (Filter.Eventually.of_forall fun ω => norm_rpow_four ω),
    fun hi => hi.congr (Filter.Eventually.of_forall fun ω => (norm_rpow_four ω).symm)⟩

/-- A fourth `L`-power is integrable, in the `x ↦ x⁴` form the file uses. -/
private lemma integrable_pow_four {f : Ω → ℝ} (hf : MemLp f 4 μ) :
    Integrable (fun ω => f ω ^ 4) μ :=
  (memLp_four_iff_integrable hf.aestronglyMeasurable).1 hf

/-- `archInfCoeffs` is finitely supported, hence summable. -/
private lemma summable_archInfCoeffs {p : ℕ} (b : Fin p → ℝ) : Summable (archInfCoeffs b) := by
  refine summable_of_ne_finset_zero (s := Finset.range p) fun j hj => ?_
  have hj' : ¬ j < p := by simpa using hj
  simp [archInfCoeffs, hj']

/-- The ARCH(∞) reading of a finite coefficient vector has the same total mass. -/
private lemma tsum_archInfCoeffs {p : ℕ} (b : Fin p → ℝ) :
    ∑' j : ℕ, archInfCoeffs b j = ∑ i, b i := by
  rw [tsum_eq_sum (s := Finset.range p) fun j hj => by
    have hj' : ¬ j < p := by simpa using hj
    simp [archInfCoeffs, hj']]
  rw [← Fin.sum_univ_eq_sum_range (fun j => archInfCoeffs b j) p]
  exact Finset.sum_congr rfl fun i _ => by simp [archInfCoeffs, i.isLt]

/-- The square of an `L⁴` variable lies in `L²`. -/
private lemma memLp_sq_of_memLp_four [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hm : Measurable f) (hf : MemLp f 4 μ) : MemLp (fun ω => f ω ^ 2) 2 μ := by
  refine (memLp_two_iff_integrable_sq (hm.pow_const 2).aestronglyMeasurable).2 ?_
  have h := integrable_pow_four hf
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  change f ω ^ 4 = (f ω ^ 2) ^ 2
  ring

/-- Strict stationarity passes to the squared process (a fixed measurable map applied
coordinatewise to every finite-dimensional distribution). -/
private lemma strictlyStationary_sq {X : ℤ → Ω → ℝ} (hstat : IsStrictlyStationary X μ)
    (hm : ∀ t, Measurable (X t)) : IsStrictlyStationary (fun t ω => X t ω ^ 2) μ := by
  intro n tt k
  have hsq : Measurable fun q : Fin n → ℝ => fun i => q i ^ 2 :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).pow_const 2
  have e : ∀ c : ℤ, (μ.map fun ω (i : Fin n) => X (tt i + c) ω ^ 2)
      = (μ.map fun ω (i : Fin n) => X (tt i + c) ω).map fun q i => q i ^ 2 := fun c => by
    rw [Measure.map_map hsq (measurable_pi_lambda _ fun i => hm (tt i + c))]
    rfl
  have e0 : (μ.map fun ω (i : Fin n) => X (tt i) ω ^ 2)
      = (μ.map fun ω (i : Fin n) => X (tt i) ω).map fun q i => q i ^ 2 := by
    rw [Measure.map_map hsq (measurable_pi_lambda _ fun i => hm (tt i))]
    rfl
  rw [e k, e0, hstat n tt k]

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

/-! ### The stationary solution (FY Theorem 4.3(i), existence)

`Stationarity/ARCH.lean` builds the stationary ARCH(∞) solution, but only as an
*existential*: its Volterra functional is `private` there, and the ARCH(p) statement needs
strictly more than the `IsARCHInf` package exports — that the solution's past sits inside
the *noise's* past, which is what makes `ε_t` independent of `σ(X_s : s < t)` (rather than
just of `σ(X_s² : s < t)`) and what transports the finite-dimensional laws along the shift.
So the finite-order solution is built here directly, by backward iteration of the
volatility recursion — finitely many terms per step, so none of §2.7.1's Volterra
bookkeeping is needed — as a fixed measurable functional of the noise path. -/

/-- The `n`-step backward iteration of `Y_t = (c₀ + Σ_i b_i Y_{t−1−i}) ε_t²`, read off a
noise path `q` (with `q 0` in the role of `ε_t`); valued in `ℝ≥0∞`, so the iteration is
unconditionally monotone and no summability side condition is carried. -/
private noncomputable def archIter (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) : ℕ → (ℤ → ℝ) → ℝ≥0∞
  | 0, _ => 0
  | n + 1, q => ENNReal.ofReal (q 0 ^ 2) * (ENNReal.ofReal c0
      + ∑ i : Fin p, ENNReal.ofReal (b i) * archIter c0 b n fun s => q (s - 1 - (i : ℕ)))

/-- The stationary square `Y_t = X_t²`, read off the noise path. -/
private noncomputable def archSq (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (q : ℤ → ℝ) : ℝ≥0∞ :=
  ⨆ n, archIter c0 b n q

/-- The stationary squared volatility `σ_t²`, read off the noise path. -/
private noncomputable def archRho (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (q : ℤ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal c0
    + ∑ i : Fin p, ENNReal.ofReal (b i) * archSq c0 b fun s => q (s - 1 - (i : ℕ))

/-- The stationary ARCH(p) process, as a fixed measurable functional of the noise path. -/
private noncomputable def archXFun (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (q : ℤ → ℝ) : ℝ :=
  Real.sqrt (archRho c0 b q).toReal * q 0

/-- The noise path seen from time `t`. -/
private def noisePath (ε : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℤ → ℝ := fun s => ε (s + t) ω

/-- The stationary ARCH(p) solution over the given noise. -/
private noncomputable def archX (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ)
    (ω : Ω) : ℝ := archXFun c0 b (noisePath ε t ω)

private lemma archIter_succ (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (n : ℕ) (q : ℤ → ℝ) :
    archIter c0 b (n + 1) q = ENNReal.ofReal (q 0 ^ 2) * (ENNReal.ofReal c0
      + ∑ i : Fin p, ENNReal.ofReal (b i) * archIter c0 b n fun s => q (s - 1 - (i : ℕ))) :=
  rfl

omit [MeasurableSpace Ω] in
private lemma noisePath_zero (ε : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    noisePath ε t ω 0 = ε t ω := by simp [noisePath]

omit [MeasurableSpace Ω] in
private lemma noisePath_shift (ε : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) (i : ℕ) :
    (fun s => noisePath ε t ω (s - 1 - (i : ℕ))) = noisePath ε (t - 1 - (i : ℕ)) ω := by
  funext s
  simp only [noisePath]
  congr 1
  ring

private lemma archIter_le_succ (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) :
    ∀ (n : ℕ) (q : ℤ → ℝ), archIter c0 b n q ≤ archIter c0 b (n + 1) q := by
  intro n
  induction n with
  | zero => intro q; simp [archIter]
  | succ n ih =>
    intro q
    rw [archIter_succ, archIter_succ]
    gcongr with i _
    exact ih _

private lemma archIter_monotone (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (q : ℤ → ℝ) :
    Monotone fun n => archIter c0 b n q :=
  monotone_nat_of_le_succ fun n => archIter_le_succ c0 b n q

/-- **The recursion satisfied by the limit**: `Y_t = σ_t² ε_t²`. -/
private lemma archSq_eq (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (q : ℤ → ℝ) :
    archSq c0 b q = ENNReal.ofReal (q 0 ^ 2) * archRho c0 b q := by
  have h1 : archSq c0 b q = ⨆ n, archIter c0 b (n + 1) q :=
    le_antisymm (iSup_le fun n =>
        (archIter_le_succ c0 b n q).trans (le_iSup (fun m => archIter c0 b (m + 1) q) n))
      (iSup_le fun n => le_iSup (fun m => archIter c0 b m q) (n + 1))
  have h3 : (⨆ n : ℕ, ∑ i : Fin p, ENNReal.ofReal (b i)
        * archIter c0 b n fun s => q (s - 1 - (i : ℕ)))
      = ∑ i : Fin p, ENNReal.ofReal (b i) * archSq c0 b fun s => q (s - 1 - (i : ℕ)) := by
    rw [← ENNReal.finsetSum_iSup_of_monotone
      (f := fun (i : Fin p) (n : ℕ) => ENNReal.ofReal (b i)
        * archIter c0 b n fun s => q (s - 1 - (i : ℕ)))
      (fun i m n hmn => mul_le_mul_left' (archIter_monotone c0 b _ hmn) _)]
    exact Finset.sum_congr rfl fun i _ => by rw [archSq, ENNReal.mul_iSup]
  rw [h1]
  simp only [archIter_succ]
  rw [← ENNReal.mul_iSup, ← ENNReal.add_iSup, h3, archRho]

/-! #### Measurability -/

private lemma measurable_archIter (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (n : ℕ) :
    Measurable (archIter c0 b n) := by
  induction n with
  | zero => simpa only [archIter] using measurable_const
  | succ n ih =>
    change Measurable fun q : ℤ → ℝ => ENNReal.ofReal (q 0 ^ 2) * (ENNReal.ofReal c0
      + ∑ i : Fin p, ENNReal.ofReal (b i) * archIter c0 b n fun s => q (s - 1 - (i : ℕ)))
    refine (((measurable_pi_apply 0).pow_const 2).ennreal_ofReal).mul
      (measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_const.mul ?_))
    exact ih.comp (measurable_pi_lambda _ fun s => measurable_pi_apply _)

private lemma measurable_archSq (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) :
    Measurable (archSq c0 b) := by
  change Measurable fun q : ℤ → ℝ => ⨆ n : ℕ, archIter c0 b n q
  exact Measurable.iSup fun n => measurable_archIter c0 b n

private lemma measurable_archRho (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) :
    Measurable (archRho c0 b) :=
  measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_const.mul
    ((measurable_archSq c0 b).comp (measurable_pi_lambda _ fun s => measurable_pi_apply _)))

private lemma measurable_archXFun (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) :
    Measurable (archXFun c0 b) :=
  ((measurable_archRho c0 b).ennreal_toReal.sqrt).mul (measurable_pi_apply 0)

private lemma measurable_noisePath {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t)) (t : ℤ) :
    Measurable (noisePath ε t) := measurable_pi_lambda _ fun s => hm (s + t)

private lemma measurable_archX {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ} {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (t : ℤ) : Measurable (archX c0 b ε t) :=
  (measurable_archXFun c0 b).comp (measurable_noisePath hm t)

/-! #### `σ`-algebra bookkeeping for the noise -/

omit [MeasurableSpace Ω] in
private lemma comap_le_sigmaLE {X : ℤ → Ω → ℝ} {s t : ℤ} (hst : s ≤ t) :
    MeasurableSpace.comap (X s) inferInstance ≤ sigmaLE X t :=
  le_iSup₂ (f := fun s (_ : s ∈ Set.Iic t) => MeasurableSpace.comap (X s) inferInstance) s hst

omit [MeasurableSpace Ω] in
private lemma sigmaLE_mono {X : ℤ → Ω → ℝ} {s t : ℤ} (hst : s ≤ t) :
    sigmaLE X s ≤ sigmaLE X t :=
  iSup₂_le fun _ hu => comap_le_sigmaLE (le_trans hu hst)

omit [MeasurableSpace Ω] in
private lemma sigmaLE_le_sigmaLT {X : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    sigmaLE X s ≤ sigmaLT X t :=
  iSup₂_le fun _ hu => comap_le_sigmaLT (lt_of_le_of_lt hu hst)

omit [MeasurableSpace Ω] in
private lemma measurable_self_sigmaLE {X : ℤ → Ω → ℝ} (t : ℤ) : Measurable[sigmaLE X t] (X t) :=
  (Measurable.of_comap_le (le_refl (MeasurableSpace.comap (X t) inferInstance))).mono
    (comap_le_sigmaLE le_rfl) le_rfl

private lemma sigmaLT_le' {X : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaLT X t ≤ (inferInstance : MeasurableSpace Ω) := sigmaLT_le hm t

/-- **One-vs-past independence of the noise**: `ε_t` is independent of `σ(ε_s : s < t)`. -/
private lemma indep_eps_sigmaLT {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t))
    (hi : iIndepFun ε μ) (t : ℤ) :
    Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT ε t) μ := by
  have hdisj : Disjoint ({t} : Set ℤ) (Set.Iio t) := Set.disjoint_singleton_left.2 (by simp)
  have := indep_iSup_of_disjoint
    (m := fun s : ℤ => MeasurableSpace.comap (ε s) inferInstance)
    (fun s => (hm s).comap_le) hi hdisj
  simpa using this

omit [MeasurableSpace Ω] in
/-- Each iterate, read at time `t`, is a function of `σ(ε_s : s ≤ t)`. -/
private lemma measurable_archIter_sigmaLE (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) {ε : ℤ → Ω → ℝ}
    (n : ℕ) : ∀ t : ℤ,
    Measurable[sigmaLE ε t] fun ω => archIter c0 b n (noisePath ε t ω) := by
  induction n with
  | zero => intro t; simpa only [archIter] using measurable_const
  | succ n ih =>
    intro t
    simp only [archIter_succ, noisePath_zero, noisePath_shift]
    refine (((measurable_self_sigmaLE (X := ε) t).pow_const 2).ennreal_ofReal).mul
      (measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_const.mul ?_))
    exact (ih (t - 1 - (i : ℕ))).mono
      (sigmaLE_mono (le_of_lt (sub_one_sub_lt t (i : ℕ)))) le_rfl

omit [MeasurableSpace Ω] in
private lemma measurable_archSq_sigmaLE (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) {ε : ℤ → Ω → ℝ}
    (t : ℤ) : Measurable[sigmaLE ε t] fun ω => archSq c0 b (noisePath ε t ω) := by
  have he : (fun ω => archSq c0 b (noisePath ε t ω))
      = fun ω => ⨆ n : ℕ, archIter c0 b n (noisePath ε t ω) := rfl
  rw [he]
  exact Measurable.iSup fun n => measurable_archIter_sigmaLE c0 b n t

private lemma measurable_archRho_sigmaLE (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) {ε : ℤ → Ω → ℝ}
    (t : ℤ) : Measurable[sigmaLE ε t] fun ω => archRho c0 b (noisePath ε t ω) := by
  simp only [archRho, noisePath_shift]
  refine measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_const.mul ?_)
  exact (measurable_archSq_sigmaLE c0 b (t - 1 - (i : ℕ))).mono
    (sigmaLE_mono (le_of_lt (sub_one_sub_lt t (i : ℕ)))) le_rfl

private lemma measurable_archX_sigmaLE (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) {ε : ℤ → Ω → ℝ}
    (t : ℤ) : Measurable[sigmaLE ε t] (archX c0 b ε t) := by
  have he : archX c0 b ε t
      = fun ω => Real.sqrt (archRho c0 b (noisePath ε t ω)).toReal * ε t ω := by
    funext ω
    simp [archX, archXFun, noisePath_zero]
  rw [he]
  exact ((measurable_archRho_sigmaLE c0 b t).ennreal_toReal.sqrt).mul
    (measurable_self_sigmaLE t)

/-! #### The mass of the iteration -/

private lemma lintegral_ofReal_sq_eps [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hε : IsIIDNoise ε 1 μ) (t : ℤ) : ∫⁻ ω, ENNReal.ofReal (ε t ω ^ 2) ∂μ = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_sq_iid hε t)
    (Filter.Eventually.of_forall fun ω => sq_nonneg _), integral_sq_iid hε t,
    ENNReal.ofReal_one]

/-- **Uniform mass bound**: every iterate has mass at most `c₀/(1 − Σ b_j)`. -/
private lemma lintegral_archIter_le [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ}
    {ε : ℤ → Ω → ℝ} (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (hsum : (∑ i, b i) < 1)
    (hε : IsIIDNoise ε 1 μ) (n : ℕ) : ∀ t : ℤ,
    ∫⁻ ω, archIter c0 b n (noisePath ε t ω) ∂μ
      ≤ ENNReal.ofReal (c0 / (1 - ∑ i, b i)) := by
  have hb0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ => hb i
  have hne : (1 : ℝ) - ∑ i, b i ≠ 0 := by linarith
  have hK0 : 0 ≤ c0 / (1 - ∑ i, b i) := div_nonneg hc0 (by linarith)
  have hKfix : c0 + (∑ i, b i) * (c0 / (1 - ∑ i, b i)) = c0 / (1 - ∑ i, b i) := by
    field_simp
    ring
  induction n with
  | zero => intro t; simp [archIter]
  | succ n ih =>
    intro t
    have hmeas : ∀ s : ℤ, Measurable fun ω => archIter c0 b n (noisePath ε s ω) := fun s =>
      (measurable_archIter c0 b n).comp (measurable_noisePath hε.measurable s)
    have hpast : Measurable[sigmaLT ε t] fun ω => ENNReal.ofReal c0
        + ∑ i : Fin p, ENNReal.ofReal (b i)
            * archIter c0 b n (noisePath ε (t - 1 - (i : ℕ)) ω) := by
      refine measurable_const.add (Finset.measurable_sum _ fun i _ => measurable_const.mul ?_)
      exact (measurable_archIter_sigmaLE c0 b n (t - 1 - (i : ℕ))).mono
        (sigmaLE_le_sigmaLT (sub_one_sub_lt t (i : ℕ))) le_rfl
    have hsplit : ∫⁻ ω, archIter c0 b (n + 1) (noisePath ε t ω) ∂μ
        = (∫⁻ ω, ENNReal.ofReal (ε t ω ^ 2) ∂μ)
          * ∫⁻ ω, (ENNReal.ofReal c0 + ∑ i : Fin p, ENNReal.ofReal (b i)
              * archIter c0 b n (noisePath ε (t - 1 - (i : ℕ)) ω)) ∂μ := by
      simp only [archIter_succ, noisePath_zero, noisePath_shift]
      exact lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
        (hε.measurable t).comap_le (sigmaLT_le' hε.measurable t)
        (indep_eps_sigmaLT hε.measurable hε.iIndep t)
        ((Measurable.of_comap_le le_rfl).pow_const 2).ennreal_ofReal hpast
    have hterm : ∫⁻ ω, (ENNReal.ofReal c0 + ∑ i : Fin p, ENNReal.ofReal (b i)
          * archIter c0 b n (noisePath ε (t - 1 - (i : ℕ)) ω)) ∂μ
        ≤ ENNReal.ofReal (c0 / (1 - ∑ i, b i)) := by
      have hfs : ∫⁻ ω, (∑ i : Fin p, ENNReal.ofReal (b i)
            * archIter c0 b n (noisePath ε (t - 1 - (i : ℕ)) ω)) ∂μ
          = ∑ i : Fin p, ∫⁻ ω, ENNReal.ofReal (b i)
            * archIter c0 b n (noisePath ε (t - 1 - (i : ℕ)) ω) ∂μ :=
        lintegral_finset_sum _ fun i _ => measurable_const.mul (hmeas (t - 1 - (i : ℕ)))
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, hfs]
      have hb' : ∀ i : Fin p, ∫⁻ ω, ENNReal.ofReal (b i)
            * archIter c0 b n (noisePath ε (t - 1 - (i : ℕ)) ω) ∂μ
          ≤ ENNReal.ofReal (b i) * ENNReal.ofReal (c0 / (1 - ∑ i, b i)) := fun i => by
        rw [lintegral_const_mul _ (hmeas (t - 1 - (i : ℕ)))]
        exact mul_le_mul_left' (ih (t - 1 - (i : ℕ))) _
      calc ENNReal.ofReal c0 + ∑ i : Fin p, ∫⁻ ω, ENNReal.ofReal (b i)
              * archIter c0 b n (noisePath ε (t - 1 - (i : ℕ)) ω) ∂μ
          ≤ ENNReal.ofReal c0
              + ∑ i : Fin p, ENNReal.ofReal (b i) * ENNReal.ofReal (c0 / (1 - ∑ i, b i)) :=
            by gcongr with i _; exact hb' i
        _ = ENNReal.ofReal (c0 / (1 - ∑ i, b i)) := by
            rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun i _ => hb i,
              ← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_add hc0
                (mul_nonneg hb0 hK0), hKfix]
    rw [hsplit, lintegral_ofReal_sq_eps hε, one_mul]
    exact hterm

private lemma lintegral_archSq_le [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ}
    {ε : ℤ → Ω → ℝ} (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (hsum : (∑ i, b i) < 1)
    (hε : IsIIDNoise ε 1 μ) (t : ℤ) :
    ∫⁻ ω, archSq c0 b (noisePath ε t ω) ∂μ ≤ ENNReal.ofReal (c0 / (1 - ∑ i, b i)) := by
  have he : ∀ ω, archSq c0 b (noisePath ε t ω)
      = ⨆ n : ℕ, archIter c0 b n (noisePath ε t ω) := fun ω => rfl
  simp only [he]
  rw [lintegral_iSup (f := fun (n : ℕ) (ω : Ω) => archIter c0 b n (noisePath ε t ω))
    (fun n => (measurable_archIter c0 b n).comp (measurable_noisePath hε.measurable t))
    (fun m n hmn ω => archIter_monotone c0 b _ hmn)]
  exact iSup_le fun n => lintegral_archIter_le hc0 hb hsum hε n t

private lemma archSq_ae_lt_top [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ} {b : Fin p → ℝ}
    {ε : ℤ → Ω → ℝ} (hc0 : 0 ≤ c0) (hb : ∀ i, 0 ≤ b i) (hsum : (∑ i, b i) < 1)
    (hε : IsIIDNoise ε 1 μ) (t : ℤ) :
    ∀ᵐ ω ∂μ, archSq c0 b (noisePath ε t ω) < ∞ := by
  refine ae_lt_top ((measurable_archSq c0 b).comp (measurable_noisePath hε.measurable t))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_archSq_le hc0 hb hsum hε t))

/-! #### The solution -/

omit [MeasurableSpace Ω] in
private lemma archX_sq (c0 : ℝ) {p : ℕ} (b : Fin p → ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    archX c0 b ε t ω ^ 2 = (archSq c0 b (noisePath ε t ω)).toReal := by
  have hq0 : noisePath ε t ω 0 = ε t ω := noisePath_zero ε t ω
  rw [archSq_eq, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  simp only [archX, archXFun, hq0]
  rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  ring

/-- **Shift-invariance of the noise path law**, the transport behind strict
stationarity. -/
private lemma map_noisePath_shift [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ε t)) (hi : iIndepFun ε μ)
    (hid : ∀ s t, IdentDistrib (ε s) (ε t) μ μ) (c : ℤ) :
    (μ.map fun ω (s : ℤ) => ε (s + c) ω) = μ.map fun ω (s : ℤ) => ε s ω := by
  have hinj : Function.Injective fun s : ℤ => s + c := fun x y h => by simpa using h
  have h1 : iIndepFun (fun s : ℤ => ε (s + c)) μ := hi.precomp hinj
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map fun s => hm (s + c)).1 h1,
    (iIndepFun_iff_map_fun_eq_infinitePi_map hm).1 hi]
  exact congrArg Measure.infinitePi (funext fun s => (hid (s + c) s).map_eq)

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
  refine ⟨archX c0 b ε, ?_, ?_, ?_⟩
  · refine
      { c0_nonneg := hc0
        b_nonneg := hb
        measurableX := fun t => measurable_archX hε.measurable t
        iid := hε
        indep_past := fun t => indep_of_indep_of_le_right
          (indep_eps_sigmaLT hε.measurable hε.iIndep t)
          (iSup₂_le fun s hs =>
            ((measurable_archX_sigmaLE c0 b s).mono (sigmaLE_le_sigmaLT hs) le_rfl).comap_le)
        recurrence := fun t => ?_ }
    filter_upwards [ae_all_iff.2 fun i : Fin p =>
      archSq_ae_lt_top hc0 hb hsum hε (t - 1 - (i : ℕ))] with ω hfin
    have hne : ∀ i : Fin p, ENNReal.ofReal (b i)
        * archSq c0 b (noisePath ε (t - 1 - (i : ℕ)) ω) ≠ ∞ := fun i =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin i).ne
    have hsumne : (∑ i : Fin p, ENNReal.ofReal (b i)
        * archSq c0 b (noisePath ε (t - 1 - (i : ℕ)) ω)) ≠ ∞ :=
      (ENNReal.sum_lt_top.2 fun i _ => lt_top_iff_ne_top.2 (hne i)).ne
    have hrho : (archRho c0 b (noisePath ε t ω)).toReal
        = c0 + ∑ i, b i * archX c0 b ε (t - 1 - (i : ℕ)) ω ^ 2 := by
      simp only [archRho, noisePath_shift]
      rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hsumne, ENNReal.toReal_ofReal hc0,
        ENNReal.toReal_sum fun i _ => hne i]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hb i), archX_sq]
    have h1 : archX c0 b ε t ω
        = Real.sqrt (archRho c0 b (noisePath ε t ω)).toReal * ε t ω := by
      simp [archX, archXFun, noisePath_zero]
    change archX c0 b ε t ω = archVol c0 b (archX c0 b ε) t ω * ε t ω
    rw [h1, archVol, ← hrho]
  · -- strict stationarity: a fixed functional of the shifted noise path
    intro n tt k
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (ℤ → ℝ) → (Fin n → ℝ),
        Ψ = fun q i => archXFun c0 b fun s => q (s + tt i) := ⟨_, rfl⟩
    have hΨm : Measurable Ψ := by
      rw [hΨ]
      exact measurable_pi_lambda _ fun i => (measurable_archXFun c0 b).comp
        (measurable_pi_lambda _ fun s => measurable_pi_apply (s + tt i))
    have hmb : ∀ c : ℤ, Measurable fun ω (s : ℤ) => ε (s + c) ω :=
      fun c => measurable_pi_lambda _ fun s => hε.measurable (s + c)
    have hfac : ∀ c : ℤ, (fun ω (i : Fin n) => archX c0 b ε (tt i + c) ω)
        = Ψ ∘ fun ω (s : ℤ) => ε (s + c) ω := by
      intro c
      funext ω i
      simp only [hΨ, Function.comp_apply, archX, add_assoc]
      rfl
    have h0 : (fun ω (i : Fin n) => archX c0 b ε (tt i) ω)
        = Ψ ∘ fun ω (s : ℤ) => ε s ω := by simpa using hfac 0
    rw [hfac k, h0, ← Measure.map_map hΨm (hmb k),
      ← Measure.map_map hΨm (measurable_pi_lambda _ fun s : ℤ => hε.measurable s),
      map_noisePath_shift hε.measurable hε.iIndep hε.identDistrib k]
  · intro t
    refine (memLp_two_iff_integrable_sq
      (measurable_archX hε.measurable t).aestronglyMeasurable).2
      ⟨((measurable_archX hε.measurable t).pow_const 2).aestronglyMeasurable, ?_⟩
    have hle : ∫⁻ ω, ‖archX c0 b ε t ω ^ 2‖ₑ ∂μ
        ≤ ∫⁻ ω, archSq c0 b (noisePath ε t ω) ∂μ := by
      refine lintegral_mono fun ω => ?_
      rw [archX_sq, Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
    change ∫⁻ ω, ‖archX c0 b ε t ω ^ 2‖ₑ ∂μ < ∞
    exact lt_of_le_of_lt hle
      (lt_of_le_of_lt (lintegral_archSq_le hc0 hb hsum hε t) ENNReal.ofReal_lt_top)

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

/-- **EXTRA DEBT — reported loudly** (Giraitis–Kokoszka–Leipus 2000; Vervaat-type
uniqueness, *not* proved in FY §4.2.1): under `Σ_j b_j < 1` a **strictly stationary**
ARCH(p) solution automatically has a finite second moment.

FY Theorem 4.3(ii) (`IsARCH.memLp_four` below) is stated with no `E X_t² < ∞` hypothesis,
while the ARCH(∞) `L²` theory it is proved from (`archInf_memLp_two_debt`, itself a
literature debt) requires integrability of `Y = X²`. Supplying it needs the a.s.-contraction
argument that identifies *every* strictly stationary solution of the random recurrence
`Y_t = (c₀ + Σ b_j Y_{t−1−j}) ε_t²` with the (integrable) Volterra series — the
`E log(b ξ) < 0` route of Vervaat/Bougerol–Picard. That machinery (an SLLN for possibly
non-integrable logarithms plus tightness of the common marginal) is outside the batch's
scope; note that the naive fixed-point argument `m = c₀ + (Σ b) m` cannot conclude, since
`m = ∞` is a fixed point too. -/
private theorem memLp_two_of_stationary_debt [IsProbabilityMeasure μ] {c0 : ℝ} {p : ℕ}
    {b : Fin p → ℝ} {X ε : ℤ → Ω → ℝ} (h : IsARCH c0 b X ε μ)
    (hstat : IsStrictlyStationary X μ) (hsum : (∑ i, b i) < 1) (t : ℤ) :
    MemLp (X t) 2 μ := by
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
  have hb0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ => h.b_nonneg i
  have hmax : (1 : ℝ) ≤ max 1 (Real.sqrt (∫ ω, ε 0 ω ^ 4 ∂μ)) := le_max_left _ _
  have hsum : (∑ i, b i) < 1 := by nlinarith
  have hL2 : ∀ s : ℤ, MemLp (X s) 2 μ := fun s =>
    memLp_two_of_stationary_debt h hstat hsum s
  -- The squared process is an ARCH(∞) process; apply FY Theorem 2.5(ii).
  have hnoise : IsARCHNoise (fun s ω => ε s ω ^ 2) μ :=
    ⟨h.isARCHInf_sq.measurableXi, h.isARCHInf_sq.xi_nonneg, h.isARCHInf_sq.iIndep,
      h.isARCHInf_sq.identDistrib, h.isARCHInf_sq.integrable_xi, h.isARCHInf_sq.integral_xi⟩
  have hξ2 : MemLp (fun ω => ε 0 ω ^ 2) 2 μ :=
    memLp_sq_of_memLp_four (h.iid.measurable 0) hε4
  have hI : ∫ ω, (ε 0 ω ^ 2) ^ 2 ∂μ = ∫ ω, ε 0 ω ^ 4 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  have h16 : max 1 (Real.sqrt (∫ ω, (ε 0 ω ^ 2) ^ 2 ∂μ))
      * ∑' j : ℕ, archInfCoeffs b j < 1 := by
    rw [hI, tsum_archInfCoeffs]
    exact h416
  have hY2 : MemLp (fun ω => X t ω ^ 2) 2 μ :=
    archInf_memLp_two_debt h.c0_nonneg h.isARCHInf_sq.bc_nonneg (summable_archInfCoeffs b)
      hnoise hξ2 h16 h.isARCHInf_sq (strictlyStationary_sq hstat h.measurableX)
      (fun s => (hL2 s).integrable_sq) t
  refine (memLp_four_iff_integrable (h.measurableX t).aestronglyMeasurable).2 ?_
  have h4 := (memLp_two_iff_integrable_sq
    ((h.measurableX t).pow_const 2).aestronglyMeasurable).1 hY2
  exact h4.congr (Filter.Eventually.of_forall fun ω => by ring)

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
  have hmY : ∀ t : ℤ, Measurable fun ω => X t ω ^ 2 := fun t => (h.measurableX t).pow_const 2
  have hY2 : ∀ t : ℤ, MemLp (fun ω => X t ω ^ 2) 2 μ := fun t =>
    memLp_sq_of_memLp_four (h.measurableX t) (hL4 t)
  have hYint : ∀ t : ℤ, Integrable (fun ω => X t ω ^ 2) μ := fun t =>
    (hY2 t).integrable one_le_two
  have hEY : ∀ t : ℤ, ∫ ω, X t ω ^ 2 ∂μ = ∫ ω, X 0 ω ^ 2 ∂μ := fun t => by
    simpa [Function.comp_def] using
      ((hstat.identDistrib h.measurableX t 0).comp (measurable_id.pow_const 2)).integral_eq
  -- The ARCH(1) volatility, in closed form.
  have hvolsq : ∀ (t : ℤ) (ω : Ω),
      archVol c0 (fun _ : Fin 1 => b1) X t ω ^ 2 = c0 + b1 * X (t - 1) ω ^ 2 := by
    intro t ω
    rw [archVol_sq h.c0_nonneg h.b_nonneg]
    simp
  -- The stationary second moment solves `m = c₀ + b₁ m`.
  have hm_fix : (∫ ω, X 0 ω ^ 2 ∂μ) = c0 + b1 * ∫ ω, X 0 ω ^ 2 ∂μ := by
    have h1 : (∫ ω, X 0 ω ^ 2 ∂μ)
        = ∫ ω, archVol c0 (fun _ : Fin 1 => b1) X 0 ω ^ 2 ∂μ := integral_sq_eq_archVol h 0
    have h2 : ∫ ω, archVol c0 (fun _ : Fin 1 => b1) X 0 ω ^ 2 ∂μ
        = c0 + b1 * ∫ ω, X 0 ω ^ 2 ∂μ := by
      have he : (fun ω => archVol c0 (fun _ : Fin 1 => b1) X 0 ω ^ 2)
          = fun ω => c0 + b1 * X (0 - 1) ω ^ 2 := funext fun ω => hvolsq 0 ω
      rw [he, integral_add (integrable_const c0) ((hYint (0 - 1)).const_mul _),
        integral_const_mul, hEY (0 - 1)]
      simp
    exact h1.trans h2
  -- The cross moment recursion at positive lags.
  have hprod : ∀ k : ℤ, 0 < k →
      ∫ ω, X k ω ^ 2 * X 0 ω ^ 2 ∂μ
        = c0 * (∫ ω, X 0 ω ^ 2 ∂μ) + b1 * ∫ ω, X (k - 1) ω ^ 2 * X 0 ω ^ 2 ∂μ := by
    intro k hk
    have hle : sigmaLT X k ≤ (inferInstance : MeasurableSpace Ω) := sigmaLT_le h.measurableX k
    have hvolM : Measurable (archVol c0 (fun _ : Fin 1 => b1) X k) :=
      (measurable_archVol_sigmaLT (c0 := c0) (b := fun _ : Fin 1 => b1) (X := X) k).mono
        hle le_rfl
    have hfm : Measurable[sigmaLT X k]
        fun ω => archVol c0 (fun _ : Fin 1 => b1) X k ω ^ 2 * X 0 ω ^ 2 :=
      ((measurable_archVol_sigmaLT k).pow_const 2).mul ((measurable_sigmaLT hk).pow_const 2)
    have hIF : IndepFun (fun ω => archVol c0 (fun _ : Fin 1 => b1) X k ω ^ 2 * X 0 ω ^ 2)
        (fun ω => ε k ω ^ 2) μ :=
      (indepFun_of_sigmaLT (h.indep_past k) hfm).comp measurable_id
        (measurable_id.pow_const 2)
    have hae : (fun ω => X k ω ^ 2 * X 0 ω ^ 2) =ᵐ[μ] fun ω =>
        (archVol c0 (fun _ : Fin 1 => b1) X k ω ^ 2 * X 0 ω ^ 2) * ε k ω ^ 2 := by
      filter_upwards [h.recurrence k] with ω hω
      rw [hω]; ring
    have hstep : ∫ ω, X k ω ^ 2 * X 0 ω ^ 2 ∂μ
        = ∫ ω, archVol c0 (fun _ : Fin 1 => b1) X k ω ^ 2 * X 0 ω ^ 2 ∂μ := by
      rw [integral_congr_ae hae, hIF.integral_fun_mul_eq_mul_integral
        ((hvolM.pow_const 2).mul (hmY 0)).aestronglyMeasurable
        ((h.iid.measurable k).pow_const 2).aestronglyMeasurable,
        integral_sq_iid h.iid k, mul_one]
    have hprodint : Integrable (fun ω => X (k - 1) ω ^ 2 * X 0 ω ^ 2) μ :=
      (hY2 (k - 1)).integrable_mul (hY2 0)
    have he : (fun ω => archVol c0 (fun _ : Fin 1 => b1) X k ω ^ 2 * X 0 ω ^ 2)
        = fun ω => c0 * X 0 ω ^ 2 + b1 * (X (k - 1) ω ^ 2 * X 0 ω ^ 2) := by
      funext ω
      rw [hvolsq]; ring
    rw [hstep, he, integral_add ((hYint 0).const_mul _) (hprodint.const_mul _),
      integral_const_mul, integral_const_mul]
  -- Yule–Walker at `p = 1`.
  have hcovrec : ∀ k : ℤ, 0 < k → acvf (fun t ω => X t ω ^ 2) μ k
      = b1 * acvf (fun t ω => X t ω ^ 2) μ (k - 1) := by
    intro k hk
    change cov[fun ω => X k ω ^ 2, fun ω => X 0 ω ^ 2; μ]
      = b1 * cov[fun ω => X (k - 1) ω ^ 2, fun ω => X 0 ω ^ 2; μ]
    rw [covariance_eq_sub (hY2 k) (hY2 0), covariance_eq_sub (hY2 (k - 1)) (hY2 0)]
    simp only [Pi.mul_apply]
    rw [hprod k hk, hEY k, hEY (k - 1)]
    linear_combination (-(∫ ω, X 0 ω ^ 2 ∂μ)) * hm_fix
  have hmain : ∀ n : ℕ, acvf (fun t ω => X t ω ^ 2) μ (n : ℤ)
      = b1 ^ n * acvf (fun t ω => X t ω ^ 2) μ 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hk : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos n
      have hkm : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by push_cast; ring
      rw [hcovrec _ hk, hkm, ih]
      ring
  have hg0 : acvf (fun t ω => X t ω ^ 2) μ 0 ≠ 0 := by
    have : acvf (fun t ω => X t ω ^ 2) μ 0 = variance (fun ω => X 0 ω ^ 2) μ :=
      covariance_self (hmY 0).aemeasurable
    rw [this]
    exact ne_of_gt hvar
  have hstatY : IsStationary (fun t ω => X t ω ^ 2) μ :=
    (strictlyStationary_sq hstat h.measurableX).isStationary hmY (hY2 0)
  rcases Int.natAbs_eq τ with hτ | hτ
  · rw [acf, hτ]
    simp only [Int.natAbs_natCast]
    rw [hmain τ.natAbs, mul_div_assoc, div_self hg0, mul_one]
  · rw [acf, hτ]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    rw [hstatY.acvf_even, hmain τ.natAbs, mul_div_assoc, div_self hg0, mul_one]

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
