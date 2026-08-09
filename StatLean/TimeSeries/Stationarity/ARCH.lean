import StatLean.TimeSeries.Models.WhiteNoise
import StatLean.TimeSeries.Process.Stationary
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration

/-!
# Stationary ARCH(∞) processes: the Volterra construction (FY §2.1.5, Theorem 2.5)

**FY Theorem 2.5(i)** with the full §2.7.1 proof: under `Σ_j b_j < 1`, the ARCH(∞)
equation (FY eq. (2.15)) has a strictly stationary, integrable, nonnegative solution with
mean `a/(1 − Σ_j b_j)` — the **Volterra series**
`Y_t = a ξ_t (1 + Σ_{k≥1} Σ_{j₁,…,j_k} b_{j₁} ⋯ b_{j_k} ξ_{t−ℓ₁} ⋯ ξ_{t−ℓ_k})`
(`ℓ_m = (j₁+1) + ⋯ + (j_m+1)` partial sums of lags) — and it is the a.e.-unique
integrable solution; if `a = 0`, the only solution is `Y ≡ 0`.
Also: FY Theorem 2.5(ii) (finite second moment under eq. (2.16)) and Theorem 2.6 (the
finite-dimensional invariance principle) as statement-level DEBTS (FY cites both to
Giraitis–Kokoszka–Leipus 2000 without in-book proofs).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.5
(Theorem 2.5, eqs. (2.15)–(2.16), Theorem 2.6, pp. 37–38) and §2.7.1 (proof of Thm
2.5(i), eq. (2.68), pp. 78–79). (`FY §2.1.5 Thm 2.5–2.6; §2.7.1`.)

**Proof formalization notes.**
* All terms are nonnegative, so the Volterra series converges by monotone convergence
  (Tonelli over the countable index set of finite lag-tuples); its layer-`k` expectation
  is `a(Σ_j b_j)^k` because strictly decreasing time indices make the `ξ`-product a
  product of independent mean-one factors.
* Strict stationarity: `Y_t` is a fixed measurable function of the shifted i.i.d. family
  `(ξ_{t−k})_{k≥0}`; the finite-dimensional laws transport along the shift-invariance of
  the infinite product law (pinned `Probability/ProductMeasure` +
  `iIndepFun` infinite-product characterization).
* Uniqueness iterates FY eq. (2.68) and uses the model's `indep_past` field (the implicit
  semantics FY's proof uses, surfaced in `IsARCHInf`). Because every term is nonnegative,
  the iteration is used in the *sharper* form: dropping the (nonnegative) depth-`k`
  remainder shows every solution dominates the whole Volterra series, while one single
  application of `indep_past` pins each integrable stationary solution's mean to
  `a/(1 − Σ_j b_j)`; a nonnegative difference of integral zero is a.e. zero. This replaces
  FY's Markov/Borel–Cantelli tail argument, which would need `ξ_t` to be independent of the
  *join* of the two solutions' pasts with the noise's own past — strictly more than the
  frozen `IsARCHInf.indep_past` supplies.

**Bibliographic comments.** L. Giraitis, P. Kokoszka and R. Leipus, "Stationary ARCH
models: dependence structure and central limit theorem", *Econometric Theory* **16**
(2000), 3–22. The Volterra-expansion method for random recurrences goes back to
V. Volterra's integral-equation calculus; in the ARCH context it was introduced by
Giraitis–Kokoszka–Leipus. ARCH itself is R. F. Engle (1982).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The i.i.d.-noise input data for the ARCH(∞) construction: a nonnegative i.i.d.
family with unit mean (the `ξ` of FY eq. (2.15)), packaged as a `Prop`. -/
structure IsARCHNoise (ξ : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- Constitutive (FY eq. (2.15)): the noise variables are random variables. -/
  measurable : ∀ t, Measurable (ξ t)
  /-- Constitutive (FY eq. (2.15)): nonnegativity. -/
  nonneg : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ ξ t ω
  /-- Constitutive (FY eq. (2.15)): mutual independence. -/
  iIndep : iIndepFun ξ μ
  /-- Constitutive (FY eq. (2.15)): identical distribution. -/
  identDistrib : ∀ s t, IdentDistrib (ξ s) (ξ t) μ μ
  /-- Constitutive (FY eq. (2.15)): integrable with `E ξ = 1`. -/
  integrable : Integrable (ξ 0) μ
  integral_eq_one : ∫ ω, ξ 0 ω ∂μ = 1

/-! ### The Volterra series (FY §2.7.1)

The construction is packaged as a fixed measurable functional of the *noise path* so that
strict stationarity is a transport along the shift-invariance of the path law. -/

/-- Layer `k` of the Volterra series read off a noise path `p` at time `0`:
`Λ₀(p) = 1`, `Λ_{k+1}(p) = Σ_j b_j · p(−1−j) · Λ_k(p(· − 1 − j))`. Working in `ℝ≥0∞` makes
the (nonnegative) series unconditionally convergent, so no summability side conditions are
carried through the construction. -/
private noncomputable def archLayer (bc : ℕ → ℝ) : ℕ → (ℤ → ℝ) → ℝ≥0∞
  | 0, _ => 1
  | k + 1, p => ∑' j : ℕ, ENNReal.ofReal (bc j) * ENNReal.ofReal (p (-1 - (j : ℤ)))
      * archLayer bc k fun s => p (s + (-1 - (j : ℤ)))

/-- The noise path seen from time `t`. -/
private def archPath (ξ : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℤ → ℝ := fun s => ξ (s + t) ω

/-- `Σ_j b_j` in `ℝ≥0∞`. -/
private noncomputable def archS (bc : ℕ → ℝ) : ℝ≥0∞ := ∑' j : ℕ, ENNReal.ofReal (bc j)

/-- The Volterra series at time `t`, valued in `ℝ≥0∞` (FY §2.7.1). -/
private noncomputable def archZ (a : ℝ) (bc : ℕ → ℝ) (ξ : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal a * ENNReal.ofReal (ξ t ω) * ∑' k : ℕ, archLayer bc k (archPath ξ t ω)

/-- The Volterra solution as a fixed measurable functional of the noise path. -/
private noncomputable def archFun (a : ℝ) (bc : ℕ → ℝ) (p : ℤ → ℝ) : ℝ :=
  (ENNReal.ofReal a * ENNReal.ofReal (p 0) * ∑' k : ℕ, archLayer bc k p).toReal

/-- The Volterra solution. -/
private noncomputable def archSol (a : ℝ) (bc : ℕ → ℝ) (ξ : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  archFun a bc (archPath ξ t ω)

omit [MeasurableSpace Ω] in
private lemma archSol_eq_toReal (a : ℝ) (bc : ℕ → ℝ) (ξ : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    archSol a bc ξ t ω = (archZ a bc ξ t ω).toReal := by
  simp [archSol, archFun, archZ, archPath]

omit [MeasurableSpace Ω] in
/-- The layer recursion along the process time index. -/
private lemma archLayer_succ_path (bc : ℕ → ℝ) (ξ : ℤ → Ω → ℝ) (k : ℕ) (t : ℤ) (ω : Ω) :
    archLayer bc (k + 1) (archPath ξ t ω)
      = ∑' j : ℕ, ENNReal.ofReal (bc j) * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
          * archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω) := by
  simp only [archLayer]
  refine tsum_congr fun j => ?_
  have h1 : archPath ξ t ω (-1 - (j : ℤ)) = ξ (t - 1 - (j : ℕ)) ω := by
    simp only [archPath]; congr 1; ring
  have h2 : (fun s => archPath ξ t ω (s + (-1 - (j : ℤ))))
      = archPath ξ (t - 1 - (j : ℕ)) ω := by
    funext s; simp only [archPath]; congr 1; ring
  rw [h1, h2]

/-- Path-space measurability of every layer. -/
private lemma measurable_archLayer (bc : ℕ → ℝ) (k : ℕ) : Measurable (archLayer bc k) := by
  induction k with
  | zero => simpa only [archLayer] using measurable_const
  | succ k ih =>
    simp only [archLayer]
    refine Measurable.ennreal_tsum fun j => ?_
    exact (measurable_const.mul
      ((measurable_pi_apply _).ennreal_ofReal)).mul
      (ih.comp (measurable_pi_lambda _ fun s => measurable_pi_apply _))

private lemma measurable_archFun (a : ℝ) (bc : ℕ → ℝ) : Measurable (archFun a bc) :=
  (((measurable_const.mul ((measurable_pi_apply _).ennreal_ofReal)).mul
    (Measurable.ennreal_tsum fun k => measurable_archLayer bc k)).ennreal_toReal)

/-- **Causality of a Volterra layer**: `archLayer bc k p` reads `p` only at coordinates
`≤ 0` (indeed only at `< 0` for `k ≥ 1`), because every recursion step steps back by at
least one unit of time. -/
private lemma archLayer_congr (bc : ℕ → ℝ) (k : ℕ) : ∀ {r r' : ℤ → ℝ},
    (∀ s ≤ (0 : ℤ), r s = r' s) → archLayer bc k r = archLayer bc k r' := by
  induction k with
  | zero => intro r r' _; rfl
  | succ k ih =>
    intro r r' h
    simp only [archLayer]
    refine tsum_congr fun j => ?_
    have h1 : r (-1 - (j : ℤ)) = r' (-1 - (j : ℤ)) := h _ (by omega)
    have h2 : (archLayer bc k fun s => r (s + (-1 - (j : ℤ))))
        = archLayer bc k fun s => r' (s + (-1 - (j : ℤ))) :=
      ih fun s hs => h _ (by omega)
    rw [h1, h2]

/-- **Causality of the Volterra functional**: `archFun a bc p` depends only on the
coordinates `p s` with `s ≤ 0`. -/
private lemma archFun_congr (a : ℝ) (bc : ℕ → ℝ) {r r' : ℤ → ℝ}
    (h : ∀ s ≤ (0 : ℤ), r s = r' s) : archFun a bc r = archFun a bc r' := by
  simp only [archFun, h 0 le_rfl]
  rw [tsum_congr fun k => archLayer_congr bc k h]

private lemma measurable_archPath {ξ : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ξ t)) (t : ℤ) :
    Measurable (archPath ξ t) :=
  measurable_pi_lambda _ fun s => hm (s + t)

private lemma measurable_archSol {ξ : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ξ t))
    (a : ℝ) (bc : ℕ → ℝ) (t : ℤ) : Measurable (archSol a bc ξ t) :=
  (measurable_archFun a bc).comp (measurable_archPath hm t)

/-! #### `σ`-algebra bookkeeping -/

omit [MeasurableSpace Ω] in
private lemma comap_le_sigmaLT {X : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    MeasurableSpace.comap (X s) inferInstance ≤ sigmaLT X t :=
  le_iSup₂ (f := fun s (_ : s ∈ Set.Iio t) => MeasurableSpace.comap (X s) inferInstance) s hst

omit [MeasurableSpace Ω] in
private lemma sigmaLT_mono {X : ℤ → Ω → ℝ} {s t : ℤ} (hst : s ≤ t) :
    sigmaLT X s ≤ sigmaLT X t :=
  iSup₂_le fun _ hu => comap_le_sigmaLT (lt_of_lt_of_le hu hst)

private lemma sigmaLT_le {X : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaLT X t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun _ _ => (hm _).comap_le

/-- **One-vs-past independence of the noise**: `ξ_t` is independent of `σ(ξ_s : s < t)`. -/
theorem indep_xi_sigmaLT {ξ : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ξ t))
    (hi : iIndepFun ξ μ) (t : ℤ) :
    Indep (MeasurableSpace.comap (ξ t) inferInstance) (sigmaLT ξ t) μ := by
  have hdisj : Disjoint ({t} : Set ℤ) (Set.Iio t) :=
    Set.disjoint_singleton_left.2 (by simp)
  have := indep_iSup_of_disjoint
    (m := fun s : ℤ => MeasurableSpace.comap (ξ s) inferInstance)
    (fun s => (hm s).comap_le) hi hdisj
  simpa using this

omit [MeasurableSpace Ω] in
/-- Each layer, read at time `t`, is measurable for the strict past `σ(ξ_s : s < t)`. -/
private lemma measurable_archLayer_sigmaLT {ξ : ℤ → Ω → ℝ}
    (bc : ℕ → ℝ) (k : ℕ) : ∀ t : ℤ,
    Measurable[sigmaLT ξ t] fun ω => archLayer bc k (archPath ξ t ω) := by
  induction k with
  | zero => intro t; simpa only [archLayer] using measurable_const
  | succ k ih =>
    intro t
    simp only [archLayer_succ_path]
    refine Measurable.ennreal_tsum fun j => ?_
    have hlt : t - 1 - (j : ℕ) < t := by
      have : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      omega
    have h1 : Measurable[sigmaLT ξ t] fun ω => ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω) :=
      ((Measurable.of_comap_le (le_refl
        (MeasurableSpace.comap (ξ (t - 1 - (j : ℕ))) inferInstance))).mono
          (comap_le_sigmaLT hlt) le_rfl).ennreal_ofReal
    exact (measurable_const.mul h1).mul
      ((ih (t - 1 - (j : ℕ))).mono (sigmaLT_mono hlt.le) le_rfl)

/-! #### Layer expectations -/

private lemma measurable_archLayer_path {ξ : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ξ t))
    (bc : ℕ → ℝ) (k : ℕ) (t : ℤ) :
    Measurable fun ω => archLayer bc k (archPath ξ t ω) :=
  (measurable_archLayer bc k).comp (measurable_archPath hm t)

/-- The noise has unit `ℝ≥0∞`-mean at every time. -/
private lemma lintegral_ofReal_xi {ξ : ℤ → Ω → ℝ}
    (hnn : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ ξ t ω) (hid : ∀ s t, IdentDistrib (ξ s) (ξ t) μ μ)
    (hint : Integrable (ξ 0) μ) (hmean : ∫ ω, ξ 0 ω ∂μ = 1) (s : ℤ) :
    ∫⁻ ω, ENNReal.ofReal (ξ s ω) ∂μ = 1 := by
  have hi : Integrable (ξ s) μ := (hid 0 s).integrable_snd hint
  have h := ofReal_integral_eq_lintegral_ofReal hi (hnn s)
  rw [← h, (hid s 0).integral_eq, hmean, ENNReal.ofReal_one]

/-- **Layer expectation** (FY §2.7.1): the layer-`k` term integrates to `(Σ_j b_j)^k`,
because the `ξ`-factors sit at strictly decreasing times, hence are independent with mean
one. -/
private lemma lintegral_archLayer [IsProbabilityMeasure μ] {ξ : ℤ → Ω → ℝ} {bc : ℕ → ℝ}
    (hm : ∀ t, Measurable (ξ t)) (hi : iIndepFun ξ μ)
    (hnn : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ ξ t ω) (hid : ∀ s t, IdentDistrib (ξ s) (ξ t) μ μ)
    (hint : Integrable (ξ 0) μ) (hmean : ∫ ω, ξ 0 ω ∂μ = 1) (k : ℕ) : ∀ t : ℤ,
    ∫⁻ ω, archLayer bc k (archPath ξ t ω) ∂μ = archS bc ^ k := by
  induction k with
  | zero => intro t; simp [archLayer]
  | succ k ih =>
    intro t
    have hterm : ∀ j : ℕ,
        ∫⁻ ω, ENNReal.ofReal (bc j) * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
            * archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω) ∂μ
          = ENNReal.ofReal (bc j) * archS bc ^ k := by
      intro j
      have hlt : t - 1 - (j : ℕ) < t := by
        have : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
        omega
      have hprod : ∀ ω, ENNReal.ofReal (bc j) * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
          * archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω)
          = ENNReal.ofReal (bc j) * (ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
              * archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω)) := fun ω => mul_assoc _ _ _
      simp only [hprod]
      rw [lintegral_const_mul _ (((hm _).ennreal_ofReal).mul
          (measurable_archLayer_path hm bc k _)),
        lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
          (hm _).comap_le (sigmaLT_le hm _) (indep_xi_sigmaLT hm hi _)
          (Measurable.of_comap_le le_rfl).ennreal_ofReal
          (measurable_archLayer_sigmaLT bc k _),
        lintegral_ofReal_xi hnn hid hint hmean, one_mul, ih]
    simp only [archLayer_succ_path]
    rw [lintegral_tsum fun j => ((measurable_const.mul ((hm _).ennreal_ofReal)).mul
      (measurable_archLayer_path hm bc k _)).aemeasurable]
    simp only [hterm]
    rw [ENNReal.tsum_mul_right, pow_succ']
    rfl

/-- The Volterra series is a.e. finite with total `ℝ≥0∞`-mass `(1 − Σ_j b_j)⁻¹`. -/
private lemma lintegral_archW [IsProbabilityMeasure μ] {ξ : ℤ → Ω → ℝ} {bc : ℕ → ℝ}
    (hm : ∀ t, Measurable (ξ t)) (hi : iIndepFun ξ μ)
    (hnn : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ ξ t ω) (hid : ∀ s t, IdentDistrib (ξ s) (ξ t) μ μ)
    (hint : Integrable (ξ 0) μ) (hmean : ∫ ω, ξ 0 ω ∂μ = 1) (t : ℤ) :
    ∫⁻ ω, (∑' k : ℕ, archLayer bc k (archPath ξ t ω)) ∂μ = (1 - archS bc)⁻¹ := by
  rw [lintegral_tsum fun k => (measurable_archLayer_path hm bc k t).aemeasurable]
  simp only [lintegral_archLayer hm hi hnn hid hint hmean]
  exact ENNReal.tsum_geometric _

/-- `Σ_j b_j` as an `ℝ≥0∞` scalar. -/
private lemma archS_eq {bc : ℕ → ℝ} (hbc : ∀ j, 0 ≤ bc j)
    (hsum : Summable bc) : archS bc = ENNReal.ofReal (∑' j, bc j) :=
  (ENNReal.ofReal_tsum_of_nonneg hbc hsum).symm

/-- The total `ℝ≥0∞`-mass of the Volterra series at any time. -/
private lemma lintegral_archZ [IsProbabilityMeasure μ] {a : ℝ} {bc : ℕ → ℝ} {ξ : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ξ t)) (hi : iIndepFun ξ μ)
    (hnn : ∀ t, ∀ᵐ ω ∂μ, 0 ≤ ξ t ω) (hid : ∀ s t, IdentDistrib (ξ s) (ξ t) μ μ)
    (hint : Integrable (ξ 0) μ) (hmean : ∫ ω, ξ 0 ω ∂μ = 1) (t : ℤ) :
    ∫⁻ ω, archZ a bc ξ t ω ∂μ = ENNReal.ofReal a * (1 - archS bc)⁻¹ := by
  simp only [archZ, mul_assoc]
  rw [lintegral_const_mul _ (((hm t).ennreal_ofReal).mul
      (Measurable.ennreal_tsum fun k => measurable_archLayer_path hm bc k t)),
    lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
      (hm t).comap_le (sigmaLT_le hm t) (indep_xi_sigmaLT hm hi t)
      (Measurable.of_comap_le le_rfl).ennreal_ofReal
      (Measurable.ennreal_tsum fun k => measurable_archLayer_sigmaLT bc k t),
    lintegral_ofReal_xi hnn hid hint hmean, one_mul,
    lintegral_archW hm hi hnn hid hint hmean]

private lemma measurable_archZ {a : ℝ} {bc : ℕ → ℝ} {ξ : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ξ t)) (t : ℤ) : Measurable (archZ a bc ξ t) :=
  (measurable_const.mul ((hm t).ennreal_ofReal)).mul
    (Measurable.ennreal_tsum fun k => measurable_archLayer_path hm bc k t)

omit [MeasurableSpace Ω] in
/-- **The Volterra series solves the ARCH(∞) equation** in `ℝ≥0∞` (FY §2.7.1): peeling the
empty layer off the series is exactly one step of the recurrence. -/
private lemma archZ_recurrence (a : ℝ) (bc : ℕ → ℝ) (ξ : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) :
    archZ a bc ξ t ω = ENNReal.ofReal (ξ t ω)
      * (ENNReal.ofReal a
          + ∑' j : ℕ, ENNReal.ofReal (bc j) * archZ a bc ξ (t - 1 - (j : ℕ)) ω) := by
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ≥0∞,
      (∑' j : ℕ, ENNReal.ofReal (bc j) * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
        * ∑' k : ℕ, archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω)) = T := ⟨_, rfl⟩
  have h1 : (∑' k : ℕ, archLayer bc (k + 1) (archPath ξ t ω)) = T := by
    rw [← hTdef]
    simp only [archLayer_succ_path]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun j => ENNReal.tsum_mul_left
  have hW : (∑' k : ℕ, archLayer bc k (archPath ξ t ω)) = 1 + T := by
    rw [tsum_eq_zero_add' (f := fun k : ℕ => archLayer bc k (archPath ξ t ω)) ENNReal.summable, h1]
    rfl
  have hT : (∑' j : ℕ, ENNReal.ofReal (bc j) * archZ a bc ξ (t - 1 - (j : ℕ)) ω)
      = ENNReal.ofReal a * T := by
    rw [← hTdef, ← ENNReal.tsum_mul_left]
    exact tsum_congr fun j => by simp only [archZ]; ring
  rw [hT]
  simp only [archZ]
  rw [hW]
  ring

/-- **Shift-invariance of the noise path law** — the reusable brick behind strict
stationarity: an i.i.d. family has the same `ℤ`-indexed path law before and after a time
shift, since both are the same infinite product measure. -/
private lemma map_path_shift [IsProbabilityMeasure μ] {ξ : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ξ t)) (hi : iIndepFun ξ μ)
    (hid : ∀ s t, IdentDistrib (ξ s) (ξ t) μ μ) (c : ℤ) :
    (μ.map fun ω (s : ℤ) => ξ (s + c) ω) = μ.map fun ω (s : ℤ) => ξ s ω := by
  have hinj : Function.Injective fun s : ℤ => s + c := fun x y h => by simpa using h
  have h1 : iIndepFun (fun s : ℤ => ξ (s + c)) μ := hi.precomp hinj
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map fun s => hm (s + c)).1 h1,
    (iIndepFun_iff_map_fun_eq_infinitePi_map hm).1 hi]
  exact congrArg Measure.infinitePi (funext fun s => (hid (s + c) s).map_eq)

/-- **Strict stationarity of a path functional of an i.i.d. family** — the reusable brick
behind FY Thm 2.5(i)'s stationarity claim (and behind FY Thm 4.4's, through the ARCH(∞)
reduction): if `X_t = F(ξ_{·+t})` for one fixed measurable `F`, then `X` is strictly
stationary, because the shifted path laws all coincide (`map_path_shift`). -/
theorem isStrictlyStationary_of_shift_comp [IsProbabilityMeasure μ] {ξ : ℤ → Ω → ℝ}
    (hm : ∀ t, Measurable (ξ t)) (hi : iIndepFun ξ μ)
    (hid : ∀ s t, IdentDistrib (ξ s) (ξ t) μ μ) {F : (ℤ → ℝ) → ℝ} (hF : Measurable F) :
    IsStrictlyStationary (fun t ω => F fun s => ξ (s + t) ω) μ := by
  intro n tt k
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (ℤ → ℝ) → (Fin n → ℝ),
      Ψ = fun p i => F fun s => p (s + tt i) := ⟨_, rfl⟩
  have hΨm : Measurable Ψ := by
    rw [hΨ]
    exact measurable_pi_lambda _ fun i => hF.comp
      (measurable_pi_lambda _ fun s => measurable_pi_apply (s + tt i))
  have hmb : ∀ c : ℤ, Measurable fun ω (s : ℤ) => ξ (s + c) ω :=
    fun c => measurable_pi_lambda _ fun s => hm (s + c)
  have hfac : ∀ c : ℤ, (fun ω (i : Fin n) => F fun s => ξ (s + (tt i + c)) ω)
      = Ψ ∘ fun ω (s : ℤ) => ξ (s + c) ω := by
    intro c
    funext ω i
    simp only [hΨ, Function.comp_apply, add_assoc]
  have h0 : (fun ω (i : Fin n) => F fun s => ξ (s + tt i) ω)
      = Ψ ∘ fun ω (s : ℤ) => ξ s ω := by simpa using hfac 0
  rw [hfac k, h0, ← Measure.map_map hΨm (hmb k),
    ← Measure.map_map hΨm (measurable_pi_lambda _ fun s : ℤ => hm s),
    map_path_shift hm hi hid k]

/-- **FY Theorem 2.5(i), existence** (proof: §2.7.1 Volterra series): if
`Σ_j bc j < 1`, there is a strictly stationary, integrable, a.e.-nonnegative solution of
the ARCH(∞) equation over the given noise, with `E Y_t = a / (1 − Σ_j bc j)`.

The final clause exposes the solution as a **measurable causal path functional** of the
noise: `Y_t = G(ξ_{·+t})` for one fixed measurable `G` that reads its argument only at
coordinates `≤ 0`. Everything the §2.7.1 construction knows about the solution's
*dependence structure* is in that clause: causality gives `σ(Y_s : s < t) ≤ σ(ξ_u : u < t)`
and shift-equivariance gives strict stationarity of any further functional built from
`Y` and `ξ` jointly (`isStrictlyStationary_of_shift_comp`). This is what makes the
theorem reusable — e.g. FY Thm 4.4's GARCH construction needs `X_t = σ_t ε_t` to be
independent of its own past and strictly stationary, neither of which follows from
`IsARCHInf`/`IsStrictlyStationary Y` alone. -/
theorem exists_stationary_archInf [IsProbabilityMeasure μ]
    {a : ℝ} {bc : ℕ → ℝ} {ξ : ℤ → Ω → ℝ}
    -- USER-INPUT: coefficients; FY eq. (2.15)
    (ha : 0 ≤ a) (hbc : ∀ j, 0 ≤ bc j)
    -- USER-INPUT: contraction Σ b_j < 1; FY Thm 2.5(i)
    (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    -- USER-INPUT: the noise; FY eq. (2.15)
    (hξ : IsARCHNoise ξ μ) :
    ∃ Y : ℤ → Ω → ℝ, IsARCHInf a bc Y ξ μ ∧ IsStrictlyStationary Y μ ∧
      (∀ t, Integrable (Y t) μ) ∧ (∀ t, ∫ ω, Y t ω ∂μ = a / (1 - ∑' j, bc j)) ∧
      ∃ G : (ℤ → ℝ) → ℝ, Measurable G ∧ (∀ t ω, Y t ω = G fun s => ξ (s + t) ω) ∧
        ∀ r r' : ℤ → ℝ, (∀ s ≤ (0 : ℤ), r s = r' s) → G r = G r' := by
  obtain ⟨hm, hnn, hi, hid, hint, hmean⟩ := hξ
  -- The contraction constant, in `ℝ≥0∞`.
  have hSeq : archS bc = ENNReal.ofReal (∑' j, bc j) := archS_eq hbc hsum
  have hS1 : archS bc < 1 := by rw [hSeq]; exact ENNReal.ofReal_lt_one.2 hlt
  have hinvfin : (1 - archS bc)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hS1).ne'
  have hden : (1 - archS bc).toReal = 1 - ∑' j, bc j := by
    rw [ENNReal.toReal_sub_of_le hS1.le ENNReal.one_ne_top, ENNReal.toReal_one, hSeq,
      ENNReal.toReal_ofReal (tsum_nonneg hbc)]
  -- The Volterra series has finite total mass at every time, hence is a.e. finite.
  have hZint : ∀ t : ℤ, ∫⁻ ω, archZ a bc ξ t ω ∂μ = ENNReal.ofReal a * (1 - archS bc)⁻¹ :=
    fun t => lintegral_archZ hm hi hnn hid hint hmean t
  have hZtop : ∀ t : ℤ, ∫⁻ ω, archZ a bc ξ t ω ∂μ ≠ ∞ := fun t => by
    rw [hZint t]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hinvfin
  have hZae : ∀ t : ℤ, ∀ᵐ ω ∂μ, archZ a bc ξ t ω < ∞ :=
    fun t => ae_lt_top (measurable_archZ hm t) (hZtop t)
  have hSolZ : ∀ (t : ℤ) (ω : Ω), archSol a bc ξ t ω = (archZ a bc ξ t ω).toReal :=
    archSol_eq_toReal a bc ξ
  -- Integrability and the mean.
  have hintY : ∀ t : ℤ, Integrable (archSol a bc ξ t) μ := by
    intro t
    refine ⟨(measurable_archSol hm a bc t).aestronglyMeasurable, ?_⟩
    have hcong : ∫⁻ ω, ‖archSol a bc ξ t ω‖ₑ ∂μ = ∫⁻ ω, archZ a bc ξ t ω ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hZae t] with ω hω
      rw [hSolZ, Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω.ne]
    change ∫⁻ ω, ‖archSol a bc ξ t ω‖ₑ ∂μ < ∞
    rw [hcong]
    exact lt_top_iff_ne_top.2 (hZtop t)
  have hmeanY : ∀ t : ℤ, ∫ ω, archSol a bc ξ t ω ∂μ = a / (1 - ∑' j, bc j) := by
    intro t
    have h1 : ∫ ω, archSol a bc ξ t ω ∂μ = (∫⁻ ω, archZ a bc ξ t ω ∂μ).toReal := by
      simp only [hSolZ]
      exact integral_toReal (measurable_archZ hm t).aemeasurable (hZae t)
    rw [h1, hZint t, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_inv, hden]
    ring
  -- The recurrence, transported from `ℝ≥0∞` to `ℝ` on the a.e.-finite set.
  have hbcR : ∀ j : ℕ, (ENNReal.ofReal (bc j)).toReal = bc j :=
    fun j => ENNReal.toReal_ofReal (hbc j)
  have hrec : ∀ t : ℤ, archSol a bc ξ t =ᵐ[μ]
      fun ω => (a + ∑' j : ℕ, bc j * archSol a bc ξ (t - 1 - (j : ℕ)) ω) * ξ t ω := by
    intro t
    have hterm : ∀ j : ℕ, ∫⁻ ω, ENNReal.ofReal (bc j) * archZ a bc ξ (t - 1 - (j : ℕ)) ω ∂μ
        = ENNReal.ofReal (bc j) * (ENNReal.ofReal a * (1 - archS bc)⁻¹) := fun j => by
      rw [lintegral_const_mul _ (measurable_archZ hm _), hZint]
    have hTint : ∫⁻ ω, (∑' j : ℕ, ENNReal.ofReal (bc j) * archZ a bc ξ (t - 1 - (j : ℕ)) ω) ∂μ
        = archS bc * (ENNReal.ofReal a * (1 - archS bc)⁻¹) := by
      rw [lintegral_tsum fun j =>
        (measurable_const.mul (measurable_archZ hm (t - 1 - (j : ℕ)))).aemeasurable]
      simp only [hterm]
      exact ENNReal.tsum_mul_right
    have hTae : ∀ᵐ ω ∂μ,
        (∑' j : ℕ, ENNReal.ofReal (bc j) * archZ a bc ξ (t - 1 - (j : ℕ)) ω) < ∞ := by
      refine ae_lt_top (Measurable.ennreal_tsum fun j =>
        measurable_const.mul (measurable_archZ hm (t - 1 - (j : ℕ)))) ?_
      rw [hTint]
      exact ENNReal.mul_ne_top hS1.ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hinvfin)
    filter_upwards [hnn t, ae_all_iff.2 fun j : ℕ => hZae (t - 1 - (j : ℕ)), hTae]
      with ω hξω hZω hTω
    simp only [hSolZ]
    rw [archZ_recurrence a bc ξ t ω, ENNReal.toReal_mul, ENNReal.toReal_ofReal hξω,
      ENNReal.toReal_add ENNReal.ofReal_ne_top hTω.ne, ENNReal.toReal_ofReal ha,
      ENNReal.tsum_toReal_eq fun j => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hZω j).ne]
    simp only [ENNReal.toReal_mul, hbcR]
    ring
  -- The past of the solution is contained in the past of the noise.
  have hmeasSolLT : ∀ t s : ℤ, s < t → Measurable[sigmaLT ξ t] (archSol a bc ξ s) := by
    intro t s hst
    have he : archSol a bc ξ s = fun ω => (archZ a bc ξ s ω).toReal := funext (hSolZ s)
    rw [he]
    refine Measurable.ennreal_toReal ?_
    change Measurable[sigmaLT ξ t] fun ω => ENNReal.ofReal a * ENNReal.ofReal (ξ s ω)
      * ∑' k : ℕ, archLayer bc k (archPath ξ s ω)
    refine (measurable_const.mul ?_).mul (Measurable.ennreal_tsum fun k =>
      (measurable_archLayer_sigmaLT bc k s).mono (sigmaLT_mono hst.le) le_rfl)
    exact ((Measurable.of_comap_le
      (le_refl (MeasurableSpace.comap (ξ s) inferInstance))).mono
        (comap_le_sigmaLT hst) le_rfl).ennreal_ofReal
  -- Strict stationarity: the solution is a fixed functional of the shifted noise path.
  have hstat : IsStrictlyStationary (archSol a bc ξ) μ :=
    isStrictlyStationary_of_shift_comp hm hi hid (measurable_archFun a bc)
  exact ⟨archSol a bc ξ,
    { a_nonneg := ha
      bc_nonneg := hbc
      measurableY := fun t => measurable_archSol hm a bc t
      measurableXi := hm
      xi_nonneg := hnn
      iIndep := hi
      identDistrib := hid
      integrable_xi := hint
      integral_xi := hmean
      indep_past := fun t => indep_of_indep_of_le_right (indep_xi_sigmaLT hm hi t)
        (iSup₂_le fun s hs => (hmeasSolLT t s hs).comap_le)
      Y_nonneg := fun t => Filter.Eventually.of_forall fun ω => by
        rw [hSolZ]; exact ENNReal.toReal_nonneg
      recurrence := hrec },
    hstat, hintY, hmeanY,
    archFun a bc, measurable_archFun a bc, fun _ _ => rfl,
    fun _ _ h => archFun_congr a bc h⟩

/-! ### Uniqueness (FY §2.7.1)

The route is the nonnegative one FY's iteration (eq. (2.68)) makes available: iterating the
recurrence `k` times shows that *every* solution dominates the depth-`k` Volterra partial
sum, hence the whole Volterra series; and one single application of the model's
`indep_past` pins the mean of every integrable stationary solution to `a/(1 − Σ_j b_j)`,
the mean of the Volterra series itself. A nonnegative difference with vanishing integral is
a.e. zero. (Iterating `indep_past` past the first level is *not* available from the frozen
data model — after one step the conditioning σ-algebra is the join of the solution's past
with the noise's past, and `IsARCHInf` only supplies independence from the former.) -/

private lemma archNoise_of_archInf {a : ℝ} {bc : ℕ → ℝ} {Y ξ : ℤ → Ω → ℝ}
    (h : IsARCHInf a bc Y ξ μ) : IsARCHNoise ξ μ :=
  ⟨h.measurableXi, h.xi_nonneg, h.iIndep, h.identDistrib, h.integrable_xi, h.integral_xi⟩

omit [MeasurableSpace Ω] in
private lemma archS_lt_one {bc : ℕ → ℝ} (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc)
    (hlt : ∑' j, bc j < 1) : archS bc < 1 := by
  rw [archS_eq hbc hsum]; exact ENNReal.ofReal_lt_one.2 hlt

omit [MeasurableSpace Ω] in
private lemma archS_ne_top {bc : ℕ → ℝ} (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc) :
    archS bc ≠ ∞ := by rw [archS_eq hbc hsum]; exact ENNReal.ofReal_ne_top

omit [MeasurableSpace Ω] in
private lemma archS_inv_ne_top {bc : ℕ → ℝ} (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc)
    (hlt : ∑' j, bc j < 1) : (1 - archS bc)⁻¹ ≠ ∞ :=
  ENNReal.inv_ne_top.2 (tsub_pos_of_lt (archS_lt_one hbc hsum hlt)).ne'

omit [MeasurableSpace Ω] in
private lemma toReal_one_sub_archS {bc : ℕ → ℝ} (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc)
    (hlt : ∑' j, bc j < 1) : (1 - archS bc).toReal = 1 - ∑' j, bc j := by
  rw [ENNReal.toReal_sub_of_le (archS_lt_one hbc hsum hlt).le ENNReal.one_ne_top,
    ENNReal.toReal_one, archS_eq hbc hsum, ENNReal.toReal_ofReal (tsum_nonneg hbc)]

private lemma archZ_ae_lt_top [IsProbabilityMeasure μ] {a : ℝ} {bc : ℕ → ℝ} {ξ : ℤ → Ω → ℝ}
    (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    (hξ : IsARCHNoise ξ μ) (t : ℤ) : ∀ᵐ ω ∂μ, archZ a bc ξ t ω < ∞ := by
  refine ae_lt_top (measurable_archZ hξ.measurable t) ?_
  rw [lintegral_archZ hξ.measurable hξ.iIndep hξ.nonneg hξ.identDistrib hξ.integrable
    hξ.integral_eq_one t]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (archS_inv_ne_top hbc hsum hlt)

private lemma integrable_archSol [IsProbabilityMeasure μ] {a : ℝ} {bc : ℕ → ℝ} {ξ : ℤ → Ω → ℝ}
    (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    (hξ : IsARCHNoise ξ μ) (t : ℤ) : Integrable (archSol a bc ξ t) μ := by
  refine ⟨(measurable_archSol hξ.measurable a bc t).aestronglyMeasurable, ?_⟩
  have hcong : ∫⁻ ω, ‖archSol a bc ξ t ω‖ₑ ∂μ = ∫⁻ ω, archZ a bc ξ t ω ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [archZ_ae_lt_top hbc hsum hlt hξ t] with ω hω
    rw [archSol_eq_toReal, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hω.ne]
  change ∫⁻ ω, ‖archSol a bc ξ t ω‖ₑ ∂μ < ∞
  rw [hcong, lintegral_archZ hξ.measurable hξ.iIndep hξ.nonneg hξ.identDistrib
    hξ.integrable hξ.integral_eq_one t]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.2 (archS_inv_ne_top hbc hsum hlt))

private lemma integral_archSol [IsProbabilityMeasure μ] {a : ℝ} {bc : ℕ → ℝ} {ξ : ℤ → Ω → ℝ}
    (ha : 0 ≤ a) (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    (hξ : IsARCHNoise ξ μ) (t : ℤ) :
    ∫ ω, archSol a bc ξ t ω ∂μ = a / (1 - ∑' j, bc j) := by
  have h1 : ∫ ω, archSol a bc ξ t ω ∂μ = (∫⁻ ω, archZ a bc ξ t ω ∂μ).toReal := by
    simp only [archSol_eq_toReal]
    exact integral_toReal (measurable_archZ hξ.measurable t).aemeasurable
      (archZ_ae_lt_top hbc hsum hlt hξ t)
  rw [h1, lintegral_archZ hξ.measurable hξ.iIndep hξ.nonneg hξ.identDistrib hξ.integrable
      hξ.integral_eq_one t,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_inv,
    toReal_one_sub_archS hbc hsum hlt]
  ring

/-- Every integrable strictly stationary solution has a time-independent `ℝ≥0∞`-mean. -/
private lemma lintegral_ofReal_sol [IsProbabilityMeasure μ] {a : ℝ} {bc : ℕ → ℝ}
    {Y ξ : ℤ → Ω → ℝ} (h : IsARCHInf a bc Y ξ μ) (hint : ∀ t, Integrable (Y t) μ)
    (hstat : IsStrictlyStationary Y μ) (t : ℤ) :
    ∫⁻ ω, ENNReal.ofReal (Y t ω) ∂μ = ENNReal.ofReal (∫ ω, Y 0 ω ∂μ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hint t) (h.Y_nonneg t),
    (hstat.identDistrib h.measurableY t 0).integral_eq]

/-- The driving series `Σ_j b_j Y_{t−1−j}` is a.e. finite for any integrable stationary
solution — the summability side condition the real-valued recurrence needs. -/
theorem archInf_tsum_ae_lt_top [IsProbabilityMeasure μ] {a : ℝ} {bc : ℕ → ℝ}
    {Y ξ : ℤ → Ω → ℝ} (hsum : Summable bc) (h : IsARCHInf a bc Y ξ μ)
    (hint : ∀ t, Integrable (Y t) μ) (hstat : IsStrictlyStationary Y μ) (t : ℤ) :
    ∀ᵐ ω ∂μ, (∑' j : ℕ, ENNReal.ofReal (bc j) * ENNReal.ofReal (Y (t - 1 - (j : ℕ)) ω)) < ∞ := by
  refine ae_lt_top (Measurable.ennreal_tsum fun j =>
    measurable_const.mul ((h.measurableY _).ennreal_ofReal)) ?_
  have hterm : ∀ j : ℕ, ∫⁻ ω, ENNReal.ofReal (bc j) * ENNReal.ofReal (Y (t - 1 - (j : ℕ)) ω) ∂μ
      = ENNReal.ofReal (bc j) * ENNReal.ofReal (∫ ω, Y 0 ω ∂μ) := fun j => by
    rw [lintegral_const_mul _ ((h.measurableY _).ennreal_ofReal),
      lintegral_ofReal_sol h hint hstat]
  rw [lintegral_tsum fun j =>
    (measurable_const.mul ((h.measurableY (t - 1 - (j : ℕ))).ennreal_ofReal)).aemeasurable]
  simp only [hterm]
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_ne_top (archS_ne_top h.bc_nonneg hsum) ENNReal.ofReal_ne_top

/-- The ARCH(∞) recurrence in `ℝ≥0∞`, for an arbitrary integrable stationary solution. -/
theorem archInf_ofReal_recurrence [IsProbabilityMeasure μ] {a : ℝ} {bc : ℕ → ℝ}
    {Y ξ : ℤ → Ω → ℝ} (hsum : Summable bc) (h : IsARCHInf a bc Y ξ μ)
    (hint : ∀ t, Integrable (Y t) μ) (hstat : IsStrictlyStationary Y μ) (t : ℤ) :
    ∀ᵐ ω ∂μ, ENNReal.ofReal (Y t ω) = ENNReal.ofReal (ξ t ω)
      * (ENNReal.ofReal a
        + ∑' j : ℕ, ENNReal.ofReal (bc j) * ENNReal.ofReal (Y (t - 1 - (j : ℕ)) ω)) := by
  filter_upwards [h.recurrence t, h.xi_nonneg t,
    ae_all_iff.2 fun j : ℕ => h.Y_nonneg (t - 1 - (j : ℕ)),
    archInf_tsum_ae_lt_top hsum h hint hstat t] with ω hrec hξω hYω hTω
  have hnn : ∀ j : ℕ, 0 ≤ bc j * Y (t - 1 - (j : ℕ)) ω :=
    fun j => mul_nonneg (h.bc_nonneg j) (hYω j)
  have hsumω : Summable fun j : ℕ => bc j * Y (t - 1 - (j : ℕ)) ω :=
    (ENNReal.summable_toReal hTω.ne).congr fun j => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (h.bc_nonneg j),
        ENNReal.toReal_ofReal (hYω j)]
  have hTnn : (0 : ℝ) ≤ ∑' j : ℕ, bc j * Y (t - 1 - (j : ℕ)) ω := tsum_nonneg hnn
  have hcv : ∀ j : ℕ, ENNReal.ofReal (bc j * Y (t - 1 - (j : ℕ)) ω)
      = ENNReal.ofReal (bc j) * ENNReal.ofReal (Y (t - 1 - (j : ℕ)) ω) :=
    fun j => ENNReal.ofReal_mul (h.bc_nonneg j)
  rw [hrec, ENNReal.ofReal_mul (add_nonneg h.a_nonneg hTnn),
    ENNReal.ofReal_add h.a_nonneg hTnn, ENNReal.ofReal_tsum_of_nonneg hnn hsumω]
  simp only [hcv]
  ring

omit [MeasurableSpace Ω] in
/-- Peeling the empty layer off a Volterra *partial* sum. -/
private lemma archLayer_partial_succ (bc : ℕ → ℝ) (ξ : ℤ → Ω → ℝ) (k : ℕ) (t : ℤ) (ω : Ω) :
    ∑ i ∈ Finset.range (k + 1), archLayer bc i (archPath ξ t ω)
      = 1 + ∑' j : ℕ, ENNReal.ofReal (bc j) * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
          * ∑ i ∈ Finset.range k, archLayer bc i (archPath ξ (t - 1 - (j : ℕ)) ω) := by
  have h0 : archLayer bc 0 (archPath ξ t ω) = 1 := rfl
  rw [Finset.sum_range_succ', h0, add_comm]
  congr 1
  simp only [archLayer_succ_path]
  rw [← Summable.tsum_finsetSum fun i _ => ENNReal.summable]
  exact tsum_congr fun j => (Finset.mul_sum _ _ _).symm

/-- **Every solution dominates the Volterra partial sums** (FY eq. (2.68) iterated): the
`k`-fold iteration of the recurrence, with the nonnegative remainder dropped. -/
private lemma archZ_partial_le [IsProbabilityMeasure μ] {a : ℝ} {bc : ℕ → ℝ}
    {Y ξ : ℤ → Ω → ℝ} (hsum : Summable bc) (h : IsARCHInf a bc Y ξ μ)
    (hint : ∀ t, Integrable (Y t) μ) (hstat : IsStrictlyStationary Y μ) (k : ℕ) :
    ∀ t : ℤ, ∀ᵐ ω ∂μ, ENNReal.ofReal a * ENNReal.ofReal (ξ t ω)
        * ∑ i ∈ Finset.range k, archLayer bc i (archPath ξ t ω)
      ≤ ENNReal.ofReal (Y t ω) := by
  induction k with
  | zero => intro t; filter_upwards with ω; simp
  | succ k ih =>
    intro t
    filter_upwards [archInf_ofReal_recurrence hsum h hint hstat t,
      ae_all_iff.2 fun j : ℕ => ih (t - 1 - (j : ℕ))] with ω hrec hih
    have hstep : ∀ j : ℕ, ENNReal.ofReal (bc j) * (ENNReal.ofReal a
          * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
          * ∑ i ∈ Finset.range k, archLayer bc i (archPath ξ (t - 1 - (j : ℕ)) ω))
        = ENNReal.ofReal a * (ENNReal.ofReal (bc j) * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
          * ∑ i ∈ Finset.range k, archLayer bc i (archPath ξ (t - 1 - (j : ℕ)) ω)) :=
      fun j => by ring
    have hL : ENNReal.ofReal a * ENNReal.ofReal (ξ t ω)
          * ∑ i ∈ Finset.range (k + 1), archLayer bc i (archPath ξ t ω)
        = ENNReal.ofReal (ξ t ω) * (ENNReal.ofReal a
            + ∑' j : ℕ, ENNReal.ofReal (bc j) * (ENNReal.ofReal a
                * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
                * ∑ i ∈ Finset.range k, archLayer bc i (archPath ξ (t - 1 - (j : ℕ)) ω))) := by
      rw [archLayer_partial_succ, tsum_congr hstep, ENNReal.tsum_mul_left]
      ring
    rw [hL, hrec]
    gcongr with j
    exact hih j

/-- **Every solution equals the Volterra series** (FY §2.7.1): it dominates it and has the
same (finite) mean. -/
private lemma archInf_eq_archSol [IsProbabilityMeasure μ] {a : ℝ} {bc : ℕ → ℝ}
    {Y ξ : ℤ → Ω → ℝ} (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    (h : IsARCHInf a bc Y ξ μ) (hint : ∀ t, Integrable (Y t) μ)
    (hstat : IsStrictlyStationary Y μ) (t : ℤ) :
    Y t =ᵐ[μ] archSol a bc ξ t := by
  have hξ : IsARCHNoise ξ μ := archNoise_of_archInf h
  -- domination
  have hdom : ∀ᵐ ω ∂μ, archSol a bc ξ t ω ≤ Y t ω := by
    filter_upwards [ae_all_iff.2 fun k : ℕ => archZ_partial_le hsum h hint hstat k t,
      h.Y_nonneg t] with ω hk hYω
    have hle : archZ a bc ξ t ω ≤ ENNReal.ofReal (Y t ω) := by
      rw [archZ, ENNReal.tsum_eq_iSup_nat, ENNReal.mul_iSup]
      exact iSup_le hk
    rw [archSol_eq_toReal]
    calc (archZ a bc ξ t ω).toReal
        ≤ (ENNReal.ofReal (Y t ω)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = Y t ω := ENNReal.toReal_ofReal hYω
  -- equal means
  have hmeanY : ∫ ω, Y t ω ∂μ = a / (1 - ∑' j, bc j) := by
    have hm := lintegral_ofReal_sol h hint hstat t
    have hGm : Measurable[sigmaLT Y t] fun ω => ENNReal.ofReal a
        + ∑' j : ℕ, ENNReal.ofReal (bc j) * ENNReal.ofReal (Y (t - 1 - (j : ℕ)) ω) := by
      refine measurable_const.add (Measurable.ennreal_tsum fun j => measurable_const.mul ?_)
      have hlt' : t - 1 - (j : ℕ) < t := by
        have : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
        omega
      exact ((Measurable.of_comap_le
        (le_refl (MeasurableSpace.comap (Y (t - 1 - (j : ℕ))) inferInstance))).mono
          (comap_le_sigmaLT hlt') le_rfl).ennreal_ofReal
    have hterm : ∀ j : ℕ, ∫⁻ ω, ENNReal.ofReal (bc j) * ENNReal.ofReal (Y (t - 1 - (j : ℕ)) ω) ∂μ
        = ENNReal.ofReal (bc j) * ENNReal.ofReal (∫ ω, Y 0 ω ∂μ) := fun j => by
      rw [lintegral_const_mul _ ((h.measurableY _).ennreal_ofReal),
        lintegral_ofReal_sol h hint hstat]
    have hG : ∫⁻ ω, (ENNReal.ofReal a
        + ∑' j : ℕ, ENNReal.ofReal (bc j) * ENNReal.ofReal (Y (t - 1 - (j : ℕ)) ω)) ∂μ
        = ENNReal.ofReal a + archS bc * ENNReal.ofReal (∫ ω, Y 0 ω ∂μ) := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_tsum fun j =>
          (measurable_const.mul ((h.measurableY (t - 1 - (j : ℕ))).ennreal_ofReal)).aemeasurable]
      simp only [hterm]
      rw [ENNReal.tsum_mul_right]
      rfl
    have hfix : ENNReal.ofReal (∫ ω, Y 0 ω ∂μ)
        = ENNReal.ofReal a + archS bc * ENNReal.ofReal (∫ ω, Y 0 ω ∂μ) :=
      calc ENNReal.ofReal (∫ ω, Y 0 ω ∂μ)
          = ∫⁻ ω, ENNReal.ofReal (Y t ω) ∂μ := hm.symm
        _ = ∫⁻ ω, ENNReal.ofReal (ξ t ω) * (ENNReal.ofReal a
              + ∑' j : ℕ, ENNReal.ofReal (bc j)
                * ENNReal.ofReal (Y (t - 1 - (j : ℕ)) ω)) ∂μ :=
            lintegral_congr_ae (archInf_ofReal_recurrence hsum h hint hstat t)
        _ = (∫⁻ ω, ENNReal.ofReal (ξ t ω) ∂μ) * ∫⁻ ω, (ENNReal.ofReal a
              + ∑' j : ℕ, ENNReal.ofReal (bc j)
                * ENNReal.ofReal (Y (t - 1 - (j : ℕ)) ω)) ∂μ :=
            lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
              (h.measurableXi t).comap_le (sigmaLT_le h.measurableY t) (h.indep_past t)
              (Measurable.of_comap_le le_rfl).ennreal_ofReal hGm
        _ = ENNReal.ofReal a + archS bc * ENNReal.ofReal (∫ ω, Y 0 ω ∂μ) := by
            rw [lintegral_ofReal_xi h.xi_nonneg h.identDistrib h.integrable_xi h.integral_xi,
              one_mul, hG]
    have hY0 : (0 : ℝ) ≤ ∫ ω, Y 0 ω ∂μ := integral_nonneg_of_ae (h.Y_nonneg 0)
    have hreal := congrArg ENNReal.toReal hfix
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (archS_ne_top h.bc_nonneg hsum) ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal h.a_nonneg, ENNReal.toReal_ofReal hY0,
      archS_eq h.bc_nonneg hsum, ENNReal.toReal_ofReal (tsum_nonneg h.bc_nonneg)] at hreal
    have hne : (1 : ℝ) - ∑' j, bc j ≠ 0 := by linarith
    rw [(hstat.identDistrib h.measurableY t 0).integral_eq, eq_div_iff hne]
    linear_combination hreal
  -- a nonnegative difference with zero integral
  have hdiff : Integrable (fun ω => Y t ω - archSol a bc ξ t ω) μ :=
    (hint t).sub (integrable_archSol h.bc_nonneg hsum hlt hξ t)
  have hzero : ∫ ω, (Y t ω - archSol a bc ξ t ω) ∂μ = 0 := by
    rw [integral_sub (hint t) (integrable_archSol h.bc_nonneg hsum hlt hξ t), hmeanY,
      integral_archSol h.a_nonneg h.bc_nonneg hsum hlt hξ t, sub_self]
  have hnn' : 0 ≤ᵐ[μ] fun ω => Y t ω - archSol a bc ξ t ω := by
    filter_upwards [hdom] with ω hω
    simpa using hω
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn' hdiff).1 hzero] with ω hω
  have h2 : Y t ω - archSol a bc ξ t ω = 0 := hω
  linarith

/-- **FY Theorem 2.5(i), uniqueness** (§2.7.1): two integrable solutions of the ARCH(∞)
equation over the same noise agree a.e. at every time. -/
theorem archInf_unique [IsProbabilityMeasure μ]
    {a : ℝ} {bc : ℕ → ℝ} {Y Y' ξ : ℤ → Ω → ℝ}
    (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    (h : IsARCHInf a bc Y ξ μ) (hint : ∀ t, Integrable (Y t) μ)
    -- USER-INPUT: stationarity of the compared solutions (uniform first moments);
    -- FY Thm 2.5(i) states uniqueness among strictly stationary solutions
    (hstat : IsStrictlyStationary Y μ)
    (h' : IsARCHInf a bc Y' ξ μ) (hint' : ∀ t, Integrable (Y' t) μ)
    (hstat' : IsStrictlyStationary Y' μ) (t : ℤ) :
    Y t =ᵐ[μ] Y' t :=
  (archInf_eq_archSol hsum hlt h hint hstat t).trans
    (archInf_eq_archSol hsum hlt h' hint' hstat' t).symm

/-- **FY Theorem 2.5(i), degenerate case**: if `a = 0`, every integrable strictly
stationary solution is a.e. zero. -/
theorem archInf_eq_zero_of_a_eq_zero [IsProbabilityMeasure μ]
    {bc : ℕ → ℝ} {Y ξ : ℤ → Ω → ℝ}
    (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    (h : IsARCHInf 0 bc Y ξ μ) (hint : ∀ t, Integrable (Y t) μ)
    (hstat : IsStrictlyStationary Y μ) (t : ℤ) :
    Y t =ᵐ[μ] 0 := by
  -- With `a = 0` the Volterra series vanishes identically, so the domination step is
  -- unnecessary: the common mean `a/(1 − Σ_j b_j)` is `0`, and `Y_t ≥ 0`.
  have h0 : archSol 0 bc ξ t =ᵐ[μ] 0 := by
    filter_upwards with ω
    simp [archSol, archFun]
  exact (archInf_eq_archSol hsum hlt h hint hstat t).trans h0

/-! ### The second moment (FY Theorem 2.5(ii))

Under eq. (2.16) the Volterra series is square-integrable, by a Minkowski estimate on its
layers: the `ξ`-factors of layer `k` sit at strictly decreasing times, so each recursion
step multiplies the `L²` norm by exactly `‖ξ‖₂ Σ_j b_j`, giving `‖Λ_k‖₂ ≤ (‖ξ‖₂ Σ_j b_j)^k`
and a geometric total. Since every integrable stationary solution *is* the Volterra series
(`archInf_eq_archSol`), the bound transfers to an arbitrary solution.

Everything is done in `ℝ≥0∞`, where the layers live; the two `rpow` bricks below are the
square root and its inverse. -/

omit [MeasurableSpace Ω] in
private lemma ennreal_sq_rpow_half (x : ℝ≥0∞) : (x ^ 2) ^ ((1 : ℝ) / 2) = x := by
  rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
  norm_num

omit [MeasurableSpace Ω] in
private lemma ennreal_rpow_half_sq (x : ℝ≥0∞) : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
  norm_num

/-- **Countable Minkowski inequality in `ℝ≥0∞`, at exponent `2`**: the `L²` norm of a sum
of nonnegative functions is at most the sum of their `L²` norms (stated in squared form,
so that no square root has to be extracted from the conclusion). -/
private lemma lintegral_sq_tsum_le {f : ℕ → Ω → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) :
    ∫⁻ ω, (∑' n : ℕ, f n ω) ^ 2 ∂μ
      ≤ (∑' n : ℕ, (∫⁻ ω, f n ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) ^ 2 := by
  have hcast : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [← ENNReal.rpow_natCast x 2]; norm_num
  have hFmeas : ∀ N : ℕ, Measurable fun ω => ∑ n ∈ Finset.range N, f n ω := fun N =>
    Finset.measurable_sum _ fun n _ => hf n
  have hmono : ∀ ω, Monotone fun N : ℕ => ∑ n ∈ Finset.range N, f n ω := by
    intro ω a b hab
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hab)
  -- finite Minkowski, by induction on the number of summands
  have hfin : ∀ N : ℕ, (∫⁻ ω, (∑ n ∈ Finset.range N, f n ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
      ≤ ∑ n ∈ Finset.range N, (∫⁻ ω, f n ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hle := ENNReal.lintegral_Lp_add_le (μ := μ) (p := 2)
        (f := fun ω => ∑ n ∈ Finset.range N, f n ω) (g := f N)
        (hFmeas N).aemeasurable (hf N).aemeasurable (by norm_num)
      simp only [Pi.add_apply, hcast] at hle
      have hrw : (∫⁻ ω, (∑ n ∈ Finset.range (N + 1), f n ω) ^ 2 ∂μ)
          = ∫⁻ ω, ((∑ n ∈ Finset.range N, f n ω) + f N ω) ^ 2 ∂μ :=
        lintegral_congr fun ω => by rw [Finset.sum_range_succ]
      rw [hrw, Finset.sum_range_succ]
      exact le_trans hle (add_le_add ih le_rfl)
  -- the squared partial sums increase to the squared series
  have hpt : ∀ ω, (∑' n : ℕ, f n ω) ^ 2
      = ⨆ N : ℕ, (∑ n ∈ Finset.range N, f n ω) ^ 2 := by
    intro ω
    rw [ENNReal.tsum_eq_iSup_nat]
    refine le_antisymm ?_ (iSup_le fun N => by
      gcongr
      exact le_iSup (fun M : ℕ => ∑ n ∈ Finset.range M, f n ω) N)
    rw [sq, ENNReal.iSup_mul]
    refine iSup_le fun N => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun M => le_iSup_of_le (max N M) ?_
    rw [sq]
    exact mul_le_mul' (hmono ω (le_max_left N M)) (hmono ω (le_max_right N M))
  rw [lintegral_congr hpt,
    lintegral_iSup (fun N => (hFmeas N).pow_const 2)
      (fun a b hab ω => pow_le_pow_left' (hmono ω hab) 2)]
  refine iSup_le fun N => ?_
  calc ∫⁻ ω, (∑ n ∈ Finset.range N, f n ω) ^ 2 ∂μ
      = ((∫⁻ ω, (∑ n ∈ Finset.range N, f n ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) ^ 2 :=
        (ennreal_rpow_half_sq _).symm
    _ ≤ (∑' n : ℕ, (∫⁻ ω, f n ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) ^ 2 := by
        gcongr
        exact (hfin N).trans (ENNReal.sum_le_tsum _)

/-- The noise has the same `ℝ≥0∞`-second moment at every time. -/
private lemma lintegral_sq_ofReal_xi {ξ : ℤ → Ω → ℝ}
    (hid : ∀ s t, IdentDistrib (ξ s) (ξ t) μ μ) (s : ℤ) :
    ∫⁻ ω, ENNReal.ofReal (ξ s ω) ^ 2 ∂μ = ∫⁻ ω, ENNReal.ofReal (ξ 0 ω) ^ 2 ∂μ := by
  have hu : Measurable fun x : ℝ => ENNReal.ofReal x ^ 2 :=
    ENNReal.measurable_ofReal.pow_const 2
  simpa [Function.comp_def] using ((hid s 0).comp hu).lintegral_eq

/-- The independence factorization at exponent `2`: the current noise is independent of
every functional of its strict past. -/
private lemma lintegral_sq_xi_mul {ξ : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ξ t))
    (hi : iIndepFun ξ μ) (s : ℤ) {g : Ω → ℝ≥0∞} (hg : Measurable[sigmaLT ξ s] g) :
    ∫⁻ ω, ENNReal.ofReal (ξ s ω) ^ 2 * g ω ∂μ
      = (∫⁻ ω, ENNReal.ofReal (ξ s ω) ^ 2 ∂μ) * ∫⁻ ω, g ω ∂μ :=
  lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (hm s).comap_le (sigmaLT_le hm s) (indep_xi_sigmaLT hm hi s)
    ((Measurable.of_comap_le le_rfl).ennreal_ofReal.pow_const 2) hg

/-- **The layer `L²` estimate** (FY eq. (2.16)): `‖Λ_k‖₂ ≤ (‖ξ‖₂ Σ_j b_j)^k`. -/
private lemma lintegral_sq_archLayer_le [IsProbabilityMeasure μ] {ξ : ℤ → Ω → ℝ} {bc : ℕ → ℝ}
    (hm : ∀ t, Measurable (ξ t)) (hi : iIndepFun ξ μ)
    (hid : ∀ s t, IdentDistrib (ξ s) (ξ t) μ μ) (k : ℕ) : ∀ t : ℤ,
    (∫⁻ ω, archLayer bc k (archPath ξ t ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
      ≤ ((∫⁻ ω, ENNReal.ofReal (ξ 0 ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * archS bc) ^ k := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ≥0∞,
      (∫⁻ ω, ENNReal.ofReal (ξ 0 ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) = r := ⟨_, rfl⟩
  simp only [hr]
  induction k with
  | zero => intro t; simp [archLayer]
  | succ k ih =>
    intro t
    -- each summand of the layer recursion, in `L²`
    have hstep : ∀ j : ℕ,
        (∫⁻ ω, (ENNReal.ofReal (bc j) * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
              * archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω)) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
          ≤ ENNReal.ofReal (bc j) * (r * (r * archS bc) ^ k) := by
      intro j
      have hlt : t - 1 - (j : ℕ) < t := by
        have : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
        omega
      have hexp : ∀ ω, (ENNReal.ofReal (bc j) * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
            * archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω)) ^ 2
          = ENNReal.ofReal (bc j) ^ 2 * (ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω) ^ 2
              * archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω) ^ 2) := fun ω => by
        rw [mul_pow, mul_pow, mul_assoc]
      have hI : (∫⁻ ω, (ENNReal.ofReal (bc j) * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
            * archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω)) ^ 2 ∂μ)
          = ENNReal.ofReal (bc j) ^ 2 * ((∫⁻ ω, ENNReal.ofReal (ξ 0 ω) ^ 2 ∂μ)
              * ∫⁻ ω, archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω) ^ 2 ∂μ) := by
        simp only [hexp]
        rw [lintegral_const_mul _ (((hm _).ennreal_ofReal.pow_const 2).mul
            ((measurable_archLayer_path hm bc k _).pow_const 2)),
          lintegral_sq_xi_mul hm hi (t - 1 - (j : ℕ))
            ((measurable_archLayer_sigmaLT bc k (t - 1 - (j : ℕ))).pow_const 2),
          lintegral_sq_ofReal_xi hid]
      rw [hI, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ (1:ℝ)/2),
        ennreal_sq_rpow_half, hr]
      gcongr
      exact ih (t - 1 - (j : ℕ))
    -- Minkowski over the summands
    have hminko := lintegral_sq_tsum_le (μ := μ)
      (f := fun (j : ℕ) ω => ENNReal.ofReal (bc j) * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
        * archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω))
      (fun j => (measurable_const.mul ((hm _).ennreal_ofReal)).mul
        (measurable_archLayer_path hm bc k _))
    have hsumle : (∑' j : ℕ, (∫⁻ ω, (ENNReal.ofReal (bc j)
            * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
            * archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω)) ^ 2 ∂μ) ^ ((1 : ℝ) / 2))
        ≤ (r * archS bc) ^ (k + 1) := by
      refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
      rw [ENNReal.tsum_mul_right, ← archS]
      rw [pow_succ']
      ring_nf
      rfl
    have hlayer : ∫⁻ ω, archLayer bc (k + 1) (archPath ξ t ω) ^ 2 ∂μ
        ≤ ((r * archS bc) ^ (k + 1)) ^ 2 := by
      have hcongr : (∫⁻ ω, archLayer bc (k + 1) (archPath ξ t ω) ^ 2 ∂μ)
          = ∫⁻ ω, (∑' j : ℕ, ENNReal.ofReal (bc j)
              * ENNReal.ofReal (ξ (t - 1 - (j : ℕ)) ω)
              * archLayer bc k (archPath ξ (t - 1 - (j : ℕ)) ω)) ^ 2 ∂μ :=
        lintegral_congr fun ω => by rw [archLayer_succ_path]
      rw [hcongr]
      exact hminko.trans (by gcongr)
    calc (∫⁻ ω, archLayer bc (k + 1) (archPath ξ t ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
        ≤ (((r * archS bc) ^ (k + 1)) ^ 2) ^ ((1 : ℝ) / 2) :=
          ENNReal.rpow_le_rpow hlayer (by norm_num)
      _ = (r * archS bc) ^ (k + 1) := ennreal_sq_rpow_half _

/-- **The Volterra series is square-integrable** under eq. (2.16). -/
private lemma lintegral_sq_archZ_lt_top [IsProbabilityMeasure μ] {a : ℝ} {bc : ℕ → ℝ}
    {ξ : ℤ → Ω → ℝ} (hξ : IsARCHNoise ξ μ) (hξ2 : MemLp (ξ 0) 2 μ)
    (h16 : max 1 (Real.sqrt (∫ ω, ξ 0 ω ^ 2 ∂μ)) * ∑' j, bc j < 1)
    (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc) (t : ℤ) :
    ∫⁻ ω, archZ a bc ξ t ω ^ 2 ∂μ < ∞ := by
  -- the second moment of the noise, as an `ℝ≥0∞` scalar
  have hnn0 : ∀ᵐ ω ∂μ, 0 ≤ ξ 0 ω := hξ.nonneg 0
  have hν : (∫⁻ ω, ENNReal.ofReal (ξ 0 ω) ^ 2 ∂μ) = ENNReal.ofReal (∫ ω, ξ 0 ω ^ 2 ∂μ) := by
    have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal (ξ 0 ω) ^ 2 = ENNReal.ofReal (ξ 0 ω ^ 2) := by
      filter_upwards [hnn0] with ω hω
      rw [ENNReal.ofReal_pow hω]
    rw [lintegral_congr_ae hpt,
      ← ofReal_integral_eq_lintegral_ofReal hξ2.integrable_sq
        (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  have hI0 : 0 ≤ ∫ ω, ξ 0 ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hr : (∫⁻ ω, ENNReal.ofReal (ξ 0 ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal (Real.sqrt (∫ ω, ξ 0 ω ^ 2 ∂μ)) := by
    rw [hν, ENNReal.ofReal_rpow_of_nonneg hI0 (by norm_num), Real.sqrt_eq_rpow]
  -- eq. (2.16) as a contraction in `ℝ≥0∞`
  have hbc0 : 0 ≤ ∑' j, bc j := tsum_nonneg hbc
  have hmax : (1 : ℝ) ≤ max 1 (Real.sqrt (∫ ω, ξ 0 ω ^ 2 ∂μ)) := le_max_left _ _
  have hsq : Real.sqrt (∫ ω, ξ 0 ω ^ 2 ∂μ) * ∑' j, bc j < 1 := by
    nlinarith [le_max_right (1 : ℝ) (Real.sqrt (∫ ω, ξ 0 ω ^ 2 ∂μ)), Real.sqrt_nonneg
      (∫ ω, ξ 0 ω ^ 2 ∂μ)]
  have hcontract : (∫⁻ ω, ENNReal.ofReal (ξ 0 ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * archS bc < 1 := by
    rw [hr, archS_eq hbc hsum, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_lt_one.2 hsq
  -- the series' `L²` norm is geometric
  have hW : ∫⁻ ω, (∑' k : ℕ, archLayer bc k (archPath ξ t ω)) ^ 2 ∂μ
      ≤ ((1 - (∫⁻ ω, ENNReal.ofReal (ξ 0 ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * archS bc)⁻¹) ^ 2 := by
    refine (lintegral_sq_tsum_le
      (fun k => measurable_archLayer_path hξ.measurable bc k t)).trans ?_
    gcongr
    refine le_trans (ENNReal.tsum_le_tsum fun k =>
      lintegral_sq_archLayer_le hξ.measurable hξ.iIndep hξ.identDistrib k t) ?_
    exact le_of_eq (ENNReal.tsum_geometric _)
  have hWtop : (∫⁻ ω, (∑' k : ℕ, archLayer bc k (archPath ξ t ω)) ^ 2 ∂μ) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ hW
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hcontract).ne')
  -- factor the current noise out of `archZ`
  have hexp : ∀ ω, archZ a bc ξ t ω ^ 2
      = ENNReal.ofReal a ^ 2 * (ENNReal.ofReal (ξ t ω) ^ 2
          * (∑' k : ℕ, archLayer bc k (archPath ξ t ω)) ^ 2) := fun ω => by
    simp only [archZ]
    rw [mul_pow, mul_pow, mul_assoc]
  rw [funext hexp, lintegral_const_mul _ ((((hξ.measurable t).ennreal_ofReal).pow_const 2).mul
      ((Measurable.ennreal_tsum fun k =>
        measurable_archLayer_path hξ.measurable bc k t).pow_const 2)),
    lintegral_sq_xi_mul hξ.measurable hξ.iIndep t
      ((Measurable.ennreal_tsum fun k => measurable_archLayer_sigmaLT bc k t).pow_const 2),
    lintegral_sq_ofReal_xi hξ.identDistrib, hν]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWtop.lt_top)

/-- **FY Theorem 2.5(ii)** (Giraitis–Kokoszka–Leipus 2000; not proved in FY):
under the second-moment contraction (FY eq. (2.16)) the stationary solution has a finite
second moment. -/
theorem archInf_memLp_two_debt [IsProbabilityMeasure μ]
    {a : ℝ} {bc : ℕ → ℝ} {Y ξ : ℤ → Ω → ℝ}
    (ha : 0 ≤ a) (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc)
    (hξ : IsARCHNoise ξ μ) (hξ2 : MemLp (ξ 0) 2 μ)
    -- USER-INPUT: FY eq. (2.16): max{1, ‖ξ‖₂}·Σ b_j < 1
    (h16 : max 1 (Real.sqrt (∫ ω, ξ 0 ω ^ 2 ∂μ)) * ∑' j, bc j < 1)
    (h : IsARCHInf a bc Y ξ μ) (hstat : IsStrictlyStationary Y μ)
    (hint : ∀ t, Integrable (Y t) μ) (t : ℤ) :
    MemLp (Y t) 2 μ := by
  have hbc0 : 0 ≤ ∑' j, bc j := tsum_nonneg hbc
  have hmax : (1 : ℝ) ≤ max 1 (Real.sqrt (∫ ω, ξ 0 ω ^ 2 ∂μ)) := le_max_left _ _
  have hlt : ∑' j, bc j < 1 := by nlinarith
  -- the solution *is* the Volterra series (FY Thm 2.5(i))
  have heq : Y t =ᵐ[μ] archSol a bc ξ t := archInf_eq_archSol hsum hlt h hint hstat t
  refine MemLp.ae_eq heq.symm ?_
  refine (memLp_two_iff_integrable_sq
    (measurable_archSol hξ.measurable a bc t).aestronglyMeasurable).2
    ⟨((measurable_archSol hξ.measurable a bc t).pow_const 2).aestronglyMeasurable, ?_⟩
  have hle : ∫⁻ ω, ‖archSol a bc ξ t ω ^ 2‖ₑ ∂μ ≤ ∫⁻ ω, archZ a bc ξ t ω ^ 2 ∂μ := by
    refine lintegral_mono fun ω => ?_
    rw [archSol_eq_toReal, Real.enorm_eq_ofReal (sq_nonneg _),
      ENNReal.ofReal_pow ENNReal.toReal_nonneg]
    exact pow_le_pow_left' ENNReal.ofReal_toReal_le 2
  change ∫⁻ ω, ‖archSol a bc ξ t ω ^ 2‖ₑ ∂μ < ∞
  exact lt_of_le_of_lt hle (lintegral_sq_archZ_lt_top hξ hξ2 h16 hbc hsum t)

/-- **FY Theorem 2.6 — DEBT** (Giraitis–Kokoszka–Leipus 2000; fdd invariance principle):
under eq. (2.16), the normalized partial sums of a stationary ARCH(∞) process are
asymptotically `N(0, σ²)` with long-run variance `σ² = Σ_k Cov(Y_k, Y_0)`. Stated at the
level of one-dimensional marginals through characteristic functions (Lévy-equivalent to
convergence in distribution; the full Brownian fdd statement of FY Thm 2.6 refines this
and can be layered on once a Brownian process is available). -/
theorem archInf_clt_debt [IsProbabilityMeasure μ]
    {a : ℝ} {bc : ℕ → ℝ} {Y ξ : ℤ → Ω → ℝ}
    (ha : 0 ≤ a) (hbc : ∀ j, 0 ≤ bc j) (hsum : Summable bc)
    (hξ : IsARCHNoise ξ μ) (hξ2 : MemLp (ξ 0) 2 μ)
    (h16 : max 1 (Real.sqrt (∫ ω, ξ 0 ω ^ 2 ∂μ)) * ∑' j, bc j < 1)
    (h : IsARCHInf a bc Y ξ μ) (hstat : IsStrictlyStationary Y μ)
    (hL2 : ∀ t, MemLp (Y t) 2 μ)
    {σ2 : ℝ} (hσ2 : HasSum (fun k : ℤ => acvf Y μ k) σ2) (hσpos : 0 < σ2) (u : ℝ) :
    Tendsto
      (fun n : ℕ => charFun
        (μ.map fun ω => (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range n, (Y t ω - ∫ ω', Y t ω' ∂μ)) u)
      atTop (nhds (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  sorry

end StatLean.TimeSeries
