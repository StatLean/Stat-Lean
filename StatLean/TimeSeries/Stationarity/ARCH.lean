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
  semantics FY's proof uses, surfaced in `IsARCHInf`), Markov's inequality and
  Borel–Cantelli.

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
private lemma indep_xi_sigmaLT {ξ : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ξ t))
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

/-- **FY Theorem 2.5(i), existence** (proof: §2.7.1 Volterra series): if
`Σ_j bc j < 1`, there is a strictly stationary, integrable, a.e.-nonnegative solution of
the ARCH(∞) equation over the given noise, with `E Y_t = a / (1 − Σ_j bc j)`. -/
theorem exists_stationary_archInf [IsProbabilityMeasure μ]
    {a : ℝ} {bc : ℕ → ℝ} {ξ : ℤ → Ω → ℝ}
    -- USER-INPUT: coefficients; FY eq. (2.15)
    (ha : 0 ≤ a) (hbc : ∀ j, 0 ≤ bc j)
    -- USER-INPUT: contraction Σ b_j < 1; FY Thm 2.5(i)
    (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    -- USER-INPUT: the noise; FY eq. (2.15)
    (hξ : IsARCHNoise ξ μ) :
    ∃ Y : ℤ → Ω → ℝ, IsARCHInf a bc Y ξ μ ∧ IsStrictlyStationary Y μ ∧
      (∀ t, Integrable (Y t) μ) ∧ ∀ t, ∫ ω, Y t ω ∂μ = a / (1 - ∑' j, bc j) := by
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
  have hstat : IsStrictlyStationary (archSol a bc ξ) μ := by
    intro n tt k
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (ℤ → ℝ) → (Fin n → ℝ),
        Ψ = fun p i => archFun a bc fun s => p (s + tt i) := ⟨_, rfl⟩
    have hΨm : Measurable Ψ := by
      rw [hΨ]
      exact measurable_pi_lambda _ fun i => (measurable_archFun a bc).comp
        (measurable_pi_lambda _ fun s => measurable_pi_apply (s + tt i))
    have hmb : ∀ c : ℤ, Measurable fun ω (s : ℤ) => ξ (s + c) ω :=
      fun c => measurable_pi_lambda _ fun s => hm (s + c)
    have hfac : ∀ c : ℤ, (fun ω (i : Fin n) => archSol a bc ξ (tt i + c) ω)
        = Ψ ∘ fun ω (s : ℤ) => ξ (s + c) ω := by
      intro c
      funext ω i
      simp only [hΨ, Function.comp_apply, archSol, add_assoc]
      rfl
    have h0 : (fun ω (i : Fin n) => archSol a bc ξ (tt i) ω)
        = Ψ ∘ fun ω (s : ℤ) => ξ s ω := by simpa using hfac 0
    rw [hfac k, h0, ← Measure.map_map hΨm (hmb k),
      ← Measure.map_map hΨm (measurable_pi_lambda _ fun s : ℤ => hm s),
      map_path_shift hm hi hid k]
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
    hstat, hintY, hmeanY⟩

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
    Y t =ᵐ[μ] Y' t := by
  sorry

/-- **FY Theorem 2.5(i), degenerate case**: if `a = 0`, every integrable strictly
stationary solution is a.e. zero. -/
theorem archInf_eq_zero_of_a_eq_zero [IsProbabilityMeasure μ]
    {bc : ℕ → ℝ} {Y ξ : ℤ → Ω → ℝ}
    (hsum : Summable bc) (hlt : ∑' j, bc j < 1)
    (h : IsARCHInf 0 bc Y ξ μ) (hint : ∀ t, Integrable (Y t) μ)
    (hstat : IsStrictlyStationary Y μ) (t : ℤ) :
    Y t =ᵐ[μ] 0 := by
  sorry

/-- **FY Theorem 2.5(ii) — DEBT** (Giraitis–Kokoszka–Leipus 2000; not proved in FY):
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
  sorry

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
