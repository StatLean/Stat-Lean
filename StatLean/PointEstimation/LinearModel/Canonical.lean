import StatLean.PointEstimation.LinearModel.Defs
import StatLean.PointEstimation.UMVU.Defs
import StatLean.PointEstimation.Completeness.Defs
import StatLean.PointEstimation.Completeness.ExpFamily
import StatLean.PointEstimation.ExponentialFamily.Basic
import StatLean.PointEstimation.Sufficiency.Defs
import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity

/-!
# The canonical normal linear model

An orthogonal change of basis carries the normal linear model with an `s`-dimensional mean
subspace to its **canonical form**: the first `s` coordinates are independent `N(ηᵢ, σ²)`
with `η` ranging freely over `ℝˢ`, and the remaining `m` coordinates are independent
`N(0, σ²)`. All optimality statements for the model are proved in this coordinate system
and transported back afterwards.

* `PosVar` — the strictly positive variances (the nuisance-parameter range);
* `CanonicalParam s` — the parameter `(η, σ²)` of the canonical model;
* `canonicalMean η` — the mean vector `(η₁, …, η_s, 0, …, 0)`;
* `canonicalModel p` — the canonical family on `EuclideanSpace ℝ (Fin (s + m))`;
* `canonicalHead y` — the first `s` coordinates `(Y₁, …, Y_s)`;
* `canonicalRSS y` — the residual sum of squares `S² = ∑_{j} Y_{s+j}²`;
* `canonicalStat y = (canonicalHead y, canonicalRSS y)` — the complete sufficient statistic;
* `canonicalStat_hasSufficientKernel`, `canonicalStat_isCompleteStat`,
  `canonical_complete_sufficient`;
* `isUMVU_coord`, `isUMVU_linear_combination`, `isUMVU_residual_variance` — the unbiased
  optimality statements: `Yᵢ` for `ηᵢ`, `∑ λᵢ Yᵢ` for `∑ λᵢ ηᵢ`, and `S²/m` for `σ²`.

**Reference.** Classical normal linear-model theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* *Parameter packaging.* The mean is indexed by a free `η : Fin s → ℝ` together with a
  positive variance, and embedded into the observation space by `canonicalMean`; the
  alternative — a subtype `{x : Fin n → ℝ // ∀ j ≥ s, x j = 0}` — was rejected because
  every statement would then carry subtype coercions, and because the completeness proof
  needs the parameter to range over a set with nonempty interior in `ℝˢ⁺¹`, which the free
  product `(Fin s → ℝ) × PosVar` exhibits directly.
* *Dimension packaging.* The observation dimension is written `n = s + m` rather than
  `s ≤ n`, so that "the first `s` coordinates" and "the last `m` coordinates" are
  `Fin.castAdd`/`Fin.natAdd` with no arithmetic side conditions. The standing assumption
  `s < n` of the model becomes `0 < m`, carried explicitly by every theorem below.
* *Variance range.* `σ² = 0` is excluded (`PosVar`): the degenerate member falls outside
  the classical statements and would break completeness bookkeeping.
* Completeness is intended to go through the full-rank exponential-family theorem, with
  natural statistic `canonicalStat` and natural parameter `(η/σ², −1/(2σ²))`, whose range
  has nonempty interior in `ℝˢ × ℝ`; the sufficiency kernel is the Gaussian conditional
  law of the observation given the statistic.

**Bibliographic comments.** The reduction of the normal linear model to canonical form by
an orthogonal transformation, and the resulting optimality of least squares, go back to
C. F. Gauss (*Theoria combinationis observationum erroribus minimis obnoxiae*, 1821/1823)
and A. A. Markov (*Wahrscheinlichkeitsrechnung*, Teubner, 1912); the modern
coordinate-free treatment is that of W. Kruskal ("When are Gauss–Markov and least squares
estimators identical?" in *Essays in Probability and Statistics*, 1965), H. Scheffé (*The
Analysis of Variance*, Wiley, 1959) and C. R. Rao (*Linear Statistical Inference and Its
Applications*, 2nd ed., Wiley, 1973). Completeness of the canonical statistic and the
resulting minimum-variance property are due to E. L. Lehmann and H. Scheffé
("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10** (1950),
305–340).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.PointEstimation

/-- The strictly positive variances: the range of the nuisance parameter `σ²` in every
normal linear model considered here (a vanishing variance degenerates the observation and
is excluded from the classical statements). -/
abbrev PosVar : Type := {v : ℝ≥0 // 0 < v}

/-- The parameter of the canonical model: `s` unrestricted mean coordinates together with
the unknown positive common variance. -/
abbrev CanonicalParam (s : ℕ) : Type := (Fin s → ℝ) × PosVar

variable {s m : ℕ}

/-! ## The model -/

/-- The **canonical mean vector** `(η₁, …, η_s, 0, …, 0)`: the free means occupy the first
`s` coordinates and the remaining `m` coordinates are centred. -/
noncomputable def canonicalMean (η : Fin s → ℝ) : EuclideanSpace ℝ (Fin (s + m)) :=
  (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m)))
    (Fin.append η (0 : Fin m → ℝ))

/-- The **canonical normal linear model**: independent coordinates, the first `s` with free
means `η` and the last `m` centred, all with common variance `σ²`. -/
noncomputable def canonicalModel (p : CanonicalParam s) :
    Measure (EuclideanSpace ℝ (Fin (s + m))) :=
  gaussianVector (canonicalMean (m := m) p.1) p.2.1

/-! ## The canonical statistic -/

/-- The **signal block** `(Y₁, …, Y_s)`: the first `s` coordinates of the observation. -/
def canonicalHead (y : EuclideanSpace ℝ (Fin (s + m))) : Fin s → ℝ :=
  fun i => y (Fin.castAdd m i)

/-- The **residual sum of squares** `S² = ∑_{j=1}^{m} Y_{s+j}²` of the canonical model. -/
def canonicalRSS (y : EuclideanSpace ℝ (Fin (s + m))) : ℝ :=
  ∑ j : Fin m, y (Fin.natAdd s j) ^ 2

/-- The **canonical statistic** `(Y₁, …, Y_s, S²)`, jointly complete and sufficient for
`(η, σ²)`. -/
def canonicalStat (y : EuclideanSpace ℝ (Fin (s + m))) : (Fin s → ℝ) × ℝ :=
  (canonicalHead y, canonicalRSS y)

/-- Measurability of the canonical statistic (needed by every consumer that pushes the
model forward along it). -/
theorem measurable_canonicalStat :
    Measurable (canonicalStat (s := s) (m := m)) := by
  have hcoord : ∀ k : Fin (s + m),
      Measurable (fun y : EuclideanSpace ℝ (Fin (s + m)) => y k) :=
    fun k => (measurable_pi_apply k).comp (WithLp.measurable_ofLp 2 (Fin (s + m) → ℝ))
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_lambda _ (fun i => hcoord (Fin.castAdd m i))
  · exact Finset.measurable_sum _ (fun j _ => (hcoord (Fin.natAdd s j)).pow_const 2)

/-- **Product-Gaussian density.** The canonical normal law is the Lebesgue measure on
`Fin n → ℝ` weighted by the product of the per-coordinate Gaussian densities. -/
private lemma canonicalNormal_eq_withDensity {n : ℕ} (η : Fin n → ℝ) {σ2 : ℝ≥0}
    (hσ : σ2 ≠ 0) :
    canonicalNormal η σ2
      = (volume : Measure (Fin n → ℝ)).withDensity
          (fun x => ∏ i, gaussianPDF (η i) σ2 (x i)) := by
  have h_each : (fun i => gaussianReal (η i) σ2)
      = fun i => (volume : Measure ℝ).withDensity (gaussianPDF (η i) σ2) := by
    funext i; exact gaussianReal_of_var_ne_zero (η i) hσ
  haveI : ∀ i : Fin n, SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF (η i) σ2)) := by
    intro i; rw [← gaussianReal_of_var_ne_zero (η i) hσ]; infer_instance
  rw [canonicalNormal, h_each, ← pi_withDensity_prod (fun i => measurable_gaussianPDF (η i) σ2),
    ← volume_pi]

/-! ## Exponential-family scaffolding (private)

The completeness proof recognizes the canonical model as a full-rank exponential family with
**total** sum of squares as the last natural coordinate (the residual form is *not* an
exponential family: a `−(1/2σ²)∑_{i<s} yᵢ²` term survives), and transports completeness of
that statistic to the frozen `canonicalStat = (head, RSS)` along the measurable shear
`(a, total) ↦ (a, total − ∑ aᵢ²)`. -/

/-- The exponential family underlying the canonical model, on the pi observation space
`Fin (s+m) → ℝ` with reference measure `volume`. Its natural statistic is
`ỹ ↦ (y₀,…,y_{s−1}, ∑ₖ yₖ²)` (head coordinates and the **total** sum of squares). -/
private noncomputable def canonicalExpFamily (s m : ℕ) :
    ExpFamily (Fin (s + m) → ℝ) (EuclideanSpace ℝ (Fin (s + 1))) where
  base := volume
  stat := fun y =>
    (WithLp.toLp 2 : (Fin (s + 1) → ℝ) → EuclideanSpace ℝ (Fin (s + 1)))
      (Fin.snoc (fun i : Fin s => y (Fin.castAdd m i)) (∑ k, y k ^ 2))
  stat_meas := by
    apply (WithLp.measurable_toLp 2 (Fin (s + 1) → ℝ)).comp
    refine measurable_pi_iff.2 fun j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
      exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).pow_const 2
    · simp only [Fin.snoc_castSucc]
      exact measurable_pi_apply _

private lemma canonicalExpFamily_stat (y : Fin (s + m) → ℝ) :
    (canonicalExpFamily s m).stat y
      = (WithLp.toLp 2 : (Fin (s + 1) → ℝ) → EuclideanSpace ℝ (Fin (s + 1)))
          (Fin.snoc (fun i : Fin s => y (Fin.castAdd m i)) (∑ k, y k ^ 2)) := rfl

private lemma canonicalExpFamily_base : (canonicalExpFamily s m).base = volume := rfl

/-- The natural parameter attached to `(η, σ²)`: `(η₁/σ², …, η_s/σ², −1/(2σ²))`. -/
private noncomputable def canonicalEta (p : CanonicalParam s) :
    EuclideanSpace ℝ (Fin (s + 1)) :=
  (WithLp.toLp 2 : (Fin (s + 1) → ℝ) → EuclideanSpace ℝ (Fin (s + 1)))
    (Fin.snoc (fun i : Fin s => p.1 i / (p.2.1 : ℝ)) (-(1 / (2 * (p.2.1 : ℝ)))))

/-- The normalizing constant of the tilted density (positive). -/
private noncomputable def canonicalC (p : CanonicalParam s) : ℝ :=
  (Real.sqrt (2 * Real.pi * (p.2.1 : ℝ)))⁻¹ ^ (s + m)
    * Real.exp (-(∑ i, p.1 i ^ 2) / (2 * (p.2.1 : ℝ)))

private lemma canonicalC_pos (p : CanonicalParam s) : 0 < canonicalC (m := m) p := by
  have hv : (0 : ℝ) < (p.2.1 : ℝ) := by exact_mod_cast p.2.2
  have h2πv : (0 : ℝ) < 2 * Real.pi * (p.2.1 : ℝ) :=
    mul_pos (mul_pos two_pos Real.pi_pos) hv
  exact mul_pos (pow_pos (inv_pos.2 (Real.sqrt_pos.2 h2πv)) _) (Real.exp_pos _)

/-- The real inner product of two scalars is their product. -/
private lemma real_inner_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  have h1 : ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_mul_norm]; simp
  calc ⟪a, b⟫_ℝ = ⟪a • (1 : ℝ), b • (1 : ℝ)⟫_ℝ := by
        rw [smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    _ = a * (b * ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ) := by rw [real_inner_smul_left, real_inner_smul_right]
    _ = a * b := by rw [h1, mul_one]

/-- The inner product `⟪canonicalEta p, T̃ y⟫` in explicit coordinate form. -/
private lemma canonicalEta_inner (p : CanonicalParam s) (y : Fin (s + m) → ℝ) :
    ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ
      = (∑ i, p.1 i / (p.2.1 : ℝ) * y (Fin.castAdd m i))
        + -(1 / (2 * (p.2.1 : ℝ))) * (∑ k, y k ^ 2) := by
  rw [canonicalEta, canonicalExpFamily_stat, PiLp.inner_apply, Fin.sum_univ_castSucc]
  simp only [real_inner_mul, Fin.snoc_castSucc, Fin.snoc_last]

/-- **Core density identity.** The product of per-coordinate Gaussian densities of the
canonical model equals `C·exp⟪η, T̃⟫` — the exponential-family form. -/
private lemma canonical_pdf_prod_eq (p : CanonicalParam s) (y : Fin (s + m) → ℝ) :
    (∏ k, gaussianPDFReal ((Fin.append p.1 (0 : Fin m → ℝ)) k) p.2.1 (y k))
      = canonicalC (m := m) p
          * Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ := by
  have hv : (0 : ℝ) < (p.2.1 : ℝ) := by exact_mod_cast p.2.2
  have hvne : (p.2.1 : ℝ) ≠ 0 := ne_of_gt hv
  set mean : Fin (s + m) → ℝ := Fin.append p.1 (0 : Fin m → ℝ) with hmean
  -- Expand the product into constant × exp of a sum.
  have hprod :
      (∏ k, gaussianPDFReal (mean k) p.2.1 (y k))
        = (Real.sqrt (2 * Real.pi * (p.2.1 : ℝ)))⁻¹ ^ (s + m)
            * Real.exp (∑ k, -(y k - mean k) ^ 2 / (2 * (p.2.1 : ℝ))) := by
    simp only [gaussianPDFReal_def]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum]
  rw [hprod, canonicalC,
    mul_assoc ((Real.sqrt (2 * Real.pi * (p.2.1 : ℝ)))⁻¹ ^ (s + m)), ← Real.exp_add]
  congr 1
  congr 1
  -- The exponent identity `∑ -(yₖ-meanₖ)²/(2v) = -(∑ηᵢ²)/(2v) + ⟪η, T̃⟫`.
  rw [canonicalEta_inner]
  have hmul : ∑ k, y k * mean k = ∑ i, y (Fin.castAdd m i) * p.1 i := by
    rw [Fin.sum_univ_add]
    simp only [hmean, Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
  have hsq : ∑ k, mean k ^ 2 = ∑ i, p.1 i ^ 2 := by
    rw [Fin.sum_univ_add]
    simp only [hmean, Fin.append_left, Fin.append_right, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero]
  have hnum : ∑ k, -(y k - mean k) ^ 2 / (2 * (p.2.1 : ℝ))
      = (-(∑ k, y k ^ 2) + 2 * (∑ k, y k * mean k) - (∑ k, mean k ^ 2)) / (2 * (p.2.1 : ℝ)) := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_congr rfl (fun k _ => show -(y k - mean k) ^ 2
          = -(y k ^ 2) + 2 * (y k * mean k) - mean k ^ 2 from by ring),
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hR : (∑ i, p.1 i / (p.2.1 : ℝ) * y (Fin.castAdd m i))
      = (∑ i, y (Fin.castAdd m i) * p.1 i) / (p.2.1 : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hnum, hmul, hsq, hR]
  field_simp
  ring

/-- Measurability of the exponential integrand `y ↦ exp⟪η, T̃ y⟫`. -/
private lemma measurable_expInner (p : CanonicalParam s) :
    Measurable
      (fun y : Fin (s + m) → ℝ => Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ) :=
  (((continuous_const.inner continuous_id).measurable).comp
    (canonicalExpFamily s m).stat_meas).exp

/-- The ENNReal density of the canonical model in exponential-family form. -/
private lemma canonical_density_eq (p : CanonicalParam s) (y : Fin (s + m) → ℝ) :
    (∏ i, gaussianPDF ((Fin.append p.1 (0 : Fin m → ℝ)) i) p.2.1 (y i))
      = ENNReal.ofReal (canonicalC (m := m) p)
          * ENNReal.ofReal (Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ) := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _),
    canonical_pdf_prod_eq, ENNReal.ofReal_mul (canonicalC_pos p).le]

/-- **The exponential-family bridge.** The canonical product-Gaussian law with mean
`(η, 0)` equals the exponential-family member `P (canonicalEta p)`. -/
private lemma canonicalNormal_eq_P (p : CanonicalParam s) :
    canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1
      = (canonicalExpFamily s m).P (canonicalEta p) := by
  set φ : (Fin (s + m) → ℝ) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ) with hφ
  set A : ℝ := (canonicalExpFamily s m).logPartition (canonicalEta p) with hA
  have hφmeas : Measurable φ := (measurable_expInner p).ennreal_ofReal
  have hσ : p.2.1 ≠ 0 := ne_of_gt p.2.2
  -- The canonical law as a weighted volume.
  have hcanon : canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1
      = volume.withDensity (fun y => ENNReal.ofReal (canonicalC (m := m) p) * φ y) := by
    rw [canonicalNormal_eq_withDensity _ hσ]
    exact withDensity_congr_ae (Filter.Eventually.of_forall fun y => canonical_density_eq p y)
  haveI : IsProbabilityMeasure (canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1) := by
    unfold canonicalNormal; infer_instance
  have hbne : (volume : Measure (Fin (s + m) → ℝ)) ≠ 0 := by
    intro h
    have h0 : canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1 = 0 := by
      rw [hcanon, h, withDensity_zero_left]
    have := measure_univ (μ := canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1)
    rw [h0] at this; simp at this
  set Z : ℝ≥0∞ := ∫⁻ y, φ y ∂(volume : Measure (Fin (s + m) → ℝ)) with hZ
  -- Total mass of the canonical law gives `ofReal C · Z = 1`.
  have hmassC : ENNReal.ofReal (canonicalC (m := m) p) * Z = 1 := by
    have := measure_univ (μ := canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1)
    rw [hcanon, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      lintegral_const_mul _ hφmeas] at this
    exact this
  have hZne : Z ≠ 0 := by
    rintro h; rw [h, mul_zero] at hmassC; exact one_ne_zero hmassC.symm
  have hZlt : Z ≠ ∞ := by
    rintro h
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (canonicalC_pos (m := m) p)).ne'] at hmassC
    exact ENNReal.top_ne_one hmassC
  -- Hence `canonicalEta p` is a natural parameter (Gaussian integrability).
  have hmem : canonicalEta p ∈ (canonicalExpFamily s m).natSet := by
    show Integrable
      (fun y => Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ)
      (canonicalExpFamily s m).base
    rw [canonicalExpFamily_base]
    refine ⟨(measurable_expInner p).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)]
    exact lt_of_le_of_ne le_top hZlt
  haveI : IsProbabilityMeasure ((canonicalExpFamily s m).P (canonicalEta p)) :=
    ExpFamily.isProbabilityMeasure_P _ (by rw [canonicalExpFamily_base]; exact hbne) hmem
  -- The member in density form.
  have hP : (canonicalExpFamily s m).P (canonicalEta p)
      = volume.withDensity (fun y => ENNReal.ofReal (Real.exp (-A)) * φ y) := by
    rw [ExpFamily.P_eq_withDensity _ hmem, canonicalExpFamily_base]
    refine withDensity_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hφ, ← hA]
    rw [show ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ - A
          = -A + ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ from by ring,
      Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hmassP : ENNReal.ofReal (Real.exp (-A)) * Z = 1 := by
    have := measure_univ (μ := (canonicalExpFamily s m).P (canonicalEta p))
    rw [hP, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      lintegral_const_mul _ hφmeas] at this
    exact this
  have hconst : ENNReal.ofReal (canonicalC (m := m) p) = ENNReal.ofReal (Real.exp (-A)) :=
    (ENNReal.mul_left_inj hZne hZlt).1 (hmassC.trans hmassP.symm)
  rw [hcanon, hP, hconst]

/-! ## Completeness and sufficiency -/

/-- **Sufficiency of the canonical statistic**: the conditional law of the observation
given `(Y₁, …, Y_s, S²)` does not depend on `(η, σ²)`. -/
theorem canonicalStat_hasSufficientKernel
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    HasSufficientKernel (canonicalModel (s := s) (m := m)) canonicalStat := by
  sorry

/-- **Completeness of the canonical statistic**: an integrable function of
`(Y₁, …, Y_s, S²)` with identically vanishing mean vanishes almost everywhere. -/
theorem canonicalStat_isCompleteStat
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    IsCompleteStat (canonicalModel (s := s) (m := m)) canonicalStat := by
  sorry

/-- `(Y₁, …, Y_s, S²)` is a **complete sufficient statistic** for `(η, σ²)`. -/
theorem canonical_complete_sufficient
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    HasSufficientKernel (canonicalModel (s := s) (m := m)) canonicalStat ∧
      IsCompleteStat (canonicalModel (s := s) (m := m)) canonicalStat :=
  ⟨canonicalStat_hasSufficientKernel (s := s) hm, canonicalStat_isCompleteStat (s := s) hm⟩

/-! ## Unbiased optimality in the canonical model -/

/-- Each coordinate `Yᵢ` of the signal block is UMVU for the corresponding mean `ηᵢ`. -/
theorem isUMVU_coord
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) (i : Fin s) :
    IsUMVU (canonicalModel (s := s) (m := m)) (fun p => p.1 i)
      (fun y => canonicalHead y i) := by
  sorry

/-- Every linear combination `∑ λᵢ Yᵢ` of the signal block is UMVU for `∑ λᵢ ηᵢ`. -/
theorem isUMVU_linear_combination
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional
    (lam : Fin s → ℝ) :
    IsUMVU (canonicalModel (s := s) (m := m)) (fun p => ∑ i, lam i * p.1 i)
      (fun y => ∑ i, lam i * canonicalHead y i) := by
  sorry

/-- The rescaled residual sum of squares `S²/m` (that is, `S²/(n − s)`) is UMVU for the
variance `σ²`. -/
theorem isUMVU_residual_variance
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    IsUMVU (canonicalModel (s := s) (m := m)) (fun p => (p.2.1 : ℝ))
      (fun y => canonicalRSS y / (m : ℝ)) := by
  sorry

end StatLean.PointEstimation
