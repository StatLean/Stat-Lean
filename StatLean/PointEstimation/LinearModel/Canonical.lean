import StatLean.PointEstimation.LinearModel.Defs
import StatLean.PointEstimation.UMVU.Defs
import StatLean.PointEstimation.Completeness.Defs
import StatLean.PointEstimation.Completeness.ExpFamily
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
open scoped ENNReal NNReal

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
