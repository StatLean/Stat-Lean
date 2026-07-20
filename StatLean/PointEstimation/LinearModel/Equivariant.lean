import StatLean.PointEstimation.LinearModel.Canonical
import StatLean.PointEstimation.LinearModel.LeastSquares
import StatLean.MultipleTesting.ForMathlib.ChiSquared
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Continuous
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Equivariant optimality in the normal linear model

The estimators that are optimal among unbiased estimators are also optimal among
equivariant ones, for the natural groups acting on the normal linear model:

* translations of the signal block, `Y ↦ Y + (a, 0)`, under which `η ↦ η + a` and a linear
  functional `∑ λᵢ ηᵢ` of the mean shifts by `∑ λᵢ aᵢ` — the group for which `∑ λᵢ Yᵢ` is
  minimum risk equivariant under any convex even loss `ρ(d − ∑ λᵢ ηᵢ)`;
* the same translations together with the scale changes `Y ↦ cY`, under which
  `σ² ↦ c²σ²` — the group for which a fixed multiple of the residual sum of squares is
  minimum risk equivariant for `σ²` under the loss `(d − σ²)²/σ⁴`; the multiplier is a
  ratio of chi-square moments, and equals `1/(n − s + 2)`;
* translations by the mean subspace in the original coordinates, `X ↦ X + b` with `b ∈ W`,
  for which the least-squares functional is minimum risk equivariant.

Contents: `IsCanonicalEquivariant`, `canonicalRisk`, `IsCanonicalMRE`;
`IsCanonicalScaleEquivariant`, `canonicalScaleRisk`, `IsCanonicalScaleMRE`,
`residualScaleConst`; `IsSubspaceEquivariant`, `linearBaseRisk`, `IsSubspaceMRE`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.4 (Normal
Linear Models), Corollary 4.5 (the equivariance of the canonical estimators). (`TPE2 §3.4 Cor
4.5`.)

**Proof formalization notes.**
* *Lightweight group formalization.* Equivariance is expressed by explicit functional
  equations on the competing estimators (`IsCanonicalEquivariant`,
  `IsCanonicalScaleEquivariant`, `IsSubspaceEquivariant`) rather than through the general
  `[Group G] [MulAction G _]` framework. The acting groups here are concrete (`ℝˢ` acting
  by translation of a coordinate block, and its semidirect product with the positive
  reals), the induced action on the decision space is a shift or a power, and routing
  through the general framework would force an instance-heavy encoding for no gain. The
  general-framework bridge lemmas can be added later without changing these statements.
* *Constant risk.* Under each group the risk of an equivariant estimator is constant in the
  parameter, so minimum risk equivariance is stated as minimality of the risk at a single
  base parameter — `(η, σ²) = (0, σ²)` for the translation group and `(0, 1)` for the
  location-scale group. Losses enter `∫⁻` through `ENNReal.ofReal` (junk-value discipline).
* *The scale clause.* The optimal multiplier of the residual sum of squares is only pinned
  down once the acting group contains the scale changes: under translations alone the risk
  still depends on `σ²`. The statement below therefore uses the location-scale group, which
  is also the route by which the classical proof obtains the constant.
* *The constant.* `residualScaleConst m r` is the ratio of chi-square moments
  `E[V^r]/E[V^{2r}]`, `V ∼ χ²_m`; for `r = 1` the moments `E[V] = m` and
  `E[V²] = m(m + 2)` (`StatLean.MultipleTesting.integral_id_chiSquared` and
  `StatLean.MultipleTesting.variance_chiSquared`) give the classical
  `1/(m + 2) = 1/(n − s + 2)` — a larger denominator than the unbiased `1/(n − s)`.

**Bibliographic comments.** Equivariant estimation of location and scale parameters is due
to E. J. G. Pitman ("The estimation of the location and scale parameters of a continuous
population of any given form," *Biometrika* **30** (1939), 391–421); its use in the linear
model follows H. Scheffé (*The Analysis of Variance*, Wiley, 1959) and C. R. Rao (*Linear
Statistical Inference and Its Applications*, 2nd ed., Wiley, 1973), with the
coordinate-free viewpoint of W. Kruskal ("When are Gauss–Markov and least squares
estimators identical?" in *Essays in Probability and Statistics*, 1965). The underlying
least-squares theory is that of C. F. Gauss (*Theoria combinationis observationum
erroribus minimis obnoxiae*, 1821/1823) and A. A. Markov (*Wahrscheinlichkeitsrechnung*,
Teubner, 1912). The distribution of the residual sum of squares goes back to F. R. Helmert
(*Z. Math. Phys.* **21** (1876), 192–218).
-/

open MeasureTheory ProbabilityTheory
open StatLean.MultipleTesting (chiSquared)
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {s m n : ℕ}

/-! ## Translations of the signal block -/

/-- **Equivariance under translations of the signal block**: shifting the first `s`
coordinates by `a` shifts the estimator of `∑ λᵢ ηᵢ` by `∑ λᵢ aᵢ`. -/
def IsCanonicalEquivariant (lam : Fin s → ℝ)
    (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  ∀ (a : Fin s → ℝ) (y : EuclideanSpace ℝ (Fin (s + m))),
    δ (y + canonicalMean a) = δ y + ∑ i, lam i * a i

/-- Risk of `δ` at the base parameter `(η, σ²) = (0, σ²)` for a loss
`ρ(d − ∑ λᵢ ηᵢ)`; for equivariant estimators the risk equals this constant. -/
noncomputable def canonicalRisk (σ2 : PosVar) (ρ : ℝ → ℝ)
    (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (ρ (δ y))
    ∂(canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), σ2))

/-- **Minimum risk equivariant** estimator of `∑ λᵢ ηᵢ` under translations of the signal
block: measurable, equivariant, and of minimal (constant) risk among all such. -/
def IsCanonicalMRE (σ2 : PosVar) (lam : Fin s → ℝ) (ρ : ℝ → ℝ)
    (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  Measurable δ ∧ IsCanonicalEquivariant lam δ ∧
    ∀ δ' : EuclideanSpace ℝ (Fin (s + m)) → ℝ,
      Measurable δ' → IsCanonicalEquivariant lam δ' →
        canonicalRisk σ2 ρ δ ≤ canonicalRisk σ2 ρ δ'

/-! ### Convex-symmetric core (private scaffolding)

The reflection of the signal block, `Y ↦ (-Y_head, Y_res)`, is a symmetry of the base law
`canonicalModel (0, σ²)` (each coordinate is centred Gaussian), it negates `∑ λᵢ Yᵢ`, and it
is a signal-block translation, so it fixes `δ' − δ₀` for every equivariant `δ'`. Combined
with the pointwise midpoint convexity `ρ(δ₀) ≤ ½ρ(δ₀+h) + ½ρ(δ₀−h)` this gives the
minimality without any explicit head/residual independence decomposition. -/

/-- The reflection of the signal block: negates the first `s` coordinates, fixes the rest. -/
private noncomputable def canonicalReflect (y : EuclideanSpace ℝ (Fin (s + m))) :
    EuclideanSpace ℝ (Fin (s + m)) :=
  (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m)))
    (fun k => if (k : ℕ) < s then -(y k) else y k)

private lemma measurable_canonicalReflect :
    Measurable (canonicalReflect (s := s) (m := m)) := by
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ (fun k => ?_))
  by_cases h : (k : ℕ) < s
  · simp only [h, if_true]
    exact ((measurable_pi_apply k).comp (WithLp.measurable_ofLp 2 _)).neg
  · simp only [h, if_false]
    exact (measurable_pi_apply k).comp (WithLp.measurable_ofLp 2 _)

/-- The reflection is a translation of the signal block by `-2 Y_head`. -/
private lemma canonicalReflect_eq (y : EuclideanSpace ℝ (Fin (s + m))) :
    canonicalReflect y = y + canonicalMean (fun i => -2 * canonicalHead y i) := by
  ext k
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · show (if ((Fin.castAdd m a : Fin (s + m)) : ℕ) < s then -(y (Fin.castAdd m a))
          else y (Fin.castAdd m a))
        = y (Fin.castAdd m a) + (canonicalMean (fun i => -2 * canonicalHead y i)) (Fin.castAdd m a)
    rw [if_pos (by simpa using a.isLt)]
    rw [show (canonicalMean (fun i => -2 * canonicalHead y i)) (Fin.castAdd m a)
          = Fin.append (fun i => -2 * canonicalHead y i) (0 : Fin m → ℝ) (Fin.castAdd m a) from rfl,
        Fin.append_left]
    show -(y (Fin.castAdd m a)) = y (Fin.castAdd m a) + -2 * y (Fin.castAdd m a)
    ring
  · show (if ((Fin.natAdd s b : Fin (s + m)) : ℕ) < s then -(y (Fin.natAdd s b))
          else y (Fin.natAdd s b))
        = y (Fin.natAdd s b) + (canonicalMean (fun i => -2 * canonicalHead y i)) (Fin.natAdd s b)
    rw [if_neg (by simp)]
    rw [show (canonicalMean (fun i => -2 * canonicalHead y i)) (Fin.natAdd s b)
          = Fin.append (fun i => -2 * canonicalHead y i) (0 : Fin m → ℝ) (Fin.natAdd s b) from rfl,
        Fin.append_right, Pi.zero_apply, add_zero]

/-- The reflection preserves the base law `canonicalModel (0, σ²)`. -/
private lemma canonicalModel_zero_map_reflect (σ2 : PosVar) :
    (canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), σ2)).map canonicalReflect
      = canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), σ2) := by
  have hmeas_toLp :
      Measurable (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m))) :=
    WithLp.measurable_toLp 2 _
  set f : Fin (s + m) → ℝ → ℝ := fun k t => if (k : ℕ) < s then -t else t with hf
  have hmeas_f : ∀ k, Measurable (f k) := by
    intro k; by_cases h : (k : ℕ) < s <;> simp only [hf, h, if_true, if_false] <;> fun_prop
  have hcoord : ∀ k, (gaussianReal (0 : ℝ) σ2.1).map (f k) = gaussianReal 0 σ2.1 := by
    intro k
    by_cases h : (k : ℕ) < s
    · have hfk : f k = (fun t => -t) := by funext t; simp only [hf, h, if_true]
      rw [hfk, gaussianReal_map_neg, neg_zero]
    · have hfk : f k = fun t => t := by funext t; simp only [hf, h, if_false]
      rw [hfk, Measure.map_id']
  haveI hsf : ∀ k, SigmaFinite ((gaussianReal (0 : ℝ) σ2.1).map (f k)) := by
    intro k; rw [hcoord k]; infer_instance
  have hfam : (fun i : Fin (s + m) => gaussianReal ((canonicalMean (0 : Fin s → ℝ)) i) σ2.1)
      = (fun _ => gaussianReal (0 : ℝ) σ2.1) := by
    funext i
    congr 1
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · show (Fin.append (0 : Fin s → ℝ) (0 : Fin m → ℝ)) (Fin.castAdd m a) = 0
      rw [Fin.append_left]; rfl
    · show (Fin.append (0 : Fin s → ℝ) (0 : Fin m → ℝ)) (Fin.natAdd s b) = 0
      rw [Fin.append_right]; rfl
  have hbase : canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), σ2)
      = (Measure.pi (fun _ : Fin (s + m) => gaussianReal (0 : ℝ) σ2.1)).map (WithLp.toLp 2) := by
    rw [canonicalModel]
    show (Measure.pi
          (fun i => gaussianReal ((canonicalMean (0 : Fin s → ℝ)) i) σ2.1)).map (WithLp.toLp 2)
        = (Measure.pi (fun _ => gaussianReal (0 : ℝ) σ2.1)).map (WithLp.toLp 2)
    rw [hfam]
  rw [hbase, Measure.map_map measurable_canonicalReflect hmeas_toLp]
  have hcomp :
      canonicalReflect ∘ (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m)))
        = (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m)))
            ∘ (fun x k => f k (x k)) := by
    funext x
    show canonicalReflect (WithLp.toLp 2 x) = WithLp.toLp 2 (fun k => f k (x k))
    rfl
  have hprod : Measurable (fun x : Fin (s + m) → ℝ => fun k => f k (x k)) :=
    measurable_pi_lambda _ (fun k => (hmeas_f k).comp (measurable_pi_apply k))
  rw [hcomp, ← Measure.map_map hmeas_toLp hprod,
    Measure.pi_map_pi (f := f) (fun k => (hmeas_f k).aemeasurable)]
  simp only [hcoord]

/-- The unbiased optimal estimator `∑ λᵢ Yᵢ` of `∑ λᵢ ηᵢ` is also minimum risk equivariant
under translations of the signal block, for every convex even loss. -/
theorem isCanonicalMRE_linear_combination
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional
    (lam : Fin s → ℝ) (σ2 : PosVar) {ρ : ℝ → ℝ}
    -- USER-INPUT: convex loss in the estimation error
    (hconv : ConvexOn ℝ Set.univ ρ)
    -- USER-INPUT: even loss in the estimation error
    (heven : ∀ t : ℝ, ρ (-t) = ρ t) :
    IsCanonicalMRE (m := m) σ2 lam ρ (fun y => ∑ i, lam i * canonicalHead y i) := by
  set δ₀ : EuclideanSpace ℝ (Fin (s + m)) → ℝ := fun y => ∑ i, lam i * canonicalHead y i with hδ₀
  set M := canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), σ2) with hM
  -- `δ₀` is measurable and equivariant.
  have hδ₀meas : Measurable δ₀ := by
    rw [hδ₀]
    refine Finset.measurable_sum _ (fun i _ => measurable_const.mul ?_)
    exact (measurable_pi_apply (Fin.castAdd m i)).comp (WithLp.measurable_ofLp 2 _)
  have hHD : ∀ (a : Fin s → ℝ) (y : EuclideanSpace ℝ (Fin (s + m))) (i : Fin s),
      canonicalHead (y + canonicalMean a) i = canonicalHead y i + a i := by
    intro a y i
    have hsum : canonicalHead (y + canonicalMean a) i
        = canonicalHead y i + canonicalHead (canonicalMean (m := m) a) i := rfl
    have hcm : canonicalHead (canonicalMean (m := m) a) i = a i := by
      have hval : canonicalHead (canonicalMean (m := m) a) i
          = Fin.append a (0 : Fin m → ℝ) (Fin.castAdd m i) := rfl
      rw [hval, Fin.append_left]
    rw [hsum, hcm]
  have hδ₀equiv : IsCanonicalEquivariant lam δ₀ := by
    intro a y
    show ∑ i, lam i * canonicalHead (y + canonicalMean a) i
        = (∑ i, lam i * canonicalHead y i) + ∑ i, lam i * a i
    simp_rw [hHD, mul_add]
    rw [Finset.sum_add_distrib]
  refine ⟨hδ₀meas, hδ₀equiv, fun δ' hδ'meas hδ'equiv => ?_⟩
  -- `ρ` is continuous, hence measurable.
  have hρmeas : Measurable ρ :=
    (continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)).measurable
  -- `h := δ' − δ₀`; the reflection sends `δ'` to `δ₀ − (δ' − δ₀)` up to the even loss.
  set h : EuclideanSpace ℝ (Fin (s + m)) → ℝ := fun y => δ' y - δ₀ y with hh
  have hδ'eq : ∀ y, δ' y = δ₀ y + h y := fun y => by rw [hh]; ring
  -- reflection identity via equivariance of `δ'`
  have hsa : ∀ y, ∑ i, lam i * (-2 * canonicalHead y i) = -2 * δ₀ y := by
    intro y; rw [hδ₀, Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have hδ'R : ∀ y, δ' (canonicalReflect y) = -δ₀ y + h y := by
    intro y
    rw [canonicalReflect_eq y, hδ'equiv (fun i => -2 * canonicalHead y i) y, hsa y, hδ'eq y]
    ring
  -- pointwise midpoint convexity: `2 ρ(δ₀) ≤ ρ(δ₀+h) + ρ(δ₀−h)`
  have hpt : ∀ y, 2 * ρ (δ₀ y) ≤ ρ (δ₀ y + h y) + ρ (δ₀ y - h y) := by
    intro y
    have hc := hconv.2 (Set.mem_univ (δ₀ y + h y)) (Set.mem_univ (δ₀ y - h y))
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
    simp only [smul_eq_mul] at hc
    rw [show (1 / 2 : ℝ) * (δ₀ y + h y) + (1 / 2 : ℝ) * (δ₀ y - h y) = δ₀ y by ring] at hc
    linarith
  -- measurability of the ENNReal integrands
  have hmeas0 : Measurable (fun y => ENNReal.ofReal (ρ (δ₀ y))) :=
    ENNReal.measurable_ofReal.comp (hρmeas.comp hδ₀meas)
  have hhmeas : Measurable h := hδ'meas.sub hδ₀meas
  have hmeasP : Measurable (fun y => ENNReal.ofReal (ρ (δ₀ y + h y))) :=
    ENNReal.measurable_ofReal.comp (hρmeas.comp (hδ₀meas.add hhmeas))
  have hmeasM : Measurable (fun y => ENNReal.ofReal (ρ (δ₀ y - h y))) :=
    ENNReal.measurable_ofReal.comp (hρmeas.comp (hδ₀meas.sub hhmeas))
  have hmeas' : Measurable (fun y => ENNReal.ofReal (ρ (δ' y))) :=
    ENNReal.measurable_ofReal.comp (hρmeas.comp hδ'meas)
  -- write the risk of `δ'` two ways using the reflection symmetry of the base law
  have hJp : canonicalRisk σ2 ρ δ' = ∫⁻ y, ENNReal.ofReal (ρ (δ₀ y + h y)) ∂M := by
    show ∫⁻ y, ENNReal.ofReal (ρ (δ' y)) ∂M = _
    refine lintegral_congr (fun y => ?_)
    rw [hδ'eq y]
  have hJm : canonicalRisk σ2 ρ δ' = ∫⁻ y, ENNReal.ofReal (ρ (δ₀ y - h y)) ∂M := by
    show ∫⁻ y, ENNReal.ofReal (ρ (δ' y)) ∂M = _
    calc ∫⁻ y, ENNReal.ofReal (ρ (δ' y)) ∂M
        = ∫⁻ y, ENNReal.ofReal (ρ (δ' y)) ∂(M.map canonicalReflect) := by
          rw [hM, canonicalModel_zero_map_reflect]
      _ = ∫⁻ y, ENNReal.ofReal (ρ (δ' (canonicalReflect y))) ∂M :=
          lintegral_map hmeas' measurable_canonicalReflect
      _ = ∫⁻ y, ENNReal.ofReal (ρ (δ₀ y - h y)) ∂M := by
          refine lintegral_congr (fun y => ?_)
          rw [hδ'R y, show -δ₀ y + h y = -(δ₀ y - h y) by ring, heven]
  -- assemble: `2 · risk δ₀ ≤ 2 · risk δ'`
  have hfinal : 2 * canonicalRisk σ2 ρ δ₀ ≤ 2 * canonicalRisk σ2 ρ δ' := by
    calc 2 * canonicalRisk σ2 ρ δ₀
        = ∫⁻ y, 2 * ENNReal.ofReal (ρ (δ₀ y)) ∂M := by
          show 2 * ∫⁻ y, ENNReal.ofReal (ρ (δ₀ y)) ∂M = _
          rw [← lintegral_const_mul 2 hmeas0]
      _ ≤ ∫⁻ y, (ENNReal.ofReal (ρ (δ₀ y + h y)) + ENNReal.ofReal (ρ (δ₀ y - h y))) ∂M := by
          refine lintegral_mono (fun y => ?_)
          calc 2 * ENNReal.ofReal (ρ (δ₀ y))
              = ENNReal.ofReal (2 * ρ (δ₀ y)) := by
                rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
            _ ≤ ENNReal.ofReal (ρ (δ₀ y + h y) + ρ (δ₀ y - h y)) := ENNReal.ofReal_le_ofReal (hpt y)
            _ ≤ ENNReal.ofReal (ρ (δ₀ y + h y)) + ENNReal.ofReal (ρ (δ₀ y - h y)) :=
                ENNReal.ofReal_add_le
      _ = (∫⁻ y, ENNReal.ofReal (ρ (δ₀ y + h y)) ∂M)
            + ∫⁻ y, ENNReal.ofReal (ρ (δ₀ y - h y)) ∂M :=
          lintegral_add_left hmeasP _
      _ = canonicalRisk σ2 ρ δ' + canonicalRisk σ2 ρ δ' := by rw [← hJp, ← hJm]
      _ = 2 * canonicalRisk σ2 ρ δ' := (two_mul _).symm
  exact (ENNReal.mul_le_mul_left (by norm_num) (by norm_num)).mp hfinal

/-! ## Translations of the signal block together with scale changes -/

/-- **Equivariance of degree `2r` under the location-scale group**: the transformation
`y ↦ c(y + (a, 0))` multiplies an estimator of `σ^{2r} = (σ²)^r` by `c^{2r}`. -/
def IsCanonicalScaleEquivariant (r : ℕ) (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → ∀ (a : Fin s → ℝ) (y : EuclideanSpace ℝ (Fin (s + m))),
    δ (c • (y + canonicalMean a)) = c ^ (2 * r) * δ y

/-- Risk of `δ` at the base parameter `(η, σ²) = (0, 1)` for the loss
`(d − (σ²)^r)²/(σ²)^{2r}`; for equivariant estimators the risk equals this constant. -/
noncomputable def canonicalScaleRisk (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal ((δ y - 1) ^ 2)
    ∂(canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), ⟨1, zero_lt_one⟩))

/-- **Minimum risk equivariant** estimator of `(σ²)^r` under the location-scale group. -/
def IsCanonicalScaleMRE (r : ℕ) (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  Measurable δ ∧ IsCanonicalScaleEquivariant r δ ∧
    ∀ δ' : EuclideanSpace ℝ (Fin (s + m)) → ℝ,
      Measurable δ' → IsCanonicalScaleEquivariant r δ' →
        canonicalScaleRisk δ ≤ canonicalScaleRisk δ'

/-- The optimal multiplier of `(S²)^r`: the ratio `E[V^r]/E[V^{2r}]` of chi-square moments
with `k` degrees of freedom — the constant minimizing `E(c·V^r − 1)²`. -/
noncomputable def residualScaleConst (k r : ℕ) : ℝ :=
  (∫ v, v ^ r ∂(chiSquared k)) / (∫ v, v ^ (2 * r) ∂(chiSquared k))

open Set in
/-- Integrability of `x ↦ xᵏ` under `χ²ₘ` (`m ≥ 1`): mirrors the Gamma-moment brick. -/
private lemma integrable_pow_chiSquared {m : ℕ} (hm : 0 < m) (k : ℕ) :
    Integrable (fun x => x ^ k) (chiSquared m) := by
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set a : ℝ := (m : ℝ) / 2 with ha_def
  have ha : (0 : ℝ) < a := by rw [ha_def]; linarith
  have hr : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
  rw [show chiSquared m = gammaMeasure a (1 / 2) from rfl]
  rw [gammaMeasure, integrable_withDensity_iff
        (show Measurable (gammaPDF a (1 / 2)) from
          (measurable_gammaPDFReal a (1 / 2)).ennreal_ofReal)
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hcongr : (fun x => x ^ k * (gammaPDF a (1 / 2) x).toReal)
      = fun x => x ^ k * gammaPDFReal a (1 / 2) x := by
    funext x
    rw [show gammaPDF a (1 / 2) x = ENNReal.ofReal (gammaPDFReal a (1 / 2) x) from rfl,
        ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]
  rw [hcongr]
  have hmodel : IntegrableOn (fun x => x ^ (a + (k : ℝ) - 1) * Real.exp (-((1 / 2) * x)))
      (Ioi (0 : ℝ)) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a + (k : ℝ) - 1) (b := 1 / 2)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith) le_rfl hr
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [mem_Ioi] at hx
    rw [Real.rpow_one, neg_mul]
  have hIoi : IntegrableOn (fun x => x ^ k * gammaPDFReal a (1 / 2) x) (Ioi (0 : ℝ)) volume := by
    refine IntegrableOn.congr_fun (hmodel.const_mul ((1 / 2) ^ a / Real.Gamma a))
      (fun x hx => ?_) measurableSet_Ioi
    rw [mem_Ioi] at hx
    rw [gammaPDFReal, if_pos hx.le, ← Real.rpow_natCast x k,
        show a + (k : ℝ) - 1 = (a - 1) + (k : ℝ) by ring, Real.rpow_add hx (a - 1) (k : ℝ)]
    ring
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  refine ⟨?_, hIoi⟩
  refine integrableOn_zero.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic, MeasureTheory.ae_iff]
  refine measure_mono_null (t := {(0 : ℝ)}) ?_ Real.volume_singleton
  intro x hx
  simp only [mem_setOf_eq, Classical.not_imp, mem_Iic] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rcases lt_or_eq_of_le hx1 with h | h
  · exact absurd (show x ^ k * gammaPDFReal a (1 / 2) x = 0 by
      rw [gammaPDFReal, if_neg (not_le.mpr h), mul_zero]).symm hx2
  · exact h

/-- The multiplier at `r = 1`: `E[V] = m` and `E[V²] = m(m + 2)` give
`residualScaleConst m 1 = 1/(m + 2)`, the classical `1/(n − s + 2)`. -/
theorem residualScaleConst_one
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    residualScaleConst m 1 = 1 / ((m : ℝ) + 2) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hI1 : ∫ v, v ^ 1 ∂(chiSquared m) = (m : ℝ) := by
    simp only [pow_one]; exact StatLean.MultipleTesting.integral_id_chiSquared hm
  have hI2 : ∫ v, v ^ (2 * 1) ∂(chiSquared m) = (m : ℝ) * ((m : ℝ) + 2) := by
    have e21 : (2 * 1 : ℕ) = 2 := rfl
    rw [e21]
    have hint1 : Integrable (fun x : ℝ => x) (chiSquared m) := by
      simpa using integrable_pow_chiSquared hm 1
    have hint2 : Integrable (fun x : ℝ => x ^ 2) (chiSquared m) := integrable_pow_chiSquared hm 2
    have hvar := StatLean.MultipleTesting.variance_chiSquared hm
    have hmean := StatLean.MultipleTesting.integral_id_chiSquared hm
    have hexp : ∀ x : ℝ, (x - (m : ℝ)) ^ 2 = x ^ 2 - 2 * (m : ℝ) * x + (m : ℝ) ^ 2 :=
      fun x => by ring
    have hf : Integrable (fun x : ℝ => x ^ 2 - 2 * (m : ℝ) * x) (chiSquared m) :=
      hint2.sub (hint1.const_mul (2 * (m : ℝ)))
    rw [show (∫ x, (x - (m : ℝ)) ^ 2 ∂(chiSquared m))
          = (∫ x, x ^ 2 ∂(chiSquared m)) - 2 * (m : ℝ) * (∫ x, x ∂(chiSquared m)) + (m : ℝ) ^ 2
        from by
        simp_rw [hexp]
        rw [integral_add hf (integrable_const _),
            integral_sub hint2 (hint1.const_mul (2 * (m : ℝ))), integral_const_mul,
            integral_const, probReal_univ, smul_eq_mul, one_mul]] at hvar
    rw [hmean] at hvar
    linarith [hvar]
  rw [residualScaleConst, hI1, hI2]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- Measurability of the residual sum of squares. -/
private lemma measurable_canonicalRSS :
    Measurable (canonicalRSS (s := s) (m := m)) :=
  Finset.measurable_sum _ (fun j _ =>
    (((measurable_pi_apply (Fin.natAdd s j)).comp (WithLp.measurable_ofLp 2 _))).pow_const 2)

/-- The residual sum of squares scales by `c²` under the location-scale group action
`y ↦ c(y + (a, 0))`: the signal shift `a` leaves every residual coordinate untouched and the
scaling multiplies each by `c`. -/
private lemma canonicalRSS_smul_add_canonicalMean (c : ℝ) (a : Fin s → ℝ)
    (y : EuclideanSpace ℝ (Fin (s + m))) :
    canonicalRSS (c • (y + canonicalMean a)) = c ^ 2 * canonicalRSS y := by
  simp only [canonicalRSS, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hmean : (canonicalMean a) (Fin.natAdd s j) = 0 := by
    show (Fin.append a (0 : Fin m → ℝ)) (Fin.natAdd s j) = 0
    rw [Fin.append_right]; rfl
  rw [PiLp.smul_apply, PiLp.add_apply, hmean, add_zero, smul_eq_mul, mul_pow]

/-- **Analytic core of the location-scale MRE clause (lifted `private` debt).** Minimality of
the χ²-calibrated multiple `residualScaleConst m r · (S²)^r` of the residual sum of squares,
against every measurable degree-`2r` location-scale-equivariant competitor.

TODO. This is the Pitman location-scale optimality reduction and is the single remaining
open piece of the file. Precise route and obstruction, both verified on paper:

* *Reduction.* Head-translation equivariance (`c = 1`) makes any equivariant `δ'` invariant
  under `y ↦ y + (a, 0)`, so `δ'(y) = f(y_res)` depends only on the residual block; the
  scaling clause then makes `f : ℝᵐ → ℝ` positively homogeneous of degree `2r`
  (`f(c • w) = c^{2r} f(w)`). Under the base law `(0, 1)` the residual block is standard
  Gaussian `γₘ = N(0, Iₘ)`, so the risk is `∫ (f(w) − 1)² dγₘ`, with the reference
  `f₀(w) = t⋆‖w‖^{2r}`, `t⋆ = residualScaleConst m r = E[V^r]/E[V^{2r}]`, `V = ‖w‖² ∼ χ²ₘ`.

* *L²-projection identity.* In `L²(γₘ)` the degree-`2r` homogeneous functions form a linear
  subspace, and `f₀` is exactly the orthogonal projection of the constant `1` onto it:
  `∫ (f − f₀)(f₀ − 1) dγₘ = 0` for every such `f`, whence
  `∫ (f − 1)² = ∫ (f − f₀)² + ∫ (f₀ − 1)² ≥ ∫ (f₀ − 1)²`. The orthogonality is equivalent to
  the moment identity `∫ g dγₘ = t⋆ ∫ ‖w‖^{2r} g dγₘ` for every degree-`2r` homogeneous `g`.

* *The moment identity* follows by iterating the base recursion
  `∫ h ‖w‖² dγₘ = (m + 2q) ∫ h dγₘ` for `h` positively homogeneous of degree `2q` (giving
  `∫ ‖w‖^{2r} g dγₘ = ∏_{j<r}(m + 2r + 2j) · ∫ g dγₘ`, and `t⋆ = 1/∏_{j<r}(m + 2r + 2j)`
  by taking `g = ‖w‖^{2r}` and `map_sum_sq_eq_chiSquared` + `integrable_pow_chiSquared`).

* *The base recursion* is the only genuinely analytic step. It is obtained from the exact
  variance-scaling identity `∫ h d(N(0, σ²Iₘ)) = σ^{2q} ∫ h dγₘ` (immediate from
  `gaussianReal_map_const_mul` + homogeneity, no calculus) by differentiating the Gaussian
  expectation in the variance `σ²` at `σ² = 1`, where the density-side derivative equals
  `½(∫ h‖w‖² dγₘ − m ∫ h dγₘ)` and the scaling side equals `q ∫ h dγₘ`.

* *Obstruction.* The differentiation-under-the-integral step
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) must dominate the `σ²`-derivative of
  `h(w)·(density)` on a neighbourhood of `σ² = 1` by a fixed integrable envelope, for a
  merely *measurable* homogeneous `h ∈ L²(γₘ)` — the envelope
  `|h|(1 + ‖w‖²)e^{-c‖w‖²}`, `¼ < c < ½`, is integrable by Cauchy–Schwarz against the
  `L²(γₘ)` bound, but assembling this and the full `L²` orthogonality expansion is a large
  development. Mathlib has no isotropic-Gaussian polar decomposition
  (`‖w‖ ⊥ w/‖w‖`) that would give the moment identity directly, so this analytic route is
  the available one. -/
private lemma canonicalScaleRisk_residualScaleConst_le
    (hm : 0 < m) {r : ℕ} (hr : 0 < r)
    (δ' : EuclideanSpace ℝ (Fin (s + m)) → ℝ) (hδ'meas : Measurable δ')
    (hδ'equiv : IsCanonicalScaleEquivariant r δ') :
    canonicalScaleRisk (s := s) (m := m) (fun y => residualScaleConst m r * canonicalRSS y ^ r)
      ≤ canonicalScaleRisk δ' := by
  sorry

/-- A fixed multiple of `(S²)^r` is minimum risk equivariant for `(σ²)^r` under the
location-scale group, the multiplier being the chi-square moment ratio. -/
theorem isCanonicalScaleMRE_residual_pow
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m)
    -- USER-INPUT: the degree of the estimated power of the variance
    {r : ℕ} (hr : 0 < r) :
    IsCanonicalScaleMRE (s := s) (m := m) r
      (fun y => residualScaleConst m r * canonicalRSS y ^ r) := by
  refine ⟨measurable_const.mul (measurable_canonicalRSS.pow_const r), ?_, ?_⟩
  · -- equivariance: `S²` scales by `c²`, so `(S²)^r` scales by `c^{2r}`
    intro c _ a y
    show residualScaleConst m r * canonicalRSS (c • (y + canonicalMean a)) ^ r
        = c ^ (2 * r) * (residualScaleConst m r * canonicalRSS y ^ r)
    rw [canonicalRSS_smul_add_canonicalMean, mul_pow, ← pow_mul]
    ring
  · -- minimality: the analytic core, lifted to a named `private` lemma
    exact fun δ' hδ'meas hδ'equiv =>
      canonicalScaleRisk_residualScaleConst_le hm hr δ' hδ'meas hδ'equiv

/-- The classical variance clause: under the loss `(d − σ²)²/σ⁴`, the minimum risk
equivariant estimator of `σ²` is `S²/(m + 2)`, that is `S²/(n − s + 2)`. -/
theorem isCanonicalScaleMRE_residual_variance
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    IsCanonicalScaleMRE (s := s) (m := m) 1 (fun y => canonicalRSS y / ((m : ℝ) + 2)) := by
  -- The variance clause is the `r = 1` case of `isCanonicalScaleMRE_residual_pow`, with the
  -- chi-square moment ratio evaluated by `residualScaleConst_one`.
  have h := isCanonicalScaleMRE_residual_pow (s := s) (m := m) hm (r := 1) one_pos
  have heq : (fun y : EuclideanSpace ℝ (Fin (s + m)) => residualScaleConst m 1 * canonicalRSS y ^ 1)
      = fun y => canonicalRSS y / ((m : ℝ) + 2) := by
    funext y; rw [residualScaleConst_one hm, pow_one]; ring
  rw [heq] at h
  exact h

/-! ## Translations by the mean subspace, in the original coordinates -/

/-- **Equivariance under translations by the mean subspace**: shifting the observation by
`b ∈ W` shifts an estimator of `⟪γ, ξ⟫` by `⟪γ, b⟫`. -/
def IsSubspaceEquivariant (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (γ : EuclideanSpace ℝ (Fin n)) (δ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ b ∈ W, ∀ y : EuclideanSpace ℝ (Fin n), δ (y + b) = δ y + ⟪γ, b⟫_ℝ

/-- Risk of `δ` at the base parameter `ξ = 0` for a loss `ρ(d − ⟪γ, ξ⟫)`; for equivariant
estimators the risk equals this constant. -/
noncomputable def linearBaseRisk (σ2 : PosVar) (ρ : ℝ → ℝ)
    (δ : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (ρ (δ y)) ∂(gaussianVector (0 : EuclideanSpace ℝ (Fin n)) σ2.1)

/-- **Minimum risk equivariant** estimator of `⟪γ, ξ⟫` under translations by the mean
subspace. -/
def IsSubspaceMRE (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (σ2 : PosVar)
    (γ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ → ℝ) (δ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Measurable δ ∧ IsSubspaceEquivariant W γ δ ∧
    ∀ δ', Measurable δ' → IsSubspaceEquivariant W γ δ' →
      linearBaseRisk σ2 ρ δ ≤ linearBaseRisk σ2 ρ δ'

/-- The least-squares functional is minimum risk equivariant for `⟪γ, ξ⟫` under
translations by the mean subspace, for every convex even loss. -/
theorem isSubspaceMRE_lse_functional (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection]
    -- USER-INPUT: the mean subspace is a proper subspace (`s < n`); standing dimension
    -- condition of the model
    (hW : Module.finrank ℝ W < n) (σ2 : PosVar)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional, taken
    -- inside the mean subspace (a general one is replaced by its projection)
    {γ : EuclideanSpace ℝ (Fin n)} (hγ : γ ∈ W) {ρ : ℝ → ℝ}
    -- USER-INPUT: convex loss in the estimation error
    (hconv : ConvexOn ℝ Set.univ ρ)
    -- USER-INPUT: even loss in the estimation error
    (heven : ∀ t : ℝ, ρ (-t) = ρ t) :
    IsSubspaceMRE W σ2 γ ρ (fun y => ⟪γ, lse W y⟫_ℝ) := by
  classical
  obtain ⟨m, hm, hsm, L, hmean, hsurj, hRSS, hlse⟩ := exists_headSubspace_isometry W hW
  set δ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ⟪γ, lse W y⟫_ℝ with hδdef
  set lam : Fin (Module.finrank ℝ W) → ℝ := canonicalHead (L γ) with hlam
  have hρmeas : Measurable ρ :=
    (continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)).measurable
  have hLmeas : Measurable L := L.continuous.measurable
  have hLsymm : Measurable (L.symm : _ → EuclideanSpace ℝ (Fin n)) := L.symm.continuous.measurable
  -- the base law transports to the canonical base law
  have hcm0 : canonicalMean (0 : Fin (Module.finrank ℝ W) → ℝ)
      = (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + m))) := by
    ext k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
    · show (Fin.append (0 : Fin (Module.finrank ℝ W) → ℝ) (0 : Fin m → ℝ)) (Fin.castAdd m a)
          = (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + m))) (Fin.castAdd m a)
      rw [Fin.append_left]; rfl
    · show (Fin.append (0 : Fin (Module.finrank ℝ W) → ℝ) (0 : Fin m → ℝ)) (Fin.natAdd _ b)
          = (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + m))) (Fin.natAdd _ b)
      rw [Fin.append_right]; rfl
  have hbaseL : (gaussianVector (0 : EuclideanSpace ℝ (Fin n)) σ2.1).map L
      = canonicalModel (s := Module.finrank ℝ W) (m := m)
          ((0 : Fin (Module.finrank ℝ W) → ℝ), σ2) := by
    rw [gaussianVector_map_linearIsometryEquiv L 0 σ2.1, map_zero, canonicalModel, hcm0]
  -- risk change of variables `linearBaseRisk f = canonicalRisk (f ∘ L⁻¹)`
  have hbridge : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Measurable f →
      linearBaseRisk σ2 ρ f = canonicalRisk σ2 ρ (fun z => f (L.symm z)) := by
    intro f hf
    have hφ : Measurable (fun z => ENNReal.ofReal (ρ (f (L.symm z)))) :=
      ENNReal.measurable_ofReal.comp (hρmeas.comp (hf.comp hLsymm))
    show ∫⁻ y, ENNReal.ofReal (ρ (f y)) ∂(gaussianVector (0 : EuclideanSpace ℝ (Fin n)) σ2.1)
        = ∫⁻ z, ENNReal.ofReal (ρ (f (L.symm z)))
            ∂(canonicalModel (s := Module.finrank ℝ W) (m := m) (_, σ2))
    rw [← hbaseL, lintegral_map hφ hLmeas]
    refine lintegral_congr (fun y => ?_)
    rw [L.symm_apply_apply]
  -- the estimator, transported, is exactly `δ₀` of the canonical core
  have hδL : (fun z => δ (L.symm z)) = fun z => ∑ i, lam i * canonicalHead z i := by
    funext z
    rw [hδdef]
    show ⟪γ, lse W (L.symm z)⟫_ℝ = ∑ i, lam i * canonicalHead z i
    rw [hlse γ hγ (L.symm z), L.apply_symm_apply]
  have hδmeas : Measurable δ := by
    rw [hδdef]
    exact (continuous_const.inner W.starProjection.continuous).measurable
  refine ⟨hδmeas, ?_, fun δ' hδ'meas hδ'equiv => ?_⟩
  · -- subspace-equivariance of `δ`
    intro b hb y
    rw [hδdef]
    show ⟪γ, lse W (y + b)⟫_ℝ = ⟪γ, lse W y⟫_ℝ + ⟪γ, b⟫_ℝ
    rw [show lse W (y + b) = W.starProjection (y + b) from rfl,
      show lse W y = W.starProjection y from rfl, map_add,
      Submodule.starProjection_eq_self_iff.mpr hb, inner_add_right]
  · -- minimality via the canonical convex-symmetric core
    obtain ⟨_, _, hmin⟩ :=
      isCanonicalMRE_linear_combination (s := Module.finrank ℝ W) (m := m) hm lam σ2 hconv heven
    rw [hbridge δ hδmeas, hbridge δ' hδ'meas, hδL]
    refine hmin (fun z => δ' (L.symm z)) (hδ'meas.comp hLsymm) ?_
    -- `δ' ∘ L⁻¹` is canonically equivariant with coefficient vector `lam`
    intro a z
    show δ' (L.symm (z + canonicalMean a)) = δ' (L.symm z) + ∑ i, lam i * a i
    obtain ⟨x, hx⟩ := hsurj a
    change canonicalHead (L (x : EuclideanSpace ℝ (Fin n))) = a at hx
    have hLx : L (x : EuclideanSpace ℝ (Fin n)) = canonicalMean a := by
      rw [hmean (x : EuclideanSpace ℝ (Fin n)) x.2, hx]
    have hsymm : L.symm (canonicalMean a) = (x : EuclideanSpace ℝ (Fin n)) := by
      rw [← hLx, L.symm_apply_apply]
    rw [map_add, hsymm, hδ'equiv (x : EuclideanSpace ℝ (Fin n)) x.2 (L.symm z)]
    congr 1
    have hxproj : lse W (x : EuclideanSpace ℝ (Fin n)) = (x : EuclideanSpace ℝ (Fin n)) :=
      Submodule.starProjection_eq_self_iff.mpr x.2
    have hxval := hlse γ hγ (x : EuclideanSpace ℝ (Fin n))
    rw [hxproj] at hxval
    rw [hxval]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hlam, hx]

end StatLean.PointEstimation
