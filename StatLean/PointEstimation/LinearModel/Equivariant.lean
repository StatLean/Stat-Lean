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

/-! ### Gaussian scaling bricks (private scaffolding)

The location-scale optimality below rests on one analytic fact about the isotropic Gaussian:
a function invariant under positive scalings is *uncorrelated with the radius*. It is derived
here from the exact Gaussian tilt identity — tilting the standard product Gaussian by
`exp(-((λ−1)/2)‖x‖²)` is the same as changing the variance from `1` to `1/λ`, which a
scale-invariant integrand cannot see. -/

/-- Product of `N` centred Gaussians of variance `v` on `Fin N → ℝ`. -/
private noncomputable def piGauss (N : ℕ) (v : ℝ≥0) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ : Fin N => gaussianReal 0 v

private instance instIsProbPiGauss (N : ℕ) (v : ℝ≥0) :
    IsProbabilityMeasure (piGauss N v) := by
  unfold piGauss; infer_instance

private lemma piGauss_withDensity (N : ℕ) {v : ℝ≥0} (hv : v ≠ 0) :
    piGauss N v
      = (volume : Measure (Fin N → ℝ)).withDensity
          (fun x => ∏ i, gaussianPDF 0 v (x i)) := by
  have h_each : (fun _ : Fin N => gaussianReal (0 : ℝ) v)
      = fun _ : Fin N => (volume : Measure ℝ).withDensity (gaussianPDF 0 v) := by
    funext _; exact gaussianReal_of_var_ne_zero 0 hv
  haveI : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF (0 : ℝ) v)) := by
    rw [← gaussianReal_of_var_ne_zero (0 : ℝ) hv]; infer_instance
  rw [piGauss, h_each, ← pi_withDensity_prod (fun _ : Fin N => measurable_gaussianPDF (0 : ℝ) v),
    ← volume_pi]

private lemma piGauss_map_smul (N : ℕ) (c : ℝ) :
    (piGauss N 1).map (fun x => c • x) = piGauss N ⟨c ^ 2, sq_nonneg c⟩ := by
  have hf : ∀ _ : Fin N, AEMeasurable (fun t : ℝ => c * t) (gaussianReal 0 1) :=
    fun _ => (measurable_const_mul c).aemeasurable
  have hmap : ∀ _ : Fin N, (gaussianReal (0 : ℝ) 1).map (fun t : ℝ => c * t)
      = gaussianReal 0 ⟨c ^ 2, sq_nonneg c⟩ := by
    intro _
    rw [gaussianReal_map_const_mul (c := c), mul_zero, mul_one]
  haveI : ∀ _ : Fin N, SigmaFinite ((gaussianReal (0 : ℝ) 1).map (fun t : ℝ => c * t)) := by
    intro i; rw [hmap i]; infer_instance
  have hcast : (fun x : Fin N → ℝ => c • x) = fun (x : Fin N → ℝ) (i : Fin N) => c * x i := rfl
  rw [piGauss, piGauss, hcast, Measure.pi_map_pi hf]
  exact congrArg Measure.pi (funext hmap)

/-- The product of `N` centred Gaussian densities of variance `w`, in closed form. -/
private lemma prod_gaussianPDFReal (N : ℕ) (w : ℝ≥0) (x : Fin N → ℝ) :
    ∏ i, gaussianPDFReal 0 w (x i)
      = (Real.sqrt (2 * Real.pi * w))⁻¹ ^ N
          * Real.exp (-(∑ i, x i ^ 2) / (2 * (w : ℝ))) := by
  simp only [gaussianPDFReal, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  rw [neg_div, ← Finset.sum_div, Finset.sum_neg_distrib, neg_div]

/-- **Gaussian tilt identity.** For a measurable function `u` that is invariant under positive
scalings, tilting the standard product Gaussian by `exp(-((λ−1)/2)‖x‖²)` only multiplies the
integral of `u` by the constant `λ^{−N/2}` — the tilt is exactly a change of variance, and `u`
does not see it. -/
private lemma lintegral_hom_exp_tilt {N : ℕ} {u : (Fin N → ℝ) → ℝ≥0∞}
    (hu : Measurable u) (hhom : ∀ c : ℝ, 0 < c → ∀ x, u (c • x) = u x)
    {lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ x, u x * ENNReal.ofReal (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2)) ∂(piGauss N 1)
      = ENNReal.ofReal ((Real.sqrt lam)⁻¹ ^ N) * ∫⁻ x, u x ∂(piGauss N 1) := by
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  set c : ℝ := (Real.sqrt lam)⁻¹ with hc_def
  have hcpos : 0 < c := by rw [hc_def]; positivity
  set v : ℝ≥0 := ⟨c ^ 2, sq_nonneg c⟩ with hv_def
  have hvcoe : (v : ℝ) = lam⁻¹ := by
    rw [hv_def]
    show c ^ 2 = lam⁻¹
    rw [hc_def, inv_pow, Real.sq_sqrt hlam.le]
  have hvne : v ≠ 0 := by
    intro h
    have : (v : ℝ) = 0 := by rw [h]; simp
    rw [hvcoe] at this
    exact absurd this (by positivity)
  -- the pointwise density identity
  have hdens : ∀ x : Fin N → ℝ,
      (∏ i, gaussianPDF 0 1 (x i)) * ENNReal.ofReal
          (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2))
        = ENNReal.ofReal ((Real.sqrt lam)⁻¹ ^ N) * ∏ i, gaussianPDF 0 v (x i) := by
    intro x
    have hprod : ∀ w : ℝ≥0, ∏ i, gaussianPDF 0 w (x i)
        = ENNReal.ofReal (∏ i, gaussianPDFReal 0 w (x i)) := by
      intro w
      simp only [gaussianPDF_def]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)]
    rw [hprod, hprod, ← ENNReal.ofReal_mul (Finset.prod_nonneg
        (fun i _ => gaussianPDFReal_nonneg _ _ _)),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [prod_gaussianPDFReal, prod_gaussianPDFReal, hvcoe, NNReal.coe_one, mul_one]
    have hlne : lam ≠ 0 := hlam.ne'
    have hconst : (Real.sqrt lam)⁻¹ ^ N * (Real.sqrt (2 * Real.pi * lam⁻¹))⁻¹ ^ N
        = (Real.sqrt (2 * Real.pi))⁻¹ ^ N := by
      have hcancel : lam * (2 * Real.pi * lam⁻¹) = 2 * Real.pi := by field_simp
      rw [← mul_pow, ← mul_inv, ← Real.sqrt_mul hlam.le, hcancel]
    have hexp : (-(∑ i, x i ^ 2)) / (2 * 1) + -((lam - 1) / 2) * ∑ i, x i ^ 2
        = (-(∑ i, x i ^ 2)) / (2 * lam⁻¹) := by
      field_simp
      ring
    rw [mul_assoc, ← Real.exp_add, ← mul_assoc, hconst, hexp]
  -- rewrite both sides as Lebesgue integrals against the explicit densities
  have hmeasD : ∀ w : ℝ≥0, Measurable (fun x : Fin N → ℝ => ∏ i, gaussianPDF 0 w (x i)) :=
    fun w => Finset.measurable_prod _
      (fun i _ => (measurable_gaussianPDF 0 w).comp (measurable_pi_apply i))
  have hmeasE : Measurable (fun x : Fin N → ℝ =>
      ENNReal.ofReal (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2))) := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact measurable_const.mul (Finset.measurable_sum _
      (fun i _ => (measurable_pi_apply i).pow_const 2))
  have hstep1 : ∫⁻ x, u x * ENNReal.ofReal
        (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2)) ∂(piGauss N 1)
      = ENNReal.ofReal ((Real.sqrt lam)⁻¹ ^ N) * ∫⁻ x, u x ∂(piGauss N v) := by
    rw [piGauss_withDensity N (one_ne_zero), piGauss_withDensity N hvne,
      lintegral_withDensity_eq_lintegral_mul _ (hmeasD 1) (hu.mul hmeasE),
      lintegral_withDensity_eq_lintegral_mul _ (hmeasD v) hu]
    simp only [Pi.mul_apply]
    rw [← lintegral_const_mul _ ((hmeasD v).mul hu)]
    refine lintegral_congr (fun x => ?_)
    rw [show (∏ i, gaussianPDF 0 1 (x i)) * (u x * ENNReal.ofReal
          (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2)))
        = ((∏ i, gaussianPDF 0 1 (x i)) * ENNReal.ofReal
          (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2))) * u x from by ring,
      hdens x, mul_assoc]
  rw [hstep1]
  congr 1
  rw [show v = ⟨c ^ 2, sq_nonneg c⟩ from rfl, ← piGauss_map_smul N c,
    lintegral_map hu (measurable_const_smul c)]
  exact lintegral_congr (fun x => hhom c hcpos x)


/-- The squared radius on the pi space. -/
private def sqSum {N : ℕ} (x : Fin N → ℝ) : ℝ := ∑ i, x i ^ 2

private lemma measurable_sqSum {N : ℕ} : Measurable (sqSum (N := N)) :=
  Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).pow_const 2)

/-- **Radius independence, bounded form.** A bounded, positively-scale-invariant `u` is
uncorrelated with every measurable function of the squared radius under the standard
product Gaussian. -/
private lemma lintegral_hom_mul_bounded {N : ℕ} {u : (Fin N → ℝ) → ℝ≥0∞}
    (hu : Measurable u) (hhom : ∀ c : ℝ, 0 < c → ∀ x, u (c • x) = u x)
    {K : ℝ≥0∞} (hK : K ≠ ⊤) (hbdd : ∀ x, u x ≤ K)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x, u x * φ (sqSum x) ∂(piGauss N 1)
      = (∫⁻ x, u x ∂(piGauss N 1)) * ∫⁻ x, φ (sqSum x) ∂(piGauss N 1) := by
  set μ : Measure (Fin N → ℝ) := piGauss N 1 with hμ
  set C : ℝ≥0∞ := ∫⁻ x, u x ∂μ with hC
  have hCfin : C ≠ ⊤ := by
    have h1 : C ≤ K := by
      calc C ≤ ∫⁻ _, K ∂μ := lintegral_mono hbdd
        _ = K := by rw [lintegral_const, measure_univ, mul_one]
    exact ne_top_of_le_ne_top hK h1
  set ν₁ : Measure ℝ := (μ.withDensity u).map sqSum with hν₁
  set ν₂ : Measure ℝ := C • (μ.map sqSum) with hν₂
  have hval₁ : ∀ ψ : ℝ → ℝ≥0∞, Measurable ψ →
      ∫⁻ y, ψ y ∂ν₁ = ∫⁻ x, u x * ψ (sqSum x) ∂μ := by
    intro ψ hψ
    have hcomp : Measurable (fun x : Fin N → ℝ => ψ (sqSum x)) := hψ.comp measurable_sqSum
    rw [hν₁, lintegral_map hψ measurable_sqSum,
      lintegral_withDensity_eq_lintegral_mul _ hu hcomp]
    rfl
  have hval₂ : ∀ ψ : ℝ → ℝ≥0∞, Measurable ψ →
      ∫⁻ y, ψ y ∂ν₂ = C * ∫⁻ x, ψ (sqSum x) ∂μ := by
    intro ψ hψ
    rw [hν₂, lintegral_smul_measure, lintegral_map hψ measurable_sqSum, smul_eq_mul]
  haveI hfin₁ : IsFiniteMeasure ν₁ := by
    constructor
    rw [hν₁, Measure.map_apply measurable_sqSum MeasurableSet.univ, Set.preimage_univ,
      withDensity_apply u MeasurableSet.univ, setLIntegral_univ]
    exact hCfin.lt_top
  haveI hfin₂ : IsFiniteMeasure ν₂ := by
    constructor
    rw [hν₂, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply measurable_sqSum MeasurableSet.univ, Set.preimage_univ,
      measure_univ, mul_one]
    exact hCfin.lt_top
  -- the two Laplace transforms agree on `(-∞, 1/2)`
  have hexpmeas : ∀ t : ℝ, Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (t * y))) :=
    fun t => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul t))
  have hlap : ∀ t : ℝ, t < 1 / 2 →
      (∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν₁
          = ENNReal.ofReal ((Real.sqrt (1 - 2 * t))⁻¹ ^ N) * C
        ∧ ∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν₂
          = ENNReal.ofReal ((Real.sqrt (1 - 2 * t))⁻¹ ^ N) * C) := by
    intro t ht
    have hlam : (0 : ℝ) < 1 - 2 * t := by linarith
    have hcoef : -((1 - 2 * t - 1) / 2) = t := by ring
    constructor
    · rw [hval₁ _ (hexpmeas t)]
      have := lintegral_hom_exp_tilt (N := N) hu hhom hlam
      rw [hcoef] at this
      rw [show (fun x : Fin N → ℝ => u x * ENNReal.ofReal (Real.exp (t * sqSum x)))
            = fun x => u x * ENNReal.ofReal (Real.exp (t * ∑ i, x i ^ 2)) from rfl]
      exact this
    · rw [hval₂ _ (hexpmeas t)]
      have := lintegral_hom_exp_tilt (N := N) (u := fun _ => 1) measurable_const
        (fun c _ x => rfl) hlam
      rw [hcoef] at this
      simp only [one_mul, lintegral_const, measure_univ, mul_one] at this
      rw [show (fun x : Fin N → ℝ => ENNReal.ofReal (Real.exp (t * sqSum x)))
            = fun x => ENNReal.ofReal (Real.exp (t * ∑ i, x i ^ 2)) from rfl, this,
        mul_comm]
  have hfinlap : ∀ t : ℝ, t < 1 / 2 →
      ∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν₁ ≠ ⊤ := by
    intro t ht
    rw [(hlap t ht).1]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCfin
  have hint : ∀ (ν : Measure ℝ) (t : ℝ),
      (∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν ≠ ⊤) →
      Integrable (fun y => Real.exp (t * y)) ν := by
    intro ν t htop
    refine ⟨(Real.measurable_exp.comp (measurable_const_mul t)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun y => (Real.exp_pos _).le))]
    exact lt_top_iff_ne_top.mpr htop
  have hbochner : ∀ (ν : Measure ℝ) (t : ℝ),
      ∫ y, Real.exp (t * y) ∂ν = (∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν).toReal := by
    intro ν t
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun y => (Real.exp_pos _).le))
      (Real.measurable_exp.comp (measurable_const_mul t)).aestronglyMeasurable
  have hfinlap₂ : ∀ t : ℝ, t < 1 / 2 →
      ∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν₂ ≠ ⊤ := by
    intro t ht
    rw [(hlap t ht).2]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCfin
  have hkey : ν₁ = ν₂ := by
    refine ext_of_integral_exp_eqOn (S := Set.Iio (1 / 2 : ℝ))
      (by rw [interior_Iio]; exact ⟨0, by norm_num⟩)
      (fun t ht => hint _ t (hfinlap t ht))
      (fun t ht => hint _ t (hfinlap₂ t ht))
      (fun t ht => ?_)
    rw [hbochner, hbochner, (hlap t ht).1, (hlap t ht).2]
  rw [← hval₁ φ hφ, hkey, hval₂ φ hφ]

/-- **Radius independence.** A positively-scale-invariant `u` is uncorrelated with every
measurable function of the squared radius under the standard product Gaussian. -/
private lemma lintegral_hom_mul {N : ℕ} {u : (Fin N → ℝ) → ℝ≥0∞}
    (hu : Measurable u) (hhom : ∀ c : ℝ, 0 < c → ∀ x, u (c • x) = u x)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x, u x * φ (sqSum x) ∂(piGauss N 1)
      = (∫⁻ x, u x ∂(piGauss N 1)) * ∫⁻ x, φ (sqSum x) ∂(piGauss N 1) := by
  set μ : Measure (Fin N → ℝ) := piGauss N 1 with hμ
  set w : ℕ → (Fin N → ℝ) → ℝ≥0∞ := fun n x => min (u x) (n : ℝ≥0∞) with hw
  have hwmeas : ∀ n, Measurable (w n) := fun n => hu.min measurable_const
  have hwhom : ∀ n, ∀ c : ℝ, 0 < c → ∀ x, w n (c • x) = w n x := by
    intro n c hc x; rw [hw]; simp only [hhom c hc x]
  have hwmono : Monotone w := by
    intro a b hab x
    exact min_le_min le_rfl (by exact_mod_cast Nat.cast_le.mpr hab)
  have hwsup : ∀ x, ⨆ n, w n x = u x := by
    intro x
    refine le_antisymm (iSup_le (fun n => min_le_left _ _)) ?_
    exact le_of_forall_lt (fun b hb => by
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hb)
      exact lt_of_lt_of_le (lt_min hb hn) (le_iSup (fun n => w n x) n))
  have hstep : ∀ n, ∫⁻ x, w n x * φ (sqSum x) ∂μ
      = (∫⁻ x, w n x ∂μ) * ∫⁻ x, φ (sqSum x) ∂μ :=
    fun n => lintegral_hom_mul_bounded (hwmeas n) (hwhom n)
      (ENNReal.natCast_ne_top n) (fun x => min_le_right _ _) hφ
  have hφc : Measurable (fun x : Fin N → ℝ => φ (sqSum x)) := hφ.comp measurable_sqSum
  have hL : ∫⁻ x, u x * φ (sqSum x) ∂μ = ⨆ n, ∫⁻ x, w n x * φ (sqSum x) ∂μ := by
    rw [← lintegral_iSup (fun n => (hwmeas n).mul hφc)
      (fun a b hab x => mul_le_mul' (hwmono hab x) le_rfl)]
    refine lintegral_congr (fun x => ?_)
    rw [← hwsup x, ENNReal.iSup_mul]
  have hR : ∫⁻ x, u x ∂μ = ⨆ n, ∫⁻ x, w n x ∂μ := by
    rw [← lintegral_iSup hwmeas (fun a b hab x => hwmono hab x)]
    exact lintegral_congr (fun x => (hwsup x).symm)
  rw [hL, hR, ENNReal.iSup_mul]
  exact iSup_congr hstep


private lemma sqSum_nonneg {N : ℕ} (x : Fin N → ℝ) : 0 ≤ sqSum x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

private lemma sqSum_smul {N : ℕ} (c : ℝ) (x : Fin N → ℝ) :
    sqSum (c • x) = c ^ 2 * sqSum x := by
  simp only [sqSum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [Pi.smul_apply, smul_eq_mul, mul_pow])

/-- The last `m` coordinates of a standard product Gaussian are again a standard product
Gaussian. -/
private lemma piGauss_map_tail (s m : ℕ) :
    (piGauss (s + m) 1).map (fun (x : Fin (s + m) → ℝ) (j : Fin m) => x (Fin.natAdd s j))
      = piGauss m 1 := by
  classical
  have hmeas : Measurable (fun (x : Fin (s + m) → ℝ) (j : Fin m) => x (Fin.natAdd s j)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  change (Measure.pi fun _ : Fin (s + m) => gaussianReal (0 : ℝ) 1).map _
      = Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1
  refine (Measure.pi_eq (μ := fun _ : Fin m => gaussianReal (0 : ℝ) 1) (fun t ht => ?_)).symm
  set t' : Fin (s + m) → Set ℝ := Fin.addCases (fun _ => Set.univ) t with ht'
  have hleft : ∀ i : Fin s, t' (Fin.castAdd m i) = Set.univ := fun i => by
    rw [ht']; exact Fin.addCases_left i
  have hright : ∀ j : Fin m, t' (Fin.natAdd s j) = t j := fun j => by
    rw [ht']; exact Fin.addCases_right j
  have hpre : (fun (x : Fin (s + m) → ℝ) (j : Fin m) => x (Fin.natAdd s j)) ⁻¹'
      (Set.univ.pi t) = Set.univ.pi t' := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [hleft i]; exact Set.mem_univ _
      · rw [hright j]; exact h j
    · intro h j
      have hk := h (Fin.natAdd s j)
      rwa [hright j] at hk
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi ht), hpre, Measure.pi_pi,
    Fin.prod_univ_add]
  have hone : ∀ i : Fin s, (gaussianReal (0 : ℝ) 1) (t' (Fin.castAdd m i)) = 1 := by
    intro i; rw [hleft i]; exact measure_univ
  rw [Finset.prod_congr rfl (fun i _ => hone i), Finset.prod_const_one, one_mul]
  exact Finset.prod_congr rfl (fun j _ => by rw [hright j])

/-- The squared radius of a standard product Gaussian is `χ²ₘ`. -/
private lemma piGauss_map_sqSum {m : ℕ} (hm : 0 < m) :
    (piGauss m 1).map sqSum = chiSquared m := by
  have hlaw : ∀ i : Fin m,
      Measure.map (fun x : Fin m → ℝ => x i) (piGauss m 1) = gaussianReal 0 1 := fun i =>
    (measurePreserving_eval (fun _ : Fin m => gaussianReal (0 : ℝ) 1) i).map_eq
  have hindep : iIndepFun (fun (i : Fin m) (x : Fin m → ℝ) => x i) (piGauss m 1) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  exact StatLean.MultipleTesting.map_sum_sq_eq_chiSquared hm (piGauss m 1)
    (fun i x => x i) (fun i => measurable_pi_apply i) hlaw hindep

/-- Integrability of the powers of the squared radius. -/
private lemma integrable_sqSum_pow {m : ℕ} (hm : 0 < m) (k : ℕ) :
    Integrable (fun w : Fin m → ℝ => sqSum w ^ k) (piGauss m 1) := by
  have hasm : AEStronglyMeasurable (fun v : ℝ => v ^ k) ((piGauss m 1).map sqSum) :=
    (continuous_pow k).measurable.aestronglyMeasurable
  have h := integrable_pow_chiSquared hm k
  rw [← piGauss_map_sqSum hm] at h
  exact (integrable_map_measure hasm measurable_sqSum.aemeasurable).mp h

/-- The moments of the squared radius are the `χ²ₘ` moments. -/
private lemma integral_sqSum_pow {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∫ w : Fin m → ℝ, sqSum w ^ k ∂(piGauss m 1) = ∫ v, v ^ k ∂(chiSquared m) := by
  have hasm : AEStronglyMeasurable (fun v : ℝ => v ^ k) ((piGauss m 1).map sqSum) :=
    (continuous_pow k).measurable.aestronglyMeasurable
  rw [← piGauss_map_sqSum hm, integral_map measurable_sqSum.aemeasurable hasm]

/-- The `ℝ≥0∞` form of the moments of the squared radius. -/
private lemma lintegral_sqSum_pow {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∫⁻ w : Fin m → ℝ, ENNReal.ofReal (sqSum w ^ k) ∂(piGauss m 1)
      = ENNReal.ofReal (∫ v, v ^ k ∂(chiSquared m)) := by
  rw [← integral_sqSum_pow hm k,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_sqSum_pow hm k)
      (ae_of_all _ (fun w => pow_nonneg (sqSum_nonneg w) k))]

/-- Positivity of the `χ²ₘ` moments (`m ≥ 1`). -/
private lemma chiSquared_moment_pos {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : 0 < k) :
    0 < ∫ v, v ^ k ∂(chiSquared m) := by
  classical
  rw [← integral_sqSum_pow hm k]
  rw [integral_pos_iff_support_of_nonneg (fun w => pow_nonneg (sqSum_nonneg w) k)
    (integrable_sqSum_pow hm k)]
  obtain ⟨j₀⟩ : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hZ : MeasurableSet {w : Fin m → ℝ | sqSum w = 0} :=
    measurableSet_eq_fun measurable_sqSum measurable_const
  have hnull : (piGauss m 1) {w : Fin m → ℝ | sqSum w = 0} = 0 := by
    have hsub : {w : Fin m → ℝ | sqSum w = 0} ⊆ {w : Fin m → ℝ | w j₀ = 0} := by
      intro w hw
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (w i))).mp hw
      have h0 := this j₀ (Finset.mem_univ j₀)
      exact sq_eq_zero_iff.mp h0
    refine measure_mono_null hsub ?_
    have hev : {w : Fin m → ℝ | w j₀ = 0} = (fun x : Fin m → ℝ => x j₀) ⁻¹' {(0 : ℝ)} := rfl
    haveI : NoAtoms (gaussianReal (0 : ℝ) 1) := noAtoms_gaussianReal one_ne_zero
    have hmapev : Measure.map (fun x : Fin m → ℝ => x j₀) (piGauss m 1) = gaussianReal 0 1 :=
      (measurePreserving_eval (fun _ : Fin m => gaussianReal (0 : ℝ) 1) j₀).map_eq
    rw [hev, ← Measure.map_apply (measurable_pi_apply j₀) (measurableSet_singleton _), hmapev]
    exact measure_singleton 0
  have hsupp : (Function.support fun w : Fin m → ℝ => sqSum w ^ k)
      = {w : Fin m → ℝ | sqSum w = 0}ᶜ := by
    ext w
    simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_setOf_eq]
    exact ⟨fun h hc => h (by rw [hc, zero_pow hk.ne']), fun h hc =>
      h ((pow_eq_zero_iff hk.ne').mp hc)⟩
  rw [hsupp, prob_compl_eq_one_sub hZ, hnull, tsub_zero]
  exact zero_lt_one


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
