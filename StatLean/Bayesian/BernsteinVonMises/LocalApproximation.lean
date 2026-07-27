import StatLean.Bayesian.BernsteinVonMises.MixtureContiguity
import StatLean.Bayesian.BernsteinVonMises.PosteriorConcentration
import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianDensity
import StatLean.Bayesian.Dominated.PosteriorLintegral
import StatLean.Bayesian.Updating.IID

/-!
# Step B: Gaussian approximation of the conditioned local posterior

The second half of the proof of vdV Theorem 10.1: on every **fixed** ball `C = B̄(0, R)` of
the local parameter, the total-variation distance between the `C`-conditioned local
posterior and the `C`-conditioned Gaussian `N(Δ_{n,θ₀}, J⁻¹)` tends to zero in
`P^n_{θ₀}`-probability.

Objects (all with the Lebesgue-density normalizations *dropped* — only ratios matter):

* `bvmJointDens` — the unnormalized local joint density
  `h ↦ ∏ᵢ p_{θ₀+h/√n}(ωᵢ) · f(θ₀+h/√n)` (likelihood times prior density in local
  coordinates; the Jacobian `n^{-k/2}` cancels in all ratios);
* `bvmNumer` — its integral over a set of local parameters;
* `bvmGaussDens` — the unnormalized Gaussian density
  `h ↦ exp(⟪h, Δ̃ₙ⟫ − ⟪h, Jh⟫/2)` with `Δ̃ₙ = scoreSum` (so that `J·Δ_{n,θ₀} = Δ̃ₙ`);
* `bvmLogRatio` — the log of vdV's pair ratio
  `[p_{n,g} π_n(g) / p_{n,h} π_n(h)] / [dN(Δₙ,J⁻¹)(g)/dN(Δₙ,J⁻¹)(h)]`.

Main statements:

* `cond_bvmLocalPosterior_apply_ae` — the conditioned local posterior as a ratio of
  `bvmNumer`s (predictive-a.e., once the rescaled ball sits inside the prior's
  absolute-continuity zone);
* `cond_bvmGaussian_apply` — the conditioned Gaussian as a ratio of `bvmGaussDens`
  integrals;
* `bvmLogRatio_tendsto` — for **fixed** `g, h`, the log pair ratio tends to zero in
  `P^n_{θ₀}`-probability (two applications of the LAN residual + continuity of the prior
  density at `θ₀`); no uniformity in `(g,h)` is needed;
* `local_tv_tendsto` — the Step-B conclusion, for every fixed radius `R`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Theorem 10.1, pp. 142–143 (the second step, from "Next consider the posterior measures
relative to the priors `Π_n^C`").

**Proof formalization notes.** The chain: `tvDist_normalize_le_double_lintegral` (the
pair-ratio Jensen bound) reduces the conditioned TV distance to a double integral of
`(1 − exp(bvmLogRatio))⁺`; the third measure is replaced by normalized Lebesgue on `C`
through the two-sided Gaussian/Lebesgue comparisons of `MultivariateGaussianDensity` on the
event `‖Δₙ‖ ≤ K` (score-CLT tightness); per-(g,h) convergence (`bvmLogRatio_tendsto`)
lifts to the triple product by Fubini and bounded convergence; the resulting expectation
under the mixture transfers to `P^n_{θ₀}` by `mutuallyContiguous_mixture_base`. The good
events where the a.e. density identities hold are discharged by
`measure_tendsto_zero_of_predictive_null`. Everything is phrased with the **true product
densities** `∏ᵢ p_θ(ωᵢ)` (never `exp ∘ logLikelihood`, which differs off the common-support
rectangle); the LAN residual enters only through `bvmLogRatio_tendsto`, whose proof
restricts to the good rectangle using the DQM singular-mass controls
(`dqm_perturbation_excess/deficit_mass_tendsto`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure scoreSum logLikelihood)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {κ : Kernel (EuclideanSpace ℝ (Fin k)) 𝓧} [IsMarkovKernel κ]
variable {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- The **unnormalized local joint density** at local parameter `h`:
`∏ᵢ p_{θ₀+h/√n}(ωᵢ) · f(θ₀ + h/√n)` (vdV p. 141: `p_{n,h}(x) πₙ(h)`, with the constant
Jacobian dropped). -/
noncomputable def bvmJointDens (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (h : EuclideanSpace ℝ (Fin k)) (ω : Fin n → 𝓧) : ℝ≥0∞ :=
  (∏ i, ENNReal.ofReal (M.density (bvmLocalUnscale θ₀ n h) (ω i)))
    * ENNReal.ofReal (f (bvmLocalUnscale θ₀ n h))

/-- The **local numerator**: the integral of the local joint density over a set `C` of local
parameters, against Lebesgue measure. -/
noncomputable def bvmNumer (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (C : Set (EuclideanSpace ℝ (Fin k))) (ω : Fin n → 𝓧) : ℝ≥0∞ :=
  ∫⁻ h in C, bvmJointDens M f θ₀ n h ω ∂volume

lemma measurable_bvmNumer
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- LEAN-ONLY: measurable prior density (regularity)
    (hf : Measurable f) (n : ℕ) {C : Set (EuclideanSpace ℝ (Fin k))}
    -- LEAN-ONLY: measurable localization set (regularity)
    (hC : MeasurableSet C) :
    Measurable fun ω : Fin n → 𝓧 => bvmNumer M f θ₀ n C ω := by
  have hun : Measurable fun hh : EuclideanSpace ℝ (Fin k) => bvmLocalUnscale θ₀ n hh :=
    measurable_bvmLocalUnscale θ₀ n
  have hjoint : Measurable fun p : (Fin n → 𝓧) × EuclideanSpace ℝ (Fin k) =>
      bvmJointDens M f θ₀ n p.2 p.1 := by
    unfold bvmJointDens
    refine Measurable.mul ?_ ?_
    · refine Finset.univ.measurable_prod fun i _ => ?_
      exact ENNReal.measurable_ofReal.comp
        (hM_joint.comp ((hun.comp measurable_snd).prodMk
          ((measurable_pi_apply i).comp measurable_fst)))
    · exact ENNReal.measurable_ofReal.comp (hf.comp (hun.comp measurable_snd))
  unfold bvmNumer
  exact hjoint.lintegral_prod_right' (ν := volume.restrict C)

/-- The **unnormalized Gaussian density** of `N(Δ_{n,θ₀}, J⁻¹)` in local coordinates:
`exp(⟪h, Δ̃ₙ(ω)⟫ − ⟪h, Jh⟫/2)` with `Δ̃ₙ = scoreSum` (note `J Δ_{n,θ₀} = Δ̃ₙ`; the
Lebesgue normalizer and the factor `exp(−⟪Δₙ, JΔₙ⟫/2)` are dropped — they cancel in
ratios). -/
noncomputable def bvmGaussDens (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (h : EuclideanSpace ℝ (Fin k))
    (ω : Fin n → 𝓧) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (⟪h, scoreSum sc n ω⟫
    - (1 / 2 : ℝ) * ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))

-- The unnormalized Gaussian density is measurable in the local parameter.
private lemma measurable_bvmGaussDens (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) :
    Measurable fun h : EuclideanSpace ℝ (Fin k) => bvmGaussDens J sc n h ω := by
  have hcont : Continuous fun h : EuclideanSpace ℝ (Fin k) =>
      (⟪h, scoreSum sc n ω⟫ - (1 / 2 : ℝ) * ⟪h, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) h⟫) := by
    fun_prop
  exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hcont).measurable

-- A positive finite scalar cancels between the two `cond` factors.
private lemma ennreal_smul_cond_ratio {d X Y : ℝ≥0∞} (hd : d ≠ 0) (hd' : d ≠ ∞) :
    (d * X)⁻¹ * (d * Y) = Y / X := by
  rw [ENNReal.mul_inv (Or.inl hd) (Or.inl hd'), div_eq_mul_inv,
    show d⁻¹ * X⁻¹ * (d * Y) = (d⁻¹ * d) * (Y * X⁻¹) from by ring,
    ENNReal.inv_mul_cancel hd hd', one_mul]

/-- The random Gaussian `N(Δₙ, J⁻¹)` is a positive finite multiple of the Lebesgue measure
with density `bvmGaussDens`: the normalizer and the mean-dependent constant of the tilt are
absorbed into the scalar, which then cancels in every conditional ratio. -/
private lemma exists_bvmGaussian_eq_smul_withDensity (hJ_pd : J.PosDef) (n : ℕ)
    (ω : Fin n → 𝓧) :
    ∃ d : ℝ≥0∞, 0 < d ∧ d ≠ ∞ ∧
      bvmGaussian J sc n ω
        = d • volume.withDensity fun h => bvmGaussDens J sc n h ω := by
  classical
  have hJunit : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).mp hJ_pd.isUnit
  have hS : (J⁻¹).PosDef := hJ_pd.inv
  have hSS : (J⁻¹)⁻¹ = J := Matrix.nonsing_inv_nonsing_inv _ hJunit
  -- `J Δₙ = scoreSum`, since `Δₙ = J⁻¹ scoreSum`
  have hJm : (Matrix.toEuclideanCLM (𝕜 := ℝ) J) (bvmEffScore J sc n ω) = scoreSum sc n ω := by
    rw [bvmEffScore, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      ← map_mul, Matrix.mul_nonsing_inv _ hJunit, map_one]
    rfl
  obtain ⟨c, hcpos, hctop, hc⟩ := AsymptoticStatistics.multivariateGaussian_eq_smul_withDensity hS
  have htilt := AsymptoticStatistics.multivariateGaussian_eq_withDensity_tilt hS
    (bvmEffScore J sc n ω)
  rw [hSS] at hc htilt
  rw [hJm] at htilt
  set a : ℝ := ⟪bvmEffScore J sc n ω, scoreSum sc n ω⟫ with ha
  have hD0meas : Measurable fun x : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (Real.exp (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) x⟫ / 2)) := by
    have : Continuous fun x : EuclideanSpace ℝ (Fin k) =>
        (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) x⟫ / 2) := by fun_prop
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp this).measurable
  have hD1meas : Measurable fun y : EuclideanSpace ℝ (Fin k) =>
      ENNReal.ofReal (Real.exp (⟪scoreSum sc n ω, y⟫ - a / 2)) := by
    have : Continuous fun y : EuclideanSpace ℝ (Fin k) =>
        (⟪scoreSum sc n ω, y⟫ - a / 2) := by fun_prop
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp this).measurable
  have hGmeas := measurable_bvmGaussDens J sc n ω
  have hprod : ((fun x : EuclideanSpace ℝ (Fin k) =>
        ENNReal.ofReal (Real.exp (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) x⟫ / 2)))
      * fun y : EuclideanSpace ℝ (Fin k) =>
        ENNReal.ofReal (Real.exp (⟪scoreSum sc n ω, y⟫ - a / 2)))
      = ENNReal.ofReal (Real.exp (-a / 2)) • fun x => bvmGaussDens J sc n x ω := by
    funext x
    have hq : ⟪x, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) x))⟫
        = ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) J) x⟫ := rfl
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, bvmGaussDens]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hq, real_inner_comm (scoreSum sc n ω) x]
    ring_nf
  refine ⟨c * ENNReal.ofReal (Real.exp (-a / 2)), ?_, ?_, ?_⟩
  · exact ENNReal.mul_pos hcpos.ne' (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  · exact ENNReal.mul_ne_top hctop ENNReal.ofReal_ne_top
  · rw [bvmGaussian, htilt, hc, withDensity_smul_measure,
      ← withDensity_mul _ hD0meas hD1meas, hprod, withDensity_smul _ hGmeas, smul_smul]

/-- **The conditioned Gaussian as a density ratio**: for positive definite `J`,
`(N(Δₙ, J⁻¹))[|C] A = (∫_{A∩C} bvmGaussDens dλ) / (∫_C bvmGaussDens dλ)`. -/
theorem cond_bvmGaussian_apply
    -- USER-INPUT: nonsingular Fisher information; vdV Thm 10.1
    (hJ_pd : J.PosDef) (n : ℕ) (ω : Fin n → 𝓧)
    {C A : Set (EuclideanSpace ℝ (Fin k))}
    -- LEAN-ONLY: measurable localization and target sets (regularity)
    (hC : MeasurableSet C) (hA : MeasurableSet A) :
    ((bvmGaussian J sc n ω)[|C]) A
      = (∫⁻ h in A ∩ C, bvmGaussDens J sc n h ω ∂volume)
          / ∫⁻ h in C, bvmGaussDens J sc n h ω ∂volume := by
  obtain ⟨d, hdpos, hdtop, hd⟩ := exists_bvmGaussian_eq_smul_withDensity (sc := sc) hJ_pd n ω
  have hGmeas := measurable_bvmGaussDens J sc n ω
  rw [ProbabilityTheory.cond_apply hC, hd, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, withDensity_apply _ hC, withDensity_apply _ (hC.inter hA),
    Set.inter_comm C A, ennreal_smul_cond_ratio hdpos.ne' hdtop]

/-- **First display of vdV p. 143, Gaussian side**: the `C`-conditioned Gaussian is exactly
the normalized `bvmGaussDens` density against Lebesgue measure on `C` — the shape consumed by
`tvDist_normalize_le_double_lintegral`. -/
private lemma cond_bvmGaussian_eq_withDensity (hJ_pd : J.PosDef) (n : ℕ) (ω : Fin n → 𝓧)
    {C : Set (EuclideanSpace ℝ (Fin k))} (hC : MeasurableSet C) :
    ((bvmGaussian J sc n ω)[|C])
      = (volume.restrict C).withDensity fun h =>
          bvmGaussDens J sc n h ω / ∫⁻ y in C, bvmGaussDens J sc n y ω ∂volume := by
  have hGmeas := measurable_bvmGaussDens J sc n ω
  ext A hA
  rw [cond_bvmGaussian_apply hJ_pd n ω hC hA, withDensity_apply _ hA,
    Measure.restrict_restrict hA]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hGmeas.aemeasurable]

-- LEAN-ONLY affine change of variables `θ = θ₀ + h/√n` on a rescaled set: the Jacobian is the
-- constant `(√n)^{-k}` (`k = dim`).
private lemma lintegral_preimage_bvmLocalScale (θ₀ : EuclideanSpace ℝ (Fin k)) {n : ℕ}
    (hn1 : 1 ≤ n) {D : Set (EuclideanSpace ℝ (Fin k))} (hD : MeasurableSet D)
    {G : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ θ in bvmLocalScale θ₀ n ⁻¹' D, G θ
      = ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k)
          * ∫⁻ hh in D, G (bvmLocalUnscale θ₀ n hh) := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set a : ℝ := (Real.sqrt n)⁻¹ with hadef
  have hapos : 0 < a := by rw [hadef]; exact inv_pos.mpr (Real.sqrt_pos.mpr hnpos)
  set T : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := bvmLocalUnscale θ₀ n with hT
  have hTmeas : Measurable T := measurable_bvmLocalUnscale θ₀ n
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  have hmap : Measure.map T (volume : Measure (EuclideanSpace ℝ (Fin k)))
      = ENNReal.ofReal ((a ^ k)⁻¹) • (volume : Measure (EuclideanSpace ℝ (Fin k))) := by
    have h1 : Measure.map (fun hh : EuclideanSpace ℝ (Fin k) => a • hh) volume
        = ENNReal.ofReal |(a ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin k))))⁻¹|
            • (volume : Measure (EuclideanSpace ℝ (Fin k))) :=
      Measure.map_addHaar_smul volume hapos.ne'
    have h2 : T = (fun y : EuclideanSpace ℝ (Fin k) => θ₀ + y)
        ∘ (fun hh : EuclideanSpace ℝ (Fin k) => a • hh) := by
      funext hh; simp [hT, bvmLocalUnscale, hadef]
    rw [h2, ← Measure.map_map (measurable_const_add θ₀) (measurable_const_smul a), h1,
      Measure.map_smul, Measure.IsAddLeftInvariant.map_add_left_eq_self
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin k)))) θ₀]
    rw [hfr, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a ^ k)⁻¹)]
  have hpre : MeasurableSet (bvmLocalScale θ₀ n ⁻¹' D) := (measurable_bvmLocalScale θ₀ n) hD
  have hmem : ∀ hh, (T hh ∈ bvmLocalScale θ₀ n ⁻¹' D) ↔ hh ∈ D := by
    intro hh
    simp only [Set.mem_preimage, hT, bvmLocalScale_bvmLocalUnscale θ₀ hn1 hh]
  have hind : ∀ hh, (bvmLocalScale θ₀ n ⁻¹' D).indicator G (T hh)
      = D.indicator (fun y => G (T y)) hh := by
    intro hh
    by_cases hmem' : hh ∈ D
    · rw [Set.indicator_of_mem ((hmem hh).mpr hmem'), Set.indicator_of_mem hmem']
    · rw [Set.indicator_of_notMem (fun hc => hmem' ((hmem hh).mp hc)),
        Set.indicator_of_notMem hmem']
  have hkey := (lintegral_map (μ := (volume : Measure (EuclideanSpace ℝ (Fin k))))
      (f := (bvmLocalScale θ₀ n ⁻¹' D).indicator G) (g := T)
      (hG.indicator hpre) hTmeas).symm
  rw [hmap, lintegral_smul_measure, lintegral_indicator hpre] at hkey
  simp_rw [hind] at hkey
  rw [lintegral_indicator hD] at hkey
  rw [hkey, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (pow_pos hapos k)),
    mul_inv_cancel₀ (pow_pos hapos k).ne', ENNReal.ofReal_one, one_mul]

-- The `π`-integral of the product likelihood over the rescaled set is the Jacobian times
-- `bvmNumer`: on the rescaled set the prior is `f · volume`, and the affine substitution
-- `θ = θ₀ + h/√n` turns the integrand into `bvmJointDens`.
private lemma lintegral_preimage_eq_jac_mul_bvmNumer
    (hπ : HasLocalDensity π θ₀ r₀ f)
    (hM_joint : Measurable (Function.uncurry M.density)) {n : ℕ} (hn1 : 1 ≤ n)
    {D : Set (EuclideanSpace ℝ (Fin k))} (hD : MeasurableSet D)
    (hDsub : bvmLocalScale θ₀ n ⁻¹' D ⊆ Metric.ball θ₀ r₀) (ω : Fin n → 𝓧) :
    ∫⁻ θ in bvmLocalScale θ₀ n ⁻¹' D, (∏ i, ENNReal.ofReal (M.density θ (ω i))) ∂π
      = ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) * bvmNumer M f θ₀ n D ω := by
  classical
  have hsm : MeasurableSet (bvmLocalScale θ₀ n ⁻¹' D) := (measurable_bvmLocalScale θ₀ n) hD
  have hGmeas : Measurable fun θ : EuclideanSpace ℝ (Fin k) =>
      ∏ i, ENNReal.ofReal (M.density θ (ω i)) := by
    refine Finset.univ.measurable_prod fun i _ => ?_
    exact ENNReal.measurable_ofReal.comp (hM_joint.comp (measurable_id.prodMk measurable_const))
  have hFmeas : Measurable fun θ : EuclideanSpace ℝ (Fin k) => ENNReal.ofReal (f θ) :=
    ENNReal.measurable_ofReal.comp hπ.measurable
  have hres : π.restrict (bvmLocalScale θ₀ n ⁻¹' D)
      = (volume.restrict (bvmLocalScale θ₀ n ⁻¹' D)).withDensity
          fun θ => ENNReal.ofReal (f θ) := by
    rw [← Measure.restrict_restrict_of_subset hDsub, hπ.restrict_eq,
      restrict_withDensity hsm, Measure.restrict_restrict_of_subset hDsub]
  rw [hres, lintegral_withDensity_eq_lintegral_mul _ hFmeas hGmeas]
  simp only [Pi.mul_apply]
  rw [lintegral_preimage_bvmLocalScale θ₀ hn1 hD (hFmeas.mul hGmeas)]
  congr 1
  refine lintegral_congr fun hh => ?_
  simp only [bvmJointDens]
  ring

-- The scalar `q` (Jacobian) and the predictive normalizer `Z` cancel in the conditional ratio.
private lemma ennreal_posterior_ratio {q Z X Y : ℝ≥0∞} (hq : q ≠ 0) (hq' : q ≠ ∞)
    (hZ : Z ≠ 0) (hZ' : Z ≠ ∞) :
    ((q * X) / Z)⁻¹ * ((q * Y) / Z) = Y / X := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr hZ)) (Or.inr (ENNReal.inv_ne_zero.mpr hZ')),
    ENNReal.mul_inv (Or.inl hq) (Or.inl hq'), inv_inv,
    show q⁻¹ * X⁻¹ * Z * (q * Y * Z⁻¹) = q⁻¹ * q * (Z * Z⁻¹) * (Y * X⁻¹) from by ring,
    ENNReal.inv_mul_cancel hq hq', ENNReal.mul_inv_cancel hZ hZ', one_mul, one_mul]

/-- **The conditioned local posterior as a `bvmNumer` ratio** (predictive-a.e.): once the
rescaled ball `C/√n + θ₀` lies inside the prior's absolute-continuity ball
(`R < r₀ √n`), for predictive-a.e. `ω` with nonvanishing local mass,
`(localPosterior ω)[|C] A = bvmNumer (A∩C) / bvmNumer C`. -/
theorem cond_bvmLocalPosterior_apply_ae
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {R : ℝ}
    -- LEAN-ONLY: nontrivial localization radius
    (hR : 0 < R) {n : ℕ}
    -- LEAN-ONLY: the rescaled ball sits inside the absolute-continuity zone
    (hn : R < r₀ * Real.sqrt n)
    {C A : Set (EuclideanSpace ℝ (Fin k))}
    -- LEAN-ONLY: measurable sets, localization inside the radius-`R` ball (regularity)
    (hC : MeasurableSet C) (hCsub : C ⊆ Metric.closedBall 0 R) (hA : MeasurableSet A) :
    ∀ᵐ ω ∂(iidKernel κ n ∘ₘ π), bvmNumer M f θ₀ n C ω ≠ 0 →
      ((bvmLocalPosterior κ π θ₀ n ω)[|C]) A
        = bvmNumer M f θ₀ n (A ∩ C) ω / bvmNumer M f θ₀ n C ω := by
  classical
  have hr₀ : 0 < r₀ := hπ.rad_pos
  have hsqrt : 0 < Real.sqrt n := by
    rcases le_or_gt (Real.sqrt n) 0 with hle | hlt
    · exact absurd hn (by nlinarith)
    · exact hlt
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h1
    · subst h0; simp at hsqrt
    · exact h1
  -- The rescaled sets sit inside the prior's absolute-continuity ball.
  have hsub : ∀ D : Set (EuclideanSpace ℝ (Fin k)), D ⊆ Metric.closedBall 0 R →
      bvmLocalScale θ₀ n ⁻¹' D ⊆ Metric.ball θ₀ r₀ := by
    intro D hD θ hθ
    have h1 : bvmLocalScale θ₀ n θ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R :=
      hD hθ
    rw [Metric.mem_closedBall, dist_zero_right, bvmLocalScale, norm_smul, Real.norm_eq_abs,
      abs_of_pos hsqrt] at h1
    rw [Metric.mem_ball, dist_eq_norm]
    have h2 : Real.sqrt n * ‖θ - θ₀‖ < Real.sqrt n * r₀ :=
      lt_of_le_of_lt h1 (by rw [mul_comm]; exact hn)
    exact lt_of_mul_lt_mul_left h2 hsqrt.le
  -- The dominated iid experiment, in `withDensity` form.
  have hdens_meas : Measurable
      (Function.uncurry fun θ (x : 𝓧) => ENNReal.ofReal (M.density θ x)) :=
    ENNReal.measurable_ofReal.comp hM_joint
  have hP : Measurable (Function.uncurry
      fun (θ : EuclideanSpace ℝ (Fin k)) (x : Fin n → 𝓧) =>
        ∏ i, ENNReal.ofReal (M.density θ (x i))) :=
    measurable_uncurry_prod_likelihood hdens_meas
  have hκ' : ∀ θ, iidKernel κ n θ
      = (Measure.pi fun _ : Fin n => μ).withDensity
          fun x => ∏ i, ENNReal.ofReal (M.density θ (x i)) :=
    fun θ => iidKernel_withDensity hdens_meas hκ n θ
  have hpreC : MeasurableSet (bvmLocalScale θ₀ n ⁻¹' C) := (measurable_bvmLocalScale θ₀ n) hC
  have hpreCA : MeasurableSet (bvmLocalScale θ₀ n ⁻¹' (C ∩ A)) :=
    (measurable_bvmLocalScale θ₀ n) (hC.inter hA)
  filter_upwards [posterior_apply_eq_div (π := π) hP hκ' hpreC,
    posterior_apply_eq_div (π := π) hP hκ' hpreCA,
    posterior_apply_eq_div (π := π) hP hκ' (MeasurableSet.univ
      (α := EuclideanSpace ℝ (Fin k)))] with ω hωC hωCA hωU _
  -- The predictive normalizer is positive and finite, since the posterior is Markov.
  have hZ1 : (∫⁻ θ', (∏ i, ENNReal.ofReal (M.density θ' (ω i))) ∂π)
      / ∫⁻ θ', (∏ i, ENNReal.ofReal (M.density θ' (ω i))) ∂π = 1 := by
    have h := hωU
    simp only [Measure.restrict_univ, measure_univ] at h
    exact h.symm
  have hZne : (∫⁻ θ', (∏ i, ENNReal.ofReal (M.density θ' (ω i))) ∂π) ≠ 0 := by
    intro h0; rw [h0] at hZ1; simp at hZ1
  have hZtop : (∫⁻ θ', (∏ i, ENNReal.ofReal (M.density θ' (ω i))) ∂π) ≠ ∞ := by
    intro h0; rw [h0] at hZ1; simp at hZ1
  -- The Jacobian scalar.
  have hqpos : (0 : ℝ) < ((Real.sqrt n)⁻¹) ^ k := by positivity
  have hq : ENNReal.ofReal (((Real.sqrt n)⁻¹) ^ k) ≠ 0 := (ENNReal.ofReal_pos.mpr hqpos).ne'
  -- Push the conditioning through the rescaling map.
  have hmap : ∀ S : Set (EuclideanSpace ℝ (Fin k)), MeasurableSet S →
      bvmLocalPosterior κ π θ₀ n ω S
        = ((iidKernel κ n)†π) ω (bvmLocalScale θ₀ n ⁻¹' S) := by
    intro S hS
    rw [bvmLocalPosterior, Kernel.map_apply' _ (measurable_bvmLocalScale θ₀ n) _ hS]
  rw [ProbabilityTheory.cond_apply hC, hmap C hC, hmap (C ∩ A) (hC.inter hA), hωC, hωCA,
    lintegral_preimage_eq_jac_mul_bvmNumer hπ hM_joint hn1 hC (hsub C hCsub) ω,
    lintegral_preimage_eq_jac_mul_bvmNumer hπ hM_joint hn1 (hC.inter hA)
      (hsub (C ∩ A) (Set.inter_subset_left.trans hCsub)) ω,
    Set.inter_comm C A, ennreal_posterior_ratio hq ENNReal.ofReal_ne_top hZne hZtop]

/-- **The log pair ratio** of vdV p. 143: the logarithm of
`[p_{n,g} πₙ(g) / p_{n,h} πₙ(h)] · [dN(Δₙ,J⁻¹)(h) / dN(Δₙ,J⁻¹)(g)]`, i.e.
`(Lₙ(g) − Lₙ(h)) + (log f(θ₀+g/√n) − log f(θ₀+h/√n))
  − (⟪g − h, Δ̃ₙ⟫ − ⟪g,Jg⟫/2 + ⟪h,Jh⟫/2)`. -/
noncomputable def bvmLogRatio (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (J : Matrix (Fin k) (Fin k) ℝ) (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (g h : EuclideanSpace ℝ (Fin k)) (ω : Fin n → 𝓧) : ℝ :=
  (logLikelihood M θ₀ g n ω - logLikelihood M θ₀ h n ω)
    + (Real.log (f (bvmLocalUnscale θ₀ n g)) - Real.log (f (bvmLocalUnscale θ₀ n h)))
    - (⟪g - h, scoreSum sc n ω⟫
        - (1 / 2 : ℝ) * ⟪g, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) g))⟫
        + (1 / 2 : ℝ) * ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)

/-- **Fixed-pair vanishing of the log pair ratio** (vdV p. 143: "the integrand converges to
zero in probability … by Theorem 7.2 and the continuity of `π` at `θ₀`"): for every fixed
`g, h`, the log pair ratio tends to zero in `P^n_{θ₀}`-probability. Two applications of the
LAN residual (`lanResidual_tendsto_productMeasure`) plus the deterministic convergence of
the prior-density log ratio. -/
theorem bvmLogRatio_tendsto
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    (g h : EuclideanSpace ℝ (Fin k)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω | ε ≤ |bvmLogRatio M f θ₀ J sc n g h ω|}) atTop (𝓝 0) := by
  classical
  haveI hProb : ∀ n : ℕ, IsProbabilityMeasure (productMeasure M μ θ₀ n) := fun n =>
    AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
      M μ hPDF θ₀ n
  -- The LAN residual at an arbitrary fixed local parameter.
  set res : EuclideanSpace ℝ (Fin k) → ∀ n : ℕ, (Fin n → 𝓧) → ℝ := fun x n ω =>
    logLikelihood M θ₀ x n ω - (⟪x, scoreSum sc n ω⟫ - (1 / 2 : ℝ) *
      ⟪x, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) x))⟫) with hres_def
  have hres : ∀ x : EuclideanSpace ℝ (Fin k), ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |res x n ω|}) atTop (𝓝 0) := fun x =>
    AsymptoticStatistics.AsymptoticRepresentation.lanResidual_tendsto_productMeasure
      M μ θ₀ sc hsc (hPDF.density_integral_eq_one θ₀) (hPDF.density_integrable θ₀)
      (fun _ _ => hPDF.density_integral_eq_one _) (fun _ _ => hPDF.density_integrable _)
      hDQM J hJ x
  -- The prior log-ratio is deterministic and vanishes, by continuity and positivity at `θ₀`.
  have hunsc : ∀ x : EuclideanSpace ℝ (Fin k),
      Tendsto (fun n : ℕ => bvmLocalUnscale θ₀ n x) atTop (𝓝 θ₀) := by
    intro x
    have hsq : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hsm : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ • x) atTop (𝓝 ((0 : ℝ) • x)) :=
      hsq.smul_const x
    have := tendsto_const_nhds (x := θ₀) (f := (atTop : Filter ℕ)) |>.add hsm
    simpa [bvmLocalUnscale] using this
  have hlog : ∀ x : EuclideanSpace ℝ (Fin k),
      Tendsto (fun n : ℕ => Real.log (f (bvmLocalUnscale θ₀ n x))) atTop
        (𝓝 (Real.log (f θ₀))) := by
    intro x
    exact ((Real.continuousAt_log hπ.pos.ne').comp hπ.continuousAt).tendsto.comp (hunsc x)
  have hpterm : Tendsto (fun n : ℕ =>
      Real.log (f (bvmLocalUnscale θ₀ n g)) - Real.log (f (bvmLocalUnscale θ₀ n h)))
      atTop (𝓝 0) := by simpa using (hlog g).sub (hlog h)
  -- The algebraic decomposition: the two score/quadratic terms recombine exactly.
  have hdecomp : ∀ (n : ℕ) (ω : Fin n → 𝓧),
      bvmLogRatio M f θ₀ J sc n g h ω = res g n ω - res h n ω
        + (Real.log (f (bvmLocalUnscale θ₀ n g))
            - Real.log (f (bvmLocalUnscale θ₀ n h))) := by
    intro n ω
    have hsub : ⟪g - h, scoreSum sc n ω⟫
        = ⟪g, scoreSum sc n ω⟫ - ⟪h, scoreSum sc n ω⟫ := inner_sub_left (𝕜 := ℝ) _ _ _
    simp only [bvmLogRatio, hres_def, hsub]
    ring
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_
    (by simpa using (hres g (ε / 3) hε3).add (hres h (ε / 3) hε3))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hpterm (ε / 3) hε3
  filter_upwards [eventually_ge_atTop N] with n hn
  have hincl : {ω : Fin n → 𝓧 | ε ≤ |bvmLogRatio M f θ₀ J sc n g h ω|}
      ⊆ {ω : Fin n → 𝓧 | ε / 3 ≤ |res g n ω|} ∪ {ω : Fin n → 𝓧 | ε / 3 ≤ |res h n ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hp : |Real.log (f (bvmLocalUnscale θ₀ n g))
        - Real.log (f (bvmLocalUnscale θ₀ n h))| < ε / 3 := by
      have := hN n hn
      rwa [Real.dist_eq, sub_zero] at this
    have hb1 : |bvmLogRatio M f θ₀ J sc n g h ω|
        ≤ |res g n ω - res h n ω| + |Real.log (f (bvmLocalUnscale θ₀ n g))
            - Real.log (f (bvmLocalUnscale θ₀ n h))| := by
      rw [hdecomp n ω]; exact abs_add_le _ _
    have hb2 : |res g n ω - res h n ω| ≤ |res g n ω| + |res h n ω| := by
      have := abs_add_le (res g n ω) (-(res h n ω))
      simpa [sub_eq_add_neg] using this
    linarith
  calc (productMeasure M μ θ₀ n).real {ω | ε ≤ |bvmLogRatio M f θ₀ J sc n g h ω|}
      ≤ (productMeasure M μ θ₀ n).real
          ({ω : Fin n → 𝓧 | ε / 3 ≤ |res g n ω|}
            ∪ {ω : Fin n → 𝓧 | ε / 3 ≤ |res h n ω|}) := measureReal_mono hincl
    _ ≤ (productMeasure M μ θ₀ n).real {ω : Fin n → 𝓧 | ε / 3 ≤ |res g n ω|}
          + (productMeasure M μ θ₀ n).real {ω : Fin n → 𝓧 | ε / 3 ≤ |res h n ω|} :=
        measureReal_union_le _ _

/-- **Step B: the conditioned Bernstein–von Mises convergence** (vdV pp. 142–143). For every
fixed radius `R > 0` and every `δ > 0`, the `P^n_{θ₀}`-probability that the conditioned
local posterior and the conditioned Gaussian differ by at least `δ` in total variation tends
to zero. -/
theorem local_tv_tendsto
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV Thm 10.1
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: dominated iid model, `κ θ = p_θ · μ`; vdV §10.2, p. 140
    (hκ : ∀ θ, κ θ = μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    -- LEAN-ONLY: joint measurability of the model densities (regularity)
    (hM_joint : Measurable (Function.uncurry M.density))
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f)
    {R : ℝ}
    -- LEAN-ONLY: nontrivial localization radius
    (hR : 0 < R) :
    ∀ δ : ℝ≥0∞, 0 < δ →
      Tendsto (fun n => productMeasure M μ θ₀ n
          {ω | δ ≤ Minimaxity.tvDist
            ((bvmLocalPosterior κ π θ₀ n ω)[|Metric.closedBall 0 R])
            ((bvmGaussian J sc n ω)[|Metric.closedBall 0 R])})
        atTop (𝓝 0) := by
  sorry

end StatLean.Bayesian
