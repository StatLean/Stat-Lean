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
  sorry

/-- The **unnormalized Gaussian density** of `N(Δ_{n,θ₀}, J⁻¹)` in local coordinates:
`exp(⟪h, Δ̃ₙ(ω)⟫ − ⟪h, Jh⟫/2)` with `Δ̃ₙ = scoreSum` (note `J Δ_{n,θ₀} = Δ̃ₙ`; the
Lebesgue normalizer and the factor `exp(−⟪Δₙ, JΔₙ⟫/2)` are dropped — they cancel in
ratios). -/
noncomputable def bvmGaussDens (J : Matrix (Fin k) (Fin k) ℝ)
    (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (h : EuclideanSpace ℝ (Fin k))
    (ω : Fin n → 𝓧) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (⟪h, scoreSum sc n ω⟫
    - (1 / 2 : ℝ) * ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))

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
  sorry

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
  sorry

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
  sorry

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
