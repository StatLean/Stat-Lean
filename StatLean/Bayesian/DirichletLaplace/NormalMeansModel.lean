import StatLean.Bayesian.DirichletLaplace.Defs
import StatLean.Bayesian.ForMathlib.GaussianShift
import StatLean.Bayesian.Dominated.PosteriorLintegral
import StatLean.Bayesian.Dominated.PredictiveDensity

/-!
# The normal-means model: the posterior ↔ likelihood-ratio bridge

This is the single point at which the abstract Mathlib posterior `κ†Π` of the Dirichlet–Laplace
normal-means experiment is exchanged for the explicit, pointwise likelihood-ratio functions
`dlNumer / dlDenom` on which the entire Section 3/6 analysis is carried out. Everything downstream
(`TestingBound`, `CompressEngine`, the two headline theorems) reads the posterior mass only through
`lintegral_posterior_eq_lintegral_ratio`; the a.e.-hygiene of Bayes' theorem is discharged here,
once.

Setup. The likelihood kernel is `K = gaussShiftKernel ι`, `K θ = N(θ, I)` (BPPD model (1)). Choosing
the **base measure `ν := K θ₀ = N(θ₀, I)`** (a probability measure) and the Gaussian likelihood
ratio `p θ y = dlLR θ₀ θ y = dN(θ,I)/dN(θ₀,I)(y)`, the model is dominated:
`K θ = (K θ₀).withDensity (dlLR θ₀ θ)` (Girsanov, `gaussShiftKernel_eq_withDensity`). Then
`predictiveDensity p Π = dlDenom θ₀ Π` and `∫_C p(·,y) dΠ = dlNumer θ₀ Π C y`, so the dominated
Bayes formula `posterior_apply_eq_div` (Robert §1.4) reads `(K†Π) y C = dlNumer/dlDenom` for
predictive-a.e. `y`. Because the theorems integrate against the **truth** `P₀ = K θ₀` rather than the
predictive `K ∘ₘ Π`, we transfer this a.e. identity along `P₀ ≪ K ∘ₘ Π` (`comp_absolutelyContinuous`;
both are equivalent to Lebesgue since Gaussian densities are strictly positive).

Contents:
* `gaussShiftKernel_eq_withDensity` — the Girsanov density identity (the dominated-model hypothesis).
* `lintegral_dlLR_eq_one` — the likelihood ratio integrates to `1` against the base `K θ₀`.
* `dlLR_fubini`, `lintegral_dlNumer_eq_prior` — change-of-measure Tonelli: `E_{θ₀}[dlNumer C] = Π C`.
* `comp_absolutelyContinuous` — `K θ' ≪ K ∘ₘ Π` (truth dominated by the predictive).
* `dlDenom_pos_ae`, `dlDenom_lt_top_ae` — `0 < dlDenom < ∞` holds `P₀`-a.e. (forced, not assumed).
* `dlRatio_le_one_ae` — the posterior ratio is `≤ 1`.
* `lintegral_posterior_eq_lintegral_ratio` — **the bridge**; invokes `posterior_apply_eq_div`
  exactly once and transfers along `comp_absolutelyContinuous`.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, J. Amer. Statist. Assoc. 110 (2015), 1479–1490 (arXiv:1401.5398). Model (1), §6
(the posterior ratio `Π(·|y) = ∫ e^{ℓ} dΠ / ∫ e^{ℓ} dΠ`). The dominated Bayes formula consumed here
is Robert, *The Bayesian Choice* (2nd ed., Springer, 2007), §1.4, eq. (1.2.3).

**Proof formalization notes.** `gaussShiftKernel_eq_withDensity` is `stdGaussianShift_withDensity`
(F5) transported through `gaussShiftKernel_apply`. `dlDenom_pos_ae` / `dlDenom_lt_top_ae` are the
`Dominated.PredictiveDensity` facts `predictiveDensity_pos_ae` / `predictiveDensity_lt_top_ae_comp`
(which are *derived* from finiteness, not hypotheses) pulled back to `P₀` via
`comp_absolutelyContinuous`. `lintegral_posterior_eq_lintegral_ratio` is the only consumer of
`posterior_apply_eq_div`: it filter-upgrades that predictive-a.e. equality to a `P₀`-a.e. equality
using `AbsolutelyContinuous.ae_le`, then closes with `lintegral_congr_ae`. The standard-Borel /
nonempty instances required by `†` and by `posterior_apply_eq_div` resolve automatically for
`EuclideanSpace ℝ ι` (`standardBorel_of_polish` from its Borel + Polish structure); `IsFiniteKernel`
and `IsFiniteMeasure` come from `IsMarkovKernel (gaussShiftKernel ι)` and `IsProbabilityMeasure π`.

**Bibliographic comments.** The absolute-continuity transfer `P₀ ≪ predictive` is what makes the
Ghosal–Ghosh–van der Vaart (*Ann. Statist.* 28 (2000), 500–531) posterior-contraction program
run under the sampling measure rather than under the (analytically convenient) prior predictive;
the equivalence of shifted Gaussians is the finite-dimensional shadow of the Cameron–Martin /
Girsanov theorem (R. H. Cameron and W. T. Martin, *Ann. of Math.* 45 (1944), 386–396).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Girsanov density identity** (the dominated-model hypothesis for `posterior_apply_eq_div`):
`N(θ, I) = N(θ₀, I).withDensity (dN(θ,I)/dN(θ₀,I))`, i.e.
`gaussShiftKernel ι θ = (gaussShiftKernel ι θ₀).withDensity (dlLR θ₀ θ)`. -/
theorem gaussShiftKernel_eq_withDensity (θ₀ θ : EuclideanSpace ℝ ι) :
    gaussShiftKernel ι θ = (gaussShiftKernel ι θ₀).withDensity (fun y => dlLR θ₀ θ y) := by
  sorry

/-- The Gaussian likelihood ratio integrates to `1` against the base measure `K θ₀`
(it is a probability density: `∫ dN(θ,I)/dN(θ₀,I) dN(θ₀,I) = N(θ,I)(univ) = 1`). -/
theorem lintegral_dlLR_eq_one (θ₀ θ : EuclideanSpace ℝ ι) :
    ∫⁻ y, dlLR θ₀ θ y ∂(gaussShiftKernel ι θ₀) = 1 := by
  sorry

/-- **Change-of-measure Tonelli**: swapping the order of integration in
`E_{θ₀}[dlNumer C] = ∫ (∫_C dlLR dΠ) dP₀` yields `∫_C (∫ dlLR dP₀) dΠ`. -/
theorem dlLR_fubini (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι)) [SFinite π]
    {C : Set (EuclideanSpace ℝ ι)}
    -- LEAN-ONLY: target parameter set measurable (regularity)
    (hC : MeasurableSet C) :
    ∫⁻ y, dlNumer θ₀ π C y ∂(gaussShiftKernel ι θ₀)
      = ∫⁻ θ in C, (∫⁻ y, dlLR θ₀ θ y ∂(gaussShiftKernel ι θ₀)) ∂π := by
  sorry

/-- **Numerator expectation = prior mass** (BPPD §6): combining `dlLR_fubini` with
`lintegral_dlLR_eq_one`, the truth-expectation of the un-normalized posterior numerator over `C`
equals the prior mass of `C`. -/
theorem lintegral_dlNumer_eq_prior (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι))
    [SFinite π] {C : Set (EuclideanSpace ℝ ι)}
    -- LEAN-ONLY: target parameter set measurable (regularity)
    (hC : MeasurableSet C) :
    ∫⁻ y, dlNumer θ₀ π C y ∂(gaussShiftKernel ι θ₀) = π C := by
  sorry

/-- **Truth dominated by the predictive**: `N(θ', I) ≪ (K ∘ₘ Π)`. Both are equivalent to Lebesgue
measure (Gaussian densities are strictly positive and the predictive density
`m(y) = ∫ φ(y−θ) dΠ(θ) > 0` for a probability prior), so this holds for every `θ'`. -/
theorem comp_absolutelyContinuous (θ' : EuclideanSpace ℝ ι)
    (π : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure π] :
    gaussShiftKernel ι θ' ≪ (gaussShiftKernel ι) ∘ₘ π := by
  sorry

/-- The posterior denominator is `P₀`-a.e. strictly positive (forced by finiteness of the
predictive, transferred along `P₀ ≪ K ∘ₘ Π`; not a hypothesis). -/
theorem dlDenom_pos_ae (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure π] :
    ∀ᵐ y ∂(gaussShiftKernel ι θ₀), 0 < dlDenom θ₀ π y := by
  sorry

/-- The posterior denominator is `P₀`-a.e. finite (forced by finiteness of the predictive,
transferred along `P₀ ≪ K ∘ₘ Π`; not a hypothesis). -/
theorem dlDenom_lt_top_ae (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure π] :
    ∀ᵐ y ∂(gaussShiftKernel ι θ₀), dlDenom θ₀ π y < ∞ := by
  sorry

/-- The posterior ratio is `≤ 1` (indeed pointwise, since `dlNumer ≤ dlDenom`). -/
theorem dlRatio_le_one_ae (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι))
    (C : Set (EuclideanSpace ℝ ι)) :
    ∀ᵐ y ∂(gaussShiftKernel ι θ₀), dlNumer θ₀ π C y / dlDenom θ₀ π y ≤ 1 := by
  sorry

/-- **The posterior ↔ ratio bridge.** For a measurable parameter set `C`, the truth-averaged
posterior mass of `C` equals the truth-average of the explicit likelihood-ratio function
`dlNumer θ₀ Π C / dlDenom θ₀ Π`. This is the *sole* invocation of the dominated Bayes formula
`posterior_apply_eq_div` in the milestone; the predictive-a.e. identity it provides is transferred
to a `P₀`-a.e. identity via `comp_absolutelyContinuous`. -/
theorem lintegral_posterior_eq_lintegral_ratio (θ₀ : EuclideanSpace ℝ ι)
    (π : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure π]
    {C : Set (EuclideanSpace ℝ ι)}
    -- LEAN-ONLY: target parameter set measurable (regularity)
    (hC : MeasurableSet C) :
    ∫⁻ y, ((gaussShiftKernel ι)†π) y C ∂(gaussShiftKernel ι θ₀)
      = ∫⁻ y, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀) := by
  sorry

end StatLean.Bayesian
