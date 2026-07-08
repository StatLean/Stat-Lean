import StatLean.Bayesian.EmpiricalBayes.Defs

/-!
# The nonparametric maximum-likelihood mixing distribution (NPMLE)

The NPMLE maximizes the marginal likelihood `∏ᵢ f_G(xᵢ)` over *all* mixing distributions `G`. Two
structural facts: the marginal likelihood is **linear** in `G` (so the log-likelihood is concave
and the optimization is convex), and the maximizer can be taken to have **finite support on at
most `n+1` points** (Lindsay's geometry of mixture likelihoods).

**Reference.** Not in Robert (Robert §10.4.1 mentions nonparametric EB). B. G. Lindsay, "The
geometry of mixture likelihoods: a general theory," *Ann. Statist.* 11 (1983), 86–94; J. Kiefer and
J. Wolfowitz, "Consistency of the maximum likelihood estimator in the presence of infinitely many
incidental parameters," *Ann. Math. Statist.* 27 (1956), 887–906.

**Proof formalization notes.** `mixtureDensity_linear_in_mixing` is linearity of `∫ p dG` in the
measure `G` (`lintegral_add_measure`, `lintegral_smul_measure`). `NPMLE_exists_finiteSupport_le_
card_add_one` is Lindsay's Carathéodory/convex-geometry argument: the likelihood vector
`G ↦ (f_G(x₁), …, f_G(xₙ))` ranges over the convex hull of the `n`-dimensional likelihood curve, and
a boundary maximizer is a convex combination of at most `n+1` extreme points (Dirac masses).
Existence of a maximizer (a compactness step) is taken as input; the finite-support conclusion is
the geometric content. If the Carathéodory bound resists it is a recorded Batch-4 stretch.

**Bibliographic comments.** The finite-support NPMLE is Lindsay's theorem (1983), refining Kiefer
and Wolfowitz (1956); its consistency is the Kiefer–Wolfowitz theorem, and its use for normal-means
estimation (GMLEB) is W. Jiang and C.-H. Zhang (*Ann. Statist.* 37 (2009), 1647–1684). It is the
nonparametric backbone of modern empirical-Bayes deconvolution (Efron, *Large-Scale Inference*,
2010, §5).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- **The marginal likelihood is linear in the mixing distribution** (the convexity behind the
NPMLE): `f_{tG₀+(1−t)G₁} = t·f_{G₀} + (1−t)·f_{G₁}` (Lindsay 1983). -/
theorem mixtureDensity_linear_in_mixing (p : Θ → 𝓧 → ℝ≥0∞) (t : ℝ≥0∞) (G₀ G₁ : Measure Θ) (x : 𝓧) :
    mixtureDensity p (t • G₀ + (1 - t) • G₁) x
      = t * mixtureDensity p G₀ x + (1 - t) * mixtureDensity p G₁ x := by
  simp only [mixtureDensity, predictiveDensity, lintegral_add_measure, lintegral_smul_measure]

/-- **Lindsay's finite-support theorem** (3F.7, stretch): the NPMLE can be taken supported on at
most `n+1` points (Lindsay 1983). -/
theorem NPMLE_exists_finiteSupport_le_card_add_one {n : ℕ} [MeasurableSingletonClass Θ]
    (p : Θ → 𝓧 → ℝ≥0∞) (x : Fin n → 𝓧)
    -- USER-INPUT: existence of an NPMLE (a compactness step on the likelihood range); Lindsay 1983
    (hex : ∃ Ghat, IsNPMLE p x Ghat) :
    ∃ (Ghat : Measure Θ) (S : Finset Θ),
      IsNPMLE p x Ghat ∧ Ghat ((↑S : Set Θ)ᶜ) = 0 ∧ S.card ≤ n + 1 := by
  sorry

end StatLean.Bayesian
