import StatLean.StatisticalModels.FactorModels.Rotation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The observed-data likelihood of the normal factor model

The likelihood a factor analysis is actually fitted by. Because the latent factors are
integrated out, the observed-data likelihood is **not** a latent-data likelihood at all: it
is the ordinary multivariate normal likelihood evaluated at the structured covariance
`Σ = Λ Φ Λᵀ + Ψ`.

* `gaussianLogDensity m S x` — the multivariate normal log density
  `−(p/2)log 2π − ½ log det S − ½ (x−m)ᵀ S⁻¹ (x−m)`;
* `factorLogLik P x` — the factor model's observed-data log-likelihood contribution at `x`,
  *defined* as `gaussianLogDensity μ (factorCovariance P) x`, and tied to the actual law by
  `factorLaw_eq_withDensity_exp_factorLogLik` (the density theorem — the one genuinely new
  analytic statement in this file);
* `factorLogLikSample P x` — the log-likelihood of an i.i.d. sample `x : Fin n → ℝᵖ`;
* **`factorLogLik_rotateParams`** — the likelihood is invariant under every nonsingular
  reparameterization of the latent space; this is an immediate corollary of
  `Rotation.factorCovariance_rotateParams` and is the precise sense in which maximum
  likelihood cannot select a rotation (`BKM` §3.3, p. 50; §3.13.1).

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, Eq. (3.5) (the marginal law whose
density this is), Eq. (3.12) (`Σ = Λ Λ′ + Ψ`), §3.3, p. 50 (requiring `Λ′Ψ⁻¹Λ` diagonal
"removes the freedom to arbitrarily rotate `Λ`"), §3.12.1 (identifiability) (`BKM`);
D. N. Lawley, "The estimation of factor loadings by the method of maximum likelihood,"
*Proc. Roy. Soc. Edinburgh* **60** (1940), 64–82 (`Law40`).

**Proof formalization notes.** The rotation invariance is one rewrite by
`Rotation.factorCovariance_rotateParams` — the whole point of stating the likelihood as a
function of `(μ, Σ)`. The density theorem is the only real analytic content: the pin's
`multivariateGaussian` is defined through `stdGaussian` and its Lebesgue density is **not** in
Mathlib, so `factorLaw_eq_withDensity_exp_factorLogLik` is a named debt (route: the Gaussian
law is the affine image of `stdGaussian` under `S^{1/2}`, `Gaussian.multivariateGaussian_map_affine`
plus the change-of-variables formula `MeasureTheory.Measure.map_withDensity_eq_withDensity_...`
for a linear isomorphism, with `volume` on `EuclideanSpace ℝ (Fin p)` the standard
orthonormal-basis Haar measure). *Junk values:* `Matrix.det` of a singular `Σ` is `0` and
`Real.log 0 = 0`, and `Matrix.inv` is `0`, so `gaussianLogDensity` is finite nonsense at a
degenerate `Σ`; every statement about it as a likelihood carries `(factorCovariance P).PosDef`.
*Book vs Lean:* `BKM` writes the likelihood at `Φ = I`; the general-`Φ` form here specializes
to it.

**Bibliographic comments.** Maximum-likelihood factor analysis is Lawley (1940); the modern
EM treatment is D. B. Rubin and D. T. Thayer, "EM algorithms for ML factor analysis,"
*Psychometrika* **47** (1982), 69–76. Only the likelihood *function* and its exact invariance
are formalized here — no estimator, no EM, no asymptotics.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

variable {p q : ℕ}

/-- The **multivariate normal log density** at mean `m` and covariance `S`:
`−(p/2) log 2π − ½ log det S − ½ (x−m)ᵀ S⁻¹ (x−m)`.

*Edge behavior:* at a singular `S` this is finite nonsense (`Matrix.det S = 0` with
`Real.log 0 = 0`, and `S⁻¹ = 0`); it represents a density only under `S.PosDef`. Stated in
the `FactorModels` namespace because the Gaussian slice has no likelihood file yet;
promoting it to `StatisticalModels.Gaussian` is a laptop follow-up. -/
noncomputable def gaussianLogDensity (m : EuclideanSpace ℝ (Fin p))
    (S : Matrix (Fin p) (Fin p) ℝ) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  -(p / 2 : ℝ) * Real.log (2 * Real.pi) - (1 / 2 : ℝ) * Real.log S.det
    - (1 / 2 : ℝ) * (WithLp.ofLp (x - m) ⬝ᵥ S⁻¹ *ᵥ WithLp.ofLp (x - m))

/-- The **observed-data log-likelihood contribution** of the normal factor model at a single
observation `x` (`BKM` Eq. (3.5) with Eq. (3.12)): the multivariate normal log density at the
structured covariance `Σ = Λ Φ Λᵀ + Ψ`. The latent factors are already integrated out — this
is not a complete-data likelihood. -/
noncomputable def factorLogLik (P : FactorParams p q) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  gaussianLogDensity P.μ (factorCovariance P) x

theorem factorLogLik_eq_gaussianLogDensity (P : FactorParams p q)
    (x : EuclideanSpace ℝ (Fin p)) :
    factorLogLik P x = gaussianLogDensity P.μ (factorCovariance P) x := rfl

/-- The **log-likelihood of an i.i.d. sample** `x₁, …, x_n` (`BKM` §3.4). -/
noncomputable def factorLogLikSample {n : ℕ} (P : FactorParams p q)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i, factorLogLik P (x i)

/-- **The density theorem** — the observed law of the normal factor model has
`exp (factorLogLik P ·)` as its Lebesgue density, i.e. `factorLogLik` really is the
observed-data log-likelihood and not merely a formula named after one (`BKM` Eq. (3.5)).

Named debt: the pin has no Lebesgue density for `multivariateGaussian`. -/
theorem factorLaw_eq_withDensity_exp_factorLogLik (P : FactorParams p q)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hP : IsProperFactorParams P)
    -- USER-INPUT: nondegenerate observed covariance — a singular Σ has no Lebesgue
    -- density at all; BKM Eq. (3.5)
    (hSig : (factorCovariance P).PosDef) :
    factorLaw P (multivariateGaussian 0 P.factorCov) (multivariateGaussian 0 P.uniqueCov)
      = volume.withDensity fun x => ENNReal.ofReal (Real.exp (factorLogLik P x)) := by
  sorry

/-- The likelihood sees the parameters only through `(μ, Σ)` — definitional, and the reason
every invariance below is a one-line corollary. -/
theorem factorLogLik_congr (P P' : FactorParams p q)
    -- LEAN-ONLY: the two parameter tuples agree on the pair the density depends on;
    -- antecedent, no scope change
    (hμ : P.μ = P'.μ) (hSig : factorCovariance P = factorCovariance P')
    (x : EuclideanSpace ℝ (Fin p)) :
    factorLogLik P x = factorLogLik P' x := by
  rw [factorLogLik_eq_gaussianLogDensity, factorLogLik_eq_gaussianLogDensity, hμ, hSig]

/-- **HEADLINE — the likelihood is rotation invariant** (`BKM` §3.3, p. 50; §3.13.1): every
nonsingular reparameterization `Λ ↦ Λ A`, `Φ ↦ A⁻¹ Φ A⁻ᵀ` of the latent space leaves the
observed-data log-likelihood unchanged. Immediate from
`Rotation.factorCovariance_rotateParams`; this is why maximum likelihood determines `Λ` only
up to rotation and why an identifying restriction (`BKM`: `Λ′Ψ⁻¹Λ` diagonal) must be
imposed. -/
theorem factorLogLik_rotateParams (P : FactorParams p q) {A : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: the reparameterization is a change of basis of the latent space;
    -- BKM §2.11
    (hA : IsUnit A.det) (x : EuclideanSpace ℝ (Fin p)) :
    factorLogLik (rotateParams P A) x = factorLogLik P x :=
  factorLogLik_congr (rotateParams P A) P rfl (factorCovariance_rotateParams P hA) x

/-- The sample log-likelihood inherits rotation invariance. -/
theorem factorLogLikSample_rotateParams {n : ℕ} (P : FactorParams p q)
    {A : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: the reparameterization is a change of basis of the latent space;
    -- BKM §2.11
    (hA : IsUnit A.det) (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    factorLogLikSample (rotateParams P A) x = factorLogLikSample P x :=
  Finset.sum_congr rfl fun i _ => factorLogLik_rotateParams P hA (x i)

/-- **Orthogonal rotations leave the likelihood unchanged** — the statement `BKM` §3.13.1
makes for standardized factors. -/
theorem factorLogLik_rotateParams_orthogonal (P : FactorParams p q)
    {Q : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: `Q` is orthogonal; BKM §2.11, Eq. (2.24)
    (hQ : Q * Qᵀ = 1) (x : EuclideanSpace ℝ (Fin p)) :
    factorLogLik (rotateParams P Q) x = factorLogLik P x :=
  factorLogLik_congr (rotateParams P Q) P rfl
    (factorCovariance_rotateParams_orthogonal P hQ) x

end StatLean.StatisticalModels.FactorModels
