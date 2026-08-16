import StatLean.StatisticalModels.FactorModels.Defs
import StatLean.StatisticalModels.MixedEffects.Marginal

/-!
# The factor model **is** a linear mixed model — the anti-duplication bridge

The one theorem this whole area is organized around:

* **`factorLaw_eq_lmmLaw`** — `factorLaw P F E = lmmLaw (factorDesign P) P.μ F E`, i.e. the
  linear factor model `x = μ + Λ y + e` is literally the linear mixed model with
  fixed-effects design `X = 1`, fixed effect `β = μ`, and random-effects design `Z = Λ`;
* `meanVec_factorLaw` and `covMatrix_factorLaw` — the first two moments, obtained by
  transporting `MixedEffects.meanVec_lmmLaw` and `MixedEffects.covMatrix_lmmLaw` across the
  bridge. **The covariance decomposition is not re-derived here**: `covMatrix_lmmLaw` already
  says `Cov = Z · Cov(latent) · Zᵀ + Cov(noise)` for an arbitrary latent law, which at
  `Z = Λ` *is* `Σ = Λ Φ Λᵀ + Ψ`.

Specializing these to the declared parameters `(Φ, Ψ)` — i.e. `Σ = factorCovariance P` — is
`FactorModels.Moments`.

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, §3.2, Eq. (3.3) (`BKM`); N. M. Laird and
J. H. Ware, "Random-effects models for longitudinal data," *Biometrics* **38** (1982),
963–974, Eq. (1.1)–(1.2) (`LW82`).

**Proof formalization notes.** The bridge is a `Measure.bind`-versus-`Measure.prod`-image
identity: `(measurementKernel P E ∘ₘ F) s = ∫⁻ y, E {z ∣ Λ y + μ + z ∈ s} ∂F`, which is
`Measure.prod_apply` applied to `lmmLaw`'s definition after `add_comm`/`add_assoc` on
`μ + Λ y + z`. Both moment corollaries then need only `toEuclideanLin (1 : Matrix) x = x`.
*Book vs Lean:* `BKM` Eq. (3.12) is the orthogonal case `Φ = I` of `covMatrix_factorLaw`;
the general `Φ` is our generalization, inherited free from the mixed model.

**Bibliographic comments.** That factor analysis, random-effects models and variance
components are the same linear latent-variable calculus is folklore going back to
C. R. Henderson (1950); `BKM` ch. 1 makes the "unified approach" its organizing theme.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

variable {p q : ℕ}

/-- LEAN-ONLY: the identity matrix acts as the identity on Euclidean space. (The same
one-line `simp` fact exists in `MixedEffects.Marginal`, but it is `private` there and hence
unreachable; this is the only thing in the area that is restated rather than imported.) -/
theorem toEuclideanLin_one_apply {a : ℕ} (x : EuclideanSpace ℝ (Fin a)) :
    Matrix.toEuclideanLin (𝕜 := ℝ) (1 : Matrix (Fin a) (Fin a) ℝ) x = x := by
  simp

/-- **The anti-duplication hinge**: the linear factor model is the linear mixed model with
`X = 1`, `β = μ`, `Z = Λ` (`BKM` Eq. (3.3) = `LW82` Eq. (1.1)). Everything the repo proves
about `lmmLaw` transports along this identity; nothing about `Λ Φ Λᵀ + Ψ` is ever
re-derived. -/
theorem factorLaw_eq_lmmLaw (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p)))
    -- LEAN-ONLY: s-finiteness of both free laws; without it `Measure.bind` and
    -- `Measure.prod` are junk on both sides and the identity carries no content
    [SFinite F] [SFinite E] :
    factorLaw P F E = MixedEffects.lmmLaw (factorDesign P) P.μ F E := by
  sorry

/-- **First moment** (`BKM` Eq. (3.3); `LW82` Eq. (1.2)): with centered latent and specific
factors the observed mean is `μ`. Transported from `MixedEffects.meanVec_lmmLaw`. -/
theorem meanVec_factorLaw (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure F]
    [IsProbabilityMeasure E]
    -- USER-INPUT: centered latent factors and specific factors; BKM Eq. (3.2)–(3.3)
    (hF : meanVec F = 0) (hE : meanVec E = 0)
    -- USER-INPUT: first moments exist; BKM Eq. (3.3)
    (hF1 : Integrable id F) (hE1 : Integrable id E) :
    meanVec (factorLaw P F E) = P.μ := by
  sorry

/-- **Second moment, latent form** (`LW82` Eq. (1.2) at `Z = Λ`): the observed covariance is
`Λ · Cov(y) · Λᵀ + Cov(e)`, for **arbitrary** latent and error laws. This is
`MixedEffects.covMatrix_lmmLaw` transported across the bridge — the covariance decomposition
of `BKM` Eq. (3.12) is a corollary of it, never a separate derivation. -/
theorem covMatrix_factorLaw (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure F]
    [IsProbabilityMeasure E]
    -- USER-INPUT: second moments of the latent and specific factors; BKM Eq. (3.2)–(3.3)
    (hF2 : MemLp id 2 F) (hE2 : MemLp id 2 E) :
    covMatrix (factorLaw P F E)
      = P.loading * covMatrix F * P.loadingᵀ + covMatrix E := by
  sorry

end StatLean.StatisticalModels.FactorModels
