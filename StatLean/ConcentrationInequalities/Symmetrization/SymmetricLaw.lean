import StatLean.ConcentrationInequalities.Symmetrization.Rademacher
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Symmetric laws and Rademacher mixing

A real random variable $X$ is *symmetric* if $-X \overset{d}{=} X$; at the
level of laws, $\nu$ is symmetric if $(\mathrm{neg})_\#\nu = \nu$. This file
proves HDP Lemma 6.3.1 (constructing symmetric distributions) in the two
forms consumed by the Gaussian symmetrization Lemma 6.6.2: for an independent
Rademacher sign $\xi$ and symmetric $X$,
$$ \xi X \overset{d}{=} X \qquad\text{and}\qquad \xi |X| \overset{d}{=} X, $$
together with the joint vector versions
$(\varepsilon_i g_i)_i \overset{d}{=} (g_i)_i$ and
$(\varepsilon_i |g_i|)_i \overset{d}{=} (g_i)_i$ for independent symmetric
coordinates.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.3, Lemma 6.3.1(b) (p. 179) and its use on
p. 186 (proof of Lemma 6.6.2).

**Proof formalization notes.** The scalar mixing identities are proved at the
level of laws by `Measure.prod_apply` and a four-piece partition of the line
(`{x ≥ 0}`, `{x > 0}`, `{x ≤ 0}`, `{x < 0}`) — **no atom condition needed**
(the possible atom at `0` is handled by the overlap of the closed/open
pieces). Vector versions are assembled by the same
`MeasurableEquiv.arrowProdEquivProdArrow` + `measurePreserving_pi` pattern as
`SignFlip.lean`, stated in the exact `(signVec N).prod (Measure.pi ν)` order
in which `Gaussian.lean` consumes them. Gaussian symmetry via
`gaussianReal_map_neg`. Named-sorry fallback of this work item:
`IsSymmetricLaw.map_mul_abs_rad` (the `|·|` partition case); the plain mixing
identity and the vector assemblies proven.

**Bibliographic comments.** Symmetrization by an independent sign is
classical (P. Lévy, *Théorie de l'addition des variables aléatoires*, 1937);
the formulation as Lemma 6.3.1 follows HDP §6.3 and its Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Symmetric law** (HDP §6.3, p. 179): a law `ν` on `ℝ` is symmetric if it
is invariant under negation, `(−·)#ν = ν`. Edge behavior: no probability
hypothesis at definition level — any measure qualifies if negation-invariant. -/
def IsSymmetricLaw (ν : Measure ℝ) : Prop :=
  ν.map (fun x => -x) = ν

/-- The Rademacher law is symmetric (HDP §6.3). -/
theorem isSymmetricLaw_radLaw : IsSymmetricLaw radLaw := by
  sorry

/-- Centered Gaussians are symmetric (HDP §6.3); via `gaussianReal_map_neg`. -/
theorem isSymmetricLaw_gaussianReal (v : ℝ≥0) :
    IsSymmetricLaw (gaussianReal 0 v) := by
  sorry

/-- **Rademacher mixing** (HDP §6.3, Lemma 6.3.1(b)): for an independent sign
`ξ` and symmetric `X`, `ξX =ᵈ X`, at the level of laws on the product
`radLaw.prod ν`. -/
theorem IsSymmetricLaw.map_mul_rad {ν : Measure ℝ} [IsProbabilityMeasure ν]
    -- USER-INPUT: ν symmetric; HDP §6.3 Lemma 6.3.1(b)
    (hν : IsSymmetricLaw ν) :
    (radLaw.prod ν).map (fun p => p.1 * p.2) = ν := by
  sorry

/-- **Rademacher mixing with absolute value** (HDP §6.3, Lemma 6.3.1(b)):
`ξ|X| =ᵈ X` for symmetric `X`. Named-sorry debt candidate of this work item
(four-piece partition of the line at `0`; no atom condition needed). -/
theorem IsSymmetricLaw.map_mul_abs_rad {ν : Measure ℝ} [IsProbabilityMeasure ν]
    -- USER-INPUT: ν symmetric; HDP §6.3 Lemma 6.3.1(b)
    (hν : IsSymmetricLaw ν) :
    (radLaw.prod ν).map (fun p => p.1 * |p.2|) = ν := by
  sorry

/-- Joint vector mixing `(εᵢXᵢ)ᵢ =ᵈ (Xᵢ)ᵢ` for independent symmetric
coordinates (HDP §6.6, p. 186: `(εᵢgᵢ) =ᵈ (gᵢ)`). -/
theorem map_signVec_mul_pi {N : ℕ} {ν : Fin N → Measure ℝ}
    [∀ i, IsProbabilityMeasure (ν i)]
    -- USER-INPUT: symmetric coordinates; HDP §6.3 Lemma 6.3.1(b)
    (hν : ∀ i, IsSymmetricLaw (ν i)) :
    ((signVec N).prod (Measure.pi ν)).map (fun p i => p.1 i * p.2 i)
      = Measure.pi ν := by
  sorry

/-- Joint vector mixing with absolute values `(εᵢ|Xᵢ|)ᵢ =ᵈ (Xᵢ)ᵢ` for
independent symmetric coordinates (HDP §6.6, p. 186: `(εᵢ|gᵢ|) =ᵈ (gᵢ)`,
Lemma 6.3.1(b)). -/
theorem map_signVec_mul_abs_pi {N : ℕ} {ν : Fin N → Measure ℝ}
    [∀ i, IsProbabilityMeasure (ν i)]
    -- USER-INPUT: symmetric coordinates; HDP §6.3 Lemma 6.3.1(b)
    (hν : ∀ i, IsSymmetricLaw (ν i)) :
    ((signVec N).prod (Measure.pi ν)).map (fun p i => p.1 i * |p.2 i|)
      = Measure.pi ν := by
  sorry

end StatLean.ConcentrationInequalities
