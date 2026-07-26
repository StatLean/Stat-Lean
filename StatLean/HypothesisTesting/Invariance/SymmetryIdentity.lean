import StatLean.HypothesisTesting.Tests.Defs
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The sign-change identity for symmetric tests of symmetry

Tests of the hypothesis that a distribution is symmetric about the origin are usually
built from the ranks of the absolute observations together with the signs. Such tests are
calibrated under the assumption that the observations are an i.i.d. sample from a
continuous distribution symmetric about the origin. That assumption is often the doubtful
part of the model — the observations may be gathered under different experimental
conditions and need be neither identically distributed nor even independent.

The identity below shows that for tests **symmetric in their arguments** the calibration
survives this loss of assumptions entirely. If a symmetric critical function has mean `α`
under every i.i.d. sample from a continuous distribution symmetric about the origin, then
it has mean `α` under *any* joint distribution invariant under the `2^N` coordinatewise
sign changes — no independence, no common distribution. In the paired-comparison design
this invariance is guaranteed by construction, since the treatment is assigned at random
within each pair; so the stated significance level is exactly right regardless of how the
pairs differ from one another.

The mechanism is that the null-calibration forces the *average over the `2^N` sign
patterns* of the test to equal `α` pointwise, and sign-change invariance of the joint law
makes the conditional distribution of the signs given the absolute values uniform over
those `2^N` patterns — so the pointwise average is exactly the conditional expectation.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.10
(The Hypothesis of Symmetry), Lemma 6.10.1 (the sign-change identity for testing symmetry).
(`TSH4 §6.10 Lem 6.10.1`.)

**Main results.**
* `signFlip` — the coordinatewise sign-change transformation;
* `measurable_signFlip` — its measurability;
* `integral_eq_of_sign_invariant` — the identity.

**Proof formalization notes.**
* The `2^N` sign changes are indexed by `Fin N → Bool` and applied through `signFlip`.
  They are *not* packaged as a group action: the statement quantifies over the family of
  transformations directly, which is all the argument uses and avoids importing a group
  structure on the index type.
* Symmetry in the arguments is stated as invariance under precomposition with an arbitrary
  permutation of the coordinates.
* The null class is transcribed literally: i.i.d. samples (`Measure.pi` of a common `D`)
  from a distribution that is **continuous** (no atoms, `D {t} = 0`) and **symmetric about
  the origin** (`D` invariant under negation).
* The step from "mean `α` under every such i.i.d. sample" to the pointwise sign-average
  identity is a completeness-style argument over the class of continuous symmetric
  distributions. Per the campaign plan this sub-lemma may be lifted into a **named
  deferral** rather than proved inline; if so it should be stated as a separate top-level
  lemma so the gap remains visible.

**Bibliographic comments.** Randomization within matched pairs as the source of exact
significance levels for sign and signed-rank procedures goes back to R. A. Fisher (*The
Design of Experiments*, Oliver & Boyd, 1935). The observation that a symmetric rank test
retains its level under any sign-change-invariant joint law — dispensing with both
independence and identical distribution — belongs to the non-parametric program of
E. L. Lehmann and C. Stein ("On the theory of some non-parametric hypotheses," *Ann. Math.
Statist.* **20** (1949), 28–45), and was developed further in E. L. Lehmann's work of the
1950s. The one-sample signed-rank statistic itself is due to F. Wilcoxon ("Individual
comparisons by ranking methods," *Biometrics Bull.* **1** (1945), 80–83).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

/-- **Coordinatewise sign change**: flip the sign of the coordinates selected by `ε`. The
`2^N` maps obtained as `ε` ranges over `Fin N → Bool` are the sign-change transformations
of the sample space. -/
def signFlip {N : ℕ} (ε : Fin N → Bool) (z : Fin N → ℝ) : Fin N → ℝ :=
  fun i => if ε i then -(z i) else z i

/-- Sign changes are measurable. -/
theorem measurable_signFlip {N : ℕ} (ε : Fin N → Bool) :
    Measurable (signFlip ε) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : ε i = true
  · have : (fun z : Fin N → ℝ => signFlip ε z i) = fun z => -(z i) := by
      funext z; simp only [signFlip, if_pos h]
    rw [this]; exact (measurable_pi_apply i).neg
  · have : (fun z : Fin N → ℝ => signFlip ε z i) = fun z => z i := by
      funext z; simp only [signFlip, if_neg h]
    rw [this]; exact measurable_pi_apply i

/-- **Named deferral (completeness step).** For a symmetric critical function calibrated on
continuous symmetric distributions, the *average of `φ` over the `2^N` sign patterns* equals
`α` off a `Q`-null set. This is the completeness-style content flagged in the module note:
under an i.i.d. continuous symmetric `D` the conditional law of the signs given the absolute
values is uniform over the `2^N` patterns (continuity kills ties, symmetry makes each pattern
equally likely), so `hnull` forces the sign-average — a function of the absolute values — to
be `α` for the rich class of such `D`, and completeness of that class collapses it to `α`.

It is isolated as a separate lemma so the gap stays visible; the headline
`integral_eq_of_sign_invariant` is proved from it by an exact change-of-variables average
(no further gap). Not proved here: the completeness argument itself is not available from
Mathlib v4.29.1 (it needs the conditional-uniformity-of-signs disintegration and completeness
of the family of continuous symmetric product measures). -/
private theorem signAverage_ae_eq_const {N : ℕ} {α : ℝ} {φ : (Fin N → ℝ) → ℝ}
    (hφ : IsCriticalFn φ)
    (hsym : ∀ (σ : Equiv.Perm (Fin N)) (z : Fin N → ℝ), φ (z ∘ σ) = φ z)
    (hnull : ∀ D : Measure ℝ, IsProbabilityMeasure D → (∀ t : ℝ, D {t} = 0) →
      D.map (fun t => -t) = D →
      ∫ z, φ z ∂(Measure.pi fun _ : Fin N => D) = α)
    {Q : Measure (Fin N → ℝ)} [IsProbabilityMeasure Q]
    (hQ : ∀ ε : Fin N → Bool, Q.map (signFlip ε) = Q) :
    (fun z => (Fintype.card (Fin N → Bool) : ℝ)⁻¹ *
        ∑ ε : Fin N → Bool, φ (signFlip ε z)) =ᵐ[Q] (fun _ => α) := by
  -- TODO: completeness of the continuous-symmetric family + conditional-uniformity of signs.
  sorry

/-- **A symmetric test calibrated on continuous symmetric distributions keeps its level
under any sign-change-invariant law.** If a symmetric critical function has mean `α` under
every i.i.d. sample from a continuous distribution symmetric about the origin, then it has
mean `α` under every joint law invariant under the `2^N` coordinatewise sign changes — in
particular without assuming the coordinates independent or identically distributed. -/
theorem integral_eq_of_sign_invariant {N : ℕ} {α : ℝ} {φ : (Fin N → ℝ) → ℝ}
    -- USER-INPUT: `φ` is a critical function
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: `φ` is symmetric in its `N` arguments
    (hsym : ∀ (σ : Equiv.Perm (Fin N)) (z : Fin N → ℝ), φ (z ∘ σ) = φ z)
    -- USER-INPUT: `φ` has mean `α` under every i.i.d. sample from a continuous
    -- distribution symmetric about the origin
    (hnull : ∀ D : Measure ℝ, IsProbabilityMeasure D → (∀ t : ℝ, D {t} = 0) →
      D.map (fun t => -t) = D →
      ∫ z, φ z ∂(Measure.pi fun _ : Fin N => D) = α)
    {Q : Measure (Fin N → ℝ)} [IsProbabilityMeasure Q]
    -- USER-INPUT: the joint law is unchanged by all `2^N` coordinatewise sign changes
    (hQ : ∀ ε : Fin N → Bool, Q.map (signFlip ε) = Q) :
    ∫ z, φ z ∂Q = α := by
  have hφmeas : Measurable φ := hφ.1
  -- `φ` and each of its sign-translates are bounded by `1`, hence `Q`-integrable.
  have hbound : ∀ (f : (Fin N → ℝ) → ℝ), Measurable f → (∀ z, f z ∈ Set.Icc (0 : ℝ) 1) →
      Integrable f Q := by
    intro f hfm hfb
    refine (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable (ae_of_all _ ?_)
    intro z; rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hfb z).1], (hfb z).2⟩
  have hInt : Integrable φ Q := hbound φ hφmeas hφ.2
  have hIntg : ∀ ε : Fin N → Bool, Integrable (fun z => φ (signFlip ε z)) Q := fun ε =>
    hbound _ (hφmeas.comp (measurable_signFlip ε)) (fun z => hφ.2 _)
  -- each sign change is `Q`-measure preserving, so it leaves the integral of `φ` unchanged.
  have hEach : ∀ ε : Fin N → Bool, ∫ z, φ (signFlip ε z) ∂Q = ∫ z, φ z ∂Q := by
    intro ε
    have h : ∫ y, φ y ∂(Q.map (signFlip ε)) = ∫ z, φ (signFlip ε z) ∂Q :=
      integral_map (measurable_signFlip ε).aemeasurable hφmeas.aestronglyMeasurable
    rw [hQ ε] at h; exact h.symm
  -- the average over the `2^N` patterns has the same `Q`-integral as `φ` itself.
  set M : ℝ := (Fintype.card (Fin N → Bool) : ℝ) with hMdef
  have hMne : M ≠ 0 := by
    rw [hMdef]; exact_mod_cast Fintype.card_ne_zero
  have hAvg : ∫ z, M⁻¹ * ∑ ε : Fin N → Bool, φ (signFlip ε z) ∂Q = ∫ z, φ z ∂Q := by
    rw [integral_const_mul, integral_finset_sum Finset.univ (fun ε _ => hIntg ε)]
    rw [Finset.sum_congr rfl (fun ε _ => hEach ε), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hMdef, ← mul_assoc, inv_mul_cancel₀ hMne, one_mul]
  -- the deferred completeness step makes that average `α` off a `Q`-null set.
  have hConst : ∫ z, M⁻¹ * ∑ ε : Fin N → Bool, φ (signFlip ε z) ∂Q = α := by
    rw [hMdef, integral_congr_ae (signAverage_ae_eq_const hφ hsym hnull hQ)]
    simp
  rw [← hAvg, hConst]

end StatLean.HypothesisTesting
