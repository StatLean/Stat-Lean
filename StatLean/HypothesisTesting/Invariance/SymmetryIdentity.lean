import StatLean.HypothesisTesting.Tests.Defs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

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

**Verdict: the identity as transcribed is FALSE.** `not_integral_eq_of_sign_invariant`
refutes it with `N = 1`, `α = 0`, `φ = 1_{\{0\}}` and `Q = δ₀`, and the docstring there
gives a second counterexample with no zeros and no ties. The calibration hypothesis pins
the sign-average to `α` only off a set null for every *non-atomic* law, and a sign-change
invariant `Q` may sit on that set. Repairs: `Q ≪` Lebesgue, or `φ` a function of the signs
and of the ranks of the absolute values (the classical signed-rank setting the prose above
describes). Everything except "the sign-average is `α`" is proved.

**Main results.**
* `signFlip` — the coordinatewise sign-change transformation;
* `measurable_signFlip` — its measurability;
* `not_integral_eq_of_sign_invariant` — the counterexample refuting the identity;
* `integral_eq_of_sign_invariant` — the identity (false as stated; see above).

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
  distributions. It is isolated as the separate lemma `signAverage_ae_eq_const` so the gap
  remains visible — and it is exactly the step that fails: completeness over the non-atomic
  laws controls the sign-average only off a set those laws all miss, while `Q` is allowed to
  be atomic.

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

/-- **FALSE as stated.** For a symmetric critical function calibrated on continuous
symmetric distributions, the *average of `φ` over the `2^N` sign patterns* is claimed to
equal `α` off a `Q`-null set.

This is refuted by `not_integral_eq_of_sign_invariant` below. The completeness step it
appeals to does deliver something — the sign-average, being a function of the absolute
values only, is pinned to `α` off a set that every *non-atomic* law gives measure zero —
but `Q` is only assumed sign-change invariant, and a sign-change invariant law may sit
entirely on that exceptional set. Concretely, with `N = 1`, `α = 0`,
`φ = 1_{\{0\}}` and `Q = δ₀`: `φ` is a symmetric critical function, every continuous
symmetric i.i.d. sample gives it mean `0`, `δ₀` is invariant under both sign changes (since
`-0 = 0`), and yet the sign-average at `0` is `φ 0 = 1 ≠ 0 = α`. Excluding zeros and ties
does not repair the statement either: take `α = 1/2`, `φ = 1/2 + (1/2)·1_{\{t₀, -t₀\}}` and
`Q = ½ δ_{t₀} + ½ δ_{-t₀}` for any `t₀ > 0`.

What *is* true is the statement with `Q` absolutely continuous with respect to Lebesgue
measure (so that the exceptional set is `Q`-null), or the statement for `φ` a function of
the signs and the ranks of the absolute values rather than an arbitrary permutation-symmetric
critical function — the classical signed-rank setting the source has in mind. Neither
repair is carried out here; the lemma is left as the visible false hypothesis so that the
refutation and the headline stay in one place. -/
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
  -- FALSE: see the docstring and `not_integral_eq_of_sign_invariant`.
  sorry

/-- **Refutation of the sign-change identity as transcribed.** The identity below is *not*
a theorem for an arbitrary permutation-symmetric critical function and an arbitrary
sign-change-invariant law.

Counterexample: `N = 1`, `α = 0`, `φ = 1_{\{0\}}`, `Q = δ₀`. Then `φ` is a critical function,
it is (vacuously) symmetric in its single argument, every i.i.d. sample from a continuous
symmetric `D` gives it mean `D{0} = 0 = α`, and `δ₀` is invariant under both coordinatewise
sign changes because `-0 = 0`; but `∫ φ dQ = φ 0 = 1 ≠ 0 = α`.

The failure is not confined to the degenerate point `0`. Taking `α = 1/2`,
`φ = 1/2 + (1/2)·1_{\{t₀, -t₀\}}` and `Q = ½ δ_{t₀} + ½ δ_{-t₀}` with `t₀ > 0` gives a
counterexample with no zeros and no ties, so adding "`Q` charges no zeros and no ties" does
not repair it. What the calibration hypothesis really delivers is that the sign-average
equals `α` off a set null for every *non-atomic* law; a sign-change-invariant `Q` may live
on that set. -/
theorem not_integral_eq_of_sign_invariant :
    ¬ ∀ (N : ℕ) (α : ℝ) (φ : (Fin N → ℝ) → ℝ), IsCriticalFn φ →
        (∀ (σ : Equiv.Perm (Fin N)) (z : Fin N → ℝ), φ (z ∘ σ) = φ z) →
        (∀ D : Measure ℝ, IsProbabilityMeasure D → (∀ t : ℝ, D {t} = 0) →
          D.map (fun t => -t) = D →
          ∫ z, φ z ∂(Measure.pi fun _ : Fin N => D) = α) →
        ∀ Q : Measure (Fin N → ℝ), IsProbabilityMeasure Q →
          (∀ ε : Fin N → Bool, Q.map (signFlip ε) = Q) →
          ∫ z, φ z ∂Q = α := by
  intro h
  classical
  have hSmeas : MeasurableSet ({0} : Set (Fin 1 → ℝ)) := measurableSet_singleton _
  have hmeas : Measurable (Set.indicator ({0} : Set (Fin 1 → ℝ)) (1 : (Fin 1 → ℝ) → ℝ)) :=
    measurable_const.indicator hSmeas
  have hcrit : IsCriticalFn (Set.indicator ({0} : Set (Fin 1 → ℝ)) (1 : (Fin 1 → ℝ) → ℝ)) := by
    refine ⟨hmeas, fun z => ?_⟩
    by_cases hz : z ∈ ({0} : Set (Fin 1 → ℝ))
    · rw [Set.indicator_of_mem hz]; norm_num
    · rw [Set.indicator_of_notMem hz]; norm_num
  have hsym : ∀ (σ : Equiv.Perm (Fin 1)) (z : Fin 1 → ℝ),
      Set.indicator ({0} : Set (Fin 1 → ℝ)) (1 : (Fin 1 → ℝ) → ℝ) (z ∘ σ)
        = Set.indicator ({0} : Set (Fin 1 → ℝ)) (1 : (Fin 1 → ℝ) → ℝ) z := by
    intro σ z
    have hz : z ∘ σ = z := funext fun i => congrArg z (Subsingleton.elim _ _)
    rw [hz]
  have hsingleton : ({0} : Set (Fin 1 → ℝ)) = Set.univ.pi fun _ => ({0} : Set ℝ) := by
    ext z; simp [funext_iff]
  have hnull : ∀ D : Measure ℝ, IsProbabilityMeasure D → (∀ t : ℝ, D {t} = 0) →
      D.map (fun t => -t) = D →
      ∫ z, Set.indicator ({0} : Set (Fin 1 → ℝ)) (1 : (Fin 1 → ℝ) → ℝ) z
        ∂(Measure.pi fun _ : Fin 1 => D) = 0 := by
    intro D hD hatom _
    haveI := hD
    have hzero : (Measure.pi fun _ : Fin 1 => D) {(0 : Fin 1 → ℝ)} = 0 := by
      rw [hsingleton, Measure.pi_pi]
      simp [hatom]
    rw [integral_indicator_one hSmeas]
    simp [measureReal_def, hzero]
  have hQinv : ∀ ε : Fin 1 → Bool,
      (Measure.dirac (0 : Fin 1 → ℝ)).map (signFlip ε) = Measure.dirac 0 := by
    intro ε
    rw [Measure.map_dirac' (measurable_signFlip ε)]
    congr 1
    funext i
    by_cases hε : ε i <;> simp [signFlip, hε]
  have hcontra := h 1 0 _ hcrit hsym hnull (Measure.dirac 0) inferInstance hQinv
  rw [integral_dirac' _ _ hmeas.stronglyMeasurable,
    Set.indicator_of_mem (Set.mem_singleton _)] at hcontra
  norm_num at hcontra

/-- **A symmetric test calibrated on continuous symmetric distributions keeps its level
under any sign-change-invariant law.**

**FALSE as stated** — see `not_integral_eq_of_sign_invariant` just above for an explicit
counterexample (`N = 1`, `α = 0`, `φ = 1_{\{0\}}`, `Q = δ₀`), and a second one with no zeros
and no ties. The statement is retained in the shape the source's Lemma 6.10.1 is transcribed
in, and is derived below from the (consequently also false) sign-average lemma
`signAverage_ae_eq_const`, so that the exact point of failure stays visible: everything
except "the sign-average is `α`" is proved here. Repairs: assume `Q` absolutely continuous
with respect to Lebesgue measure, or restrict `φ` to functions of the signs and of the ranks
of the absolute values (the classical signed-rank setting).

If a symmetric critical function has mean `α` under every i.i.d. sample from a continuous
distribution symmetric about the origin, then it has mean `α` under every joint law
invariant under the `2^N` coordinatewise sign changes — in particular without assuming the
coordinates independent or identically distributed. -/
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
