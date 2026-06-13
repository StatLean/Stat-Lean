import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
import Mathlib.Probability.IdentDistrib

/-!
# Random functions in a Donsker class (Lemma 19.24)

If `F` is a `P`-Donsker class of measurable functions and `f̂_n` is a
sequence of random functions taking values in `F` such that
`∫ (f̂_n − f₀)² dP →_P 0` for some `f₀ ∈ L²(P)`, then `G_n(f̂_n − f₀) →_P 0`
and hence `G_n f̂_n ⇝ G_P f₀`.

vdV §19.4 Lemma 19.24. vdV's proof uses the continuous-mapping theorem on
`ℓ^∞(F) × F → ℝ` together with Lemma 18.15 (almost all sample paths of the
limiting Gaussian process are continuous on `(F, ‖·‖_{P,2})`); the proof here
routes directly through the random-pair-in-probability form of
`IsAsymptoticallyEquicontinuous`, with no `ℓ^∞(F)`-topology infrastructure.

Headline declaration: `donsker_random_function_consistency`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ENNReal
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 19.24 (Random functions in a Donsker class)**.

Suppose `F` is a `P`-Donsker class of measurable functions and `f_hat n`
is a sequence of jointly measurable random functions taking values in
`F` such that `∫ (f_hat n − f₀)² dP →_P 0` for some `f₀ ∈ F` with
`f₀ ∈ L²(P)`. Then for every `η > 0`,
`μ{ξ | η < |G_n(f_hat n ξ) − G_n(f₀)|} → 0`,
i.e. `G_n(f_hat n) − G_n(f₀) →_P 0`.

vdV §19.4 Lemma 19.24.

Hypotheses:
* `h_donsker` — vdV §19.4 Theorem 19.24: `F` is `P`-Donsker.
* `_hf₀_in_F` — vdV §19.4: WLOG `f₀ ∈ F`.
* `_hf₀` — vdV §19.4: `f₀ ∈ L²(P)`.
* `h_range` — vdV §19.4: random functions take values in `F`.
* `h_l2_consistent` — vdV §19.4: the `→_P 0` of the L²(P)-distance
  hypothesis, expressed in expectation form (which is equivalent given
  the L² envelope of `F` and is more compact in Lean than the iterated
  `→_P` form).
* `hf₀_meas`, `h_fhat_meas` — joint measurability adapters required to
  apply equicontinuity at the random pair `(f_hat n, const f₀)`.
* `hX_*` — iid hypotheses on the sample (empirical-process setup).

**Proof.** The `IsAsymptoticallyEquicontinuous` predicate
(`Donsker.lean`) is in consumer form: it says that for any iid sample
and any pair of measurable random functions in `F` whose L²(P)-distance
squared has expectation tending to 0, the empirical process applied to
the difference tends to 0 in `μ`-probability. We apply this directly to
the pair `(f_hat n, fun _ => f₀)`. -/
theorem donsker_random_function_consistency
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_donsker : IsPDonsker F P)
    (f₀ : Ω → ℝ) (_hf₀ : MemLp f₀ 2 P)
    (_hf₀_in_F : f₀ ∈ F)
    (hf₀_meas : Measurable f₀)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (f_hat : ℕ → Ξ → (Ω → ℝ))
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (f_hat n)))
    (h_range : ∀ n ω, f_hat n ω ∈ F)
    -- Expectation of squared L²-distance. The
    -- `IsAsymptoticallyEquicontinuous` predicate consumes this; we pass it
    -- through unchanged with `ghat = const f₀`.
    (h_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (f_hat n ξ x - f₀ x) ^ 2 ∂P) μ)
    (h_l2_consistent :
      Tendsto (fun n =>
        ∫ ω, (∫ x, (f_hat n ω x - f₀ x) ^ 2 ∂P) ∂μ) atTop (𝓝 0)) :
    ∀ η : ℝ, 0 < η → Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
                  empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|}) atTop (𝓝 0) := by
  intro η hη
  -- Apply the equicontinuity predicate to the pair (f_hat, const f₀).
  -- The constant random function `(n, ξ) ↦ f₀` has uncurry `(ξ, x) ↦ f₀ x = f₀ ∘ Prod.snd`,
  -- jointly measurable iff `f₀` is.
  set ghat : ℕ → Ξ → (Ω → ℝ) := fun (_ : ℕ) (_ : Ξ) => f₀
  have hghat_meas : ∀ n : ℕ, Measurable (Function.uncurry (ghat n)) := by
    intro _
    exact hf₀_meas.comp measurable_snd
  have hghat_range : ∀ (n : ℕ) (ξ : Ξ), ghat n ξ ∈ F := fun _ _ => _hf₀_in_F
  exact h_donsker.asymptoticallyEquicontinuous μ X hX_meas hX_iindep hX_idem hX_law
    f_hat ghat h_fhat_meas hghat_meas h_range hghat_range
    h_l2_int h_l2_consistent η hη

end AsymptoticStatistics.EmpiricalProcess
