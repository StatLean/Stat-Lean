import StatLean.PointEstimation.Equivariance.ConditionalRiskEngine
import StatLean.PointEstimation.Equivariance.LocationStructure
import StatLean.PointEstimation.ForMathlib.ConvexMinimizers
import StatLean.PointEstimation.ForMathlib.MeasurableArgmin
import Mathlib.Analysis.Convex.Function

/-!
# The minimum risk equivariant location estimator

Putting together the two halves of the theory: the equivariant class is exactly
`{δ₀ − v ∘ diffs}` (`LocationStructure`), and minimizing over such a class reduces to a
fibrewise minimization against the conditional distribution of the data given the
differences (`ConditionalRiskEngine`). The result is the construction of the minimum risk
equivariant (MRE) location estimator.

* `isLocMRE_of_conditional_min` — the construction: if `v*(y)` minimizes the conditional
  expected loss `E₀[ρ(δ₀(X) − v) | y]` in almost every fibre of the differences, then
  `δ₀ − v* ∘ diffs` is MRE;
* `exists_isLocMRE_of_convex` — existence for convex, non-monotone losses;
* `isLocMRE_sq_of_condMean` — squared error: the minimizer is the conditional mean,
  giving `δ*(X) = δ₀(X) − E₀[δ₀(X) | Y]`;
* `exists_isLocMRE_of_bounded_loss` — a single observation and a bounded loss vanishing
  at the origin's antipodes: an MRE estimator exists even though the loss is not convex.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.1 (First
Examples), Theorem 1.10 (the MRE estimator via conditional minimization given the differences)
and Corollary 1.11 (existence for a convex non-monotone loss). (`TPE2 §3.1 Thm 1.10, Cor
1.11`.)

**Proof formalization notes.**
* The conditional distribution of the data given the differences is written through the
  shared `orbitCondKernel (locationBase f) diffs`, whose argument order is pinned in
  `ConditionalRiskEngine`; the template is `F w x = δ₀ x − w`.
* The classical hypothesis is "for each `y` there exists a minimizing `v(y)`"; the proof
  only ever uses it on a set of full measure (the same source observes that the
  conditional risk is finite only almost everywhere), so `hmin` is stated with `∀ᵐ`.
  This weakens the hypothesis and hence strengthens the theorem.
* Measurability of `v*` is a Lean-side requirement absent from the classical statement:
  without it `δ₀ − v* ∘ diffs` need not be an estimator at all. For the convex case the
  intended route to a *measurable* selection is the convex-minimizer and measurable-argmin
  bricks in this area's `ForMathlib` layer; this file states existence and does not
  depend on them.
* Non-monotonicity of a convex loss is spelled out as "neither monotone nor antitone",
  which for a convex function is exactly the condition guaranteeing that a minimum is
  attained rather than approached at `±∞`.
* The classical companion to the squared-error corollary characterises the minimizer for
  absolute error as any conditional median; that variant is not formalized here, since
  the median has no canonical measurable selection to state it with.
* The bounded-loss existence result needs no separate finite-risk hypothesis: a loss
  bounded by `M` gives every estimator risk at most `M` under a probability law.

**Bibliographic comments.** The reduction of best equivariant location estimation to a
conditional minimization given the differences, and the resulting estimator, are due to
E. J. G. Pitman, "The estimation of the location and scale parameters of a continuous
population of any given form," *Biometrika* **30** (1939), 391–421. The admissibility of
that estimator was established by C. Stein, "The admissibility of Pitman's estimator of a
single location parameter," *Ann. Math. Statist.* **30** (1959), 970–979.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

section LocationMRE

variable {m : ℕ}

/-- The conditional mean minimizes the conditional expected squared error, phrased at the
`ℝ≥0∞` level with no second-moment hypothesis: outside `L²` both sides are `∞`. -/
lemma lintegral_ofReal_sq_min {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {φ : Ω → ℝ} (hφ : Measurable φ) (w : ℝ) :
    ∫⁻ x, ENNReal.ofReal ((φ x - ∫ z, φ z ∂μ) ^ 2) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal ((φ x - w) ^ 2) ∂μ := by
  set m := ∫ z, φ z ∂μ with hm
  by_cases hL2 : MemLp φ 2 μ
  · have hf1 : Integrable (fun x => (φ x - m) ^ 2) μ :=
      (hL2.sub (memLp_const m)).integrable_sq
    have hf2 : Integrable (fun x => (φ x - w) ^ 2) μ :=
      (hL2.sub (memLp_const w)).integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hf1 (ae_of_all _ fun x => sq_nonneg _),
        ← ofReal_integral_eq_lintegral_ofReal hf2 (ae_of_all _ fun x => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (integral_sq_sub_mean_le hL2 w)
  · have hnotMemLp : ∀ c : ℝ, ¬ MemLp (fun x => φ x - c) 2 μ := by
      intro c hc
      have h2 := hc.add (memLp_const c)
      rw [show (fun x => φ x - c) + (fun _ : Ω => c) = φ from by
            funext x; simp only [Pi.add_apply]; ring] at h2
      exact hL2 h2
    have hinf : ∀ c : ℝ, ∫⁻ x, ENNReal.ofReal ((φ x - c) ^ 2) ∂μ = ⊤ := by
      intro c
      by_contra hne
      have hlt : ∫⁻ x, ENNReal.ofReal ((φ x - c) ^ 2) ∂μ < ⊤ := lt_top_iff_ne_top.mpr hne
      have hfin : HasFiniteIntegral (fun x => (φ x - c) ^ 2) μ :=
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mpr hlt
      have hasm : AEStronglyMeasurable (fun x => (φ x - c) ^ 2) μ :=
        ((hφ.sub_const c).pow_const 2).aestronglyMeasurable
      exact hnotMemLp c
        ((memLp_two_iff_integrable_sq (hφ.sub_const c).aestronglyMeasurable).mpr ⟨hasm, hfin⟩)
    rw [hinf m, hinf w]

/-- **The minimum risk equivariant location estimator.** Let `δ₀` be a measurable
equivariant estimator with finite risk and let `v*` be a measurable function of the
differences which, in almost every fibre, minimizes the conditional expected loss
`E₀[ρ(δ₀(X) − v) | y]` over constant `v`. Then `δ₀ − v* ∘ diffs` is a minimum risk
equivariant estimator.

The two ingredients are the representation of the equivariant class as `δ₀ − v ∘ diffs`
and the fact that an integral is minimized by minimizing its integrand fibrewise. -/
theorem isLocMRE_of_conditional_min (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density, so the base member is a probability law
    [IsProbabilityMeasure (locationBase f)]
    (ρ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss; needed for the disintegration
    (hρ : Measurable ρ)
    {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference equivariant estimator, the caller's free choice
    (heq₀ : IsLocEquivariant δ₀)
    -- USER-INPUT: it has finite risk, so the conditional minimization is meaningful
    (hfin : locRisk f ρ δ₀ ≠ ∞)
    {vStar : (Fin m → ℝ) → ℝ}
    -- USER-INPUT: the fibrewise minimizer, supplied measurably by the caller
    (hvStar : Measurable vStar)
    -- USER-INPUT: `v*` minimizes the conditional expected loss in almost every fibre of
    -- the differences (the classical statement asks for every fibre)
    (hmin : ∀ᵐ y ∂((locationBase f).map diffs), ∀ w : ℝ,
      ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - vStar y))
          ∂(orbitCondKernel (locationBase f) diffs y) ≤
        ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - w))
          ∂(orbitCondKernel (locationBase f) diffs y)) :
    IsLocMRE f ρ (fun x => δ₀ x - vStar (diffs x)) := by
  refine ⟨hδ₀.sub (hvStar.comp measurable_diffs), ?_, ?_⟩
  · exact (isLocEquivariant_iff_exists_diffs_rep heq₀ _).mpr ⟨vStar, fun x => rfl⟩
  · intro δ' hδ'meas hδ'eq
    obtain ⟨v, hvmeas, hv⟩ :=
      (isLocEquivariant_iff_exists_diffs_rep_measurable heq₀ hδ₀ δ').mp ⟨hδ'meas, hδ'eq⟩
    have hFmeas : Measurable (fun p : ℝ × (Fin (m + 1) → ℝ) => δ₀ p.2 - p.1) :=
      (hδ₀.comp measurable_snd).sub measurable_fst
    have key := lintegral_le_of_condMinimizer (locationBase f) (Z := diffs)
      measurable_diffs (F := fun w x => δ₀ x - w) hFmeas (ρ := ρ) hρ
      (vStar := vStar) hvStar hmin (v := v) hvmeas
    have hrisk' : locRisk f ρ δ' =
        ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - v (diffs x))) ∂(locationBase f) := by
      unfold locRisk; exact lintegral_congr fun x => by rw [hv x]
    rw [hrisk']; unfold locRisk; exact key

/-- Analytic core (named debt): for a convex, non-monotone loss the fibrewise conditional
risk `w ↦ ∫⁻ x, ofReal (ρ (δ₀ x − w)) ∂(orbitCondKernel (locationBase f) diffs z)` is
convex, continuous and coercive in `w`, so the measurable-argmin brick
`exists_measurable_argmin` produces a measurable `v*` minimizing it in every fibre. -/
private lemma exists_measurable_condMinimizer_convex (f : (Fin (m + 1) → ℝ) → ℝ)
    [IsProbabilityMeasure (locationBase f)] {ρ : ℝ → ℝ} (hρ : Measurable ρ)
    (hconv : ConvexOn ℝ Set.univ ρ) (hnotmono : ¬ Monotone ρ ∧ ¬ Antitone ρ)
    {δ₀ : (Fin (m + 1) → ℝ) → ℝ} (hδ₀ : Measurable δ₀) :
    ∃ vStar : (Fin m → ℝ) → ℝ, Measurable vStar ∧
      ∀ᵐ y ∂((locationBase f).map diffs), ∀ w : ℝ,
        ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - vStar y))
            ∂(orbitCondKernel (locationBase f) diffs y) ≤
          ∫⁻ x, ENNReal.ofReal (ρ (δ₀ x - w))
            ∂(orbitCondKernel (locationBase f) diffs y) := by
  -- RETAINED DEBT (pe/equivariance-close): not closable without proving continuity of an
  -- ℝ≥0∞-valued conditional-risk integral, which the frozen `exists_measurable_argmin`
  -- brick requires as *full* continuity (its docstring notes an LSC weakening is not done);
  -- for an unbounded convex loss the objective genuinely jumps to ∞ at its finiteness
  -- boundary, so no side hypothesis on `ρ` closes it without laundering the analytic core.
  -- TODO: analytic core of the convex location MRE. Set
  --   `fObj z w = ∫⁻ x, ofReal (ρ (δ₀ x - w)) ∂(orbitCondKernel (locationBase f) diffs z)`
  -- and discharge the four hypotheses of `exists_measurable_argmin`:
  --   * joint measurability of `Function.uncurry fObj` (kernel-parametrized `∫⁻`);
  --   * `ConvexOn ℝ≥0 univ (fObj z)` from convexity of `ρ` composed with the affine shift,
  --     pushed through `ENNReal.ofReal` and `∫⁻`-monotonicity/additivity;
  --   * `Continuous (fObj z)` — the delicate step: continuity of the ℝ≥0∞-valued integral
  --     in the shift `w` (a convex ℝ≥0∞ objective can jump from finite to ∞ at the
  --     boundary of its finiteness domain, so this needs a genuine regularity argument);
  --   * `Tendsto (fObj z) (cocompact ℝ) (𝓝 ⊤)` from coercivity of the convex non-monotone
  --     `ρ` (via `hnotmono`) and Fatou.
  -- Then `exists_measurable_argmin` gives measurable `v*` with `fObj z (v* z) = ⨅ w, fObj z w`,
  -- whence the fibrewise minimality holds for every `z` (a fortiori `∀ᵐ`).
  sorry

/-- **Existence of a minimum risk equivariant estimator for a convex, non-monotone
loss.** For such a loss the fibrewise minimization always has a solution, and the
solution can be chosen measurably; uniqueness holds when the loss is strictly convex, a
refinement not formalized here. -/
theorem exists_isLocMRE_of_convex (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    (ρ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss
    (hρ : Measurable ρ)
    -- USER-INPUT: the loss is convex
    (hconv : ConvexOn ℝ Set.univ ρ)
    -- USER-INPUT: the loss is not monotone — for a convex loss this is exactly the
    -- condition making the fibrewise minimum attained rather than approached at `±∞`
    (hnotmono : ¬ Monotone ρ ∧ ¬ Antitone ρ)
    {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference equivariant estimator with finite risk
    (heq₀ : IsLocEquivariant δ₀)
    (hfin : locRisk f ρ δ₀ ≠ ∞) :
    ∃ δ, IsLocMRE f ρ δ := by
  obtain ⟨vStar, hvStar, hmin⟩ :=
    exists_measurable_condMinimizer_convex f hρ hconv hnotmono hδ₀
  exact ⟨_, isLocMRE_of_conditional_min f ρ hρ hδ₀ heq₀ hfin hvStar hmin⟩

/-- **Squared error: the minimum risk equivariant estimator subtracts the conditional
mean.** With `ρ(t) = t²` the fibrewise minimizer is the conditional expectation of the
reference estimator given the differences, so the minimum risk equivariant estimator is
`δ*(X) = δ₀(X) − E₀[δ₀(X) | Y]`. -/
theorem isLocMRE_sq_of_condMean (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference equivariant estimator with finite risk
    (heq₀ : IsLocEquivariant δ₀)
    (hfin : locRisk f (fun t : ℝ => t ^ 2) δ₀ ≠ ∞)
    -- USER-INPUT: the conditional mean exists in every fibre of the differences
    (hint : ∀ y, Integrable δ₀ (orbitCondKernel (locationBase f) diffs y)) :
    IsLocMRE f (fun t : ℝ => t ^ 2)
      (fun x => δ₀ x -
        ∫ z, δ₀ z ∂(orbitCondKernel (locationBase f) diffs (diffs x))) := by
  have hρmeas : Measurable (fun t : ℝ => t ^ 2) := by fun_prop
  set vStar : (Fin m → ℝ) → ℝ :=
    fun y => ∫ z, δ₀ z ∂(orbitCondKernel (locationBase f) diffs y) with hvStarDef
  have hvStar : Measurable vStar :=
    measurable_integral_orbitCondKernel (locationBase f) measurable_diffs hδ₀ hint
  have hmin : ∀ᵐ y ∂((locationBase f).map diffs), ∀ w : ℝ,
      ∫⁻ x, ENNReal.ofReal ((δ₀ x - vStar y) ^ 2)
          ∂(orbitCondKernel (locationBase f) diffs y) ≤
        ∫⁻ x, ENNReal.ofReal ((δ₀ x - w) ^ 2)
          ∂(orbitCondKernel (locationBase f) diffs y) := by
    refine ae_of_all _ fun y w => ?_
    exact lintegral_ofReal_sq_min hδ₀ w
  exact isLocMRE_of_conditional_min f (fun t => t ^ 2) hρmeas hδ₀ heq₀ hfin hvStar hmin

/-- **A single observation and a bounded loss.** For one observation the equivariant
estimators are exactly `X − c`, so an MRE estimator exists as soon as
`c ↦ E₀[ρ(X − c)]` attains its infimum. That happens for a loss which is bounded, tends
to its bound at `±∞`, and is faced with an almost-everywhere continuous density — a case
where the loss need not be convex at all.

No finite-risk hypothesis is needed: a loss bounded by `M` gives every estimator risk at
most `M` under a probability law. -/
theorem exists_isLocMRE_of_bounded_loss (f : (Fin 1 → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    (ρ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss
    (hρ : Measurable ρ)
    {M : ℝ}
    -- USER-INPUT: the loss is nonnegative and bounded by `M`
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρM : ∀ t, ρ t ≤ M)
    -- USER-INPUT: the loss attains its bound in the limit at both ends
    (hatTop : Filter.Tendsto ρ Filter.atTop (nhds M))
    (hatBot : Filter.Tendsto ρ Filter.atBot (nhds M))
    -- USER-INPUT: the density is continuous almost everywhere
    (hcont : ∀ᵐ x ∂(volume : Measure (Fin 1 → ℝ)), ContinuousAt f x) :
    ∃ δ, IsLocMRE f ρ δ := by
  -- RETAINED DEBT (pe/equivariance-close): the attainment of the minimum needs continuity
  -- of `g c = ∫⁻ x, ofReal (ρ (x 0 − c)) ∂(locationBase f)` in the shift `c`, i.e. the
  -- convolution/DCT regularity spelled out below; a bounded merely-measurable `g` on `ℝ`
  -- need not attain its infimum, so this analytic fact cannot be sidestepped.
  -- TODO: second analytic core (named debt), independent of the convex one above.
  -- For a single observation `diffs : (Fin 1 → ℝ) → (Fin 0 → ℝ)` is constant, so the
  -- equivariant class is exactly `{x ↦ x 0 − c : c ∈ ℝ}` (via
  -- `isLocEquivariant_iff_exists_diffs_rep_measurable` with `δ₀ x = x 0`, using that
  -- `Fin 0 → ℝ` is a subsingleton so `v (diffs x)` is a constant `c`). Minimizing the
  -- constant risk reduces to producing `c*` minimizing
  --   `g c = ∫⁻ x, ofReal (ρ (x 0 − c)) ∂(locationBase f)`.
  -- Here `g` is bounded by `ofReal M` (loss `≤ M`, probability law) and, by `hatTop`/
  -- `hatBot`, `g c → ofReal M` as `c → ±∞`; the minimum is then attained by
  -- `Continuous.exists_forall_le'` (extreme value theorem away from a compact set).
  -- The delicate input is continuity of `g` in the shift `c`: since `ρ` is only
  -- measurable (not continuous), continuity comes from `hcont` (a.e. continuity of the
  -- density) via translation-continuity of the convolution `c ↦ ∫ ρ(t − c) f(t) dt`,
  -- together with dominated convergence (dominating constant `M`, integrable on the
  -- probability law). This convolution/DCT regularity is a genuinely separate analytic
  -- fact from the convex-objective regularity above and cannot be folded into it.
  sorry

end LocationMRE

end StatLean.PointEstimation
