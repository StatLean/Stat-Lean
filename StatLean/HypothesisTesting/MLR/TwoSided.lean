import StatLean.HypothesisTesting.MLR.OneSided
import StatLean.HypothesisTesting.NeymanPearson.Generalized

/-!
# Two-sided hypotheses in a one-parameter exponential family

Uniformly most powerful tests survive one step beyond the one-sided problem: for
`H : θ ≤ θ₁ or θ ≥ θ₂` against `K : θ₁ < θ < θ₂` in a one-parameter exponential family
there is a UMP test, which rejects on a *bounded* interval of the natural statistic,
$$ \varphi(x) = 1 \ \text{ if } C_1 < T(x) < C_2, \qquad \gamma_i \ \text{ if } T(x) = C_i,
\qquad 0 \ \text{ otherwise}, $$
with the four constants pinned down by the two size conditions
`E_{θ₁}φ = E_{θ₂}φ = α`. Two constraints, hence the generalized fundamental lemma with
`m = 2` rather than the plain one.

Contents:
* `twoSidedTest T C₁ C₂ γ₁ γ₂` — the test displayed above;
* `isUMP_twoSided` — existence of the four constants and uniform optimality;
* `power_min_twoSided` — outside `[θ₁, θ₂]` the same test *minimizes* the rejection
  probability among all tests meeting the two size conditions;
* `power_lt_of_twoSided_right` — comparison of two such tests with a common size at `θ₁`:
  shifting the rejection interval to the right raises the power above `θ₁` and lowers it
  below;
* `twoSided_ae_unique` — the two size conditions determine the test almost everywhere.

**Proof formalization notes.**
* The rejection region is an interval of the natural statistic, so the test cannot be
  obtained from a single likelihood-ratio comparison; the two size conditions are handled
  by the two-constraint form of the generalized fundamental lemma, whose multipliers
  produce the two boundaries.
* The order of branches in `twoSidedTest` puts the two boundary cases first, so the
  definition is unambiguous even for degenerate constants: at `C₁ = C₂` the value is `γ₁`,
  and for `C₂ ≤ C₁` the test rejects nowhere except possibly at the two boundary points.
  The theorems all produce or assume `C₁ < C₂`.
* The comparison lemma requires the *strict* form of the monotone likelihood ratio
  together with strictly positive densities. Both are transcribed explicitly: the strict
  ratio condition is written division-free as `p_{θ'}(x)·p_θ(y) < p_θ(x)·p_{θ'}(y)` for
  `T x < T y`, matching the frozen non-strict `HasMLR`.
* "`φ*` lies to the right of `φ`" is transcribed as the lexicographic condition on the
  left boundary: either `C₁ < C₁'`, or the boundaries agree and the randomization weight
  there is smaller, `γ₁' < γ₁`.
* Uniqueness is stated as `μ`-a.e. equality. Since the densities are strictly positive,
  this coincides with almost-sure equality under every member of the family.
* The unimodality clause of the classical statement — for `0 < α < 1` the power function
  has an interior maximum and decreases strictly away from it, unless the statistic is
  supported on two points — is not stated here.

**Bibliographic comments.** Two-sided problems and the tests solving them appear in
J. Neyman and E. S. Pearson ("Contributions to the theory of testing statistical
hypotheses," *Stat. Res. Mem.* **1** (1936), 1–37); the two-constraint fundamental lemma
they rest on is due to G. B. Dantzig and A. Wald ("On the fundamental lemma of Neyman and
Pearson," *Ann. Math. Statist.* **22** (1951), 87–93), and the underlying monotonicity
properties of exponential families to S. Karlin and H. Rubin ("The theory of decision
procedures for distributions with monotone likelihood ratio," *Ann. Math. Statist.* **27**
(1956), 272–299).
-/

open MeasureTheory

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **two-sided test** based on the statistic `T`: reject when `C₁ < T < C₂`, reject
with probability `γᵢ` when `T = Cᵢ`, accept outside. The boundary branches are tested
first, so the definition is total and unambiguous: at `C₁ = C₂` the value is `γ₁`, and for
`C₂ ≤ C₁` the test rejects only (possibly) at the two boundary points. All theorems below
produce or assume `C₁ < C₂` and `γᵢ ∈ [0,1]`. -/
noncomputable def twoSidedTest (T : 𝓧 → ℝ) (C₁ C₂ γ₁ γ₂ : ℝ) : 𝓧 → ℝ := fun x =>
  if T x = C₁ then γ₁
  else if T x = C₂ then γ₂
  else if C₁ < T x ∧ T x < C₂ then 1
  else 0

/-- **UMP test of a two-sided hypothesis.** In a one-parameter exponential family, with the
parametrization strictly increasing, there are constants `C₁ < C₂` and boundary weights
`γ₁, γ₂ ∈ [0,1]` for which the two-sided test has size exactly `α` at both `θ₁` and `θ₂`
and is uniformly most powerful at level `α` for `H : θ ≤ θ₁ or θ₂ ≤ θ` against
`K : θ₁ < θ < θ₂`. -/
theorem isUMP_twoSided
    -- USER-INPUT: the exponential family, with σ-finite reference measure
    (E : ExpFamily 𝓧 ℝ) [SigmaFinite E.base]
    -- USER-INPUT: the model, a family of probability measures on a real parameter
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the parametrization, strictly increasing (the printed hypothesis on `Q`)
    {ηmap : ℝ → ℝ} (hη : StrictMono ηmap)
    -- USER-INPUT: the model is the canonical family read through `ηmap`
    (hrepr : IsCanonicalRepr P E ηmap)
    -- USER-INPUT: every parameter value lies in the natural parameter set, so no member
    -- degenerates to the junk zero measure
    (hnat : ∀ θ, ηmap θ ∈ E.natSet)
    -- USER-INPUT: the two null boundaries, in order
    {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    -- USER-INPUT: nondegenerate level
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) :
    ∃ C₁ C₂ γ₁ γ₂ : ℝ, C₁ < C₂ ∧ γ₁ ∈ Set.Icc (0 : ℝ) 1 ∧ γ₂ ∈ Set.Icc (0 : ℝ) 1 ∧
      power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₁ = α ∧
      power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₂ = α ∧
      IsUMP P {θ : ℝ | θ ≤ θ₁ ∨ θ₂ ≤ θ} (Set.Ioo θ₁ θ₂) α
        (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) := by
  sorry

/-- **Minimum rejection probability outside the interval.** Among all tests whose size is
exactly `α` at both `θ₁` and `θ₂`, the two-sided test minimizes the rejection probability
at every parameter value below `θ₁` or above `θ₂`. -/
theorem power_min_twoSided
    -- USER-INPUT: the exponential family, with σ-finite reference measure
    (E : ExpFamily 𝓧 ℝ) [SigmaFinite E.base]
    -- USER-INPUT: the model, and its canonical presentation through a strictly
    -- increasing parametrization
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {ηmap : ℝ → ℝ} (hη : StrictMono ηmap) (hrepr : IsCanonicalRepr P E ηmap)
    (hnat : ∀ θ, ηmap θ ∈ E.natSet)
    -- USER-INPUT: the two null boundaries and the level
    {θ₁ θ₂ α : ℝ} (hθ : θ₁ < θ₂)
    -- USER-INPUT: the constants of the test under study
    {C₁ C₂ γ₁ γ₂ : ℝ} (hC : C₁ < C₂)
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the test satisfies the two size conditions
    (hsize₁ : power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₁ = α)
    (hsize₂ : power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₂ = α) :
    ∀ ψ, IsCriticalFn ψ → power P ψ θ₁ = α → power P ψ θ₂ = α →
      ∀ θ : ℝ, θ < θ₁ ∨ θ₂ < θ →
        power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ ≤ power P ψ θ := by
  sorry

/-- **Comparison of two two-sided tests with a common size at `θ₁`.** If the rejection
interval of the second test lies to the right of that of the first — a larger left
boundary, or the same boundary with a smaller randomization weight there — then the second
test is strictly more powerful above `θ₁` and strictly less powerful below it. -/
theorem power_lt_of_twoSided_right
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic
    (T : 𝓧 → ℝ) (hT : Measurable T)
    -- USER-INPUT: densities strictly positive everywhere
    (hpos : ∀ θ x, 0 < p θ x)
    -- USER-INPUT: *strict* monotone likelihood ratio, division-free: the ratio
    -- `p_{θ'}/p_θ` is strictly increasing in `T` for `θ < θ'`
    (hstrict : ∀ θ θ' : ℝ, θ < θ' → ∀ x y, T x < T y → p θ' x * p θ y < p θ x * p θ' y)
    -- USER-INPUT: the constants of the two tests, each an honest rejection interval
    {C₁ C₂ C₁' C₂' γ₁ γ₂ γ₁' γ₂' : ℝ} (hC : C₁ < C₂) (hC' : C₁' < C₂')
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    (hγ₁' : γ₁' ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : γ₂' ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the reference parameter value
    {θ₁ : ℝ}
    -- USER-INPUT: the two tests have the same size at `θ₁`
    (hsize : power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ₁ =
      power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ₁)
    -- USER-INPUT: the second rejection interval lies to the right of the first
    (hright : C₁ < C₁' ∨ (C₁ = C₁' ∧ γ₁' < γ₁)) :
    (∀ θ : ℝ, θ₁ < θ → power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ <
        power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ) ∧
      ∀ θ : ℝ, θ < θ₁ → power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ <
        power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ := by
  sorry

/-- **The size conditions determine the test.** Two two-sided tests with size exactly `α`
at both `θ₁` and `θ₂` agree almost everywhere. -/
theorem twoSided_ae_unique
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic
    (T : 𝓧 → ℝ) (hT : Measurable T)
    -- USER-INPUT: densities strictly positive everywhere
    (hpos : ∀ θ x, 0 < p θ x)
    -- USER-INPUT: *strict* monotone likelihood ratio, division-free
    (hstrict : ∀ θ θ' : ℝ, θ < θ' → ∀ x y, T x < T y → p θ' x * p θ y < p θ x * p θ' y)
    -- USER-INPUT: the constants of the two tests
    {C₁ C₂ C₁' C₂' γ₁ γ₂ γ₁' γ₂' : ℝ} (hC : C₁ < C₂) (hC' : C₁' < C₂')
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    (hγ₁' : γ₁' ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : γ₂' ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the two null boundaries, in order, and the level
    {θ₁ θ₂ α : ℝ} (hθ : θ₁ < θ₂)
    -- USER-INPUT: both tests meet both size conditions
    (hsize₁ : power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ₁ = α)
    (hsize₂ : power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ₂ = α)
    (hsize₁' : power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ₁ = α)
    (hsize₂' : power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ₂ = α) :
    twoSidedTest T C₁ C₂ γ₁ γ₂ =ᵐ[μ] twoSidedTest T C₁' C₂' γ₁' γ₂' := by
  sorry

end StatLean.HypothesisTesting
