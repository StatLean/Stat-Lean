import StatLean.PointEstimation.Sufficiency.HalmosSavageCriterion

/-!
# The factorization theorem

The working criterion for sufficiency in a dominated model: if the members of the family
have densities `p_θ` with respect to a σ-finite measure `μ`, then a statistic `T` is
sufficient exactly when the densities split into a factor that sees the data only through
`T` and a factor that does not see the parameter at all,
$$ p_\theta(x) \;=\; g_\theta\bigl(T(x)\bigr)\, h(x) \qquad (\mu\text{-a.e.}). $$

* `isSufficient_of_isFactorizedDensity` — a factorization makes `T` sufficient;
* `isFactorizedDensity_of_isSufficient` — a sufficient `T` produces a factorization.

**Reference.** Classical factorization criterion for sufficiency in dominated models.

**Proof formalization notes.**
* Both directions are stated relative to an arbitrary σ-finite dominating measure `μ` and
  fixed densities `p`, matching the classical statement. The bridge to the mixture form is
  the criterion of `Sufficiency.HalmosSavageCriterion`: writing `ν = ∑ᵢ cᵢ P_{θᵢ}` for an
  equivalent mixture, one direction takes `h = dν/dμ` (finite `ν` over σ-finite `μ`, so the
  derivative exists), and the other rescales, `g*_θ(t) = g_θ(t)/k(t)` with
  `k(t) = ∑ᵢ cᵢ g_{θᵢ}(t)`, choosing an arbitrary value where `k` vanishes. Consequently
  this file consumes the *existence* of an equivalent countable mixture for a dominated
  family; the criterion file itself takes the mixture as data.
* The factorization is the `μ`-a.e. predicate `IsFactorizedDensity` of `Sufficiency.Defs`,
  not a pointwise identity: the rescaling step above genuinely only controls a.e. behavior,
  and no downstream consumer needs more.
* All densities are `ℝ≥0∞`-valued, so there are no positivity or finiteness side conditions;
  measurability of `p_θ`, `g_θ` and `h` is what the change-of-variables steps consume.
* The existential direction returns the factorization data (`g`, `h`) rather than asserting
  it for a caller-supplied pair, because the classical construction determines `h` only up to
  the choice of mixture.

**Bibliographic comments.** The criterion is due to J. Neyman ("Sur un teorema concernente le
cosiddette statistiche sufficienti," *Giorn. Ist. Ital. Attuari* **6** (1935), 320–334),
following the introduction of sufficiency by R. A. Fisher ("On the mathematical foundations
of theoretical statistics," *Phil. Trans. R. Soc. A* **222** (1922), 309–368); its
measure-theoretic form for arbitrary dominated families, which is what is stated here, is due
to P. R. Halmos and L. J. Savage ("Application of the Radon–Nikodym theorem to the theory of
sufficient statistics," *Ann. Math. Statist.* **20** (1949), 225–241).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- **Factorization ⇒ sufficiency.** If the densities of a dominated family split as
`p_θ = (g_θ ∘ T) · h` almost everywhere, then `T` is sufficient. -/
theorem isSufficient_of_isFactorizedDensity (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (μ : Measure 𝓧) [SigmaFinite μ] (p : Θ → 𝓧 → ℝ≥0∞)
    -- LEAN-ONLY: measurability of the densities
    (hp : ∀ θ, Measurable (p θ))
    -- USER-INPUT: the model is dominated by `μ` with densities `p`; the classical setup
    (hP : ∀ θ, P θ = μ.withDensity (p θ)) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {g : Θ → S → ℝ≥0∞}
    -- LEAN-ONLY: measurability of the parameter-dependent factor
    (hg : ∀ θ, Measurable (g θ)) {h : 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: measurability of the carrier
    (hh : Measurable h)
    -- USER-INPUT: the Fisher–Neyman factorization of the densities
    (hfac : IsFactorizedDensity p μ T g h) :
    IsSufficient P T := by
  sorry

/-- **Sufficiency ⇒ factorization.** A sufficient statistic for a dominated family produces
a Fisher–Neyman factorization of its densities. -/
theorem isFactorizedDensity_of_isSufficient (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (μ : Measure 𝓧) [SigmaFinite μ] (p : Θ → 𝓧 → ℝ≥0∞)
    -- LEAN-ONLY: measurability of the densities
    (hp : ∀ θ, Measurable (p θ))
    -- USER-INPUT: the model is dominated by `μ` with densities `p`; the classical setup
    (hP : ∀ θ, P θ = μ.withDensity (p θ)) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T)
    -- USER-INPUT: sufficiency of `T` in the per-event sense
    (hsuf : IsSufficient P T) :
    ∃ (g : Θ → S → ℝ≥0∞) (h : 𝓧 → ℝ≥0∞), (∀ θ, Measurable (g θ)) ∧ Measurable h ∧
      IsFactorizedDensity p μ T g h := by
  sorry

end StatLean.PointEstimation
