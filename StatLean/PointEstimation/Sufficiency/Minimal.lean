import StatLean.PointEstimation.Sufficiency.Factorization

/-!
# Minimal sufficiency: the likelihood-ratio vector

A sufficient statistic is *minimal* when it reduces the data as far as any sufficient
statistic can — every sufficient statistic determines it. For a finite family with densities
`p₀, …, p_k` sharing a common support, the vector of likelihood ratios against a fixed
baseline member,
$$ T(x) \;=\; \Bigl(\frac{p_1(x)}{p_0(x)},\, \dots,\, \frac{p_k(x)}{p_0(x)}\Bigr), $$
is minimal sufficient. The engine behind this is a sharpening of the factorization criterion:
a statistic is sufficient exactly when all the density ratios of the family are functions of
it, so any sufficient statistic determines `T`, and `T` is itself sufficient.

* `likelihoodRatioVec` — the statistic displayed above;
* `isMinimalSufficient_likelihoodRatioVec` — it is minimal sufficient;
* `isSufficient_iff_ratio_factors` — sufficiency of a statistic `U` is equivalent to every
  density ratio factoring through `U` almost everywhere.

**Reference.** Classical construction of a minimal sufficient statistic for a finite family
with common support, and the likelihood-ratio criterion for sufficiency.

**Proof formalization notes.**
* Ratios are formed in `ℝ≥0∞`, where division is total (`a / 0 = ∞` for `a ≠ 0`, `0 / 0 = 0`),
  so `likelihoodRatioVec` is a genuine total definition with no junk-value caveats at the
  level of the definition; the common-support hypothesis enters as the positivity assumption
  `hpos` and makes the ratios meaningful almost everywhere.
* The "common support" of the classical statement is formalized as: every density is
  a.e. strictly positive with respect to the dominating measure. This is not a loss of
  generality — restrict `μ` to the common support — but it *is* a genuine restriction of the
  theorem relative to families whose supports vary with the parameter, which is exactly the
  restriction the classical statement makes.
* `hfin` (a.e. finiteness of the densities) is a Lean-side addition with no classical
  counterpart: `ℝ≥0∞`-valued densities may take the value `∞` on a `μ`-positive set only if
  the corresponding member is not σ-finite there, but ruling it out keeps the ratio algebra
  (`(a/b) * b = a`) usable without case analysis.
* `IsMinimalSufficient` quantifies competitor statistics over a fixed universe (see
  `Sufficiency.Defs`); the universe parameter is left to be inferred here.
* The subfamily lemma ("minimal for a subfamily plus sufficient for the whole family implies
  minimal for the whole family"), which is the classical route from finite families to
  general ones, is deliberately **not** stated here: it is not part of this campaign's
  ledger.

**Bibliographic comments.** Minimal sufficiency and the likelihood-ratio construction are due
to E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and unbiased estimation,"
*Sankhyā* **10** (1950), 305–340), with the general existence theory developed by
E. B. Dynkin ("Necessary and sufficient statistics for a family of probability
distributions," *Uspekhi Mat. Nauk* **6** (1951), 68–90) and R. R. Bahadur ("Sufficiency and
statistical decision functions," *Ann. Math. Statist.* **25** (1954), 423–462; "Statistics
and subfields," *Ann. Math. Statist.* **26** (1955), 490–497). The underlying factorization
criterion is due to J. Neyman ("Sur un teorema concernente le cosiddette statistiche
sufficienti," *Giorn. Ist. Ital. Attuari* **6** (1935), 320–334) and P. R. Halmos and
L. J. Savage ("Application of the Radon–Nikodym theorem to the theory of sufficient
statistics," *Ann. Math. Statist.* **20** (1949), 225–241).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **likelihood-ratio vector** of a finite family with densities `p₀, …, p_k`: the
statistic `x ↦ (p₁(x)/p₀(x), …, p_k(x)/p₀(x))`, with the ratios taken in `ℝ≥0∞`. -/
noncomputable def likelihoodRatioVec {k : ℕ} (p : Fin (k + 1) → 𝓧 → ℝ≥0∞) (x : 𝓧) :
    Fin k → ℝ≥0∞ :=
  fun i => p i.succ x / p 0 x

/-- **The likelihood-ratio vector is minimal sufficient** for a finite dominated family whose
densities share a common support. -/
theorem isMinimalSufficient_likelihoodRatioVec {k : ℕ} (μ : Measure 𝓧) [SigmaFinite μ]
    (p : Fin (k + 1) → 𝓧 → ℝ≥0∞)
    -- LEAN-ONLY: measurability of the densities
    (hp : ∀ i, Measurable (p i))
    -- USER-INPUT: common support, in the form "every density is a.e. positive"
    (hpos : ∀ i, ∀ᵐ x ∂μ, 0 < p i x)
    -- LEAN-ONLY: a.e. finiteness of the `ℝ≥0∞`-valued densities, so the ratio algebra needs
    -- no case analysis; no classical counterpart
    (hfin : ∀ i, ∀ᵐ x ∂μ, p i x ≠ ∞) (P : Fin (k + 1) → Measure 𝓧)
    [∀ i, IsProbabilityMeasure (P i)]
    -- USER-INPUT: the family is dominated by `μ` with densities `p`; the classical setup
    (hP : ∀ i, P i = μ.withDensity (p i)) :
    IsMinimalSufficient P (likelihoodRatioVec p) := by
  sorry

/-- **Sufficiency ⟺ the density ratios factor through the statistic.** For a dominated family
with a common support, a statistic `U` is sufficient exactly when, for every pair of
parameter values, the ratio of the corresponding densities is almost everywhere a measurable
function of `U`. -/
theorem isSufficient_iff_ratio_factors {S' : Type*} [MeasurableSpace S'] (μ : Measure 𝓧)
    [SigmaFinite μ] (p : Θ → 𝓧 → ℝ≥0∞)
    -- LEAN-ONLY: measurability of the densities
    (hp : ∀ θ, Measurable (p θ))
    -- USER-INPUT: common support, in the form "every density is a.e. positive"
    (hpos : ∀ θ, ∀ᵐ x ∂μ, 0 < p θ x)
    -- LEAN-ONLY: a.e. finiteness of the densities (see `isMinimalSufficient_likelihoodRatioVec`)
    (hfin : ∀ θ, ∀ᵐ x ∂μ, p θ x ≠ ∞) (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the family is dominated by `μ` with densities `p`; the classical setup
    (hP : ∀ θ, P θ = μ.withDensity (p θ)) {U : 𝓧 → S'}
    -- LEAN-ONLY: measurability of the candidate statistic
    (hU : Measurable U) :
    IsSufficient P U ↔
      ∀ θ θ₀, ∃ r : S' → ℝ≥0∞, Measurable r ∧
        (fun x => p θ x / p θ₀ x) =ᵐ[μ] fun x => r (U x) := by
  sorry

end StatLean.PointEstimation
