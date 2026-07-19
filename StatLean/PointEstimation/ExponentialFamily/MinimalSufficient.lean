import StatLean.PointEstimation.ExponentialFamily.Defs
import StatLean.PointEstimation.Sufficiency.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Intrinsic

/-!
# Minimal sufficiency of the natural statistic

For a canonical exponential family the natural statistic `T` is minimal sufficient as soon as
the parameter set is rich enough to separate the coordinates of `T`: it must contain `s + 1`
natural parameters that do not lie in a proper affine subspace of the parameter space. The
likelihood ratios based on such a configuration are
$$ \frac{p_{\eta^{(j)}}(x)}{p_{\eta^{(0)}}(x)}
   \;=\; \exp\bigl(\langle \eta^{(j)} - \eta^{(0)}, T(x)\rangle
         - A(\eta^{(j)}) + A(\eta^{(0)})\bigr), $$
a one-to-one function of the vector `(⟨η^{(j)} − η^{(0)}, T(x)⟩)_j`; when the differences
`η^{(j)} − η^{(0)}` span the parameter space this vector determines `T(x)`, so `T` is
equivalent to the minimal sufficient statistic of the finite subfamily.

* `ExpFamily.fullRank_exists_affineSpan` — a full-rank parameter set contains such a
  configuration;
* `ExpFamily.isMinimalSufficient_stat` — minimal sufficiency of the natural statistic under
  the affine-span condition.

**Reference.** Classical exponential-family and sufficiency theory; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* The two classical hypotheses — full rank, and the existence of an affinely spanning
  configuration of `s + 1` parameters — are kept apart. The affine-span condition is what the
  minimality proof actually uses, so it is the hypothesis of the headline theorem;
  `fullRank_exists_affineSpan` supplies it from full rank, and consumes only the
  nonempty-interior half of `ExpFamily.FullRank` (an open ball in a finite-dimensional space
  contains an affinely spanning configuration). Affine independence of the statistic, the
  other half of full rank, is what makes the parametrization identifiable; it is not needed
  here.
* Sufficiency of `T` itself is the factorization criterion: the density of `P_η` against the
  reference measure is `exp(⟨η, T⟩ − A(η))`, a function of `T` alone. σ-finiteness of the
  reference measure is required for the passage from that factorization to the θ-free
  conditional determinations demanded by `IsSufficient`; every dominated statistical model
  supplies it.
* Members of a canonical exponential family are mutually equivalent measures — the density
  `exp(⟨η, T⟩ − A(η))` is strictly positive — so the classical "common support" proviso of the
  minimal-sufficiency theory holds automatically and does not appear as a hypothesis.
* The span condition is stated as `affineSpan ℝ (Set.range η') = ⊤` with the ambient
  `AffineSubspace ℝ V` pinned by ascription. The equivalent working form, and the one the
  proof will use, is that the differences `η' i − η' 0` span `V` as a submodule.

**Bibliographic comments.** Minimal sufficiency and the likelihood-ratio construction are due
to E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and unbiased estimation,"
*Sankhyā* **10** (1950), 305–340) and R. R. Bahadur ("Sufficiency and statistical decision
functions," *Ann. Math. Statist.* **25** (1954), 423–462; "On unbiased estimates of uniformly
minimum variance," *Sankhyā* **18** (1957), 211–224). The characterization of sufficient
statistics by exponential structure goes back to R. A. Fisher (*Proc. R. Soc. Lond. A* **144**
(1934), 285–307), G. Darmois (*C. R. Acad. Sci. Paris* **200** (1935), 1265–1266),
B. O. Koopman (*Trans. Amer. Math. Soc.* **39** (1936), 399–409) and E. J. G. Pitman (*Proc.
Camb. Phil. Soc.* **32** (1936), 567–579); see also E. B. Dynkin ("Necessary and sufficient
statistics for a family of probability distributions," *Uspekhi Mat. Nauk* **6** (1951),
68–90) and O. Barndorff-Nielsen (*Information and Exponential Families in Statistical
Theory*, Wiley, 1978, Ch. 8).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [SecondCountableTopology V]

namespace ExpFamily

/-- A **full-rank parameter set contains an affinely spanning configuration**: from a
parameter set with nonempty interior in a finite-dimensional parameter space one can extract
`finrank ℝ V + 1` points that lie in no proper affine subspace. Only the nonempty-interior
part of `ExpFamily.FullRank` is used. -/
theorem fullRank_exists_affineSpan [FiniteDimensional ℝ V] (E : ExpFamily 𝓧 V) (Ξ' : Set V)
    -- USER-INPUT: the classical full-rank condition on the parameter set
    (hFR : E.FullRank Ξ') :
    ∃ η' : Fin (Module.finrank ℝ V + 1) → V, (∀ i, η' i ∈ Ξ') ∧
      affineSpan ℝ (Set.range η') = (⊤ : AffineSubspace ℝ V) := by
  obtain ⟨-, hint, -⟩ := hFR
  -- a nonempty-interior set affinely spans the whole space
  have hspanΞ : affineSpan ℝ Ξ' = (⊤ : AffineSubspace ℝ V) := by
    obtain ⟨x₀, hx₀⟩ := hint
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx₀)
    have hballspan : affineSpan ℝ (Metric.ball x₀ r) = (⊤ : AffineSubspace ℝ V) :=
      (convex_ball x₀ r).interior_nonempty_iff_affineSpan_eq_top.mp
        (by rw [Metric.isOpen_ball.interior_eq]; exact ⟨x₀, Metric.mem_ball_self hr⟩)
    have hle := affineSpan_mono ℝ hball
    rw [hballspan] at hle
    exact top_le_iff.mp hle
  -- extract an affinely independent spanning subset of `Ξ'`
  obtain ⟨t, hts, htspan, htind⟩ := exists_affineIndependent ℝ V Ξ'
  rw [hspanΞ] at htspan
  haveI : Finite t := finite_of_fin_dim_affineIndependent ℝ htind
  haveI : Fintype t := Fintype.ofFinite t
  have htspan' : affineSpan ℝ (Set.range (Subtype.val : t → V)) = (⊤ : AffineSubspace ℝ V) := by
    rwa [Subtype.range_coe]
  have hcard : Fintype.card t = Module.finrank ℝ V + 1 :=
    htind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp htspan'
  let e : Fin (Module.finrank ℝ V + 1) ≃ t := (Fintype.equivFinOfCardEq hcard).symm
  have hrange : Set.range (fun i => ((e i : t) : V)) = (t : Set V) := by
    ext v
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hv; exact ⟨e.symm ⟨v, hv⟩, by simp⟩
  refine ⟨fun i => ((e i : t) : V), fun i => hts (e i).2, ?_⟩
  rw [hrange]; exact htspan

/-- **The natural statistic is minimal sufficient** for a canonical exponential family whose
parameter set contains `s + 1` natural parameters spanning the parameter space affinely. -/
theorem isMinimalSufficient_stat {s : ℕ} (E : ExpFamily 𝓧 V)
    -- LEAN-ONLY: σ-finiteness of the reference measure; needed to turn the density
    -- factorization into the θ-free conditional determinations of `IsSufficient`
    [SigmaFinite E.base] (Ξ' : Set V)
    -- USER-INPUT: the parameter set lies in the natural parameter set, so every member is a
    -- genuine probability measure of the family
    (hΞ : Ξ' ⊆ E.natSet)
    -- USER-INPUT: nondegenerate reference measure
    (hbase : E.base ≠ 0)
    -- USER-INPUT: the parameter set contains `s + 1` points lying in no proper affine
    -- subspace; the classical rank condition for minimality
    (hspan : ∃ η' : Fin (s + 1) → V, (∀ i, η' i ∈ Ξ') ∧
      affineSpan ℝ (Set.range η') = (⊤ : AffineSubspace ℝ V)) :
    IsMinimalSufficient (fun θ : Ξ' => E.P (θ : V)) E.stat := by
  -- TODO: the two halves of `IsMinimalSufficient`.
  -- (1) Sufficiency of `E.stat`: the density of `E.P η` against `E.base` is
  --     `exp(⟨η, T⟩ - A(η))`, a function of `T` alone, giving the Fisher–Neyman factorization
  --     `IsFactorizedDensity`; `Sufficiency.Factorization.isSufficient_of_isFactorizedDensity`
  --     then yields `IsSufficient`. (That bridging lemma is itself an open `sorry` in this
  --     worktree's `Sufficiency/Factorization.lean`, so this half cannot currently be
  --     discharged without laundering another file's debt.)
  -- (2) Minimality: for a competing sufficient `U`, the likelihood ratios
  --     `p_{η^{(j)}}/p_{η^{(0)}} = exp(⟨η^{(j)} - η^{(0)}, T⟩ - ΔA)` are `U`-measurable; the
  --     affine-span hypothesis makes the vector `(⟨η^{(j)} - η^{(0)}, T⟩)_j` determine `T` up
  --     to `a.e.` equality, so `T` factors through `U` by Doob–Dynkin
  --     (`Measurable.exists_eq_measurable_comp`). This is a substantial development
  --     (log-likelihood inversion + measurable selection) beyond the imported API.
  -- The statement is left exactly as posed; only the proof is deferred.
  sorry

end ExpFamily

end StatLean.PointEstimation
