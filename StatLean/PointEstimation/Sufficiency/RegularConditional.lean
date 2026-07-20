import StatLean.PointEstimation.Sufficiency.Factorization
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# From per-event determinations to a θ-free regular conditional distribution

The definition of sufficiency only asks that *each* event `A` admit a determination of
`P_θ(A ∣ T = t)` free of `θ`. What decision theory actually uses is stronger: a single θ-free
Markov kernel `Q : S ⇝ 𝓧` which, for each fixed `t`, is a genuine probability measure and
which disintegrates the joint law of `(T(X), X)` under every member. On a standard Borel
sample space the two coincide.

* `hasSufficientKernel_of_isSufficient_dominated` — the **dominated** version: for a family
  dominated by a σ-finite measure on a standard Borel sample space, a sufficient statistic
  admits a θ-free reconstruction kernel. This is the version the rest of the area consumes.
* `hasSufficientKernel_of_isSufficient` — the general standard Borel version, without
  domination. Named planned debt (see below).

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 2 (The Probability
Background), §2.6 (Sufficient Statistics), Theorem 2.6.1 (existence of a θ-free regular
conditional distribution given a sufficient statistic). (`TSH4 Thm 2.6.1`.)

**Proof formalization notes.**
* The dominated route avoids gluing per-event determinations altogether. Fix an equivalent
  countable mixture `ν` of members of the family and let `Q` be the conditional kernel of the
  graph law of `(T, id)` under `ν`, which exists on a standard Borel sample space
  (`MeasureTheory.Measure.condKernel`, requiring `[StandardBorelSpace 𝓧]` and `[Nonempty 𝓧]`
  on the *second* factor of the product; no condition on the value space `S` of the
  statistic). The Halmos–Savage criterion then shows that this single kernel disintegrates
  the graph law of *every* member: the density `dP_θ/dν` is a function of `T`, so tilting the
  disintegration of `ν` by it changes only the first marginal.
* `[Nonempty 𝓧]` is a technical requirement of Mathlib's disintegration API (a Markov kernel
  must have somewhere to put its mass) and is no restriction: the family consists of
  probability measures, so the sample space is nonempty whenever the parameter set is.
* The general (undominated) version genuinely needs the gluing argument — choose
  determinations along a countable generating algebra, repair finite additivity and
  continuity at `∅` on a null set, and extend by Carathéodory — which on standard Borel
  spaces goes through the regularity of the associated conditional distribution functions.
  It is **DEFERRAL-ELIGIBLE**: a named planned debt, pre-agreed for this campaign. Nothing in
  the area consumes it; every downstream user routes through the dominated version.
* Both statements deliver the graph/compProd carrier `HasSufficientKernel` rather than a
  bare reconstruction identity, so that the fiber property of `Sufficiency.Basic` comes for
  free at the point of use.

**Bibliographic comments.** The existence of θ-free conditional distributions given a
sufficient statistic on Euclidean sample spaces is classical; the measure-theoretic treatment
for dominated families is due to P. R. Halmos and L. J. Savage ("Application of the
Radon–Nikodym theorem to the theory of sufficient statistics," *Ann. Math. Statist.* **20**
(1949), 225–241), and the decision-theoretic formulation, in which the reconstruction kernel
is the object of interest, to R. R. Bahadur ("Sufficiency and statistical decision
functions," *Ann. Math. Statist.* **25** (1954), 423–462; "Statistics and subfields," *Ann.
Math. Statist.* **26** (1955), 490–497).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- Tilting the first marginal of a compProd by a density of the first coordinate. -/
private theorem compProd_withDensity_left (μ : Measure S) [SFinite μ] (Q : Kernel S 𝓧)
    [IsSFiniteKernel Q] {w : S → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity w) ⊗ₘ Q = (μ ⊗ₘ Q).withDensity (fun p => w p.1) := by
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs, ← lintegral_indicator hs,
      Measure.lintegral_compProd
        ((show Measurable fun p : S × 𝓧 => w p.1 from hw.comp measurable_fst).indicator hs),
      lintegral_withDensity_eq_lintegral_mul _ hw (Kernel.measurable_kernel_prodMk_left hs)]
  refine lintegral_congr fun a => ?_
  rw [Pi.mul_apply]
  have hind : (fun x => s.indicator (fun p => w p.1) (a, x))
      = (Prod.mk a ⁻¹' s).indicator (fun _ => w a) := by
    funext x
    by_cases hx : (a, x) ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_preimage.mpr hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt Set.mem_preimage.mp hx)]
  rw [hind, lintegral_indicator_const (measurable_prodMk_left hs)]

/-- **Dominated existence of a θ-free reconstruction kernel.** On a standard Borel sample
space, a sufficient statistic for a family dominated by a σ-finite measure admits a single
θ-free Markov kernel disintegrating the graph law of `(T, id)` under every member. -/
theorem hasSufficientKernel_of_isSufficient_dominated [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model is dominated by the σ-finite measure `μ`; classical setup
    (hdom : ∀ θ, P θ ≪ μ)
    -- USER-INPUT: sufficiency of `T` in the per-event sense
    (hsuf : IsSufficient P T) :
    HasSufficientKernel P T := by
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · haveI : IsProbabilityMeasure (Measure.dirac (Classical.arbitrary 𝓧)) :=
      Measure.dirac.isProbabilityMeasure
    exact ⟨Kernel.const S (Measure.dirac (Classical.arbitrary 𝓧)), inferInstance,
      fun θ => (hΘ.false θ).elim⟩
  obtain ⟨θs, c, ν, hν, hcpos, hcsum, hdomν, -⟩ :=
    exists_equivalent_countable_mixture P μ hdom
  haveI : IsProbabilityMeasure ν := ⟨by
    rw [hν, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact hcsum⟩
  have he : Measurable (fun x => (T x, x)) := hT.prodMk measurable_id
  haveI : IsProbabilityMeasure (ν.map fun x => (T x, x)) :=
    Measure.isProbabilityMeasure_map he.aemeasurable
  have hρfst : (ν.map fun x => (T x, x)).fst = ν.map T :=
    Measure.fst_map_prodMk measurable_id
  set Q : Kernel S 𝓧 := (ν.map fun x => (T x, x)).condKernel with hQdef
  have hρcompProd : (ν.map T) ⊗ₘ Q = ν.map fun x => (T x, x) := by
    rw [hQdef, ← hρfst]; exact Measure.disintegrate _ _
  refine ⟨Q, Measure.instIsMarkovKernelCondKernel _, fun θ => ?_⟩
  obtain ⟨w, hw, hweq⟩ := rnDeriv_comp_of_isSufficient P hT θs c ν hν hdomν hsuf θ
  have hPθ : P θ = ν.withDensity (fun x => w (T x)) :=
    calc P θ = ν.withDensity ((P θ).rnDeriv ν) :=
          (Measure.withDensity_rnDeriv_eq (P θ) ν (hdomν θ)).symm
      _ = ν.withDensity (fun x => w (T x)) := withDensity_congr_ae hweq
  have hmapwd : (ν.withDensity (fun x => w (T x))).map (fun x => (T x, x))
      = (ν.map fun x => (T x, x)).withDensity (fun q => w q.1) := by
    refine Measure.ext fun C hC => ?_
    rw [Measure.map_apply he hC, withDensity_apply _ (he hC), withDensity_apply _ hC,
        setLIntegral_map hC (show Measurable fun q : S × 𝓧 => w q.1 from hw.comp measurable_fst) he]
  have hmapT : (ν.withDensity (fun x => w (T x))).map T = (ν.map T).withDensity w := by
    refine Measure.ext fun C hC => ?_
    rw [Measure.map_apply hT hC, withDensity_apply _ (hT hC), withDensity_apply _ hC,
        setLIntegral_map hC hw hT]
  have hstat : statLaw P T θ = (ν.map T).withDensity w := by rw [statLaw, hPθ, hmapT]
  calc (P θ).map (fun x => (T x, x))
      = (ν.map fun x => (T x, x)).withDensity (fun q => w q.1) := by rw [hPθ, hmapwd]
    _ = ((ν.map T) ⊗ₘ Q).withDensity (fun q => w q.1) := by rw [hρcompProd]
    _ = ((ν.map T).withDensity w) ⊗ₘ Q := (compProd_withDensity_left (ν.map T) Q hw).symm
    _ = (statLaw P T θ) ⊗ₘ Q := by rw [hstat]

/-- **General existence of a θ-free reconstruction kernel** on a standard Borel sample space,
without any domination assumption.

**DEFERRAL-ELIGIBLE (named planned debt).** The proof requires gluing the per-event
determinations of `IsSufficient` into a single kernel — choosing determinations along a
countable generating algebra and repairing additivity and continuity at `∅` off a null set —
rather than reading the kernel off a disintegration. No result in this area depends on it:
every consumer uses `hasSufficientKernel_of_isSufficient_dominated`. -/
theorem hasSufficientKernel_of_isSufficient [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)] {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T)
    -- USER-INPUT: sufficiency of `T` in the per-event sense
    (hsuf : IsSufficient P T) :
    HasSufficientKernel P T := by
  -- TODO (DEFERRAL-ELIGIBLE, named planned debt): glue the per-event determinations of
  -- `hsuf` into a single Markov kernel. Choose determinations `κ_{A_n}` along a countable
  -- generating algebra `{A_n}` of `𝓧`, repair finite additivity in `A` and continuity at
  -- `∅` off a `statLaw`-null set of `t`, and extend by Carathéodory to a genuine kernel
  -- `Q : S ⇝ 𝓧`; on a standard Borel `𝓧` this goes through the regularity of the associated
  -- conditional distribution functions. No result in this area consumes this theorem: every
  -- downstream user routes through `hasSufficientKernel_of_isSufficient_dominated`.
  sorry

end StatLean.PointEstimation
