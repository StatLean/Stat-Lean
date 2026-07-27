import StatLean.Bayesian.DoobConsistency.Defs
import StatLean.Bayesian.DoobConsistency.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Accessibility: the parameter is a measurable function of the data sequence

The measure-theoretic heart of vdV Theorem 10.10, display (10.11): under identifiability,
there is a measurable `g : 𝓧^ℕ → Θ` with `g(X₁, X₂, …) = Θ̄` almost surely under the joint
law. vdV proves this via "accessible functions" and the monotone-class Lemmas 10.12/10.13;
here the retraction is constructed explicitly, absorbing both lemmas:

* `exists_countable_measure_determining` — a countable measure-determining family of sets
  in a standard Borel space (countably generated σ-algebra; π-system uniqueness);
* `empirical_freq_ae_tendsto` — the strong law for the empirical frequencies
  `n⁻¹ #{i < n : Xᵢ ∈ A} → K θ (A)`, `K θ`-iid-a.s.;
* `exists_measurable_retraction` — the headline (10.11): the map
  `F : θ ↦ (K θ (Aₘ))ₘ ∈ ℝ^ℕ` is measurable and injective (identifiability +
  determining family), hence a measurable embedding by Lusin–Souslin; composing a
  measurable retraction of `F` with the empirical-limit map recovers `Θ̄` from the data
  a.s.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.4, proof of
Theorem 10.10, pp. 149–150 (accessible functions; the strong law step), and p. 151,
Lemmas 10.12–10.13 (absorbed by the explicit construction).

**Proof formalization notes.** Lusin–Souslin is `Measurable.measurableEmbedding` (injective
Borel maps between standard Borel spaces are embeddings); the retraction is assembled from
`MeasurableEmbedding.measurableSet_range` and `measurable_rangeSplitting`, with a default
value off the range (`[Nonempty Θ]`). The lift of the per-`θ` a.s. statement to the joint
law is `Measure.ae_compProd_of_ae_ae` (the convergence event is jointly measurable —
countably many measurable conditions). The empirical-limit map is made globally defined via
`limsup`-type expressions, measurable by countable operations.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- **A countable measure-determining family** in a standard Borel space: countably many
measurable sets such that two probability measures agreeing on all of them are equal
(countable generating π-system + `ext_of_generate_finite`). -/
theorem exists_countable_measure_determining (𝓧 : Type*) [MeasurableSpace 𝓧]
    [StandardBorelSpace 𝓧] :
    ∃ A : ℕ → Set 𝓧, (∀ m, MeasurableSet (A m)) ∧
      ∀ (P Q : Measure 𝓧), IsProbabilityMeasure P → IsProbabilityMeasure Q →
        (∀ m, P (A m) = Q (A m)) → P = Q := by
  classical
  -- a countable generating sequence, closed under finite intersections
  set b : ℕ → Set 𝓧 := MeasurableSpace.natGeneratingSequence 𝓧 with hb
  set e : ℕ → Finset ℕ := fun n => (Encodable.decode n).getD ∅ with he
  set A : ℕ → Set 𝓧 := fun n => ⋂ i ∈ (e n : Set ℕ), b i with hAdef
  have hesurj : ∀ s : Finset ℕ, e (Encodable.encode s) = s := by
    intro s; simp [he]
  have hAmeas : ∀ n, MeasurableSet (A n) := by
    intro n
    exact MeasurableSet.biInter (Finset.countable_toSet _) fun i _ =>
      MeasurableSpace.measurableSet_natGeneratingSequence i
  have hpi : IsPiSystem (Set.range A) := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩ -
    refine ⟨Encodable.encode (e n ∪ e m), ?_⟩
    simp only [hAdef, hesurj, Finset.coe_union, Set.biInter_union]
  have hgen : (inferInstance : MeasurableSpace 𝓧)
      = MeasurableSpace.generateFrom (Set.range A) := by
    refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
    · refine le_trans (le_of_eq
        (MeasurableSpace.generateFrom_natGeneratingSequence 𝓧).symm)
        (MeasurableSpace.generateFrom_mono ?_)
      rintro _ ⟨i, rfl⟩
      exact ⟨Encodable.encode ({i} : Finset ℕ), by simp [hAdef, hesurj, hb]⟩
    · rintro _ ⟨n, rfl⟩
      exact hAmeas n
  refine ⟨A, hAmeas, fun P Q hP hQ hPQ => ?_⟩
  haveI := hP
  haveI := hQ
  refine ext_of_generate_finite (Set.range A) hgen hpi ?_ (by simp)
  rintro _ ⟨n, rfl⟩
  exact hPQ n

/-- **The strong law for empirical frequencies**: for every `θ` and measurable `A`,
`K θ`-iid-almost-surely the empirical frequency of `A` among the first `n` observations
converges to `(K θ A).toReal`. -/
theorem empirical_freq_ae_tendsto (K : Kernel Θ 𝓧) [IsMarkovKernel K] (θ : Θ)
    {A : Set 𝓧}
    -- LEAN-ONLY: measurable event (regularity)
    (hA : MeasurableSet A) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => K θ),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, A.indicator 1 (ω i))
        atTop (𝓝 (K θ A).toReal) := by
  classical
  have hind : Measurable (A.indicator (1 : 𝓧 → ℝ)) := measurable_one.indicator hA
  set μ : Measure (ℕ → 𝓧) := Measure.infinitePi fun _ : ℕ => K θ with hμ
  set X : ℕ → (ℕ → 𝓧) → ℝ := fun i ω => A.indicator (1 : 𝓧 → ℝ) (ω i) with hX
  have hXmeas : ∀ i, Measurable (X i) := fun i => hind.comp (measurable_pi_apply i)
  have hmapeval : ∀ i : ℕ, μ.map (fun ω : ℕ → 𝓧 => ω i) = K θ := fun i =>
    Measure.infinitePi_map_eval _ i
  have hmap : ∀ i, μ.map (X i) = (K θ).map (A.indicator (1 : 𝓧 → ℝ)) := by
    intro i
    rw [show X i = (A.indicator (1 : 𝓧 → ℝ)) ∘ (fun ω : ℕ → 𝓧 => ω i) from rfl,
      ← Measure.map_map hind (measurable_pi_apply i), hmapeval i]
  have hindep : iIndepFun X μ :=
    ProbabilityTheory.iIndepFun_infinitePi (Ω := fun _ : ℕ => 𝓧) (P := fun _ : ℕ => K θ)
      (X := fun _ : ℕ => A.indicator (1 : 𝓧 → ℝ)) fun _ => hind
  have hX0 : X 0 = ((fun ω : ℕ → 𝓧 => ω 0) ⁻¹' A).indicator (fun _ => (1 : ℝ)) := by
    funext ω; simp [hX, Set.indicator_apply]
  have hint : Integrable (X 0) μ := by
    rw [hX0]
    exact (integrable_const _).indicator (hA.preimage (measurable_pi_apply 0))
  have hmean : ∫ ω, X 0 ω ∂μ = (K θ A).toReal := by
    rw [hX0, integral_indicator_const _ (hA.preimage (measurable_pi_apply 0)),
      measureReal_def, ← Measure.map_apply (measurable_pi_apply 0) hA, hmapeval 0]
    simp
  have hlln := ProbabilityTheory.strong_law_ae X hint (fun i j hij => hindep.indepFun hij)
    (fun i => ⟨(hXmeas i).aemeasurable, (hXmeas 0).aemeasurable, by rw [hmap i, hmap 0]⟩)
  rw [hmean] at hlln
  filter_upwards [hlln] with ω hω
  simpa only [smul_eq_mul] using hω

/-- **Display (10.11)**: under identifiability (`θ ↦ K θ` injective), with `𝓧` standard
Borel and `Θ` standard Borel and nonempty, there is a measurable `g : 𝓧^ℕ → Θ` recovering
the parameter from the data sequence almost surely under the joint law. -/
theorem exists_measurable_retraction [StandardBorelSpace Θ] [Nonempty Θ]
    [StandardBorelSpace 𝓧]
    (K : Kernel Θ 𝓧) [IsMarkovKernel K]
    -- USER-INPUT: identifiability, `P_θ ≠ P_{θ'}` for `θ ≠ θ'`; vdV Thm 10.10
    (hK_inj : Function.Injective fun θ => K θ)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    ∃ g : (ℕ → 𝓧) → Θ, Measurable g ∧
      ∀ᵐ ω ∂(doobJoint K π), g ω.1 = ω.2 := by
  sorry

end StatLean.Bayesian
