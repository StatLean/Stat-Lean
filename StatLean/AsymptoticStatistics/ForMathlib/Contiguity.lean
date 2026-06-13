import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Contiguity of sequences of probability measures

Contiguity (van der Vaart §6.3-§6.7) and Le Cam's first and third lemmas, as pure
probability-theoretic results (theorem-agnostic, candidate upstream).

Main declarations:
* `WeakConverges` — test-function-based weak convergence of measures.
* `Contiguous`, `MutuallyContiguous` — the two notions.
* `contiguous_of_asymptotically_log_normal` — vdV Example 6.5, direction `Q ⊲ P`.
* `mutuallyContiguous_of_asymptotically_log_normal` — mutual-contiguity version.
* `weak_limit_under_Q_of_lecam_third` — Le Cam's third lemma (vdV Example 6.7).
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-- Weak convergence of a sequence of probability measures (convergence in law).

Test-function characterization: for every bounded continuous real-valued `f`, the
`f`-integrals converge. Equivalent to convergence in the weak topology on
`MeasureTheory.ProbabilityMeasure E`, but given in unpacked form for convenience. -/
def WeakConverges {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (μ : ℕ → Measure E) (ν : Measure E) : Prop :=
  ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))

/-- **Continuous mapping theorem for weak convergence**: if `μ_n` weakly converges to
`ν` on `E` and `f : E → F` is continuous and measurable, then the pushforwards by `f`
weakly converge to the pushforward of the limit. Standard application of
`BoundedContinuousFunction.compContinuous` + `integral_map`. -/
lemma WeakConverges.map {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [MeasurableSpace F] [TopologicalSpace F] [PseudoMetricSpace F]
    [OpensMeasurableSpace F]
    {μ : ℕ → Measure E} {ν : Measure E}
    (hμν : WeakConverges μ ν) {f : E → F}
    (hf_cont : Continuous f) (hf_meas : Measurable f) :
    WeakConverges (fun n => (μ n).map f) (ν.map f) := by
  intro g
  -- `g ∘ f` is a bounded continuous function on `E`.
  let g_comp_f : E →ᵇ ℝ := g.compContinuous ⟨f, hf_cont⟩
  -- Both `∫ g d(μ.map f)` and `∫ g d(ν.map f)` rewrite to `∫ (g ∘ f) dμ` / `∫ (g ∘ f) dν`.
  have h_rewrite : ∀ ρ : Measure E,
      ∫ y, g y ∂(ρ.map f) = ∫ x, g_comp_f x ∂ρ := by
    intro ρ
    rw [MeasureTheory.integral_map hf_meas.aemeasurable
      g.continuous.aestronglyMeasurable]
    rfl
  simp_rw [h_rewrite]
  exact hμν g_comp_f

/-- **Subsequence preservation** of weak convergence. If `μ_n ⇝ ν` and `φ : ℕ → ℕ`
is strictly monotone, then `μ_{φ k} ⇝ ν`. -/
lemma WeakConverges.comp {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    {μ : ℕ → Measure E} {ν : Measure E}
    (h : WeakConverges μ ν) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    WeakConverges (fun k => μ (φ k)) ν :=
  fun f => (h f).comp hφ.tendsto_atTop

/-- **Weak-limit uniqueness** on a Polish-adjacent Borel space. If a sequence of
measures weakly converges to two finite measures, they agree. Pure consequence of
`ext_of_forall_integral_eq_of_IsFiniteMeasure` + `tendsto_nhds_unique`. -/
lemma WeakConverges.unique
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    [HasOuterApproxClosed E]
    {μ : ℕ → Measure E} {ν ν' : Measure E}
    [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h₁ : WeakConverges μ ν) (h₂ : WeakConverges μ ν') :
    ν = ν' :=
  MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
    (fun f => tendsto_nhds_unique (h₁ f) (h₂ f))

/-- **Marginal weak-limit identification**. If `μ_n ⇝ π` jointly on `E × F` and
`(μ_n.map snd) ⇝ ν` on `F`, then `π.map Prod.snd = ν`. Proof: continuous-mapping
gives `(μ_n.map snd) ⇝ π.map snd`, then apply weak-limit uniqueness. -/
lemma WeakConverges.snd_eq
    {E F : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [MeasurableSpace F] [TopologicalSpace F] [PseudoMetricSpace F]
    [BorelSpace F] [HasOuterApproxClosed F]
    {μ : ℕ → Measure (E × F)} {π : Measure (E × F)} [IsFiniteMeasure π]
    {ν : Measure F} [IsFiniteMeasure ν]
    (hπ : WeakConverges μ π)
    (hν : WeakConverges (fun n => (μ n).map Prod.snd) ν) :
    π.map Prod.snd = ν :=
  have : IsFiniteMeasure (π.map Prod.snd) :=
    MeasureTheory.Measure.isFiniteMeasure_map π Prod.snd
  WeakConverges.unique (hπ.map continuous_snd measurable_snd) hν

/-- **Weak-conv composition with a Feller Markov kernel** (vdV §8.5, Le Cam
representation, kernel form).

If a sequence of probability measures `μ_n` on `α` weakly converges to `ν` on
`α`, and `κ : Kernel α β` is a Markov kernel that is *Feller continuous* (i.e.
the map `a ↦ (κ a : ProbabilityMeasure β)` is continuous from the topology of
`α` to the weak topology on `ProbabilityMeasure β`), then the measure-kernel
binds `μ_n.bind κ` weakly converge to `ν.bind κ` on `β`.

The Markov typeclass `hκ_Markov` keeps `bind` of a probability measure a probability
measure. The bundled `ProbabilityMeasure`-valued map `κPM` (with agreement `hκPM`)
lets the Feller continuity hypothesis live on the bundled subtype without per-call
coercion gymnastics. Feller continuity `hκ_feller` is the canonical formulation as
continuity into the weak topology of `ProbabilityMeasure`. -/
lemma WeakConverges.bind_kernel
    {α β : Type*}
    [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [PseudoMetricSpace β]
    [OpensMeasurableSpace β] [HasOuterApproxClosed β]
    {μ_n : ℕ → Measure α} {ν : Measure α}
    [∀ n, IsProbabilityMeasure (μ_n n)] [IsProbabilityMeasure ν]
    (hμν : WeakConverges μ_n ν)
    (κ : ProbabilityTheory.Kernel α β) [ProbabilityTheory.IsMarkovKernel κ]
    (κPM : α → ProbabilityMeasure β)
    (hκPM : ∀ a, (κPM a : Measure β) = κ a)
    (hκ_feller : Continuous κPM) :
    WeakConverges (fun n => (μ_n n).bind κ) (ν.bind κ) := by
  intro f
  -- Define g(a) := ∫ x, f x ∂(κ a). We will show that g is bounded continuous and
  -- ∫ f d(ρ.bind κ) = ∫ g dρ for any probability ρ. Then weak convergence of μ_n → ν
  -- applied to g gives the result.
  -- Continuity of g via Feller hypothesis: by
  -- `ProbabilityMeasure.continuous_iff_forall_continuous_integral`, `Continuous κPM`
  -- gives `Continuous (fun a => ∫ x, f x ∂(κPM a : Measure β))`, and `hκPM` rewrites
  -- the underlying measure to `κ a`.
  have hg_cont : Continuous (fun a : α => ∫ x, f x ∂(κ a)) := by
    have := (ProbabilityMeasure.continuous_iff_forall_continuous_integral.mp hκ_feller) f
    -- `this : Continuous (fun a => ∫ x, f x ∂((κPM a) : Measure β))`
    -- Rewrite the integrand using `hκPM`.
    have heq : (fun a : α => ∫ x, f x ∂((κPM a : ProbabilityMeasure β) : Measure β))
        = (fun a : α => ∫ x, f x ∂(κ a)) := by
      funext a; rw [hκPM a]
    rw [heq] at this
    exact this
  -- Pointwise bound: |g a| ≤ ‖f‖ since κ a is a probability measure.
  have hg_bound : ∀ a : α, ‖∫ x, f x ∂(κ a)‖ ≤ ‖f‖ := by
    intro a
    have hμ : IsProbabilityMeasure (κ a) := inferInstance
    have h := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := κ a) (f := fun x => f x) (C := ‖f‖)
      (Filter.Eventually.of_forall (fun x => BoundedContinuousFunction.norm_coe_le_norm f x))
    simpa [measureReal_def, measure_univ] using h
  -- Build the bounded continuous function g : α →ᵇ ℝ.
  let g : α →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨_, hg_cont⟩ (2 * ‖f‖) (fun x y => by
      have hx := hg_bound x
      have hy := hg_bound y
      have : |(∫ z, f z ∂(κ x)) - (∫ z, f z ∂(κ y))| ≤
          |∫ z, f z ∂(κ x)| + |∫ z, f z ∂(κ y)| := abs_sub _ _
      have h1 : |∫ z, f z ∂(κ x)| ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using hx
      have h2 : |∫ z, f z ∂(κ y)| ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using hy
      have := this.trans (add_le_add h1 h2)
      simpa [Real.dist_eq, two_mul] using this)
  -- Rewrite the integrals against `ρ.bind κ` as integrals of `g` against `ρ`.
  -- Step: ρ.bind κ = (ρ ⊗ₘ κ).snd = (ρ ⊗ₘ κ).map Prod.snd, then `integral_map`
  -- + `Measure.integral_compProd` reduces it to ∫ a, ∫ b, f b ∂(κ a) ∂ρ = ∫ a, g a ∂ρ.
  have h_rewrite : ∀ ρ : Measure α, [IsProbabilityMeasure ρ] →
      ∫ y, f y ∂(ρ.bind κ) = ∫ a, g a ∂ρ := by
    intro ρ _
    -- `ρ.bind κ = (ρ ⊗ₘ κ).snd`
    rw [show ρ.bind (κ : α → Measure β) = (ρ.compProd κ).snd from
      (MeasureTheory.Measure.snd_compProd ρ κ).symm]
    -- `(ρ ⊗ₘ κ).snd = (ρ ⊗ₘ κ).map Prod.snd`
    rw [MeasureTheory.Measure.snd]
    -- `∫ y, f y d(ρ ⊗ₘ κ).map snd = ∫ z, f z.2 d(ρ ⊗ₘ κ)`
    rw [MeasureTheory.integral_map measurable_snd.aemeasurable
      f.continuous.aestronglyMeasurable]
    -- Now apply `Measure.integral_compProd`: bounded integrand against a probability
    -- measure on a product is integrable.
    have hfmeas : Measurable (fun z : α × β => f z.2) := by
      exact f.continuous.measurable.comp measurable_snd
    have hinteg : Integrable (fun z : α × β => f z.2) (ρ.compProd κ) := by
      refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
      -- Bounded by ‖f‖ on a finite (probability) measure.
      have : IsProbabilityMeasure (ρ.compProd κ) := by
        have hρ : SFinite ρ := by infer_instance
        infer_instance
      exact MeasureTheory.HasFiniteIntegral.of_bounded
        (C := ‖f‖)
        (Filter.Eventually.of_forall
          (fun z => BoundedContinuousFunction.norm_coe_le_norm f z.2))
    rw [MeasureTheory.Measure.integral_compProd hinteg]
    -- Now `∫ a, ∫ b, f b ∂(κ a) ∂ρ = ∫ a, g a ∂ρ` by definition of `g`.
    rfl
  -- Apply weak convergence to g.
  have htendsto : Tendsto (fun n => ∫ a, g a ∂(μ_n n)) atTop (𝓝 (∫ a, g a ∂ν)) := hμν g
  simp_rw [h_rewrite] at *
  exact htendsto

/-- **Commuting `withDensity` past `Measure.map`**:
`(μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ`, for measurable `φ` and `h`.

Useful for pushing a density through a measurable pushforward — e.g., when a joint
law `π_tilted = π.map φ` is `withDensity`-ed against a function `h` that factors
through `φ`, the calculation can be pulled back to `π` under the composed density. -/
lemma Measure.withDensity_map_eq_map_withDensity
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : MeasureTheory.Measure α) (φ : α → β) (hφ : Measurable φ)
    (h : β → ℝ≥0∞) (hh : Measurable h) :
    (μ.map φ).withDensity h = (μ.withDensity (h ∘ φ)).map φ := by
  refine MeasureTheory.Measure.ext (fun A hA => ?_)
  rw [MeasureTheory.withDensity_apply _ hA,
      MeasureTheory.Measure.map_apply hφ hA,
      MeasureTheory.withDensity_apply _ (hφ hA),
      MeasureTheory.setLIntegral_map hA hh hφ]
  rfl

/-- **Reparametrization of a measure-kernel bind**:
`(μ.map f).bind κ = μ.bind (κ.comap f hf)`.

Pushing forward `μ` by `f` and then averaging `κ` over it is the same as composing
`κ ∘ f` (via `Kernel.comap`) and averaging over the original `μ`. The identity is a
direct consequence of `Measure.bind_apply` + `lintegral_map` + `Kernel.comap_apply'`. -/
lemma Measure.bind_map_eq_bind_comap
    {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ}
    (μ : MeasureTheory.Measure α) (f : α → β) (hf : Measurable f)
    (κ : ProbabilityTheory.Kernel β γ) :
    (μ.map f).bind κ = μ.bind (κ.comap f hf) := by
  refine MeasureTheory.Measure.ext (fun s hs => ?_)
  rw [MeasureTheory.Measure.bind_apply hs κ.aemeasurable,
      MeasureTheory.Measure.bind_apply hs (κ.comap f hf).aemeasurable,
      MeasureTheory.lintegral_map (κ.measurable_coe hs) hf]
  simp_rw [ProbabilityTheory.Kernel.comap_apply' κ hf]

/-- **Tilted-marginal bind through conditional distribution**.

For a joint law `π` on `α × β` with first marginal analyzed conditionally on the
second, let `ν := π.map snd` and `κ := condDistrib fst snd π` (so `κ y` is the
conditional law of the first coordinate given `snd = y`). Then reweighting `ν` by
a density `f : β → ℝ≥0∞` and binding with `κ` equals marginalising the joint tilt:

`(ν.withDensity f).bind κ = (π.withDensity (fun p ↦ f p.2)).map fst`.

This is the measure-theoretic core of vdV §7.10 Step 7 — pushing a density through
the second marginal of a joint law factors through the tilted joint + marginalisation.
It sees use whenever a tilted Gaussian-shift law is re-expressed through a conditional
distribution kernel. -/
theorem Measure.withDensity_bind_condDistrib
    {α β : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    [MeasurableSpace β]
    (π : MeasureTheory.Measure (α × β)) [MeasureTheory.IsFiniteMeasure π]
    (f : β → ℝ≥0∞) (hf : Measurable f) :
    ((π.map Prod.snd).withDensity f).bind
        (ProbabilityTheory.condDistrib Prod.fst Prod.snd π) =
      (π.withDensity (fun p => f p.2)).map Prod.fst := by
  set κ := ProbabilityTheory.condDistrib (Prod.fst : α × β → α) Prod.snd π with hκ_def
  set ν := π.map Prod.snd with hν_def
  haveI : MeasureTheory.IsFiniteMeasure ν := by
    rw [hν_def]; exact MeasureTheory.Measure.isFiniteMeasure_map _ _
  refine MeasureTheory.Measure.ext (fun s hs => ?_)
  -- Measurability utilities.
  have h_κs_meas : Measurable (fun y => κ y s) := κ.measurable_coe hs
  have h_fκs_meas : Measurable (fun y : β => f y * κ y s) := hf.mul h_κs_meas
  -- Compute LHS as a `π`-integral.
  -- `bind_apply` + `lintegral_withDensity_eq_lintegral_mul` gives
  -- `∫⁻ y, f y * κ y s ∂ν`, then `lintegral_map` pulls back to `π`.
  have h_lhs :
      (((ν.withDensity f).bind κ)) s =
        ∫⁻ p : α × β, f p.2 * κ p.2 s ∂π := by
    rw [MeasureTheory.Measure.bind_apply hs κ.aemeasurable,
        MeasureTheory.lintegral_withDensity_eq_lintegral_mul _ hf h_κs_meas,
        hν_def]
    -- The integrand `(f * (κ · s)) y` is definitionally `f y * κ y s`; force the
    -- β-reduction via `change` so `lintegral_map` can match the measurable integrand.
    change ∫⁻ (y : β), f y * κ y s ∂(π.map Prod.snd) =
      ∫⁻ (p : α × β), f p.2 * κ p.2 s ∂π
    rw [MeasureTheory.lintegral_map h_fκs_meas measurable_snd]
  -- Compute RHS as a `π`-integral (order: `f p.2 * indicator`, matches compProd output).
  have h_rhs :
      ((π.withDensity (fun p : α × β => f p.2)).map Prod.fst) s =
        ∫⁻ p : α × β, f p.2 * s.indicator (1 : α → ℝ≥0∞) p.1 ∂π := by
    rw [MeasureTheory.Measure.map_apply measurable_fst hs,
        MeasureTheory.withDensity_apply _ (measurable_fst hs),
        ← MeasureTheory.lintegral_indicator (measurable_fst hs)]
    apply MeasureTheory.lintegral_congr
    intro p
    by_cases h_in : p.1 ∈ s
    · rw [Set.indicator_of_mem (show p ∈ Prod.fst ⁻¹' s from h_in),
          Set.indicator_of_mem h_in]
      simp
    · rw [Set.indicator_of_notMem (show p ∉ Prod.fst ⁻¹' s from h_in),
          Set.indicator_of_notMem h_in]
      simp
  -- Bridge via `compProd`: key identity `(π.map snd).compProd κ = π.map swap`.
  have h_compProd :
      ν.compProd κ = π.map (fun p : α × β => (p.2, p.1)) := by
    rw [hν_def, hκ_def]
    exact ProbabilityTheory.compProd_map_condDistrib measurable_fst.aemeasurable
  -- Build the common value `∫⁻ q : β × α, f q.1 * s.indicator 1 q.2 ∂(ν.compProd κ)`.
  have h_bridge :
      ∫⁻ p : α × β, f p.2 * κ p.2 s ∂π =
        ∫⁻ p : α × β, f p.2 * s.indicator (1 : α → ℝ≥0∞) p.1 ∂π := by
    -- Define `g : β × α → ℝ≥0∞` to be `fun q ↦ f q.1 * s.indicator 1 q.2`.
    set g : β × α → ℝ≥0∞ := fun q => f q.1 * s.indicator (1 : α → ℝ≥0∞) q.2 with hg_def
    have hg_meas : Measurable g := by
      refine Measurable.mul (hf.comp measurable_fst) ?_
      exact ((measurable_one.indicator hs).comp measurable_snd)
    -- LHS, expressed as a compProd integral.
    have h_L :
        ∫⁻ p : α × β, f p.2 * κ p.2 s ∂π =
          ∫⁻ q : β × α, g q ∂(ν.compProd κ) := by
      rw [MeasureTheory.Measure.lintegral_compProd hg_meas]
      -- RHS: ∫⁻ y, ∫⁻ x, g (y, x) dκ y ∂ν = ∫⁻ y, ∫⁻ x, f y * s.indicator 1 x dκ y ∂ν
      have h1 : (fun y : β =>
          ∫⁻ x : α, g (y, x) ∂κ y) = fun y => f y * κ y s := by
        funext y
        simp only [hg_def]
        rw [MeasureTheory.lintegral_const_mul _ ((measurable_one.indicator hs))]
        rw [MeasureTheory.lintegral_indicator_one hs]
      rw [h1]
      -- Now ∫⁻ y, f y * κ y s ∂ν = ∫⁻ p, f p.2 * κ p.2 s ∂π
      rw [hν_def, MeasureTheory.lintegral_map h_fκs_meas measurable_snd]
    -- RHS, via the compProd → π.map swap substitution. After map-pullback the
    -- integrand evaluates to `g (p.2, p.1) = f p.2 * s.indicator 1 p.1`, matching RHS.
    have h_R :
        ∫⁻ p : α × β, f p.2 * s.indicator (1 : α → ℝ≥0∞) p.1 ∂π =
          ∫⁻ q : β × α, g q ∂(ν.compProd κ) := by
      rw [h_compProd,
          MeasureTheory.lintegral_map hg_meas
            (measurable_snd.prodMk measurable_fst)]
    rw [h_L, ← h_R]
  rw [h_lhs, h_rhs, h_bridge]

namespace Contiguity

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- **Contiguity** (van der Vaart §6.3). A family `Q` is contiguous with respect to `P`
along filter `l` (written informally `Q ⊲ P`) if any sequence of measurable events whose
`P`-probabilities tend to 0 also has `Q`-probabilities tending to 0. -/
def Contiguous (l : Filter ι) (P Q : ∀ i, Measure (Ω i)) : Prop :=
  ∀ A : ∀ i, Set (Ω i), (∀ i, MeasurableSet (A i)) →
    Tendsto (fun i => (P i) (A i)) l (𝓝 0) →
    Tendsto (fun i => (Q i) (A i)) l (𝓝 0)

/-- **Mutual contiguity**: both directions. -/
def MutuallyContiguous (l : Filter ι) (P Q : ∀ i, Measure (Ω i)) : Prop :=
  Contiguous l P Q ∧ Contiguous l Q P

lemma Contiguous.refl (l : Filter ι) (P : ∀ i, Measure (Ω i)) :
    Contiguous l P P := fun _ _ h => h

lemma Contiguous.trans {l : Filter ι} {P Q R : ∀ i, Measure (Ω i)}
    (h₁ : Contiguous l P Q) (h₂ : Contiguous l Q R) :
    Contiguous l P R := fun A hA hP => h₂ A hA (h₁ A hA hP)

lemma MutuallyContiguous.symm {l : Filter ι} {P Q : ∀ i, Measure (Ω i)}
    (h : MutuallyContiguous l P Q) : MutuallyContiguous l Q P :=
  ⟨h.2, h.1⟩

/-! ## Le Cam's first lemma — asymptotic log normality criterion

vdV Example 6.5. If the log-likelihood ratio `log dQ_n/dP_n` is asymptotically normal
under `P_n` with mean `-σ²/2` and variance `σ²`, then `P_n ⊲⊳ Q_n`.

The direction `Q ⊲ P` is proved via a uniform-integrability argument; the
mutual-contiguity version follows by applying the same machinery to `(-log dQ/dP)`
under `Q`.
-/

section LeCamFirst

/-- **Gaussian mgf at 1**: `∫ exp(x) dN(-v/2, v) = 1`. This is the multiplicative
normalization underlying Le Cam 1 — if `W ~ N(-v/2, v)`, then `E[exp W] = 1`, which is
exactly what keeps the likelihood ratio's mass normalized. -/
private lemma integral_exp_gaussianReal_neg_half_var (v : NNReal) :
    ∫ x, Real.exp x ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) = 1 := by
  have hX :
      Measure.map (id : ℝ → ℝ) (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)
        = ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v :=
    Measure.map_id
  have h := ProbabilityTheory.mgf_gaussianReal hX 1
  rw [ProbabilityTheory.mgf] at h
  simp only [one_mul, id_eq] at h
  rw [show (-(v : ℝ) / 2 * 1 + (v : ℝ) * 1 ^ 2 / 2 : ℝ) = 0 by ring, Real.exp_zero] at h
  exact h

/-- Truncated exponential `min(exp x, M)` as a bounded continuous function, for `M ≥ 0`. -/
private noncomputable def truncExpBCF (M : ℝ) (hM : 0 ≤ M) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min (Real.exp x) M)
    (Real.continuous_exp.min continuous_const)
    M
    (fun x => by
      rw [Real.norm_eq_abs]
      have h_nonneg : 0 ≤ min (Real.exp x) M :=
        le_min (Real.exp_pos x).le hM
      rw [abs_of_nonneg h_nonneg]
      exact min_le_right _ _)

@[simp] private lemma truncExpBCF_apply (M : ℝ) (hM : 0 ≤ M) (x : ℝ) :
    truncExpBCF M hM x = min (Real.exp x) M := rfl

/-- As `M → ∞` (over naturals), `∫ min(exp x, M) dN(-v/2, v) → 1`.

Dominated convergence: `min(exp x, M) ↑ exp x` pointwise, dominated by `exp x` which is
integrable under the log-normal-tilt Gaussian (mgf exists at 1). The limit equals
`∫ exp = 1` by the Gaussian mgf. -/
private lemma tendsto_integral_truncExp_gaussianReal (v : NNReal) :
    Tendsto
      (fun M : ℕ =>
        ∫ x, min (Real.exp x) (M : ℝ) ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))
      atTop (𝓝 1) := by
  set ν : Measure ℝ := ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v with hν_def
  have h_exp_int : Integrable (fun x => Real.exp x) ν := by
    have := ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := -(v : ℝ) / 2) (v := v) 1
    simpa using this
  have h_lim : ∀ᵐ x ∂ν,
      Tendsto (fun M : ℕ => min (Real.exp x) (M : ℝ)) atTop (𝓝 (Real.exp x)) := by
    refine Eventually.of_forall (fun x => ?_)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌈Real.exp x⌉₊] with M hM
    have : Real.exp x ≤ (M : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hM)
    exact (min_eq_left this).symm
  have h_dom : ∀ M : ℕ, ∀ᵐ x ∂ν, ‖min (Real.exp x) (M : ℝ)‖ ≤ Real.exp x := by
    intro M
    refine Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs]
    have h_nonneg : 0 ≤ min (Real.exp x) (M : ℝ) :=
      le_min (Real.exp_pos x).le (Nat.cast_nonneg _)
    rw [abs_of_nonneg h_nonneg]
    exact min_le_left _ _
  have h_meas : ∀ M : ℕ, AEStronglyMeasurable (fun x => min (Real.exp x) (M : ℝ)) ν :=
    fun M => (Real.continuous_exp.min continuous_const).aestronglyMeasurable
  have h_tendsto :=
    MeasureTheory.tendsto_integral_of_dominated_convergence (F := fun M x =>
      min (Real.exp x) (M : ℝ)) (f := fun x => Real.exp x) (bound := fun x => Real.exp x)
      h_meas h_exp_int h_dom h_lim
  rw [integral_exp_gaussianReal_neg_half_var] at h_tendsto
  exact h_tendsto

/-- Under `P_n`, `exp(L n)` is integrable, because `(P n).withDensity (exp ∘ L n)` is a
probability measure. -/
private lemma exp_L_integrable
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (n : ℕ) :
    Integrable (fun ω => Real.exp (L n ω)) (P n) := by
  -- `∫⁻ ofReal (exp L) dP = Q n (univ) = 1 < ∞`, so `exp L` is integrable.
  refine ⟨(Real.continuous_exp.measurable.comp (hL_meas n)).aestronglyMeasurable, ?_⟩
  have h_univ : Q n Set.univ = 1 := measure_univ
  rw [hL_is_log_ratio n, MeasureTheory.withDensity_apply _ MeasurableSet.univ] at h_univ
  simp only [Measure.restrict_univ] at h_univ
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal]
  · rw [h_univ]; exact ENNReal.one_lt_top
  · exact Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)

/-- The Bochner integral `∫ exp(L n) dP_n = 1`. -/
private lemma integral_exp_L_eq_one
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (n : ℕ) :
    ∫ ω, Real.exp (L n ω) ∂(P n) = 1 := by
  have h_lintegral : ∫⁻ ω, ENNReal.ofReal (Real.exp (L n ω)) ∂(P n) = 1 := by
    have h_univ : Q n Set.univ = 1 := measure_univ
    rw [hL_is_log_ratio n, MeasureTheory.withDensity_apply _ MeasurableSet.univ] at h_univ
    simpa using h_univ
  have h_integral_eq := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (μ := P n) (f := fun ω => Real.exp (L n ω))
    (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))
    (Real.continuous_exp.measurable.comp (hL_meas n)).aestronglyMeasurable
  rw [h_integral_eq, h_lintegral]
  simp

/-- **For fixed `M ≥ 0`, weak convergence transfers to integrals of the truncated
exponential**: `∫ min(exp(L n), M) dP_n → ∫ min(exp, M) dN(-v/2, v)` as `n → ∞`.

Follows from `WeakConverges` applied to `truncExpBCF M`, after rewriting the map-integral
via `MeasureTheory.integral_map`. -/
private lemma tendsto_integral_truncExp_L
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))
    (M : ℝ) (hM : 0 ≤ M) :
    Tendsto
      (fun n => ∫ ω, min (Real.exp (L n ω)) M ∂(P n)) atTop
      (𝓝 (∫ x, min (Real.exp x) M ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v))) := by
  have h_bcf := h_weak (truncExpBCF M hM)
  -- Use `integral_map` to swap `(P n).map (L n)` integrals back to integrals in `P n`.
  have h_map_n : ∀ n,
      ∫ x, truncExpBCF M hM x ∂((P n).map (L n))
        = ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    intro n
    rw [MeasureTheory.integral_map (hL_meas n).aemeasurable
        (truncExpBCF M hM).continuous.aestronglyMeasurable]
    simp
  simp only [h_map_n] at h_bcf
  simpa using h_bcf

/-- **Uniform-integrability bound on `exp(L n)` under `P_n`**: for every `ε > 0` there
exist a truncation level `M` and an index `N₀` such that `∫ (exp(L n) - M)⁺ dP_n ≤ ε`
for all `n ≥ N₀`, where `(·)⁺ x = max 0 x`.

Proof idea: by `tendsto_integral_truncExp_gaussianReal` pick a natural `M` so that
`∫ min(exp, M) dN > 1 - ε/2`; by `tendsto_integral_truncExp_L` pick `N₀` so that for
`n ≥ N₀`, `∫ min(exp(L n), M) dP_n > 1 - ε`; and use `∫ exp(L n) dP_n = 1` to rearrange.

Lets downstream consumers derive the Le Cam 3 uniform-integrability hypothesis from
the log-normal weak convergence already in scope. -/
lemma uniform_integrability_exp_L
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε := by
  intro ε hε
  -- Step 1: pick a natural M₀ with `∫ min(exp, M₀) dN ≥ 1 - ε/2`.
  have h_gaussian := tendsto_integral_truncExp_gaussianReal v
  have h_ev :
      ∀ᶠ M : ℕ in atTop,
        1 - ε / 2 ≤
          ∫ x, min (Real.exp x) (M : ℝ)
            ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
    have h_mem : Set.Ici (1 - ε / 2) ∈ 𝓝 (1 : ℝ) :=
      Ici_mem_nhds (by linarith)
    exact h_gaussian h_mem
  obtain ⟨M₀, hM₀⟩ := h_ev.exists
  set M : ℝ := (M₀ : ℝ) with hM_def
  have hM_nonneg : 0 ≤ M := Nat.cast_nonneg _
  refine ⟨M, hM_nonneg, ?_⟩
  -- Step 2: for fixed M, get `∫ min(exp(L n), M) dP_n → ∫ min(exp, M) dN`.
  have h_trunc_tendsto :=
    tendsto_integral_truncExp_L P L hL_meas v h_weak M hM_nonneg
  -- Step 3: pick N₀ so that for n ≥ N₀, `∫ min(exp(L n), M) dP_n > 1 - ε`.
  have h_target :
      ∀ᶠ n : ℕ in atTop,
        1 - ε ≤ ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    have h_mem : Set.Ioi (1 - ε) ∈ 𝓝 (∫ x, min (Real.exp x) M
        ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) := by
      apply Ioi_mem_nhds
      linarith [hM₀]
    filter_upwards [h_trunc_tendsto h_mem] with n hn
    exact le_of_lt (Set.mem_Ioi.mp hn)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_target
  refine ⟨N₀, ?_⟩
  intro n hn
  -- Step 4: rearrange using `∫ exp(L n) = 1`.
  have h_exp_int := exp_L_integrable P Q L hL_meas hL_is_log_ratio n
  have h_trunc_int : Integrable (fun ω => min (Real.exp (L n ω)) M) (P n) := by
    refine h_exp_int.mono' ?_ ?_
    · exact ((Real.continuous_exp.measurable.comp
        (hL_meas n)).min measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact min_le_left _ _
      · exact le_min (Real.exp_pos _).le hM_nonneg
  have h_diff_eq :
      ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
        = 1 - ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    rw [MeasureTheory.integral_sub h_exp_int h_trunc_int,
      integral_exp_L_eq_one P Q L hL_meas hL_is_log_ratio]
  rw [h_diff_eq]
  linarith [hN₀ n hn]

/-- **Contiguity from asymptotic log-normality** (vdV Example 6.5, direction `Q ⊲ P`).

If `L n = log dQ_n/dP_n` is asymptotically `N(-σ²/2, σ²)` under `P n`, then for any
sequence of measurable events `A n` with `P_n(A_n) → 0`, we also have `Q_n(A_n) → 0`. -/
theorem contiguous_of_asymptotically_log_normal
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    Contiguous (ι := ℕ) (Ω := Ω) atTop P Q := by
  intro A hA_meas hA_tendsto
  -- Step 0: reduce to real-valued convergence via `.toReal`.
  -- `Q_n`, `P_n` are prob measures so `(Q n)(A n), (P n)(A n) < ⊤` always.
  have h_Q_lt_top : ∀ n, (Q n) (A n) ≠ ⊤ := fun n => (measure_lt_top (Q n) _).ne
  have h_P_lt_top : ∀ n, (P n) (A n) ≠ ⊤ := fun n => (measure_lt_top (P n) _).ne
  have hA_real : Tendsto (fun n => ((P n) (A n)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hA_tendsto
    simpa using this
  suffices h : Tendsto (fun n => ((Q n) (A n)).toReal) atTop (𝓝 0) by
    have h_of_real :
        Tendsto (fun n => ENNReal.ofReal ((Q n) (A n)).toReal) atTop (𝓝 0) := by
      have h_comp := (ENNReal.continuous_ofReal.tendsto 0).comp h
      simp only [ENNReal.ofReal_zero] at h_comp
      exact h_comp
    have h_eq : (fun n => ENNReal.ofReal ((Q n) (A n)).toReal) = fun n => (Q n) (A n) := by
      funext n; rw [ENNReal.ofReal_toReal (h_Q_lt_top n)]
    rw [h_eq] at h_of_real
    exact h_of_real
  -- Now prove the real-valued version.
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- UI: get M and N₁ with `∫ (exp(L n) - min(exp(L n), M)) dP_n ≤ ε/2` for `n ≥ N₁`.
  obtain ⟨M, hM_nonneg, N₁, hN₁⟩ :=
    uniform_integrability_exp_L P Q L hL_meas hL_is_log_ratio v h_weak (ε / 2) (by linarith)
  have hM1_pos : 0 < M + 1 := by linarith
  -- Pick `N₂` so for `n ≥ N₂`, `((P n) (A n)).toReal < ε / (2·(M+1))`.
  rw [Metric.tendsto_nhds] at hA_real
  have h_threshold : 0 < ε / (2 * (M + 1)) := by positivity
  have hA_ev := hA_real (ε / (2 * (M + 1))) h_threshold
  rw [Filter.eventually_atTop] at hA_ev
  obtain ⟨N₂, hN₂⟩ := hA_ev
  rw [Filter.eventually_atTop]
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  -- Unfold `dist (·) 0` for the nonneg real `((Q n)(A n)).toReal`.
  have hQ_nonneg : 0 ≤ ((Q n) (A n)).toReal := ENNReal.toReal_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hQ_nonneg]
  -- Express `((Q n) (A n)).toReal` as a set Bochner integral of `exp(L n)`.
  have h_Q_eq : ((Q n) (A n)).toReal = ∫ ω in A n, Real.exp (L n ω) ∂(P n) := by
    rw [hL_is_log_ratio n, MeasureTheory.withDensity_apply _ (hA_meas n)]
    exact (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))
      (Real.continuous_exp.measurable.comp (hL_meas n)).aestronglyMeasurable).symm
  -- Integrability of `exp(L n)` and its truncation / residue.
  have h_exp_int := exp_L_integrable P Q L hL_meas hL_is_log_ratio n
  have h_min_meas : Measurable (fun ω => min (Real.exp (L n ω)) M) :=
    (Real.continuous_exp.measurable.comp (hL_meas n)).min measurable_const
  have h_min_int : Integrable (fun ω => min (Real.exp (L n ω)) M) (P n) := by
    refine h_exp_int.mono' h_min_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.exp_pos _).le hM_nonneg)]
    exact min_le_left _ _
  have h_diff_int : Integrable
      (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M) (P n) :=
    h_exp_int.sub h_min_int
  have h_diff_nonneg :
      0 ≤ᵐ[P n] fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M :=
    Filter.Eventually.of_forall
      (fun ω => sub_nonneg.mpr (min_le_left _ _))
  -- Decompose the set integral.
  have h_int_decomp :
      ∫ ω in A n, Real.exp (L n ω) ∂(P n)
        = ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n)
          + ∫ ω in A n, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) := by
    rw [← MeasureTheory.integral_add h_min_int.restrict h_diff_int.restrict]
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    ring
  -- Bound Term 1: `∫ in A n, min(exp, M) ≤ M · P_n(A_n).real`.
  have h_T1_bound :
      ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n) ≤ M * ((P n) (A n)).toReal := by
    calc ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n)
        ≤ ∫ _ in A n, M ∂(P n) := by
          refine MeasureTheory.setIntegral_mono_on h_min_int.restrict
            (integrable_const M).restrict (hA_meas n) (fun ω _ => ?_)
          exact min_le_right _ _
      _ = ((P n) (A n)).toReal * M := by
          rw [MeasureTheory.setIntegral_const]
          rfl
      _ = M * ((P n) (A n)).toReal := by ring
  -- Bound Term 2: restrict ≤ full, then UI.
  have h_T2_bound :
      ∫ ω in A n, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε / 2 :=
    le_trans (MeasureTheory.setIntegral_le_integral h_diff_int h_diff_nonneg) (hN₁ n hn₁)
  -- Convert hN₂ from dist form to a direct inequality.
  have hP_A_real_lt : ((P n) (A n)).toReal < ε / (2 * (M + 1)) := by
    have := hN₂ n hn₂
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at this
    exact this
  -- Assemble: `((Q n)(A n)).toReal ≤ M · P_n(A_n).real + ε/2`, then show this is `< ε`.
  have h_total_le :
      ((Q n) (A n)).toReal ≤ M * ((P n) (A n)).toReal + ε / 2 := by
    calc ((Q n) (A n)).toReal
        = ∫ ω in A n, Real.exp (L n ω) ∂(P n) := h_Q_eq
      _ = ∫ ω in A n, min (Real.exp (L n ω)) M ∂(P n)
            + ∫ ω in A n, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) :=
            h_int_decomp
      _ ≤ M * ((P n) (A n)).toReal + ε / 2 := by
            linarith [h_T1_bound, h_T2_bound]
  -- Now `M · ((P n)(A n)).toReal + ε/2 < ε`, by case on `M = 0` / `M > 0`.
  rcases eq_or_lt_of_le hM_nonneg with hM_eq | hM_pos
  · -- `M = 0`: LHS = ε/2 < ε.
    have : M * ((P n) (A n)).toReal = 0 := by rw [← hM_eq]; ring
    linarith
  · -- `M > 0`: use strict `hP_A_real_lt` and the `M/(M+1) ≤ 1` bound.
    have h_strict_T1 : M * ((P n) (A n)).toReal < M * (ε / (2 * (M + 1))) :=
      mul_lt_mul_of_pos_left hP_A_real_lt hM_pos
    have h_factor_le_half : M * (ε / (2 * (M + 1))) ≤ ε / 2 := by
      have h_ratio : M / (M + 1) ≤ 1 := (div_le_one hM1_pos).mpr (by linarith)
      have hε2_nonneg : 0 ≤ ε / 2 := by linarith
      calc M * (ε / (2 * (M + 1)))
          = (M / (M + 1)) * (ε / 2) := by field_simp
        _ ≤ 1 * (ε / 2) := mul_le_mul_of_nonneg_right h_ratio hε2_nonneg
        _ = ε / 2 := one_mul _
    linarith

end LeCamFirst

section ReverseDirection

/-- **Inverse-density identity**: if `Q = P.withDensity (ofReal ∘ exp ∘ L)` with
`exp ∘ L > 0` pointwise, then `P = Q.withDensity (ofReal ∘ exp ∘ (-L))`.

Follows from `MeasureTheory.withDensity_inv_same` applied to `f = ofReal ∘ exp ∘ L`,
using that `exp > 0` (so `f` is nonzero a.e.) and `ofReal r < ⊤` (so `f ≠ ⊤` a.e.),
plus `(ofReal (exp x))⁻¹ = ofReal (exp (-x))`. -/
private lemma P_eq_Q_withDensity_neg
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (n : ℕ) :
    P n = (Q n).withDensity (fun ω => ENNReal.ofReal (Real.exp (-L n ω))) := by
  have hf_meas : Measurable (fun ω => ENNReal.ofReal (Real.exp (L n ω))) :=
    (Real.continuous_exp.measurable.comp (hL_meas n)).ennreal_ofReal
  have hf_ne_zero : ∀ᵐ ω ∂(P n), ENNReal.ofReal (Real.exp (L n ω)) ≠ 0 := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  have hf_ne_top : ∀ᵐ ω ∂(P n), ENNReal.ofReal (Real.exp (L n ω)) ≠ ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_ne_top)
  have h_inv := MeasureTheory.withDensity_inv_same hf_meas hf_ne_zero hf_ne_top
  -- `h_inv : ((P n).withDensity f).withDensity (fun ω => (f ω)⁻¹) = P n`
  rw [← hL_is_log_ratio n] at h_inv
  rw [← h_inv]
  congr 1
  funext ω
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), Real.exp_neg]

/-! ### Gaussian shift identity

The algebraic backbone of the reverse direction. Tilting `N(-v/2, v)` by `exp` yields
`N(v/2, v)`; reflecting `N(v/2, v)` through 0 yields `N(-v/2, v)` back. The net effect
is the integral identity `∫ f(-x) · exp(x) dN(-v/2, v) = ∫ f(y) dN(-v/2, v)`.
-/

/-- **Gaussian PDF multiplicative shift by `exp`**.

`gaussianPDFReal (-v/2) v x · exp(x) = gaussianPDFReal (v/2) v x`.

This is the pointwise algebraic identity underlying the measure identity
`N(-v/2, v).withDensity (exp) = N(v/2, v)`. Proved by expanding both sides to the
common form `(2πv)^{-1/2} · exp(-x²/(2v) + x/2 - v/8)` via `Real.exp_add` + field algebra. -/
private lemma gaussianPDFReal_neg_half_mul_exp_eq (v : NNReal) (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal (-(v : ℝ) / 2) v x * Real.exp x
      = ProbabilityTheory.gaussianPDFReal ((v : ℝ) / 2) v x := by
  by_cases hv : v = 0
  · subst hv
    simp [ProbabilityTheory.gaussianPDFReal_zero_var]
  have hv_pos : (0 : ℝ) < (v : ℝ) := by
    refine lt_of_le_of_ne v.coe_nonneg (Ne.symm ?_)
    intro h
    exact hv (NNReal.coe_injective h)
  have h2v_ne : (2 : ℝ) * (v : ℝ) ≠ 0 := by positivity
  simp only [ProbabilityTheory.gaussianPDFReal]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  field_simp
  ring

/-- **Gaussian tilting by `exp`**:
`(N(-v/2, v)).withDensity (x ↦ ofReal (exp x)) = N(v/2, v)`.

For `v = 0`, both sides reduce to `dirac 0` (using `dirac_withDensity` + `exp 0 = 1`).
For `v > 0`, unfold `gaussianReal` to `volume.withDensity (gaussianPDF …)`, combine the
two `withDensity` layers via `withDensity_mul`, and close by the pointwise PDF identity. -/
private lemma gaussianReal_neg_half_withDensity_exp (v : NNReal) :
    (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v).withDensity
        (fun x => ENNReal.ofReal (Real.exp x)) =
      ProbabilityTheory.gaussianReal ((v : ℝ) / 2) v := by
  by_cases hv : v = 0
  · subst hv
    simp only [NNReal.coe_zero, neg_zero, zero_div, ProbabilityTheory.gaussianReal_zero_var,
      MeasureTheory.dirac_withDensity, Real.exp_zero, ENNReal.ofReal_one, one_smul]
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ hv,
      ProbabilityTheory.gaussianReal_of_var_ne_zero _ hv]
  rw [← MeasureTheory.withDensity_mul _
      (ProbabilityTheory.measurable_gaussianPDF _ _)
      Real.continuous_exp.measurable.ennreal_ofReal]
  congr 1
  ext x
  simp only [Pi.mul_apply, ProbabilityTheory.gaussianPDF]
  rw [← ENNReal.ofReal_mul (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)]
  congr 1
  exact gaussianPDFReal_neg_half_mul_exp_eq v x

/-- **Gaussian shift integral identity**:
`∫ f(-x) · exp(x) dN(-v/2, v) = ∫ f dN(-v/2, v)` for bounded continuous `f`.

Chain: tilt `N(-v/2, v)` by `exp` → `N(v/2, v)` (via `gaussianReal_neg_half_withDensity_exp`);
reflect `N(v/2, v)` through 0 → `N(-v/2, v)` (via `gaussianReal_map_neg`). -/
private lemma integral_gaussianReal_neg_half_shift (v : NNReal) (f : ℝ →ᵇ ℝ) :
    ∫ x, f (-x) * Real.exp x ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)
      = ∫ x, f x ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
  set ν_neg := ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v with hν_neg
  set ν_pos := ProbabilityTheory.gaussianReal ((v : ℝ) / 2) v with hν_pos
  have hexp_meas : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp x)) :=
    Real.continuous_exp.measurable.ennreal_ofReal
  have hexp_lt_top : ∀ᵐ x ∂ν_neg, ENNReal.ofReal (Real.exp x) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  calc ∫ x, f (-x) * Real.exp x ∂ν_neg
      = ∫ x, (ENNReal.ofReal (Real.exp x)).toReal • f (-x) ∂ν_neg := by
        refine integral_congr_ae ?_
        refine Filter.Eventually.of_forall (fun x => ?_)
        change f (-x) * Real.exp x = (ENNReal.ofReal (Real.exp x)).toReal • f (-x)
        rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
    _ = ∫ x, f (-x) ∂(ν_neg.withDensity (fun x => ENNReal.ofReal (Real.exp x))) :=
        (integral_withDensity_eq_integral_toReal_smul hexp_meas hexp_lt_top
          (fun x => f (-x))).symm
    _ = ∫ x, f (-x) ∂ν_pos := by
        rw [hν_neg, hν_pos, gaussianReal_neg_half_withDensity_exp]
    _ = ∫ y, f y ∂(ν_pos.map (fun x => -x)) :=
        (MeasureTheory.integral_map measurable_neg.aemeasurable
          f.continuous.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(ProbabilityTheory.gaussianReal (-((v : ℝ) / 2)) v) := by
        rw [hν_pos, ProbabilityTheory.gaussianReal_map_neg]
    _ = ∫ x, f x ∂ν_neg := by
        rw [hν_neg, neg_div]

/-- **Change of measure helper**: `∫ f ∂(Q.map (-L)) = ∫ f(-x)·exp x ∂(P.map L)`,
using `Q = P.withDensity (exp ∘ L)` plus `integral_map` on both ends. -/
private lemma integral_f_neg_Q_eq_f_neg_exp_P
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω)
    (L : Ω → ℝ) (hL_meas : Measurable L)
    (hL_is_log_ratio :
        Q = P.withDensity (fun ω => ENNReal.ofReal (Real.exp (L ω))))
    (f : ℝ →ᵇ ℝ) :
    ∫ x, f x ∂(Q.map (fun ω => -L ω))
      = ∫ x, f (-x) * Real.exp x ∂(P.map L) := by
  have h_exp_meas : Measurable (fun ω => ENNReal.ofReal (Real.exp (L ω))) :=
    (Real.continuous_exp.measurable.comp hL_meas).ennreal_ofReal
  have h_exp_lt_top : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (L ω)) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have h_integrand_meas :
      AEStronglyMeasurable (fun x : ℝ => f (-x) * Real.exp x) (P.map L) :=
    ((f.continuous.comp continuous_neg).mul Real.continuous_exp).aestronglyMeasurable
  calc ∫ x, f x ∂(Q.map (fun ω => -L ω))
      = ∫ ω, f (-L ω) ∂Q :=
        MeasureTheory.integral_map hL_meas.neg.aemeasurable
          f.continuous.aestronglyMeasurable
    _ = ∫ ω, f (-L ω)
          ∂(P.withDensity (fun ω => ENNReal.ofReal (Real.exp (L ω)))) := by
        rw [← hL_is_log_ratio]
    _ = ∫ ω, (ENNReal.ofReal (Real.exp (L ω))).toReal • f (-L ω) ∂P :=
        integral_withDensity_eq_integral_toReal_smul h_exp_meas h_exp_lt_top
          (fun ω => f (-L ω))
    _ = ∫ ω, f (-L ω) * Real.exp (L ω) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
        change (ENNReal.ofReal (Real.exp (L ω))).toReal • f (-L ω)
          = f (-L ω) * Real.exp (L ω)
        rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
    _ = ∫ x, f (-x) * Real.exp x ∂(P.map L) :=
        (MeasureTheory.integral_map hL_meas.aemeasurable h_integrand_meas).symm

/-- **Tilted weak convergence**: under the tilted measure `Q n = P n.withDensity (exp ∘ L n)`,
the law of `-L n` weakly converges to `N(-v/2, v)`.

**Strategy** (the analytical content, broken into steps):

1. `integral_f_neg_Q_eq_f_neg_exp_P` rewrites `∫ f d((Q n).map (-L n))` as
   `∫ f(-x)·exp x d((P n).map L n)` (change of measure + `integral_map`).
2. `integral_gaussianReal_neg_half_shift` rewrites the target
   `∫ f dN(-v/2, v)` as `∫ f(-x)·exp x dN(-v/2, v)` — the Gaussian shift identity
   (derived from the PDF identity `gaussianPDFReal_neg_half_mul_exp_eq` +
   `gaussianReal_neg_half_withDensity_exp` + `gaussianReal_map_neg`).
3. Convergence of `∫ f(-x)·exp x dν_n → ∫ f(-x)·exp x dν` for `ν_n := (P n).map L n`
   follows from the truncation+UI argument: let
   `g_M(x) := f(-x) · min(exp x, M)` (bounded continuous),
   then
   - `|∫ f(-x)·exp x dν_n - ∫ g_M dν_n| ≤ ‖f‖ · ∫ (exp x - min(exp x, M)) dν_n`
     = `‖f‖ · ∫ (exp(L n) - min(exp(L n), M)) dP_n`, ≤ `ε/(3C)` by `uniform_integrability_exp_L`;
   - `|∫ g_M dν_n - ∫ g_M dν| < ε/3` by weak convergence of `ν_n ⇝ ν` applied to `g_M`;
   - `|∫ g_M dν - ∫ f(-x)·exp x dν| ≤ ‖f‖ · (1 - ∫ min(exp x, M) dν)`,
     ≤ `ε/(3C)` by `tendsto_integral_truncExp_gaussianReal` + choice of `M`.

   Triangle inequality closes with total `< ε`. -/
private lemma weakConverges_Q_neg_L_gaussianReal_neg_half
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    WeakConverges (fun n => (Q n).map (fun ω => -L n ω))
      (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
  intro f
  set ν := ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v with hν_def
  -- Rewrite target via Gaussian shift identity, each LHS term via change-of-measure.
  rw [← integral_gaussianReal_neg_half_shift v f]
  have h_rewrite : ∀ n, ∫ x, f x ∂((Q n).map (fun ω => -L n ω))
      = ∫ x, f (-x) * Real.exp x ∂((P n).map (L n)) := fun n =>
    integral_f_neg_Q_eq_f_neg_exp_P (P n) (Q n) (L n) (hL_meas n) (hL_is_log_ratio n) f
  simp_rw [h_rewrite]
  -- Continuity + norm bounds used throughout.
  have hfneg_cont : Continuous (fun x : ℝ => f (-x)) := f.continuous.comp continuous_neg
  have hfneg_bound : ∀ x : ℝ, ‖f (-x)‖ ≤ ‖f‖ := fun x => f.norm_coe_le_norm _
  have h_exp_nonneg : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos _).le
  -- Gaussian side: `∫ exp dν = 1`, `exp` integrable, and `tendsto ∫ min(exp, M) → 1` as M → ∞.
  have h_exp_int_ν : Integrable (fun x : ℝ => Real.exp x) ν := by
    rw [hν_def]
    have := ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := -(v : ℝ) / 2) (v := v) 1
    simpa using this
  have h_exp_int_ν_eq_one : ∫ x, Real.exp x ∂ν = 1 := by
    rw [hν_def]; exact integral_exp_gaussianReal_neg_half_var v
  -- Helper: residue bound for `|∫ f(-x) · exp x ∂μ - ∫ f(-x) · min(exp, M) ∂μ|`,
  -- `≤ ‖f‖ · ∫ (exp - min) dμ`, for any `μ` on ℝ with `exp` integrable under `μ`.
  have h_residue :
      ∀ (μ : Measure ℝ) (M : ℝ), 0 ≤ M →
        Integrable (fun x : ℝ => Real.exp x) μ →
        |∫ x, f (-x) * Real.exp x ∂μ - ∫ x, f (-x) * min (Real.exp x) M ∂μ|
          ≤ ‖f‖ * ∫ x, (Real.exp x - min (Real.exp x) M) ∂μ := by
    intro μ M hM h_exp_int
    have h_min_nn : ∀ x, 0 ≤ min (Real.exp x) M := fun x =>
      le_min (h_exp_nonneg x) hM
    have h_min_le : ∀ x, min (Real.exp x) M ≤ Real.exp x := fun x => min_le_left _ _
    have h_min_meas : Measurable (fun x : ℝ => min (Real.exp x) M) :=
      Real.continuous_exp.measurable.min measurable_const
    have h_min_int : Integrable (fun x : ℝ => min (Real.exp x) M) μ := by
      refine h_exp_int.mono' h_min_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun x => ?_))
      simp only [Real.norm_eq_abs, abs_of_nonneg (h_min_nn x)]
      exact h_min_le x
    have h_fneg_bound_ae : ∀ᵐ x ∂μ, ‖f (-x)‖ ≤ ‖f‖ :=
      Filter.Eventually.of_forall hfneg_bound
    have h_fneg_ae : AEStronglyMeasurable (fun x : ℝ => f (-x)) μ :=
      hfneg_cont.aestronglyMeasurable
    have h_fexp_int : Integrable (fun x : ℝ => f (-x) * Real.exp x) μ :=
      h_exp_int.bdd_mul h_fneg_ae h_fneg_bound_ae
    have h_fmin_int : Integrable (fun x : ℝ => f (-x) * min (Real.exp x) M) μ :=
      h_min_int.bdd_mul h_fneg_ae h_fneg_bound_ae
    rw [← integral_sub h_fexp_int h_fmin_int]
    have h_diff_eq : (fun x : ℝ => f (-x) * Real.exp x - f (-x) * min (Real.exp x) M)
        = fun x => f (-x) * (Real.exp x - min (Real.exp x) M) := by
      funext x; ring
    rw [h_diff_eq]
    have h_diff_int : Integrable
        (fun x : ℝ => f (-x) * (Real.exp x - min (Real.exp x) M)) μ := by
      have : (fun x : ℝ => f (-x) * (Real.exp x - min (Real.exp x) M))
          = fun x => f (-x) * Real.exp x - f (-x) * min (Real.exp x) M := by
        funext x; ring
      rw [this]; exact h_fexp_int.sub h_fmin_int
    calc |∫ x, f (-x) * (Real.exp x - min (Real.exp x) M) ∂μ|
        ≤ ∫ x, |f (-x) * (Real.exp x - min (Real.exp x) M)| ∂μ :=
          abs_integral_le_integral_abs
      _ = ∫ x, |f (-x)| * (Real.exp x - min (Real.exp x) M) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          change |f (-x) * (Real.exp x - min (Real.exp x) M)|
            = |f (-x)| * (Real.exp x - min (Real.exp x) M)
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (h_min_le x))]
      _ ≤ ∫ x, ‖f‖ * (Real.exp x - min (Real.exp x) M) ∂μ := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall
              (fun x => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (h_min_le x))))
            ((h_exp_int.sub h_min_int).const_mul ‖f‖)
            (Filter.Eventually.of_forall (fun x => ?_))
          refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr (h_min_le x))
          rw [← Real.norm_eq_abs]; exact hfneg_bound x
      _ = ‖f‖ * ∫ x, (Real.exp x - min (Real.exp x) M) ∂μ := integral_const_mul _ _
  -- Setup for ε argument.
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C : ℝ := ‖f‖ + 1 with hC_def
  have hC_pos : 0 < C := by positivity
  have hnorm_le_C : ‖f‖ ≤ C := by simp [hC_def]
  have hthresh_pos : 0 < ε / (3 * C) := by positivity
  -- (A) UI on sequence side.
  obtain ⟨M_UI, hM_UI_nonneg, N_UI, hN_UI⟩ :=
    uniform_integrability_exp_L P Q L hL_meas hL_is_log_ratio v h_weak
      (ε / (3 * C)) hthresh_pos
  -- (B) Pick M_target : ℕ so that `∫ min(exp, M_target) dν > 1 - ε/(3C)`.
  have h_ev_gauss : ∀ᶠ M : ℕ in atTop,
      (1 : ℝ) - ε / (3 * C) < ∫ x, min (Real.exp x) (M : ℝ) ∂ν := by
    have h_mem : Set.Ioi ((1 : ℝ) - ε / (3 * C)) ∈ 𝓝 (1 : ℝ) :=
      Ioi_mem_nhds (by linarith)
    exact tendsto_integral_truncExp_gaussianReal v h_mem
  obtain ⟨M_target, hM_target⟩ := h_ev_gauss.exists
  -- Take `M := max M_UI (M_target : ℝ) ≥ 0`.
  set M : ℝ := max M_UI (M_target : ℝ) with hM_def
  have hM_nonneg : 0 ≤ M := le_max_of_le_left hM_UI_nonneg
  have hM_ge_UI : M_UI ≤ M := le_max_left _ _
  have hM_ge_target : (M_target : ℝ) ≤ M := le_max_right _ _
  -- BCF `g_M(x) := f(-x) · min(exp x, M)`.
  let g_M : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f (-x) * min (Real.exp x) M)
    (hfneg_cont.mul (Real.continuous_exp.min continuous_const))
    (‖f‖ * M)
    (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : 0 ≤ min (Real.exp x) M := le_min (h_exp_nonneg x) hM_nonneg
      rw [abs_of_nonneg h2]
      refine mul_le_mul ?_ (min_le_right _ _) h2 (norm_nonneg _)
      rw [← Real.norm_eq_abs]; exact hfneg_bound x)
  have hg_M_apply : ∀ x, g_M x = f (-x) * min (Real.exp x) M := fun _ => rfl
  -- (D) Weak convergence at `g_M`.
  have h_weak_gM := h_weak g_M
  rw [Metric.tendsto_nhds] at h_weak_gM
  have hε3_pos : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨N_weak, hN_weak⟩ :=
    Filter.eventually_atTop.mp (h_weak_gM (ε / 3) hε3_pos)
  rw [Filter.eventually_atTop]
  refine ⟨max N_UI N_weak, fun n hn => ?_⟩
  have hn_UI : N_UI ≤ n := le_of_max_le_left hn
  have hn_weak : N_weak ≤ n := le_of_max_le_right hn
  -- Sequence-side residue bound needs `exp` integrable under `(P n).map L n`.
  have h_exp_int_Pn : Integrable (fun ω => Real.exp (L n ω)) (P n) :=
    exp_L_integrable P Q L hL_meas hL_is_log_ratio n
  have h_exp_int_map_n : Integrable (fun x : ℝ => Real.exp x) ((P n).map (L n)) := by
    rw [MeasureTheory.integrable_map_measure Real.continuous_exp.aestronglyMeasurable
        (hL_meas n).aemeasurable]
    exact h_exp_int_Pn
  -- UI bound at enlarged M: monotonicity of `min(exp, ·)` in M.
  have h_min_mono_M : ∀ ω, min (Real.exp (L n ω)) M_UI ≤ min (Real.exp (L n ω)) M :=
    fun ω => min_le_min_left _ hM_ge_UI
  have h_int_trunc_UI : Integrable
      (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI) (P n) := by
    refine h_exp_int_Pn.sub ?_
    refine h_exp_int_Pn.mono'
      ((Real.continuous_exp.measurable.comp (hL_meas n)).min
        measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_UI_nonneg)]
    exact min_le_left _ _
  have h_int_trunc_M : Integrable
      (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M) (P n) := by
    refine h_exp_int_Pn.sub ?_
    refine h_exp_int_Pn.mono'
      ((Real.continuous_exp.measurable.comp (hL_meas n)).min
        measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_nonneg)]
    exact min_le_left _ _
  have h_UI_bound_Pn :
      ∫ ω, (Real.exp (L n ω) - min (Real.exp (L n ω)) M) ∂(P n) ≤ ε / (3 * C) :=
    calc ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
        ≤ ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI ∂(P n) :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall
              (fun ω => sub_nonneg.mpr (min_le_left _ _)))
            h_int_trunc_UI
            (Filter.Eventually.of_forall
              (fun ω => by linarith [h_min_mono_M ω]))
      _ ≤ ε / (3 * C) := hN_UI n hn_UI
  have h_UI_bound_map_n :
      ∫ x, (Real.exp x - min (Real.exp x) M) ∂((P n).map (L n))
        ≤ ε / (3 * C) := by
    rw [MeasureTheory.integral_map (hL_meas n).aemeasurable]
    · exact h_UI_bound_Pn
    · exact (Real.continuous_exp.sub
        (Real.continuous_exp.min continuous_const)).aestronglyMeasurable
  -- Target-side residue bound: `∫ (exp - min(exp, M)) dν ≤ ε/(3C)`.
  have h_trunc_int_ν : Integrable (fun x : ℝ => min (Real.exp x) M) ν := by
    refine h_exp_int_ν.mono'
      (Real.continuous_exp.min continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_nonneg)]
    exact min_le_left _ _
  have h_target_trunc_M_lb :
      (1 : ℝ) - ε / (3 * C) ≤ ∫ x, min (Real.exp x) M ∂ν := by
    have h_mono :
        ∫ x, min (Real.exp x) (M_target : ℝ) ∂ν ≤ ∫ x, min (Real.exp x) M ∂ν := by
      have h_trunc_target_int : Integrable (fun x : ℝ => min (Real.exp x) (M_target : ℝ)) ν := by
        refine h_exp_int_ν.mono'
          (Real.continuous_exp.min continuous_const).aestronglyMeasurable
          (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) (Nat.cast_nonneg _))]
        exact min_le_left _ _
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall
          (fun x => le_min (h_exp_nonneg _) (Nat.cast_nonneg _)))
        h_trunc_int_ν
        (Filter.Eventually.of_forall (fun x => min_le_min_left _ hM_ge_target))
    linarith [hM_target]
  have h_target_bound_ν :
      ∫ x, (Real.exp x - min (Real.exp x) M) ∂ν ≤ ε / (3 * C) := by
    rw [integral_sub h_exp_int_ν h_trunc_int_ν, h_exp_int_ν_eq_one]
    linarith [h_target_trunc_M_lb]
  -- Apply residue bound on both sides.
  have h_res_map_n := h_residue ((P n).map (L n)) M hM_nonneg h_exp_int_map_n
  have h_res_ν := h_residue ν M hM_nonneg h_exp_int_ν
  -- Build the three pieces of the triangle inequality.
  rw [Real.dist_eq]
  have h_weak_bound : |∫ x, g_M x ∂((P n).map (L n)) - ∫ x, g_M x ∂ν| < ε / 3 := by
    have := hN_weak n hn_weak
    rwa [Real.dist_eq] at this
  have h_res_nonneg : 0 ≤ ‖f‖ := norm_nonneg _
  have h_seq_piece : |∫ x, f (-x) * Real.exp x ∂((P n).map (L n))
        - ∫ x, g_M x ∂((P n).map (L n))| ≤ ε / 3 := by
    have h_gM_eq : ∫ x, g_M x ∂((P n).map (L n))
        = ∫ x, f (-x) * min (Real.exp x) M ∂((P n).map (L n)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => hg_M_apply x))
    rw [h_gM_eq]
    calc |∫ x, f (-x) * Real.exp x ∂((P n).map (L n))
            - ∫ x, f (-x) * min (Real.exp x) M ∂((P n).map (L n))|
        ≤ ‖f‖ * ∫ x, (Real.exp x - min (Real.exp x) M) ∂((P n).map (L n)) := h_res_map_n
      _ ≤ ‖f‖ * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_left h_UI_bound_map_n h_res_nonneg
      _ ≤ C * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
      _ = ε / 3 := by field_simp
  have h_target_piece : |∫ x, g_M x ∂ν - ∫ x, f (-x) * Real.exp x ∂ν| ≤ ε / 3 := by
    have h_gM_eq : ∫ x, g_M x ∂ν = ∫ x, f (-x) * min (Real.exp x) M ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => hg_M_apply x))
    rw [h_gM_eq, abs_sub_comm]
    calc |∫ x, f (-x) * Real.exp x ∂ν - ∫ x, f (-x) * min (Real.exp x) M ∂ν|
        ≤ ‖f‖ * ∫ x, (Real.exp x - min (Real.exp x) M) ∂ν := h_res_ν
      _ ≤ ‖f‖ * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_left h_target_bound_ν h_res_nonneg
      _ ≤ C * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
      _ = ε / 3 := by field_simp
  -- Triangle inequality: split A - E = (A - B) + (B - D) + (D - E).
  set A := ∫ x, f (-x) * Real.exp x ∂((P n).map (L n))
  set B := ∫ x, g_M x ∂((P n).map (L n))
  set D := ∫ x, g_M x ∂ν
  set E := ∫ x, f (-x) * Real.exp x ∂ν
  have h_split : A - E = (A - B) + (B - D) + (D - E) := by ring
  rw [h_split]
  calc |(A - B) + (B - D) + (D - E)|
      ≤ |(A - B) + (B - D)| + |D - E| := abs_add_le _ _
    _ ≤ |A - B| + |B - D| + |D - E| := by linarith [abs_add_le (A - B) (B - D)]
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith [h_seq_piece, h_weak_bound, h_target_piece]
    _ = ε := by ring

end ReverseDirection

/-- **Le Cam's first lemma** (vdV Example 6.5, mutual-contiguity form).

If the log-likelihood ratio `L n = log dQ_n/dP_n` is asymptotically `N(-σ²/2, σ²)` under
`P n`, then `P n ⊲⊳ Q n`.

The reverse direction `P ⊲ Q` is obtained by applying the forward direction with `P` and
`Q` swapped and `L` negated:
* the inverse-density identity `P = Q.withDensity (exp ∘ (-L))` (from
  `P_eq_Q_withDensity_neg`);
* the tilted weak convergence `(Q n).map (-L n) → N(-v/2, v)` (from
  `weakConverges_Q_neg_L_gaussianReal_neg_half`). -/
theorem mutuallyContiguous_of_asymptotically_log_normal
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    MutuallyContiguous (ι := ℕ) (Ω := Ω) atTop P Q := by
  refine ⟨contiguous_of_asymptotically_log_normal P Q L hL_meas hL_is_log_ratio v h_weak, ?_⟩
  -- Reverse direction: apply the forward direction with `P` ↔ `Q` and `L ↦ -L`.
  have h_inv : ∀ n, P n = (Q n).withDensity (fun ω => ENNReal.ofReal (Real.exp (-L n ω))) :=
    P_eq_Q_withDensity_neg P Q L hL_meas hL_is_log_ratio
  have h_weak_neg :
      WeakConverges (fun n => (Q n).map (fun ω => -L n ω))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) :=
    weakConverges_Q_neg_L_gaussianReal_neg_half P Q L hL_meas hL_is_log_ratio v h_weak
  exact contiguous_of_asymptotically_log_normal Q P (fun n ω => -L n ω)
    (fun n => (hL_meas n).neg) h_inv v h_weak_neg

/-! ## Le Cam's third lemma -/

/-- **Le Cam's third lemma** (vdV Example 6.7).

`P_n ⊲⊳ Q_n`, together with joint weak convergence of `(X_n, L_n)` under `P_n` to the
law `π` on `E × ℝ` (the law of `(X, V)`), yields that `X_n` converges weakly under `Q_n`
to the tilted marginal `Measure.map Prod.fst (π.withDensity (exp ∘ Prod.snd))`.

This formulation takes the sequence-side UI (`h_UI`) and the target-side integrability
(`h_exp_int_π` + `h_exp_int_π_eq_one`) as explicit hypotheses, rather than deriving them
from `hcont`. In the log-normal log-likelihood setting (the main application, Step 5 of
Theorem 7.10), `h_UI` is discharged via `uniform_integrability_exp_L`, and the target-side
facts follow from weak convergence + sequence-side integral normalization. -/
theorem weak_limit_under_Q_of_lecam_third
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (X : ∀ n, Ω n → E) (L : ∀ n, Ω n → ℝ)
    (hX_meas : ∀ n, Measurable (X n)) (hL_meas : ∀ n, Measurable (L n))
    (hL_is_log_ratio : ∀ n,
        Q n = (P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω))))
    (π : Measure (E × ℝ)) [IsProbabilityMeasure π]
    (h_joint_weak :
      WeakConverges (fun n => (P n).map (fun ω => (X n ω, L n ω))) π)
    (h_UI : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε)
    (h_exp_int_π : Integrable (fun p : E × ℝ => Real.exp p.2) π)
    (h_exp_int_π_eq_one : ∫ p, Real.exp p.2 ∂π = 1) :
    WeakConverges (fun n => (Q n).map (X n))
      ((π.withDensity (fun p => ENNReal.ofReal (Real.exp p.2))).map Prod.fst) := by
  intro f
  -- Rewrite RHS (target integral over tilted marginal) as ∫ f(p.1)·exp(p.2) dπ.
  have h_target_rewrite : ∫ x, f x ∂((π.withDensity
        (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2))).map Prod.fst)
      = ∫ p, f p.1 * Real.exp p.2 ∂π := by
    have h_exp_meas_snd : Measurable (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2)) :=
      (Real.continuous_exp.measurable.comp measurable_snd).ennreal_ofReal
    have h_exp_lt_top : ∀ᵐ p ∂π, ENNReal.ofReal (Real.exp p.2) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable
        f.continuous.aestronglyMeasurable]
    rw [integral_withDensity_eq_integral_toReal_smul h_exp_meas_snd h_exp_lt_top
        (fun p => f p.1)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    change (ENNReal.ofReal (Real.exp p.2)).toReal • f p.1 = f p.1 * Real.exp p.2
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
  rw [h_target_rewrite]
  -- Rewrite each LHS term: ∫ f d((Q n).map X_n) = ∫ p, f(p.1)·exp(p.2) d((P n).map (X_n, L_n)).
  have h_seq_rewrite : ∀ n, ∫ x, f x ∂((Q n).map (X n))
      = ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω))) := by
    intro n
    have h_exp_meas_Ln : Measurable (fun ω => ENNReal.ofReal (Real.exp (L n ω))) :=
      (Real.continuous_exp.measurable.comp (hL_meas n)).ennreal_ofReal
    have h_exp_lt_top : ∀ᵐ ω ∂(P n), ENNReal.ofReal (Real.exp (L n ω)) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
      (hX_meas n).prodMk (hL_meas n)
    have h_integrand_meas :
        AEStronglyMeasurable (fun p : E × ℝ => f p.1 * Real.exp p.2)
          ((P n).map (fun ω => (X n ω, L n ω))) :=
      ((f.continuous.comp continuous_fst).mul
        (Real.continuous_exp.comp continuous_snd)).aestronglyMeasurable
    calc ∫ x, f x ∂((Q n).map (X n))
        = ∫ ω, f (X n ω) ∂(Q n) :=
          MeasureTheory.integral_map (hX_meas n).aemeasurable
            f.continuous.aestronglyMeasurable
      _ = ∫ ω, f (X n ω)
            ∂((P n).withDensity (fun ω => ENNReal.ofReal (Real.exp (L n ω)))) := by
          rw [← hL_is_log_ratio n]
      _ = ∫ ω, (ENNReal.ofReal (Real.exp (L n ω))).toReal • f (X n ω) ∂(P n) :=
          integral_withDensity_eq_integral_toReal_smul h_exp_meas_Ln h_exp_lt_top
            (fun ω => f (X n ω))
      _ = ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
          change (ENNReal.ofReal (Real.exp (L n ω))).toReal • f (X n ω)
            = f (X n ω) * Real.exp (L n ω)
          rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
      _ = ∫ p, f p.1 * Real.exp p.2
            ∂((P n).map (fun ω => (X n ω, L n ω))) :=
          (MeasureTheory.integral_map h_joint_meas.aemeasurable h_integrand_meas).symm
  simp_rw [h_seq_rewrite]
  -- Residue bound on both sides via BCF truncation + triangle inequality.
  have hfbound : ∀ p : E × ℝ, |f p.1| ≤ ‖f‖ := fun p => f.norm_coe_le_norm _
  have h_exp_nonneg : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos _).le
  -- Generic helper: |∫ f(p.1)·exp(p.2) dμ - ∫ f(p.1)·min(exp(p.2), M) dμ|
  --  ≤ ‖f‖ · ∫ (exp p.2 - min(exp p.2, M)) dμ, for any measure μ on E × ℝ with `exp p.2`
  -- integrable.
  have h_residue_EℝR :
      ∀ (μ : Measure (E × ℝ)) (M : ℝ), 0 ≤ M →
        Integrable (fun p : E × ℝ => Real.exp p.2) μ →
        |∫ p, f p.1 * Real.exp p.2 ∂μ - ∫ p, f p.1 * min (Real.exp p.2) M ∂μ|
          ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
    intro μ M hM h_exp_int
    have h_min_nn : ∀ p : E × ℝ, 0 ≤ min (Real.exp p.2) M := fun p =>
      le_min (h_exp_nonneg _) hM
    have h_min_le : ∀ p : E × ℝ, min (Real.exp p.2) M ≤ Real.exp p.2 :=
      fun p => min_le_left _ _
    have h_min_meas : Measurable (fun p : E × ℝ => min (Real.exp p.2) M) :=
      (Real.continuous_exp.measurable.comp measurable_snd).min measurable_const
    have h_min_int : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) μ := by
      refine h_exp_int.mono' h_min_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Real.norm_eq_abs, abs_of_nonneg (h_min_nn p)]
      exact h_min_le p
    have hf_ae :
        AEStronglyMeasurable (fun p : E × ℝ => f p.1) μ :=
      (f.continuous.comp continuous_fst).aestronglyMeasurable
    have hf_bound_ae : ∀ᵐ p ∂μ, ‖f p.1‖ ≤ ‖f‖ :=
      Filter.Eventually.of_forall (fun p => f.norm_coe_le_norm _)
    have h_fexp_int : Integrable (fun p : E × ℝ => f p.1 * Real.exp p.2) μ :=
      h_exp_int.bdd_mul hf_ae hf_bound_ae
    have h_fmin_int :
        Integrable (fun p : E × ℝ => f p.1 * min (Real.exp p.2) M) μ :=
      h_min_int.bdd_mul hf_ae hf_bound_ae
    rw [← integral_sub h_fexp_int h_fmin_int]
    have h_diff_eq :
        (fun p : E × ℝ => f p.1 * Real.exp p.2 - f p.1 * min (Real.exp p.2) M)
          = fun p => f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) := by
      funext p; ring
    rw [h_diff_eq]
    calc |∫ p, f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ|
        ≤ ∫ p, |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)| ∂μ :=
          abs_integral_le_integral_abs
      _ = ∫ p, |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
          change |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)|
            = |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M)
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (h_min_le p))]
      _ ≤ ∫ p, ‖f‖ * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall
              (fun p => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (h_min_le p))))
            ((h_exp_int.sub h_min_int).const_mul ‖f‖)
            (Filter.Eventually.of_forall (fun p => ?_))
          refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr (h_min_le p))
          exact hfbound p
      _ = ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ :=
          integral_const_mul _ _
  -- Target-side tendsto: as M → ∞, ∫ min(exp p.2, M) dπ → ∫ exp p.2 dπ = 1 (DCT under π).
  have h_target_tendsto : Tendsto
      (fun M : ℕ => ∫ p, min (Real.exp p.2) (M : ℝ) ∂π) atTop (𝓝 1) := by
    have h_lim : ∀ᵐ p ∂π,
        Tendsto (fun M : ℕ => min (Real.exp p.2) (M : ℝ)) atTop (𝓝 (Real.exp p.2)) := by
      refine Filter.Eventually.of_forall (fun p => ?_)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ⌈Real.exp p.2⌉₊] with M hM
      have : Real.exp p.2 ≤ (M : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hM)
      exact (min_eq_left this).symm
    have h_dom : ∀ M : ℕ, ∀ᵐ p ∂π,
        ‖min (Real.exp p.2) (M : ℝ)‖ ≤ Real.exp p.2 := by
      intro M
      refine Filter.Eventually.of_forall (fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) (Nat.cast_nonneg _))]
      exact min_le_left _ _
    have h_meas : ∀ M : ℕ,
        AEStronglyMeasurable (fun p : E × ℝ => min (Real.exp p.2) (M : ℝ)) π :=
      fun M => ((Real.continuous_exp.comp continuous_snd).min
        continuous_const).aestronglyMeasurable
    have h_conv := MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun (M : ℕ) (p : E × ℝ) => min (Real.exp p.2) (M : ℝ))
      (f := fun p : E × ℝ => Real.exp p.2) (bound := fun p : E × ℝ => Real.exp p.2)
      h_meas h_exp_int_π h_dom h_lim
    rw [h_exp_int_π_eq_one] at h_conv
    exact h_conv
  -- Start ε argument.
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C : ℝ := ‖f‖ + 1 with hC_def
  have hC_pos : 0 < C := by positivity
  have hnorm_le_C : ‖f‖ ≤ C := by simp [hC_def]
  have hthresh_pos : 0 < ε / (3 * C) := by positivity
  -- UI threshold on sequence side.
  obtain ⟨M_UI, hM_UI_nonneg, N_UI, hN_UI⟩ :=
    h_UI (ε / (3 * C)) hthresh_pos
  -- Target-side pick M_target so `1 - ε/(3C) < ∫ min(exp, M_target) dπ`.
  have h_ev_target : ∀ᶠ M : ℕ in atTop,
      (1 : ℝ) - ε / (3 * C) < ∫ p, min (Real.exp p.2) (M : ℝ) ∂π := by
    have h_mem : Set.Ioi ((1 : ℝ) - ε / (3 * C)) ∈ 𝓝 (1 : ℝ) :=
      Ioi_mem_nhds (by linarith)
    exact h_target_tendsto h_mem
  obtain ⟨M_target, hM_target⟩ := h_ev_target.exists
  -- Take M := max M_UI (M_target : ℝ).
  set M : ℝ := max M_UI (M_target : ℝ) with hM_def
  have hM_nonneg : 0 ≤ M := le_max_of_le_left hM_UI_nonneg
  have hM_ge_UI : M_UI ≤ M := le_max_left _ _
  have hM_ge_target : (M_target : ℝ) ≤ M := le_max_right _ _
  -- BCF `g_M(p) := f(p.1) · min(exp(p.2), M)`, norm ≤ ‖f‖ · M.
  let g_M : E × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => f p.1 * min (Real.exp p.2) M)
    ((f.continuous.comp continuous_fst).mul
      ((Real.continuous_exp.comp continuous_snd).min continuous_const))
    (‖f‖ * M)
    (fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      have h2 : 0 ≤ min (Real.exp p.2) M :=
        le_min (h_exp_nonneg _) hM_nonneg
      rw [abs_of_nonneg h2]
      refine mul_le_mul ?_ (min_le_right _ _) h2 (norm_nonneg _)
      exact hfbound p)
  have hg_M_apply : ∀ p, g_M p = f p.1 * min (Real.exp p.2) M := fun _ => rfl
  -- Weak convergence at g_M.
  have h_weak_gM := h_joint_weak g_M
  rw [Metric.tendsto_nhds] at h_weak_gM
  have hε3_pos : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨N_weak, hN_weak⟩ :=
    Filter.eventually_atTop.mp (h_weak_gM (ε / 3) hε3_pos)
  rw [Filter.eventually_atTop]
  refine ⟨max N_UI N_weak, fun n hn => ?_⟩
  have hn_UI : N_UI ≤ n := le_of_max_le_left hn
  have hn_weak : N_weak ≤ n := le_of_max_le_right hn
  -- Sequence-side: `exp` integrable under `(P n).map (X_n, L_n)`.
  have h_exp_int_Pn : Integrable (fun ω => Real.exp (L n ω)) (P n) :=
    exp_L_integrable P Q L hL_meas hL_is_log_ratio n
  have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
    (hX_meas n).prodMk (hL_meas n)
  have h_exp_int_map_n :
      Integrable (fun p : E × ℝ => Real.exp p.2)
        ((P n).map (fun ω => (X n ω, L n ω))) :=
    (MeasureTheory.integrable_map_measure
      (Real.continuous_exp.comp continuous_snd).aestronglyMeasurable
      h_joint_meas.aemeasurable).mpr h_exp_int_Pn
  -- UI bound at enlarged M: monotonicity of min(exp, ·) in M.
  have h_min_mono_M : ∀ ω,
      min (Real.exp (L n ω)) M_UI ≤ min (Real.exp (L n ω)) M :=
    fun ω => min_le_min_left _ hM_ge_UI
  have h_int_trunc_UI : Integrable
      (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI) (P n) := by
    refine h_exp_int_Pn.sub ?_
    refine h_exp_int_Pn.mono'
      ((Real.continuous_exp.measurable.comp (hL_meas n)).min
        measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (le_min (h_exp_nonneg _) hM_UI_nonneg)]
    exact min_le_left _ _
  have h_UI_bound_Pn :
      ∫ ω, (Real.exp (L n ω) - min (Real.exp (L n ω)) M) ∂(P n) ≤ ε / (3 * C) :=
    calc ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
        ≤ ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI ∂(P n) :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall
              (fun ω => sub_nonneg.mpr (min_le_left _ _)))
            h_int_trunc_UI
            (Filter.Eventually.of_forall
              (fun ω => by linarith [h_min_mono_M ω]))
      _ ≤ ε / (3 * C) := hN_UI n hn_UI
  have h_UI_bound_map_n :
      ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
          ∂((P n).map (fun ω => (X n ω, L n ω)))
        ≤ ε / (3 * C) := by
    rw [MeasureTheory.integral_map h_joint_meas.aemeasurable]
    · exact h_UI_bound_Pn
    · exact ((Real.continuous_exp.comp continuous_snd).sub
        ((Real.continuous_exp.comp continuous_snd).min
          continuous_const)).aestronglyMeasurable
  -- Target-side residue bound:
  have h_trunc_int_π : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) π := by
    refine h_exp_int_π.mono'
      ((Real.continuous_exp.comp continuous_snd).min
        continuous_const).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_nonneg)]
    exact min_le_left _ _
  have h_target_trunc_M_lb :
      (1 : ℝ) - ε / (3 * C) ≤ ∫ p, min (Real.exp p.2) M ∂π := by
    have h_mono :
        ∫ p, min (Real.exp p.2) (M_target : ℝ) ∂π
          ≤ ∫ p, min (Real.exp p.2) M ∂π := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall
          (fun p => le_min (h_exp_nonneg _) (Nat.cast_nonneg _)))
        h_trunc_int_π
        (Filter.Eventually.of_forall (fun p => min_le_min_left _ hM_ge_target))
    linarith [hM_target]
  have h_target_bound_π :
      ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π ≤ ε / (3 * C) := by
    rw [integral_sub h_exp_int_π h_trunc_int_π, h_exp_int_π_eq_one]
    linarith [h_target_trunc_M_lb]
  -- Apply residue bound on both sides.
  have h_res_map_n := h_residue_EℝR ((P n).map (fun ω => (X n ω, L n ω))) M hM_nonneg
    h_exp_int_map_n
  have h_res_π := h_residue_EℝR π M hM_nonneg h_exp_int_π
  -- Triangle inequality.
  rw [Real.dist_eq]
  have h_weak_bound :
      |∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω))) - ∫ p, g_M p ∂π| < ε / 3 := by
    have := hN_weak n hn_weak
    rwa [Real.dist_eq] at this
  have h_res_nonneg : 0 ≤ ‖f‖ := norm_nonneg _
  have h_seq_piece :
      |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
        - ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))| ≤ ε / 3 := by
    have h_gM_eq :
        ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
          = ∫ p, f p.1 * min (Real.exp p.2) M
              ∂((P n).map (fun ω => (X n ω, L n ω))) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
    rw [h_gM_eq]
    calc |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
            - ∫ p, f p.1 * min (Real.exp p.2) M
                ∂((P n).map (fun ω => (X n ω, L n ω)))|
        ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
              ∂((P n).map (fun ω => (X n ω, L n ω))) := h_res_map_n
      _ ≤ ‖f‖ * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_left h_UI_bound_map_n h_res_nonneg
      _ ≤ C * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
      _ = ε / 3 := by field_simp
  have h_target_piece :
      |∫ p, g_M p ∂π - ∫ p, f p.1 * Real.exp p.2 ∂π| ≤ ε / 3 := by
    have h_gM_eq :
        ∫ p, g_M p ∂π = ∫ p, f p.1 * min (Real.exp p.2) M ∂π :=
      integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
    rw [h_gM_eq, abs_sub_comm]
    calc |∫ p, f p.1 * Real.exp p.2 ∂π - ∫ p, f p.1 * min (Real.exp p.2) M ∂π|
        ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π := h_res_π
      _ ≤ ‖f‖ * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_left h_target_bound_π h_res_nonneg
      _ ≤ C * (ε / (3 * C)) :=
          mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
      _ = ε / 3 := by field_simp
  set A := ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
  set B := ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
  set D := ∫ p, g_M p ∂π
  set E' := ∫ p, f p.1 * Real.exp p.2 ∂π
  have h_split : A - E' = (A - B) + (B - D) + (D - E') := by ring
  rw [h_split]
  calc |(A - B) + (B - D) + (D - E')|
      ≤ |(A - B) + (B - D)| + |D - E'| := abs_add_le _ _
    _ ≤ |A - B| + |B - D| + |D - E'| := by linarith [abs_add_le (A - B) (B - D)]
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith [h_seq_piece, h_weak_bound, h_target_piece]
    _ = ε := by ring

/-- ENNReal-form variant of `weak_limit_under_Q_of_lecam_third`: the density
`ρ_n : Ω → ℝ≥0∞` (e.g. an `rnDeriv`) is converted to the real-valued log form
`L_n := log (ρ_n).toReal` via `hρ_AE_pos`, then forwarded to the exp-form theorem.

The `h_joint_weak` hypothesis is now phrased in terms of
`(X n ω, Real.log (ρ n ω).toReal)` for caller convenience.

Reference: vdV Example 6.7 (Le Cam's third lemma); the existing
exp-form `weak_limit_under_Q_of_lecam_third` does the heavy lifting. -/
theorem weak_limit_under_Q_of_lecam_third_ennreal
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (X : ∀ n, Ω n → E) (ρ : ∀ n, Ω n → ℝ≥0∞)
    (hX_meas : ∀ n, Measurable (X n)) (hρ_meas : ∀ n, Measurable (ρ n))
    (hQ_density : ∀ n, Q n = (P n).withDensity (ρ n))
    (hρ_AE_pos : ∀ n, ∀ᵐ ω ∂(P n), 0 < ρ n ω ∧ ρ n ω < ⊤)
    (π : Measure (E × ℝ)) [IsProbabilityMeasure π]
    (h_joint_weak :
      WeakConverges
        (fun n => (P n).map
          (fun ω => (X n ω, Real.log (ρ n ω).toReal))) π)
    (h_UI : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (Real.log (ρ n ω).toReal)
              - min (Real.exp (Real.log (ρ n ω).toReal)) M ∂(P n) ≤ ε)
    (h_exp_int_π : Integrable (fun p : E × ℝ => Real.exp p.2) π)
    (h_exp_int_π_eq_one : ∫ p, Real.exp p.2 ∂π = 1) :
    WeakConverges (fun n => (Q n).map (X n))
      ((π.withDensity (fun p => ENNReal.ofReal (Real.exp p.2))).map Prod.fst) := by
  set L_n : ∀ n, Ω n → ℝ := fun n ω => Real.log (ρ n ω).toReal with hL_n_def
  have hL_n_meas : ∀ n, Measurable (L_n n) := fun n =>
    ((hρ_meas n).ennreal_toReal).log
  have hρ_eq_exp : ∀ n, ρ n =ᵐ[P n]
      fun ω => ENNReal.ofReal (Real.exp (L_n n ω)) := by
    intro n
    filter_upwards [hρ_AE_pos n] with ω hω
    obtain ⟨hpos, hfin⟩ := hω
    have h_toReal_pos : (0 : ℝ) < (ρ n ω).toReal :=
      ENNReal.toReal_pos hpos.ne' hfin.ne
    rw [hL_n_def]
    rw [Real.exp_log h_toReal_pos]
    exact (ENNReal.ofReal_toReal hfin.ne).symm
  have hQ_via_exp : ∀ n,
      Q n = (P n).withDensity
              (fun ω => ENNReal.ofReal (Real.exp (L_n n ω))) := by
    intro n
    rw [hQ_density]
    exact MeasureTheory.withDensity_congr_ae (hρ_eq_exp n)
  exact weak_limit_under_Q_of_lecam_third
    (Ω := Ω) (E := E) (P := P) (Q := Q) (X := X) (L := L_n)
    hX_meas hL_n_meas hQ_via_exp π h_joint_weak h_UI
    h_exp_int_π h_exp_int_π_eq_one

/-! ## Contiguity-footing Le Cam variants

The two lemmas below are asymptotic-footing reformulations of `uniform_integrability_exp_L`
and `weak_limit_under_Q_of_lecam_third`. They replace the **exact** change-of-measure
hypothesis `hL_is_log_ratio` (`Q n = (P n).withDensity (exp ∘ L n)`, which forces absolute
continuity hence common support) by asymptotic data: an integral-comparison bound with
vanishing slack and a mass hypothesis `∫ exp(L n) dP_n → 1`. They are added alongside the
exact lemmas: concrete-support callers keep citing the exact ones. Conclusions are identical
to their exact counterparts; only the hypothesis set changes. -/

/-- **Uniform-integrability of `exp(L n)` from `∫ exp(L n) dP_n → 1`.**

Contiguity-footing variant of `uniform_integrability_exp_L`. The exact identity
`hL_is_log_ratio` is replaced by the two pieces it was only ever used to extract:
* `h_exp_int` — integrability of `exp(L n)` under `P n` (in the AC case this came from
  `exp_L_integrable`; on the contiguity footing it is supplied directly — `withDensity` is a finite
  sub-probability measure of mass `≤ 1`);
* `h_mass` — the asymptotic normalization `∫ exp(L n) dP_n → 1` (in the AC case this was the exact
  `integral_exp_L_eq_one`; now `(1 + δₙ)` with `δₙ → 0`).

Conclusion identical to the exact lemma.

**Proof:** mirror `uniform_integrability_exp_L`'s structure (Gaussian truncation pick +
`tendsto_integral_truncExp_L`), but rework the tail ε-budget: the exact `1 − ∫min` becomes
`(∫ exp(L n) dP_n) − ∫min = (1 + δₙ) − ∫min`. Split ε across the `δₙ` slack and the
truncation gap; `δₙ = o(1)` is absorbable but must be carried explicitly (UI only needs
`≤ ε` eventually). Reuse: `tendsto_integral_truncExp_L`,
`tendsto_integral_truncExp_gaussianReal`. -/
lemma uniform_integrability_exp_L_of_integral_tendsto_one
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (L : ∀ n, Ω n → ℝ) (hL_meas : ∀ n, Measurable (L n))
    -- measure `P_n.withDensity (exp(L n))` is a finite sub-probability measure (mass ≤ 1).
    (h_exp_int : ∀ n, Integrable (fun ω => Real.exp (L n ω)) (P n))
    -- asymptotic singular-mass control (not common support).
    (h_mass : Tendsto (fun n => ∫ ω, Real.exp (L n ω) ∂(P n)) atTop (𝓝 1))
    (v : NNReal)
    (h_weak :
      WeakConverges (fun n => (P n).map (L n))
        (ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε := by
  intro ε hε
  -- Step 1: pick a natural M₀ with `∫ min(exp, M₀) dN ≥ 1 - ε/4`.
  have h_gaussian := tendsto_integral_truncExp_gaussianReal v
  have h_ev :
      ∀ᶠ M : ℕ in atTop,
        1 - ε / 4 ≤
          ∫ x, min (Real.exp x) (M : ℝ)
            ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v) := by
    have h_mem : Set.Ici (1 - ε / 4) ∈ 𝓝 (1 : ℝ) :=
      Ici_mem_nhds (by linarith)
    exact h_gaussian h_mem
  obtain ⟨M₀, hM₀⟩ := h_ev.exists
  set M : ℝ := (M₀ : ℝ) with hM_def
  have hM_nonneg : 0 ≤ M := Nat.cast_nonneg _
  refine ⟨M, hM_nonneg, ?_⟩
  -- Step 2: for fixed M, get `∫ min(exp(L n), M) dP_n → ∫ min(exp, M) dN`.
  have h_trunc_tendsto :=
    tendsto_integral_truncExp_L P L hL_meas v h_weak M hM_nonneg
  -- Step 3a: pick N₁ so that for n ≥ N₁, `∫ min(exp(L n), M) dP_n ≥ 1 - ε/2`.
  have h_target :
      ∀ᶠ n : ℕ in atTop,
        1 - ε / 2 ≤ ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    have h_mem : Set.Ioi (1 - ε / 2) ∈ 𝓝 (∫ x, min (Real.exp x) M
        ∂(ProbabilityTheory.gaussianReal (-(v : ℝ) / 2) v)) := by
      apply Ioi_mem_nhds
      linarith [hM₀]
    filter_upwards [h_trunc_tendsto h_mem] with n hn
    exact le_of_lt (Set.mem_Ioi.mp hn)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h_target
  -- Step 3b: from `h_mass`, pick N₂ so that for n ≥ N₂, `∫ exp(L n) dP_n ≤ 1 + ε/2`.
  have h_mass_ub :
      ∀ᶠ n : ℕ in atTop,
        ∫ ω, Real.exp (L n ω) ∂(P n) ≤ 1 + ε / 2 := by
    have h_mem : Set.Iic (1 + ε / 2) ∈ 𝓝 (1 : ℝ) :=
      Iic_mem_nhds (by linarith)
    filter_upwards [h_mass h_mem] with n hn
    exact Set.mem_Iic.mp hn
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp h_mass_ub
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  -- Step 4: rearrange using `∫ exp(L n) dP_n ≤ 1 + ε/2` and `∫min ≥ 1 - ε/2`.
  have h_exp_int_n := h_exp_int n
  have h_trunc_int : Integrable (fun ω => min (Real.exp (L n ω)) M) (P n) := by
    refine h_exp_int_n.mono' ?_ ?_
    · exact ((Real.continuous_exp.measurable.comp
        (hL_meas n)).min measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact min_le_left _ _
      · exact le_min (Real.exp_pos _).le hM_nonneg
  have h_diff_eq :
      ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
        = (∫ ω, Real.exp (L n ω) ∂(P n))
          - ∫ ω, min (Real.exp (L n ω)) M ∂(P n) := by
    rw [MeasureTheory.integral_sub h_exp_int_n h_trunc_int]
  rw [h_diff_eq]
  linarith [hN₁ n hn₁, hN₂ n hn₂]

/-- **Le Cam's third lemma from an integral-comparison bound.**

Contiguity-footing variant of `weak_limit_under_Q_of_lecam_third`. The exact identity
`hL_is_log_ratio` is replaced by the abstract integral-comparison hypothesis
`h_integral_comparison`:
for some `ρ → 0` and every bounded continuous `f`,
`|∫ f(X n) dQ_n − ∫ f(X n)·exp(L n) dP_n| ≤ ‖f‖·ρ_n`. The exact `rw [← hL_is_log_ratio n]`
is gone; the `‖f‖·ρ_n → 0` slack is carried through the existing truncation/residue
estimate to the same weak limit (limits are exact, so the vanishing slack does not perturb them).

Conclusion identical to the exact lemma.

**Proof:** mirror `weak_limit_under_Q_of_lecam_third`'s ε-argument
(`h_residue_EℝR` + BCF truncation + triangle inequality), but where the exact lemma rewrites
`∫ f d((Q n).map X) = ∫ f(p.1)·exp(p.2) d((P n).map (X,L))` exactly, here that equality holds only
up to `‖f‖·ρ_n`; add a fourth ε/4 (or rescale to ε/3 with the slack folded into one piece) for the
`h_integral_comparison` term, eventually `< ε` since `ρ_n → 0`. Reuse: the entire existing body of
`weak_limit_under_Q_of_lecam_third` (residue bound, target-side DCT, weak-convergence at `g_M`). -/
theorem weak_limit_under_Q_of_lecam_third_of_integral_comparison
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (P Q : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] [∀ n, IsProbabilityMeasure (Q n)]
    (X : ∀ n, Ω n → E) (L : ∀ n, Ω n → ℝ)
    (hX_meas : ∀ n, Measurable (X n)) (hL_meas : ∀ n, Measurable (L n))
    -- replaces the exact identity `hL_is_log_ratio` by asymptotic singular-mass control (not common
    -- support).
    (h_integral_comparison :
      ∃ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) ∧
        ∀ (f : E →ᵇ ℝ) (n : ℕ),
          |∫ ω, f (X n ω) ∂(Q n)
            - ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)| ≤ ‖f‖ * ρ n)
    (π : Measure (E × ℝ)) [IsProbabilityMeasure π]
    (h_joint_weak :
      WeakConverges (fun n => (P n).map (fun ω => (X n ω, L n ω))) π)
    (h_UI : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n) ≤ ε)
    (h_exp_int_π : Integrable (fun p : E × ℝ => Real.exp p.2) π)
    (h_exp_int_π_eq_one : ∫ p, Real.exp p.2 ∂π = 1) :
    WeakConverges (fun n => (Q n).map (X n))
      ((π.withDensity (fun p => ENNReal.ofReal (Real.exp p.2))).map Prod.fst) := by
  intro f
  -- Rewrite RHS (target integral over tilted marginal) as ∫ f(p.1)·exp(p.2) dπ.
  have h_target_rewrite : ∫ x, f x ∂((π.withDensity
        (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2))).map Prod.fst)
      = ∫ p, f p.1 * Real.exp p.2 ∂π := by
    have h_exp_meas_snd : Measurable (fun p : E × ℝ => ENNReal.ofReal (Real.exp p.2)) :=
      (Real.continuous_exp.measurable.comp measurable_snd).ennreal_ofReal
    have h_exp_lt_top : ∀ᵐ p ∂π, ENNReal.ofReal (Real.exp p.2) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    rw [MeasureTheory.integral_map measurable_fst.aemeasurable
        f.continuous.aestronglyMeasurable]
    rw [integral_withDensity_eq_integral_toReal_smul h_exp_meas_snd h_exp_lt_top
        (fun p => f p.1)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    change (ENNReal.ofReal (Real.exp p.2)).toReal • f p.1 = f p.1 * Real.exp p.2
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]
  rw [h_target_rewrite]
  -- Map-integral identities: `bₙ` (under `Q n`) and `aₙ` (under `P n`, tilted).
  have h_bn_map : ∀ n, ∫ x, f x ∂((Q n).map (X n)) = ∫ ω, f (X n ω) ∂(Q n) := fun n =>
    MeasureTheory.integral_map (hX_meas n).aemeasurable f.continuous.aestronglyMeasurable
  have h_an_map : ∀ n,
      ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
        = ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n) := by
    intro n
    have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
      (hX_meas n).prodMk (hL_meas n)
    have h_integrand_meas :
        AEStronglyMeasurable (fun p : E × ℝ => f p.1 * Real.exp p.2)
          ((P n).map (fun ω => (X n ω, L n ω))) :=
      ((f.continuous.comp continuous_fst).mul
        (Real.continuous_exp.comp continuous_snd)).aestronglyMeasurable
    rw [MeasureTheory.integral_map h_joint_meas.aemeasurable h_integrand_meas]
  -- ── Slack data from the integral comparison. ─────────────────────────────────────────
  obtain ⟨ρ, hρ_tendsto, hρ_bound⟩ := h_integral_comparison
  -- Eventual integrability of `exp(L n)` under `P n`, recovered from the comparison applied
  -- to the constant `1` BCF: `|1 - ∫ exp(L n) dP_n| ≤ ‖(1 : E →ᵇ ℝ)‖ · ρ n`, and the RHS → 0.
  have h_eventually_int :
      ∀ᶠ n in atTop, Integrable (fun ω => Real.exp (L n ω)) (P n) := by
    have hg1_bound := hρ_bound (1 : E →ᵇ ℝ)
    -- `∫ (1 : E →ᵇ ℝ)(X n) dQ_n = 1` and `(1 : E →ᵇ ℝ)(X n ω)·exp(L n ω) = exp(L n ω)`.
    have h_one_apply : ∀ n ω, ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) = 1 := by
      intro n ω; rw [BoundedContinuousFunction.coe_one]; rfl
    have hg1_simp : ∀ n,
        |(1 : ℝ) - ∫ ω, Real.exp (L n ω) ∂(P n)| ≤ ‖(1 : E →ᵇ ℝ)‖ * ρ n := by
      intro n
      have hb := hg1_bound n
      have h1 : ∫ ω, ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) ∂(Q n) = 1 := by
        simp only [h_one_apply, integral_const, smul_eq_mul, mul_one, probReal_univ]
      have h2 : (fun ω => ((1 : E →ᵇ ℝ) : E → ℝ) (X n ω) * Real.exp (L n ω))
          = fun ω => Real.exp (L n ω) := by
        funext ω; rw [h_one_apply]; ring
      rw [h1, h2] at hb
      exact hb
    -- `‖(1 : E →ᵇ ℝ)‖ · ρ n → 0`, so eventually `< 1`.
    have h_slack_zero : Tendsto (fun n => ‖(1 : E →ᵇ ℝ)‖ * ρ n) atTop (𝓝 0) := by
      have := hρ_tendsto.const_mul ‖(1 : E →ᵇ ℝ)‖
      simpa using this
    have h_ev_lt_one : ∀ᶠ n in atTop, ‖(1 : E →ᵇ ℝ)‖ * ρ n < 1 := by
      have h_mem : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (by norm_num)
      filter_upwards [h_slack_zero h_mem] with n hn using Set.mem_Iio.mp hn
    filter_upwards [h_ev_lt_one] with n hn
    by_contra h_not_int
    have h_zero : ∫ ω, Real.exp (L n ω) ∂(P n) = 0 := integral_undef h_not_int
    have hb := hg1_simp n
    rw [h_zero, sub_zero, abs_one] at hb
    linarith
  -- ── Replay of the exact `weak_limit_under_Q_of_lecam_third` residue/ε argument to show ──
  -- `aₙ` (in map form) converges to the target. The ONLY change is that `exp(L n)`
  -- integrability under `P n` is now `h_eventually_int` (eventual) rather than the exact
  -- `exp_L_integrable`; the threshold `N₀` is enlarged to absorb `N_int`.
  have h_map_tendsto : Tendsto
      (fun n => ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω))))
      atTop (𝓝 (∫ p, f p.1 * Real.exp p.2 ∂π)) := by
    -- Residue bound on both sides via BCF truncation + triangle inequality.
    have hfbound : ∀ p : E × ℝ, |f p.1| ≤ ‖f‖ := fun p => f.norm_coe_le_norm _
    have h_exp_nonneg : ∀ x : ℝ, 0 ≤ Real.exp x := fun x => (Real.exp_pos _).le
    have h_residue_EℝR :
        ∀ (μ : Measure (E × ℝ)) (M : ℝ), 0 ≤ M →
          Integrable (fun p : E × ℝ => Real.exp p.2) μ →
          |∫ p, f p.1 * Real.exp p.2 ∂μ - ∫ p, f p.1 * min (Real.exp p.2) M ∂μ|
            ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
      intro μ M hM h_exp_int
      have h_min_nn : ∀ p : E × ℝ, 0 ≤ min (Real.exp p.2) M := fun p =>
        le_min (h_exp_nonneg _) hM
      have h_min_le : ∀ p : E × ℝ, min (Real.exp p.2) M ≤ Real.exp p.2 :=
        fun p => min_le_left _ _
      have h_min_meas : Measurable (fun p : E × ℝ => min (Real.exp p.2) M) :=
        (Real.continuous_exp.measurable.comp measurable_snd).min measurable_const
      have h_min_int : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) μ := by
        refine h_exp_int.mono' h_min_meas.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun p => ?_))
        simp only [Real.norm_eq_abs, abs_of_nonneg (h_min_nn p)]
        exact h_min_le p
      have hf_ae :
          AEStronglyMeasurable (fun p : E × ℝ => f p.1) μ :=
        (f.continuous.comp continuous_fst).aestronglyMeasurable
      have hf_bound_ae : ∀ᵐ p ∂μ, ‖f p.1‖ ≤ ‖f‖ :=
        Filter.Eventually.of_forall (fun p => f.norm_coe_le_norm _)
      have h_fexp_int : Integrable (fun p : E × ℝ => f p.1 * Real.exp p.2) μ :=
        h_exp_int.bdd_mul hf_ae hf_bound_ae
      have h_fmin_int :
          Integrable (fun p : E × ℝ => f p.1 * min (Real.exp p.2) M) μ :=
        h_min_int.bdd_mul hf_ae hf_bound_ae
      rw [← integral_sub h_fexp_int h_fmin_int]
      have h_diff_eq :
          (fun p : E × ℝ => f p.1 * Real.exp p.2 - f p.1 * min (Real.exp p.2) M)
            = fun p => f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) := by
        funext p; ring
      rw [h_diff_eq]
      calc |∫ p, f p.1 * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ|
          ≤ ∫ p, |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)| ∂μ :=
            abs_integral_le_integral_abs
        _ = ∫ p, |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
            change |f p.1 * (Real.exp p.2 - min (Real.exp p.2) M)|
              = |f p.1| * (Real.exp p.2 - min (Real.exp p.2) M)
            rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (h_min_le p))]
        _ ≤ ∫ p, ‖f‖ * (Real.exp p.2 - min (Real.exp p.2) M) ∂μ := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall
                (fun p => mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (h_min_le p))))
              ((h_exp_int.sub h_min_int).const_mul ‖f‖)
              (Filter.Eventually.of_forall (fun p => ?_))
            refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr (h_min_le p))
            exact hfbound p
        _ = ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂μ :=
            integral_const_mul _ _
    -- Target-side tendsto: as M → ∞, ∫ min(exp p.2, M) dπ → ∫ exp p.2 dπ = 1 (DCT under π).
    have h_target_tendsto : Tendsto
        (fun M : ℕ => ∫ p, min (Real.exp p.2) (M : ℝ) ∂π) atTop (𝓝 1) := by
      have h_lim : ∀ᵐ p ∂π,
          Tendsto (fun M : ℕ => min (Real.exp p.2) (M : ℝ)) atTop (𝓝 (Real.exp p.2)) := by
        refine Filter.Eventually.of_forall (fun p => ?_)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop ⌈Real.exp p.2⌉₊] with M hM
        have : Real.exp p.2 ≤ (M : ℝ) :=
          (Nat.le_ceil _).trans (by exact_mod_cast hM)
        exact (min_eq_left this).symm
      have h_dom : ∀ M : ℕ, ∀ᵐ p ∂π,
          ‖min (Real.exp p.2) (M : ℝ)‖ ≤ Real.exp p.2 := by
        intro M
        refine Filter.Eventually.of_forall (fun p => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) (Nat.cast_nonneg _))]
        exact min_le_left _ _
      have h_meas : ∀ M : ℕ,
          AEStronglyMeasurable (fun p : E × ℝ => min (Real.exp p.2) (M : ℝ)) π :=
        fun M => ((Real.continuous_exp.comp continuous_snd).min
          continuous_const).aestronglyMeasurable
      have h_conv := MeasureTheory.tendsto_integral_of_dominated_convergence
        (F := fun (M : ℕ) (p : E × ℝ) => min (Real.exp p.2) (M : ℝ))
        (f := fun p : E × ℝ => Real.exp p.2) (bound := fun p : E × ℝ => Real.exp p.2)
        h_meas h_exp_int_π h_dom h_lim
      rw [h_exp_int_π_eq_one] at h_conv
      exact h_conv
    -- Start ε argument.
    rw [Metric.tendsto_nhds]
    intro ε hε
    set C : ℝ := ‖f‖ + 1 with hC_def
    have hC_pos : 0 < C := by positivity
    have hnorm_le_C : ‖f‖ ≤ C := by simp [hC_def]
    have hthresh_pos : 0 < ε / (3 * C) := by positivity
    -- UI threshold on sequence side.
    obtain ⟨M_UI, hM_UI_nonneg, N_UI, hN_UI⟩ :=
      h_UI (ε / (3 * C)) hthresh_pos
    -- Target-side pick M_target so `1 - ε/(3C) < ∫ min(exp, M_target) dπ`.
    have h_ev_target : ∀ᶠ M : ℕ in atTop,
        (1 : ℝ) - ε / (3 * C) < ∫ p, min (Real.exp p.2) (M : ℝ) ∂π := by
      have h_mem : Set.Ioi ((1 : ℝ) - ε / (3 * C)) ∈ 𝓝 (1 : ℝ) :=
        Ioi_mem_nhds (by linarith)
      exact h_target_tendsto h_mem
    obtain ⟨M_target, hM_target⟩ := h_ev_target.exists
    -- Take M := max M_UI (M_target : ℝ).
    set M : ℝ := max M_UI (M_target : ℝ) with hM_def
    have hM_nonneg : 0 ≤ M := le_max_of_le_left hM_UI_nonneg
    have hM_ge_UI : M_UI ≤ M := le_max_left _ _
    have hM_ge_target : (M_target : ℝ) ≤ M := le_max_right _ _
    -- BCF `g_M(p) := f(p.1) · min(exp(p.2), M)`, norm ≤ ‖f‖ · M.
    let g_M : E × ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
      (fun p => f p.1 * min (Real.exp p.2) M)
      ((f.continuous.comp continuous_fst).mul
        ((Real.continuous_exp.comp continuous_snd).min continuous_const))
      (‖f‖ * M)
      (fun p => by
        rw [Real.norm_eq_abs, abs_mul]
        have h2 : 0 ≤ min (Real.exp p.2) M :=
          le_min (h_exp_nonneg _) hM_nonneg
        rw [abs_of_nonneg h2]
        refine mul_le_mul ?_ (min_le_right _ _) h2 (norm_nonneg _)
        exact hfbound p)
    have hg_M_apply : ∀ p, g_M p = f p.1 * min (Real.exp p.2) M := fun _ => rfl
    -- Weak convergence at g_M.
    have h_weak_gM := h_joint_weak g_M
    rw [Metric.tendsto_nhds] at h_weak_gM
    have hε3_pos : (0 : ℝ) < ε / 3 := by linarith
    obtain ⟨N_weak, hN_weak⟩ :=
      Filter.eventually_atTop.mp (h_weak_gM (ε / 3) hε3_pos)
    -- Eventual-integrability threshold.
    obtain ⟨N_int, hN_int⟩ := Filter.eventually_atTop.mp h_eventually_int
    rw [Filter.eventually_atTop]
    refine ⟨max (max N_UI N_weak) N_int, fun n hn => ?_⟩
    have hn_UI : N_UI ≤ n := le_of_max_le_left (le_of_max_le_left hn)
    have hn_weak : N_weak ≤ n := le_of_max_le_right (le_of_max_le_left hn)
    have hn_int : N_int ≤ n := le_of_max_le_right hn
    -- Sequence-side: `exp` integrable under `P n` (eventual) and under `(P n).map (X_n, L_n)`.
    have h_exp_int_Pn : Integrable (fun ω => Real.exp (L n ω)) (P n) := hN_int n hn_int
    have h_joint_meas : Measurable (fun ω => (X n ω, L n ω)) :=
      (hX_meas n).prodMk (hL_meas n)
    have h_exp_int_map_n :
        Integrable (fun p : E × ℝ => Real.exp p.2)
          ((P n).map (fun ω => (X n ω, L n ω))) :=
      (MeasureTheory.integrable_map_measure
        (Real.continuous_exp.comp continuous_snd).aestronglyMeasurable
        h_joint_meas.aemeasurable).mpr h_exp_int_Pn
    -- UI bound at enlarged M: monotonicity of min(exp, ·) in M.
    have h_min_mono_M : ∀ ω,
        min (Real.exp (L n ω)) M_UI ≤ min (Real.exp (L n ω)) M :=
      fun ω => min_le_min_left _ hM_ge_UI
    have h_int_trunc_UI : Integrable
        (fun ω => Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI) (P n) := by
      refine h_exp_int_Pn.sub ?_
      refine h_exp_int_Pn.mono'
        ((Real.continuous_exp.measurable.comp (hL_meas n)).min
          measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      simp only [Real.norm_eq_abs,
        abs_of_nonneg (le_min (h_exp_nonneg _) hM_UI_nonneg)]
      exact min_le_left _ _
    have h_UI_bound_Pn :
        ∫ ω, (Real.exp (L n ω) - min (Real.exp (L n ω)) M) ∂(P n) ≤ ε / (3 * C) :=
      calc ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M ∂(P n)
          ≤ ∫ ω, Real.exp (L n ω) - min (Real.exp (L n ω)) M_UI ∂(P n) :=
            integral_mono_of_nonneg
              (Filter.Eventually.of_forall
                (fun ω => sub_nonneg.mpr (min_le_left _ _)))
              h_int_trunc_UI
              (Filter.Eventually.of_forall
                (fun ω => by linarith [h_min_mono_M ω]))
        _ ≤ ε / (3 * C) := hN_UI n hn_UI
    have h_UI_bound_map_n :
        ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
            ∂((P n).map (fun ω => (X n ω, L n ω)))
          ≤ ε / (3 * C) := by
      rw [MeasureTheory.integral_map h_joint_meas.aemeasurable]
      · exact h_UI_bound_Pn
      · exact ((Real.continuous_exp.comp continuous_snd).sub
          ((Real.continuous_exp.comp continuous_snd).min
            continuous_const)).aestronglyMeasurable
    -- Target-side residue bound:
    have h_trunc_int_π : Integrable (fun p : E × ℝ => min (Real.exp p.2) M) π := by
      refine h_exp_int_π.mono'
        ((Real.continuous_exp.comp continuous_snd).min
          continuous_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Real.norm_eq_abs, abs_of_nonneg (le_min (h_exp_nonneg _) hM_nonneg)]
      exact min_le_left _ _
    have h_target_trunc_M_lb :
        (1 : ℝ) - ε / (3 * C) ≤ ∫ p, min (Real.exp p.2) M ∂π := by
      have h_mono :
          ∫ p, min (Real.exp p.2) (M_target : ℝ) ∂π
            ≤ ∫ p, min (Real.exp p.2) M ∂π := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall
            (fun p => le_min (h_exp_nonneg _) (Nat.cast_nonneg _)))
          h_trunc_int_π
          (Filter.Eventually.of_forall (fun p => min_le_min_left _ hM_ge_target))
      linarith [hM_target]
    have h_target_bound_π :
        ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π ≤ ε / (3 * C) := by
      rw [integral_sub h_exp_int_π h_trunc_int_π, h_exp_int_π_eq_one]
      linarith [h_target_trunc_M_lb]
    -- Apply residue bound on both sides.
    have h_res_map_n := h_residue_EℝR ((P n).map (fun ω => (X n ω, L n ω))) M hM_nonneg
      h_exp_int_map_n
    have h_res_π := h_residue_EℝR π M hM_nonneg h_exp_int_π
    -- Triangle inequality.
    rw [Real.dist_eq]
    have h_weak_bound :
        |∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω))) - ∫ p, g_M p ∂π| < ε / 3 := by
      have := hN_weak n hn_weak
      rwa [Real.dist_eq] at this
    have h_res_nonneg : 0 ≤ ‖f‖ := norm_nonneg _
    have h_seq_piece :
        |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
          - ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))| ≤ ε / 3 := by
      have h_gM_eq :
          ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
            = ∫ p, f p.1 * min (Real.exp p.2) M
                ∂((P n).map (fun ω => (X n ω, L n ω))) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
      rw [h_gM_eq]
      calc |∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
              - ∫ p, f p.1 * min (Real.exp p.2) M
                  ∂((P n).map (fun ω => (X n ω, L n ω)))|
          ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M)
                ∂((P n).map (fun ω => (X n ω, L n ω))) := h_res_map_n
        _ ≤ ‖f‖ * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_left h_UI_bound_map_n h_res_nonneg
        _ ≤ C * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
        _ = ε / 3 := by field_simp
    have h_target_piece :
        |∫ p, g_M p ∂π - ∫ p, f p.1 * Real.exp p.2 ∂π| ≤ ε / 3 := by
      have h_gM_eq :
          ∫ p, g_M p ∂π = ∫ p, f p.1 * min (Real.exp p.2) M ∂π :=
        integral_congr_ae (Filter.Eventually.of_forall (fun p => hg_M_apply p))
      rw [h_gM_eq, abs_sub_comm]
      calc |∫ p, f p.1 * Real.exp p.2 ∂π - ∫ p, f p.1 * min (Real.exp p.2) M ∂π|
          ≤ ‖f‖ * ∫ p, (Real.exp p.2 - min (Real.exp p.2) M) ∂π := h_res_π
        _ ≤ ‖f‖ * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_left h_target_bound_π h_res_nonneg
        _ ≤ C * (ε / (3 * C)) :=
            mul_le_mul_of_nonneg_right hnorm_le_C (by positivity)
        _ = ε / 3 := by field_simp
    set A := ∫ p, f p.1 * Real.exp p.2 ∂((P n).map (fun ω => (X n ω, L n ω)))
    set B := ∫ p, g_M p ∂((P n).map (fun ω => (X n ω, L n ω)))
    set D := ∫ p, g_M p ∂π
    set E' := ∫ p, f p.1 * Real.exp p.2 ∂π
    have h_split : A - E' = (A - B) + (B - D) + (D - E') := by ring
    rw [h_split]
    calc |(A - B) + (B - D) + (D - E')|
        ≤ |(A - B) + (B - D)| + |D - E'| := abs_add_le _ _
      _ ≤ |A - B| + |B - D| + |D - E'| := by linarith [abs_add_le (A - B) (B - D)]
      _ < ε / 3 + ε / 3 + ε / 3 := by linarith [h_seq_piece, h_weak_bound, h_target_piece]
      _ = ε := by ring
  -- ── Bridge `aₙ` (map form → `P n` form) to `bₙ = ∫ f d((Q n).map X)` via the slack. ───
  have h_a_tendsto : Tendsto
      (fun n => ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)) atTop
      (𝓝 (∫ p, f p.1 * Real.exp p.2 ∂π)) :=
    h_map_tendsto.congr h_an_map
  -- Slack `bₙ - aₙ → 0` from `|bₙ - aₙ| ≤ ‖f‖·ρ n` and `‖f‖·ρ n → 0`.
  have h_slack_tendsto : Tendsto
      (fun n => (∫ ω, f (X n ω) ∂(Q n))
        - ∫ ω, f (X n ω) * Real.exp (L n ω) ∂(P n)) atTop (𝓝 0) := by
    have h_norm_zero : Tendsto (fun n => ‖f‖ * ρ n) atTop (𝓝 0) := by
      have := hρ_tendsto.const_mul ‖f‖
      simpa using this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h_norm_zero
    rw [Real.norm_eq_abs]
    exact hρ_bound f n
  -- Conclude: `bₙ = aₙ + (bₙ - aₙ) → target + 0 = target`.
  have h_sum := h_a_tendsto.add h_slack_tendsto
  rw [add_zero] at h_sum
  refine (h_sum.congr (fun n => ?_)).congr (fun n => (h_bn_map n).symm)
  ring

end Contiguity
end AsymptoticStatistics
