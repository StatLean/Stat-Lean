import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Process.Filtration
import StatLean.ConcentrationInequalities.McDiarmid.CondHoeffding

/-! # Doob-martingale MGF bound (Lu-BDA §3.1, McDiarmid)

We prove that McDiarmid's bounded-differences function satisfies
`HasSubgaussianMGF (f(X) − E[f(X)]) (∑ₖ (‖cₖ‖₊/2)²) μ`
by building the Doob martingale Mₖ = E[f(X) | σ(X₀,...,Xₖ₋₁)] and applying
Mathlib's Azuma–Hoeffding tower theorem `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`.

MGF bound: `∀ λ, E[exp(λ(f(X) − E[f(X)]))] ≤ exp(λ² ∑ₖ cₖ²/8)`.

**Architecture:**
1. `allVars`, `natFiltration`, `doobMartingale`, `doobIncrement` — the core objects.
2. `increment_bounded_of_bounded_differences` — ONE named sorry for the missing Mathlib
   independence factorization lemma. See ESCALATE note there.
3. `increment_hasCondSubgaussianMGF` — proved by wrapping `condExp_hoeffding_mgf`
   (CondHoeffding.lean) fiber-by-fiber, using the sorry'd bound.
4. `mgf_sub_expectation_le` — proved rigorously via
   `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

section DoobDecomposition

variable {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {β : Fin n → Type*} [(i : Fin n) → MeasurableSpace (β i)]

/-! ### §1 Objects -/

/-- Pack `n` random variables into a product-valued map.
    Constitutive (Lu-BDA §3.1): the joint observable. -/
def allVars (X : ∀ i : Fin n, Ω → β i) : Ω → Π i : Fin n, β i :=
  fun ω i => X i ω

/-- Natural filtration Fₖ = σ(X₀,...,Xₖ₋₁).
    Constitutive (Lu-BDA §3.1): reveals coordinates one at a time. -/
noncomputable def natFiltration
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i)) :
    Filtration ℕ mΩ where
  seq k := ⨆ j : {j : Fin n // (j : ℕ) < k}, MeasurableSpace.comap (X j.1) inferInstance
  mono' {k l} hkl := iSup_le fun ⟨j, hj⟩ => le_iSup_of_le ⟨j, hj.trans_le hkl⟩ le_rfl
  -- LEAN-ONLY: after destructuring {j : Fin n // j.val < k}, j : Fin n so hX j applies.
  le' k := iSup_le fun ⟨j, _⟩ => measurable_iff_comap_le.mp (hX j)

/-- Doob martingale Mₖ = E[f(X) | Fₖ]. -/
noncomputable def doobMartingale
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  fun k => μ[f ∘ allVars X | (natFiltration X hX) k]

/-- Doob increment: Δ₀ = 0, Δₖ₊₁ = Mₖ₊₁ − Mₖ. -/
noncomputable def doobIncrement
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (μ : Measure Ω) : ℕ → Ω → ℝ
  | 0 => 0
  | k + 1 => doobMartingale X hX f μ (k + 1) - doobMartingale X hX f μ k

/-! ### §2 Structural lemmas -/

private lemma natFiltration_zero_eq_bot
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i)) :
    (natFiltration X hX) 0 = ⊥ := by
  show (⨆ j : {j : Fin n // (j : ℕ) < 0},
        MeasurableSpace.comap (X j.1) inferInstance) = ⊥
  exact le_antisymm
    (iSup_le (fun ⟨_, hj⟩ => absurd hj (Nat.not_lt_zero _)))
    bot_le

private lemma natFiltration_n_stronglyMeasurable
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f) :
    StronglyMeasurable[(natFiltration X hX) n] (f ∘ allVars X) := by
  -- Override the ambient MeasurableSpace Ω with (natFiltration X hX) n so that
  -- standard lemmas (measurable_pi_lambda, measurable_iff_comap_le) produce the
  -- correct domain sigma-algebra without explicit @ annotations.
  letI : MeasurableSpace Ω := (natFiltration X hX) n
  suffices h : Measurable (f ∘ allVars X) from h.stronglyMeasurable
  apply hf.comp
  apply measurable_pi_lambda
  intro i
  -- X i is measurable w.r.t. (natFiltration X hX) n because
  -- comap (X i) inferInstance ≤ ⨆ j, comap (X j) inferInstance = (natFiltration X hX) n.
  exact measurable_iff_comap_le.mpr
    (le_iSup_of_le (⟨i, i.isLt⟩ : {j : Fin n // (j : ℕ) < n}) le_rfl)

private lemma doobMartingale_zero_eq_mean
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) {μ : Measure Ω} [IsProbabilityMeasure μ] :
    doobMartingale X hX f μ 0 = fun _ => ∫ ω', f (allVars X ω') ∂μ := by
  simp only [doobMartingale]
  rw [show (natFiltration X hX) 0 = ⊥ from natFiltration_zero_eq_bot X hX]
  simp [condExp_bot, Function.comp]

private lemma doobMartingale_n_eq_f
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf_int : Integrable (f ∘ allVars X) μ) :
    doobMartingale X hX f μ n = f ∘ allVars X := by
  simp only [doobMartingale]
  -- SigmaFinite (μ.trim hm) is derived from IsFiniteMeasure, which follows from
  -- IsProbabilityMeasure μ + isFiniteMeasure_trim.
  haveI : IsFiniteMeasure (μ.trim ((natFiltration X hX).le n)) :=
    isFiniteMeasure_trim ((natFiltration X hX).le n)
  exact condExp_of_stronglyMeasurable ((natFiltration X hX).le n)
    (natFiltration_n_stronglyMeasurable X hX f hf) hf_int

private lemma sum_doobIncrement_telescope
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (μ : Measure Ω)
    (k : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range (k + 1), doobIncrement X hX f μ i ω =
      doobMartingale X hX f μ k ω - doobMartingale X hX f μ 0 ω := by
  induction k with
  | zero => simp [doobIncrement]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [doobIncrement, Pi.sub_apply]
    ring

private lemma doobIncrement_stronglyAdapted
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    StronglyAdapted (natFiltration X hX) (doobIncrement X hX f μ) := by
  intro k
  match k with
  | 0 => exact stronglyMeasurable_const
  | k + 1 =>
    -- Unfold to: StronglyMeasurable[(natFiltration X hX) (k+1)]
    --   (μ[f ∘ allVars X | (natFiltration X hX) (k+1)] - μ[f ∘ allVars X | (natFiltration X hX) k])
    simp only [doobIncrement, doobMartingale]
    exact stronglyMeasurable_condExp.sub
      (stronglyMeasurable_condExp.mono ((natFiltration X hX).mono' (Nat.le_succ k)))

/-! ### §3 Sub-Gaussian parameter book-keeping -/

private noncomputable def doobCY (c : Fin n → ℝ) : ℕ → ℝ≥0
  | 0 => 0
  | k + 1 => if hk : k < n then (‖c ⟨k, hk⟩‖₊ / 2) ^ 2 else 0

private lemma doobCY_zero (c : Fin n → ℝ) : doobCY c 0 = 0 := rfl

private lemma doobCY_succ (c : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    doobCY c (k + 1) = (‖c ⟨k, hk⟩‖₊ / 2) ^ 2 := by simp [doobCY, hk]

private lemma sum_doobCY_eq (c : Fin n → ℝ) :
    ∑ i ∈ Finset.range (n + 1), doobCY c i = ∑ k : Fin n, (‖c k‖₊ / 2) ^ 2 := by
  -- sum_range_succ' rewrites ∑_{i<n+1} = ∑_{i<n} f(i+1) + f(0).
  rw [Finset.sum_range_succ', doobCY_zero, add_zero]
  -- sum_fin_eq_sum_range rewrites ∑_{k:Fin n} = ∑_{i<n} if h:i<n then f⟨i,h⟩ else 0.
  rw [Finset.sum_fin_eq_sum_range]
  -- Both sums now over range n; each term equals doobCY c (i+1) = if h:i<n then ... else 0.
  -- congr 1 closes by definitional equality of doobCY.
  congr 1

/-! ### §4 Conditional sub-Gaussianity of each increment -/

/-- **[SORRY]** Under `iIndepFun X μ` and the bounded-differences condition, the Doob
    increment `Δₖ₊₁ = Mₖ₊₁ − Mₖ` is globally a.e. bounded in `[−cₖ, cₖ]` and fiber-wise
    a.e. bounded in an interval of length exactly `cₖ`.

    **ESCALATE:** Both bounds require the independence factorization
    `condDistrib(Xₖ | σ(X₀,...,Xₖ₋₁), μ) = const(μ.map Xₖ)` under `iIndepFun`,
    which is not yet in Mathlib. The global bound follows from the oscillation bound
    `sup_y g(y) − inf_y g(y) ≤ cₖ` (bounded differences) applied to the conditional mean
    `g(y) = E[f(x₀,...,y,...) | remaining]`; the fiber-wise bound uses the same `g` to
    identify the specific interval `[inf_y g(y) − E[g(Xₖ)], sup_y g(y) − E[g(Xₖ)]]`. -/
private lemma increment_bounded_of_bounded_differences
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    (hf_int : Integrable (f ∘ allVars X) μ)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    -- USER-INPUT: bounded differences Dᵢf ≤ cᵢ; Lu-BDA §3.1.
    (hbd : ∀ k : Fin n, ∀ x : Π i : Fin n, β i, ∀ y : β k,
        |f x - f (Function.update x k y)| ≤ c k)
    -- USER-INPUT: independence of (X i); Lu-BDA §3.1.
    (hX_indep : iIndepFun X μ)
    (k : ℕ) (hk : k < n) :
    -- Global a.e. bound (used for integrable_exp_mul).
    (∀ᵐ ω ∂μ, doobIncrement X hX f μ (k + 1) ω ∈ Set.Icc (-(c ⟨k, hk⟩)) (c ⟨k, hk⟩)) ∧
    -- Fiber-wise bound of length cₖ (used for the tight MGF constant).
    (∀ᵐ ω' ∂(μ.trim ((natFiltration X hX).le k)),
      ∃ a : ℝ, ∀ᵐ ω ∂(condExpKernel μ ((natFiltration X hX) k) ω'),
        doobIncrement X hX f μ (k + 1) ω ∈ Set.Icc a (a + c ⟨k, hk⟩)) := by
  -- ESCALATE: condDistrib(Xₖ | σ(X₀,...,Xₖ₋₁), μ) = const(μ.map Xₖ) under iIndepFun
  -- is absent from Mathlib; both parts of this conjunction require it.
  sorry

/-- Each Doob increment `Δₖ₊₁ = Mₖ₊₁ − Mₖ` satisfies `HasCondSubgaussianMGF` w.r.t. `Fₖ`
    with parameter `(‖cₖ‖₊/2)²`.

    **Proof:** The tower property `E[Mₖ₊₁|Fₖ] = Mₖ` gives zero conditional mean.
    The bounded-differences bound gives the fiber-wise range. Apply
    `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` fiber-by-fiber. -/
lemma increment_hasCondSubgaussianMGF
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    (hf_int : Integrable (f ∘ allVars X) μ)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    -- USER-INPUT: bounded differences; Lu-BDA §3.1.
    (hbd : ∀ k : Fin n, ∀ x : Π i : Fin n, β i, ∀ y : β k,
        |f x - f (Function.update x k y)| ≤ c k)
    -- USER-INPUT: independence of (X i); Lu-BDA §3.1.
    (hX_indep : iIndepFun X μ)
    (k : ℕ) (hk : k < n) :
    HasCondSubgaussianMGF ((natFiltration X hX) k) ((natFiltration X hX).le k)
      (doobIncrement X hX f μ (k + 1)) ((‖c ⟨k, hk⟩‖₊ / 2) ^ 2) μ := by
  -- hm_k is a proof term, not a MeasurableSpace instance; safe to use `have`.
  have hm_k : (natFiltration X hX) k ≤ mΩ := (natFiltration X hX).le k
  -- Δ : Ω → ℝ, not a typeclass — `let` is fine.
  let Δ := doobIncrement X hX f μ (k + 1)
  -- Integrability: Δ = Mₖ₊₁ − Mₖ, both integrable as conditional expectations.
  have h_int_k1 : Integrable (doobMartingale X hX f μ (k + 1)) μ := integrable_condExp
  have h_int_k : Integrable (doobMartingale X hX f μ k) μ := integrable_condExp
  have hΔ_int : Integrable Δ μ := h_int_k1.sub h_int_k
  have hΔ_aem : AEMeasurable Δ μ := hΔ_int.1.aemeasurable
  -- Tower: μ[Δ | Fₖ] = 0 a.e.
  -- condExp_sub gives μ[Mₖ₊₁ − Mₖ | Fₖ] = μ[Mₖ₊₁|Fₖ] − μ[Mₖ|Fₖ].
  have h_sub : μ[Δ | (natFiltration X hX) k] =ᵐ[μ]
      μ[doobMartingale X hX f μ (k + 1) | (natFiltration X hX) k] -
      μ[doobMartingale X hX f μ k | (natFiltration X hX) k] :=
    condExp_sub h_int_k1 h_int_k ((natFiltration X hX) k)
  -- Tower: μ[Mₖ₊₁ | Fₖ] = μ[μ[f∘X|Fₖ₊₁] | Fₖ] = μ[f∘X|Fₖ] = Mₖ.
  have htower :
      μ[doobMartingale X hX f μ (k + 1) | (natFiltration X hX) k] =ᵐ[μ]
      doobMartingale X hX f μ k :=
    Filtration.condExp_condExp (f ∘ allVars X) (natFiltration X hX) (Nat.le_succ k)
  -- Mₖ is Fₖ-measurable, so μ[Mₖ | Fₖ] = Mₖ (plain eq, lifted to ae).
  have hMk :
      μ[doobMartingale X hX f μ k | (natFiltration X hX) k] =ᵐ[μ]
      doobMartingale X hX f μ k :=
    ae_of_all μ (congr_fun
      (condExp_of_stronglyMeasurable hm_k stronglyMeasurable_condExp h_int_k))
  have h_condExp_zero : μ[Δ | (natFiltration X hX) k] =ᵐ[μ] (0 : Ω → ℝ) := by
    filter_upwards [h_sub, htower, hMk] with ω h1 h2 h3
    simp only [Pi.sub_apply, Pi.zero_apply] at *
    linarith
  -- Disintegration: condExp via kernel integral.
  have hμ_eq :
      condExpKernel μ ((natFiltration X hX) k) ∘ₘ μ.trim hm_k = μ :=
    condExpKernel_comp_trim hm_k
  have h_condExp_zero_trim :
      μ[Δ | (natFiltration X hX) k] =ᵐ[μ.trim hm_k] (0 : Ω → ℝ) :=
    stronglyMeasurable_condExp.ae_eq_trim_of_stronglyMeasurable hm_k
      stronglyMeasurable_zero h_condExp_zero
  have h_disint :
      μ[Δ | (natFiltration X hX) k] =ᵐ[μ.trim hm_k]
      fun ω' => ∫ y, Δ y ∂(condExpKernel μ ((natFiltration X hX) k) ω') :=
    condExp_ae_eq_trim_integral_condExpKernel hm_k hΔ_int
  -- Per-fiber zero mean.
  have h_fiber_zero : ∀ᵐ ω' ∂(μ.trim hm_k),
      ∫ y, Δ y ∂(condExpKernel μ ((natFiltration X hX) k) ω') = 0 := by
    filter_upwards [h_disint.symm.trans h_condExp_zero_trim] with ω' h
    simpa using h
  -- Per-fiber AEMeasurable.
  have h_fiber_aem : ∀ᵐ ω' ∂(μ.trim hm_k),
      AEMeasurable Δ (condExpKernel μ ((natFiltration X hX) k) ω') := by
    have h1 : Integrable Δ (condExpKernel μ ((natFiltration X hX) k) ∘ₘ μ.trim hm_k) := by
      rw [hμ_eq]; exact hΔ_int
    filter_upwards [Measure.ae_integrable_of_integrable_comp h1] with ω' hI
    exact hI.aestronglyMeasurable.aemeasurable
  -- Bounded differences → global bound + fiber-wise bound (the one sorry).
  obtain ⟨h_global, h_fiber_bound⟩ :=
    increment_bounded_of_bounded_differences X hX f hf hf_int c hc hbd hX_indep k hk
  -- Build HasCondSubgaussianMGF = Kernel.HasSubgaussianMGF.
  refine ⟨?_, ?_⟩
  · -- integrable_exp_mul: use global bound [−cₖ, cₖ].
    intro t
    rw [hμ_eq]
    exact integrable_exp_mul_of_mem_Icc hΔ_aem h_global
  · -- mgf_le: fiber-by-fiber, tight interval [a, a + cₖ].
    filter_upwards [h_fiber_bound, h_fiber_zero, h_fiber_aem] with ω' h_bd_ex h_mean h_aem
    obtain ⟨a, h_bd⟩ := h_bd_ex
    intro t
    -- Apply Hoeffding fiber-by-fiber; interval length exactly cₖ.
    have h_subg : HasSubgaussianMGF Δ ((‖c ⟨k, hk⟩‖₊ / 2) ^ 2)
        (condExpKernel μ ((natFiltration X hX) k) ω') := by
      have h' := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero h_aem h_bd h_mean
      rwa [show ‖(a + c ⟨k, hk⟩) - a‖₊ = ‖c ⟨k, hk⟩‖₊ from by congr 1; ring] at h'
    exact h_subg.mgf_le t

/-! ### §5 Main theorem: McDiarmid MGF bound -/

/-- **Doob-martingale MGF bound for McDiarmid** (Lu-BDA §3.1).

For `n` independent random variables `X = (X₀,...,Xₙ₋₁)` and a function `f` satisfying the
bounded-differences condition with constants `c : Fin n → ℝ`, the centered evaluation
`f(X) − E[f(X)]` is sub-Gaussian with parameter `∑ₖ (‖cₖ‖₊/2)²`:

  `HasSubgaussianMGF (f(X) − E[f(X)]) (∑ₖ (‖cₖ‖₊/2)²) μ`

MGF bound: `∀ λ, E[exp(λ(f(X) − E[f(X)]))] ≤ exp((∑ₖ cₖ²/4) · λ²/2) = exp(λ² ∑ₖ cₖ²/8)`.

The proof uses Mathlib's `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF` (Azuma tower
theorem), feeding `increment_hasCondSubgaussianMGF` for each step. -/
theorem mgf_sub_expectation_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    -- USER-INPUT: bounded differences; Lu-BDA §3.1.
    (hbd : ∀ k : Fin n, ∀ x : Π i : Fin n, β i, ∀ y : β k,
        |f x - f (Function.update x k y)| ≤ c k)
    -- USER-INPUT: independence of (X i); Lu-BDA §3.1.
    (hX_indep : iIndepFun X μ)
    -- USER-INPUT: f(X) integrable; Lu-BDA §3.1 (implicit regularity).
    (hf_int : Integrable (f ∘ allVars X) μ) :
    HasSubgaussianMGF (fun ω => f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)
      (∑ k : Fin n, (‖c k‖₊ / 2) ^ 2) μ := by
  -- Step 1: Apply Azuma tower theorem to doobIncrement / doobCY.
  -- Provide `cY := doobCY c` explicitly; Lean cannot infer it from a per-point constraint.
  have h_sum : HasSubgaussianMGF
      (fun ω => ∑ i ∈ Finset.range (n + 1), doobIncrement X hX f μ i ω)
      (∑ i ∈ Finset.range (n + 1), doobCY c i) μ := by
    apply HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF (cY := doobCY c)
      (doobIncrement_stronglyAdapted X hX f μ) HasSubgaussianMGF.zero (n + 1)
    intro i hi
    rw [doobCY_succ c i (by omega)]
    exact increment_hasCondSubgaussianMGF X hX f hf hf_int c hc hbd hX_indep i (by omega)
  -- Step 2: Simplify the parameter sum.
  rw [sum_doobCY_eq] at h_sum
  -- Step 3: Identify ∑ doobIncrement = f(X) − E[f(X)] pointwise.
  have h_eq : (fun ω => ∑ i ∈ Finset.range (n + 1), doobIncrement X hX f μ i ω) =
      fun ω => f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ := by
    funext ω
    -- Telescope: ∑ Δᵢ = M_n − M_0.
    rw [sum_doobIncrement_telescope X hX f μ n ω]
    -- M_n = f ∘ allVars X (a.e., here pointwise via condExp_of_stronglyMeasurable).
    have hn := congr_fun (doobMartingale_n_eq_f X hX f hf hf_int) ω
    -- M_0 = fun _ => E[f(X)].
    have h0 := congr_fun (doobMartingale_zero_eq_mean (μ := μ) X hX f) ω
    simp only [Function.comp] at hn
    simp only [h0, hn]
  rwa [h_eq] at h_sum

end DoobDecomposition

end StatLean.ConcentrationInequalities
