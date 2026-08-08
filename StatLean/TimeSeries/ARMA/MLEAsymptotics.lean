import StatLean.TimeSeries.ARMA.Consistency
import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.BrownCLT
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Hannan's theorem: asymptotic normality of the ARMA Gaussian MLE (FY Theorem 3.2)

The head of the commissioned Hannan program (ledger (a), batches C–D): for a
stationary causal invertible ARMA(p, q) with **iid** noise and coprime minimal orders,
any measurable approximate-MLE sequence over a compact identifiable region satisfies

`√T (θ̂_T − θ₀) →d N(0, W)`, `W = (hannanVarZ b₀ a₀)⁻¹` (FY eq. (3.14)),

stated in Cramér–Wold/charFun form, together with `σ̂² →p σ²`. FY's remarks are
honored: **no fourth moment is required**, and the noise assumption is exactly iid
(the martingale-difference weakening is future work, not stated).

Also here:
* **FY Proposition 3.1** (PACF asymptotics; misprint corrected — the scaling is `√T`,
  not `T^{−1/2}`): for a causal AR(p) with iid noise and `k > p`, the sample PACF
  `π̂(k)` (Yule–Walker form on the sample ACVF) satisfies `√T π̂(k) →d N(0, 1)`;
* literature DEBTS: the asymptotic equivalence LS = YW = MLE (B&D Thm 10.8.2) and the
  reciprocal-variance identity `(Γ_k⁻¹)_{kk} = σ⁻²` for `k > p` (FY "can be proved" —
  attempted in the lane, demotable).

**Assembly plan** (lane prompt carries detail): consistency (`mle_consistent`) +
score MDS (`armaScore_condexp_zero` + Brown `mds_clt_sequence`) + Hessian/information
LLN + the standard Taylor/sandwich argument on the profiled criterion.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.3.2,
Theorem 3.2, eq. (3.14), Prop 3.1 (pp. 96–99); E. J. Hannan, J. Appl. Probab. 10
(1973) 130–145; Brockwell & Davis (1991) §8.7–§10.8. (`FY §3.3 Thm 3.2 / Hannan
1973`.)
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section CharFunBricks

/-! ### charFun bricks

Two elementary tools used throughout the file: the pushforward characteristic function
as an integral over the base space, and the **charFun form of Slutsky's theorem**
(`tendsto_charFun_of_tendstoInProb_sub`) — the only limit-theory glue the assembly
below needs, since the scalar multiplier of the sandwich is absorbed into the Gaussian
scale by `charFun_map_mul_comp` rather than by a multiplier-Slutsky argument. -/

/-- charFun of a pushforward, as an integral on the base space. -/
private lemma charFun_map_eq_integral {f : Ω → ℝ} (hf : AEMeasurable f μ) (u : ℝ) :
    charFun (μ.map f) u = ∫ ω, Complex.exp (Complex.I * (u * f ω : ℝ)) ∂μ := by
  rw [charFun_apply_real, integral_map hf (by fun_prop)]
  simp only [Complex.ofReal_mul]
  congr 1 with ω
  ring_nf

private lemma integrable_cexp_mul_I {f : Ω → ℝ} [IsFiniteMeasure μ] (hf : Measurable f) :
    Integrable (fun ω => Complex.exp (Complex.I * (f ω : ℝ))) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (Complex.measurable_exp.comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with ω
  simp [Complex.norm_exp]

/-- The elementary two-point bound `‖e^{ix} − e^{iy}‖ ≤ min(|x − y|, 2)`. -/
private lemma norm_cexp_sub_cexp_le (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℝ)) - Complex.exp (Complex.I * (y : ℝ))‖
      ≤ min |x - y| 2 := by
  have hfact : Complex.exp (Complex.I * (x : ℝ)) - Complex.exp (Complex.I * (y : ℝ))
      = Complex.exp (Complex.I * (y : ℝ)) * (Complex.exp (Complex.I * ((x - y : ℝ))) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hfact, norm_mul, show ‖Complex.exp (Complex.I * (y : ℝ))‖ = 1 by simp [Complex.norm_exp],
    one_mul, le_min_iff]
  refine ⟨by simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y), ?_⟩
  calc ‖Complex.exp (Complex.I * ((x - y : ℝ))) - 1‖
      ≤ ‖Complex.exp (Complex.I * ((x - y : ℝ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by simp [Complex.norm_exp]; norm_num

/-- **Slutsky's theorem at the charFun level**: two sequences of random variables whose
difference tends to `0` in probability have the same characteristic-function limits.
The quantitative core is `‖E e^{iuZ} − E e^{iuY}‖ ≤ |u| δ + 2 μ{|Z − Y| ≥ δ}`. -/
private lemma tendsto_charFun_of_tendstoInProb_sub [IsProbabilityMeasure μ]
    {Y Z : ℕ → Ω → ℝ} (hY : ∀ T, Measurable (Y T)) (hZ : ∀ T, Measurable (Z T))
    {L : ℂ} {u : ℝ}
    (hlim : Tendsto (fun T => charFun (μ.map (Y T)) u) atTop (𝓝 L))
    (hsub : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun T => (μ {ω | δ ≤ |Z T ω - Y T ω|}).toReal) atTop (𝓝 0)) :
    Tendsto (fun T => charFun (μ.map (Z T)) u) atTop (𝓝 L) := by
  have key : ∀ (δ : ℝ), 0 < δ → ∀ T : ℕ,
      ‖charFun (μ.map (Z T)) u - charFun (μ.map (Y T)) u‖
        ≤ |u| * δ + 2 * (μ {ω | δ ≤ |Z T ω - Y T ω|}).toReal := by
    intro δ hδ T
    have hmset : MeasurableSet {ω | δ ≤ |Z T ω - Y T ω|} :=
      measurableSet_le measurable_const ((hZ T).sub (hY T)).abs
    rw [charFun_map_eq_integral (hZ T).aemeasurable, charFun_map_eq_integral (hY T).aemeasurable,
      ← integral_sub (integrable_cexp_mul_I ((hZ T).const_mul u))
        (integrable_cexp_mul_I ((hY T).const_mul u))]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ ω, ‖Complex.exp (Complex.I * ((u * Z T ω : ℝ)))
          - Complex.exp (Complex.I * ((u * Y T ω : ℝ)))‖
        ≤ |u| * δ + 2 * Set.indicator {ω | δ ≤ |Z T ω - Y T ω|} (1 : Ω → ℝ) ω := by
      intro ω
      refine (norm_cexp_sub_cexp_le _ _).trans ?_
      have hind : (0 : ℝ) ≤ Set.indicator {ω | δ ≤ |Z T ω - Y T ω|} (1 : Ω → ℝ) ω :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      have huδ : (0 : ℝ) ≤ |u| * δ := mul_nonneg (abs_nonneg _) hδ.le
      by_cases hω : ω ∈ {ω | δ ≤ |Z T ω - Y T ω|}
      · rw [Set.indicator_of_mem hω]
        exact le_trans (min_le_right _ (2 : ℝ)) (by simp; linarith)
      · simp only [Set.mem_setOf_eq, not_le] at hω
        have h1 : |u * Z T ω - u * Y T ω| ≤ |u| * δ := by
          rw [show u * Z T ω - u * Y T ω = u * (Z T ω - Y T ω) by ring, abs_mul]
          exact mul_le_mul_of_nonneg_left hω.le (abs_nonneg _)
        exact le_trans (min_le_left _ _) (by linarith)
    refine (integral_mono ?_ ?_ hpt).trans_eq ?_
    · exact ((integrable_cexp_mul_I ((hZ T).const_mul u)).sub
        (integrable_cexp_mul_I ((hY T).const_mul u))).norm
    · exact (integrable_const _).add
        (((integrable_const (1 : ℝ)).indicator hmset).const_mul 2)
    · have h1 : Integrable (fun _ : Ω => |u| * δ) μ := integrable_const _
      have h2 : Integrable
          (fun x : Ω => 2 * Set.indicator {ω | δ ≤ |Z T ω - Y T ω|} (1 : Ω → ℝ) x) μ :=
        ((integrable_const (1 : ℝ)).indicator hmset).const_mul 2
      have h3 : ∫ x : Ω, 2 * Set.indicator {ω | δ ≤ |Z T ω - Y T ω|} (1 : Ω → ℝ) x ∂μ
          = 2 * (μ {ω | δ ≤ |Z T ω - Y T ω|}).toReal := by
        rw [integral_const_mul, integral_indicator_one hmset, measureReal_def]
      rw [integral_add h1 h2, integral_const, h3, probReal_univ, smul_eq_mul, one_mul]
  have hdiff : Tendsto (fun T => charFun (μ.map (Z T)) u - charFun (μ.map (Y T)) u)
      atTop (𝓝 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨δ, hδ, hδlt⟩ : ∃ δ : ℝ, 0 < δ ∧ |u| * δ < ε := by
      refine ⟨ε / (|u| + 1), by positivity, ?_⟩
      have hstep : |u| * (ε / (|u| + 1)) < (|u| + 1) * (ε / (|u| + 1)) :=
        mul_lt_mul_of_pos_right (by linarith) (by positivity)
      have heq : (|u| + 1) * (ε / (|u| + 1)) = ε := by field_simp
      linarith [heq ▸ hstep]
    have hev : ∀ᶠ T in atTop, 2 * (μ {ω | δ ≤ |Z T ω - Y T ω|}).toReal < ε - |u| * δ :=
      ((hsub δ hδ).const_mul 2).eventually_lt_const (by simpa using sub_pos.2 hδlt)
    filter_upwards [hev] with T hT
    exact lt_of_le_of_lt (key δ hδ T) (by linarith)
  simpa using hdiff.add hlim

/-- Splitting a bad event into two, at the level of the real-valued measure. -/
private lemma toReal_measure_le_of_subset_union [IsFiniteMeasure μ] {A B C : Set Ω}
    (hsub : A ⊆ B ∪ C) : (μ A).toReal ≤ (μ B).toReal + (μ C).toReal := by
  rw [← ENNReal.toReal_add (measure_ne_top μ B) (measure_ne_top μ C)]
  exact ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨measure_ne_top μ B, measure_ne_top μ C⟩)
    ((measure_mono hsub).trans (measure_union_le B C))

/-- The three-way version of `toReal_measure_le_of_subset_union`. -/
private lemma toReal_measure_le_of_subset_union₃ [IsFiniteMeasure μ] {A B C D : Set Ω}
    (hsub : A ⊆ B ∪ (C ∪ D)) :
    (μ A).toReal ≤ (μ B).toReal + ((μ C).toReal + (μ D).toReal) := by
  have h1 := toReal_measure_le_of_subset_union (μ := μ) hsub
  have h2 := toReal_measure_le_of_subset_union (μ := μ) (A := C ∪ D) (B := C) (C := D) subset_rfl
  linarith

end CharFunBricks

/-- **FY Theorem 3.2 (Hannan), Cramér–Wold/charFun form**: under the `mle_consistent`
setting, every linear combination of `√T (θ̂_T − θ₀)` is asymptotically
`N(0, cᵀ W c)` with `W = (hannanVarZ b₀ a₀)⁻¹`. -/
theorem hannan_mle_clt [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ)
    -- USER-INPUT: iid innovations; FY Thm 3.2 (no 4th moment required)
    (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    -- USER-INPUT: (b₀, a₀) ∈ 𝓑; FY eq. (3.11)
    (hB0 : ARMAInvertibleParams b0 a0)
    -- USER-INPUT: coprime minimal orders; Hannan 1973 (FY implicit)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    -- USER-INPUT: exact orders (see `hannanVarZ_posDef`'s docstring — coprimality alone
    -- does not make the information matrix invertible); Hannan 1973 §2
    (hbdeg : (arPoly b0).natDegree = p) (hadeg : (maPoly a0).natDegree = q)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))}
    -- USER-INPUT: compact identifiable search region with θ₀ interior; Hannan §2
    (hK : IsCompact K) (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
    -- USER-INPUT: the search region consists of minimal models (see `mle_consistent`'s
    -- docstring for the Lean witness showing this cannot be dropped); Hannan 1973 §2
    (hcopK : ∀ ba ∈ K, IsCoprime (arPoly ba.1) (maPoly ba.2))
    (hK0 : (b0, a0) ∈ interior K)
    (θ : (T : ℕ) → Ω → (Fin p → ℝ) × (Fin q → ℝ))
    (hθmeas : ∀ T, Measurable (θ T))
    {δT : ℕ → ℝ} (hδT0 : ∀ T, 0 ≤ δT T)
    -- USER-INPUT: approximate minimization at rate o(1/T) (exact minimizers
    -- qualify); FY eq. (3.10) argmax corrected
    (hδTfast : Tendsto (fun T : ℕ => (T : ℝ) * δT T) atTop (𝓝 0))
    (hargmin : ∀ (T : ℕ) (ω : Ω), θ T ω ∈ K ∧ ∀ ba ∈ K,
      armaProfileCriterion (θ T ω).1 (θ T ω).2
          (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
        ≤ armaProfileCriterion ba.1 ba.2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) + δT T)
    (c : Fin p ⊕ Fin q → ℝ) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T *
          ((∑ i : Fin p, c (.inl i) * ((θ T ω).1 i - b0 i)) +
            ∑ j : Fin q, c (.inr j) * ((θ T ω).2 j - a0 j))) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (c ⬝ᵥ ((hannanVarZ b0 a0)⁻¹ *ᵥ c)))) u)) := by
  sorry

section Sigma2

/-! ### The two inputs of the variance part

`S(θ̂_T)/T = (S(θ̂_T)/T − S(θ₀)/T) + S(θ₀)/T`: the second term is the quadratic-form
LLN at the truth, the first is killed by consistency plus a local equicontinuity
estimate. Both are recorded as named debts below; everything else is proved. -/

/-- **DEBT — the quadratic-form LLN at the truth**: `T⁻¹ xᵀ Γ_T(θ₀)⁻¹ x →p σ²`.

This is **not a second copy** of Consistency's ergodic debt: it is exactly that lane's
`armaProfileS_tendstoInProb` specialised to `θ = θ₀` (where the contrast variance is
`1`, by `armaContrastVar_eq_one_iff`). That lemma is `private` to
`ARMA/Consistency.lean` and therefore not citeable from this module, and the public
`criterion_tendsto_contrast` is **strictly weaker** than what is needed here: it
controls `log(S_T/T) + T⁻¹ log det Γ_T`, and `Real.log` is not injective at Lean's junk
value (`Real.log 0 = 0`), so at `σ² = 1` the degenerate event `{S_T = 0}` is invisible
at the `log` level and the `exp`-transfer back to `S_T/T` fails. Relocating the
statement is the only repair available inside this lane's touch-set; the project-level
fix is to make Consistency's lemma public. -/
private theorem armaProfileS_atTruth_tendstoInProb [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T : ℕ => (μ {ω | η ≤
        |armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2|}).toReal)
      atTop (𝓝 0) := by
  sorry

/-- **DEBT — local stochastic equicontinuity of the profiled sum of squares**: the
oscillation of `θ ↦ T⁻¹ S_T(θ)` over a small ball around `θ₀` is uniformly (in `T`)
negligible in probability.

Hannan's ergodic route proves this together with the pointwise LLN: `T⁻¹ S_T(θ)` is,
up to the `O(1/T)` edge effect controlled by `logdet_armaToeplitz_vanishes`'s
whitened-Toeplitz factorisation, the time average `T⁻¹ Σ_t r_t(θ)²` of the squared
`θ`-residual process, and `θ ↦ r_t(θ)` is Lipschitz in `θ` on the compact `K ⊆ 𝓑`
with an `L²`-integrable Lipschitz constant (geometric decay of `∂π_j/∂θ`, uniform on
`K` by `exists_geometric_bound_armaPi`). The missing ingredient is the same one that
blocks Consistency's lane — the pointwise ergodic theorem, absent from Mathlib — so
this is recorded rather than proved. It is the same brick Consistency's `mle_consistent`
needs for its finite-subcover step. -/
private theorem armaProfileS_equicontinuous [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))}
    (hK : IsCompact K) (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun T : ℕ => (μ {ω | ∃ ba ∈ K, dist ba (b0, a0) < ρ ∧
          η ≤ |armaProfileS ba.1 ba.2 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T
            - armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T|}).toReal)
        atTop (𝓝 0) := by
  sorry

end Sigma2

/-- **FY Theorem 3.2, variance part**: the profiled variance estimator is consistent,
`σ̂²_T = S(θ̂_T)/T →p σ²`. -/
theorem hannan_sigma2_consistent [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    -- USER-INPUT: exact orders (see `hannanVarZ_posDef`); Hannan 1973 §2
    (hbdeg : (arPoly b0).natDegree = p) (hadeg : (maPoly a0).natDegree = q)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))}
    (hK : IsCompact K) (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
    -- USER-INPUT: the search region consists of minimal models (see `mle_consistent`'s
    -- docstring for the Lean witness showing this cannot be dropped); Hannan 1973 §2
    (hcopK : ∀ ba ∈ K, IsCoprime (arPoly ba.1) (maPoly ba.2))
    (hK0 : (b0, a0) ∈ interior K)
    (θ : (T : ℕ) → Ω → (Fin p → ℝ) × (Fin q → ℝ)) (hθmeas : ∀ T, Measurable (θ T))
    {δT : ℕ → ℝ} (hδT0 : ∀ T, 0 ≤ δT T)
    (hδTfast : Tendsto (fun T : ℕ => (T : ℝ) * δT T) atTop (𝓝 0))
    (hargmin : ∀ (T : ℕ) (ω : Ω), θ T ω ∈ K ∧ ∀ ba ∈ K,
      armaProfileCriterion (θ T ω).1 (θ T ω).2
          (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
        ≤ armaProfileCriterion ba.1 ba.2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) + δT T)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ => (μ {ω | δ ≤
        |armaProfileS (θ T ω).1 (θ T ω).2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2|}).toReal)
      atTop (𝓝 0) := by
  classical
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  -- `hδTfast` (rate `o(1/T)`) certainly gives the plain `δ_T → 0` that consistency needs
  have hδT : Tendsto δT atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall hδT0) ?_ hδTfast
    filter_upwards [eventually_ge_atTop 1] with T hT
    have h1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    nlinarith [hδT0 T]
  -- the three inputs
  obtain ⟨ρ, hρ, hequi⟩ :=
    armaProfileS_equicontinuous h hiid hσ hB0 hcausal hmeas hK hKB hδ2
  have htruth := armaProfileS_atTruth_tendstoInProb h hiid hσ hB0 hcausal hmeas hδ2
  have hcons := mle_consistent h hiid hσ hB0 hcop hcausal hmeas hK hKB hcopK
    (interior_subset hK0) θ hθmeas hδT hδT0 hargmin hρ
  -- `|S(θ̂)/T − σ²| ≥ δ` forces either `|S(θ₀)/T − σ²| ≥ δ/2`, or `θ̂` far from `θ₀`,
  -- or an oscillation of size `δ/2` inside the `ρ`-ball
  have hg : Tendsto (fun T : ℕ =>
      (μ {ω | δ / 2 ≤
          |armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2|}).toReal
        + ((μ {ω | ρ ≤ dist (θ T ω) (b0, a0)}).toReal
          + (μ {ω | ∃ ba ∈ K, dist ba (b0, a0) < ρ ∧
              δ / 2 ≤ |armaProfileS ba.1 ba.2
                  (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T
                - armaProfileS b0 a0
                    (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T|}).toReal))
      atTop (𝓝 0) := by
    simpa using htruth.add (hcons.add hequi)
  refine squeeze_zero (fun T => ENNReal.toReal_nonneg) (fun T => ?_) hg
  refine toReal_measure_le_of_subset_union₃ (fun ω hω => ?_)
  simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
  by_cases hB : δ / 2 ≤ |armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2|
  · exact Or.inl hB
  refine Or.inr ?_
  push_neg at hB
  by_cases hC : ρ ≤ dist (θ T ω) (b0, a0)
  · exact Or.inl hC
  push_neg at hC
  refine Or.inr ⟨θ T ω, (hargmin T ω).1, hC, ?_⟩
  have habs := abs_sub_abs_le_abs_sub
    (armaProfileS (θ T ω).1 (θ T ω).2 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2)
    (armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2)
  have hrw : (armaProfileS (θ T ω).1 (θ T ω).2
        (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2)
      - (armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2)
      = armaProfileS (θ T ω).1 (θ T ω).2 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T
        - armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T := by ring
  rw [hrw] at habs
  linarith

/-- The **sample PACF** at order `k` (Yule–Walker form on the sample ACVF): the last
coordinate of the solution of the sample Yule–Walker system (junk `0` at `k = 0` or
when the sample Toeplitz matrix is singular, by the matrix-inverse convention). -/
noncomputable def samplePACF {T : ℕ} (x : Fin T → ℝ) (k : ℕ) : ℝ :=
  if hk : 0 < k then
    (((Matrix.of fun i j : Fin k =>
          sampleACVF x ((i : ℤ) - (j : ℤ)).natAbs)⁻¹)
        *ᵥ fun i : Fin k => sampleACVF x ((i : ℕ) + 1)) ⟨k - 1, by omega⟩
  else 0

/-- **FY Proposition 3.1** (misprint corrected: `√T`, not `T^{−1/2}`): for a causal
AR(p) with iid noise and lag `k > p`, the sample PACF is asymptotically standard
normal: `√T π̂(k) →d N(0, 1)`. -/
theorem samplePACF_clt [IsProbabilityMeasure μ] {p : ℕ}
    {b0 : Fin p → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsAR b0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hroot : NoRootClosedDisc b0)
    (hcausal :
      IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {k : ℕ} (hk : p < k) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * samplePACF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) k) u)
      atTop (𝓝 (charFun (gaussianReal 0 1) u)) := by
  sorry

/-- **DEBT (B&D Thm 10.8.2; FY §3.3.2 remark)**: least-squares, Yule–Walker, and
Gaussian-MLE estimator sequences of a causal AR(p) are asymptotically equivalent
(`√T`-differences vanish in probability). Statement recorded at the coarse level FY
cites. -/
theorem ls_yw_mle_equivalent_debt [IsProbabilityMeasure μ] {p : ℕ}
    {b0 : Fin p → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsAR b0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hroot : NoRootClosedDisc b0)
    (hcausal : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: the Yule–Walker estimator (sample-YW solution) and any
    -- MLE sequence as in `hannan_mle_clt`; B&D Thm 10.8.2
    (bYW : (T : ℕ) → Ω → Fin p → ℝ)
    (hYW : ∀ (T : ℕ) (ω : Ω) (i : Fin p),
      bYW T ω i = (((Matrix.of fun i' j : Fin p =>
          sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
            ((i' : ℤ) - (j : ℤ)).natAbs)⁻¹) *ᵥ
        fun i' : Fin p => sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          ((i' : ℕ) + 1)) i)
    (bMLE : (T : ℕ) → Ω → Fin p → ℝ) (hMLEmeas : ∀ T, Measurable (bMLE T))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ => (μ {ω | δ ≤
        Real.sqrt T * dist (bYW T ω) (bMLE T ω)}).toReal) atTop (𝓝 0) := by
  sorry

end StatLean.TimeSeries
