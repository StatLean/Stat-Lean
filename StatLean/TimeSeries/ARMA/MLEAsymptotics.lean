import StatLean.TimeSeries.ARMA.Consistency
import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.BrownCLT
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
-- Consumed only by the falsity witness `ls_yw_mle_equivalent_debt_false` below: the
-- coordinate white noise on `(ℤ → ℝ, ⊗ N(0,1))`.
import Mathlib.Probability.Independence.InfinitePi

/-!
# ARMA variance consistency and sample PACF

`hannan_sigma2_consistent` proves consistency of the profiled innovation-variance
estimate, using the quadratic-form LLN and local stochastic equicontinuity from
`ARMA/Consistency.lean`. The module also defines the sample partial autocorrelation
`samplePACF` and proves the measurability facts used by that construction.

The white-noise counterexample `ls_yw_mle_equivalent_debt_false` shows why a
measurable estimator cannot be substituted for an actual least-squares, Yule–Walker
or maximum-likelihood estimator when asserting their asymptotic equivalence.

**Scope.** The Hannan parameter CLT (FY Theorem 3.2: `√T (θ̂_T − θ₀) →d N(0, W)` with
`W = (hannanVarZBack b₀ a₀)⁻¹`, the inverse covariance of the *backward* score vector — see
FINDING 26 in `ARMA/ScoreAnalysis.lean`), the PACF CLT (FY Proposition 3.1) and the general
equivalence of least-squares, Yule–Walker and maximum-likelihood estimators (B&D
Thm 10.8.2) are not formalized here.
Variance consistency uses the LLN for `S_T/T` itself: the logarithmic criterion
alone loses information at `S_T = 0`, because `Real.log 0 = 0`.

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

/-! ### Measure-splitting bricks

The two measure-splitting bounds below control unions of bad events in
`hannan_sigma2_consistent`. -/

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

section Sigma2

/-! ### The two inputs of the variance part

`S(θ̂_T)/T = (S(θ̂_T)/T − S(θ₀)/T) + S(θ₀)/T`: the second term is the quadratic-form
LLN at the truth, the first is killed by consistency plus a local equicontinuity
estimate. Both are stated as separate lemmas below; everything else is proved. -/

/-- At the truth the composite filter is `δ₀`, so the contrast variance is `1`. This is
the convolution identity `π(θ₀) ∗ ψ(θ₀) = δ` (`armaPi_conv_armaPsi`) read off term by
term; unlike `armaContrastVar_eq_one_iff` it needs no coprimality hypothesis. -/
private lemma armaContrastVar_self {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ) :
    armaContrastVar b0 a0 b0 a0 = 1 := by
  have hterm : ∀ n : ℕ,
      (∑ jk ∈ Finset.range (n + 1), armaPi b0 a0 jk * armaPsi b0 a0 (n - jk)) ^ 2
        = if n = 0 then (1 : ℝ) else 0 := by
    intro n
    rw [armaPi_conv_armaPsi]
    split_ifs <;> norm_num
  rw [armaContrastVar, tsum_congr hterm]
  simp

/-- **The quadratic-form LLN at the truth**: `T⁻¹ xᵀ Γ_T(θ₀)⁻¹ x →p σ²`.

This specializes `armaProfileS_tendstoInProb` from `ARMA/Consistency.lean` to `θ = θ₀`,
where the contrast variance is `1` (`armaContrastVar_self`, above — the coprimality-free half of
`armaContrastVar_eq_one_iff`). The public `criterion_tendsto_contrast` is **strictly
weaker** than what is needed here: it controls `log(S_T/T) + T⁻¹ log det Γ_T`, and
`Real.log` is not injective at Lean's junk value (`Real.log 0 = 0`), so at `σ² = 1` the
degenerate event `{S_T = 0}` is invisible at the `log` level and the `exp`-transfer back
to `S_T/T` fails.

Using the quadratic-form LLN directly avoids this loss of information at zero. -/
private theorem armaProfileS_atTruth_tendstoInProb [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T : ℕ => (μ {ω | η ≤
        |armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2|}).toReal)
      atTop (𝓝 0) := by
  refine (armaProfileS_tendstoInProb h hiid hσ hB0 hB0 hcausal hmeas hη).congr fun T => ?_
  congr 1
  refine congrArg _ (Set.ext fun ω => ?_)
  simp only [Set.mem_ofPred_eq, armaContrastVar_self, mul_one, div_eq_inv_mul]

/-- **Local stochastic equicontinuity of the profiled sum of squares**: the oscillation of
`θ ↦ T⁻¹ S_T(θ)` over a small ball around `θ₀` is uniformly (in `T`) negligible in
probability.

This is `armaProfileS_locallyEquicontinuous` from `ARMA/Consistency.lean`, where the
estimate is carried out. Its proof uses the locally uniform geometric bound
`Consistency.exists_uniform_geometric_bound_arma` and the `ℓ¹` modulus of continuity
`Consistency.exists_armaPi_l1_modulus` of the inversion filter on a compact parameter set.
The Gram-tail correction `T⁻¹uᵀG_T(θ)u` is `o_p(1)` uniformly in `θ`, by the `θ`-free
envelope `Consistency.quadForm_gramTail_le_env` and one Markov inequality; no `∂π/∂θ`
companion and no pointwise ergodic theorem is needed. -/
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
        atTop (𝓝 0) :=
  armaProfileS_locallyEquicontinuous h hiid hσ hB0 hcausal hmeas hK hKB hη

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
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
  by_cases hB : δ / 2 ≤ |armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2|
  · exact Or.inl hB
  refine Or.inr ?_
  push Not at hB
  by_cases hC : ρ ≤ dist (θ T ω) (b0, a0)
  · exact Or.inl hC
  push Not at hC
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

section PACF

/-! ### Measurability bricks for the sample PACF

These measurability lemmas are used by `wnYW_measurable` in the white-noise
counterexample `ls_yw_mle_equivalent_debt_false` below. -/

/-- Entrywise measurability of a matrix inverse with measurable entries (via
`A⁻¹ = (det A)⁻¹ • adj A`, both polynomial in the entries). -/
private lemma measurable_inv_mulVec {α : Type*} [MeasurableSpace α] {n : ℕ}
    {M : α → Matrix (Fin n) (Fin n) ℝ} {v : α → Fin n → ℝ}
    (hM : ∀ i j, Measurable fun x => M x i j) (hv : ∀ i, Measurable fun x => v x i)
    (i : Fin n) : Measurable fun x => ((M x)⁻¹ *ᵥ v x) i := by
  classical
  have hdet : ∀ N : α → Matrix (Fin n) (Fin n) ℝ, (∀ i j, Measurable fun x => N x i j) →
      Measurable fun x => (N x).det := by
    intro N hN
    simp only [Matrix.det_apply]
    exact Finset.measurable_sum _ fun σ _ =>
      (Finset.measurable_prod _ fun j _ => hN _ _).const_smul _
  have hadj : ∀ i' j' : Fin n, Measurable fun x => (M x).adjugate i' j' := by
    intro i' j'
    simp only [Matrix.adjugate_apply]
    refine hdet _ fun r s => ?_
    simp only [Matrix.updateRow_apply]
    rcases eq_or_ne r j' with rfl | hr
    · simp
    · simpa [hr] using hM r s
  have hexp : (fun x => ((M x)⁻¹ *ᵥ v x) i)
      = fun x => ∑ j, ((M x).det)⁻¹ * ((M x).adjugate i j * v x j) := by
    funext x
    simp [Matrix.mulVec, dotProduct, Matrix.inv_def, Ring.inverse_eq_inv', mul_assoc]
  rw [hexp]
  exact Finset.measurable_sum _ fun j _ =>
    ((hdet M hM).inv).mul ((hadj i j).mul (hv j))

/-- `sampleACVF` of the observation window is measurable. -/
private lemma measurable_sampleACVF {T : ℕ} {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (m : ℕ) : Measurable fun ω => sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) m := by
  classical
  have hmean : Measurable fun ω => sampleMean (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) := by
    simp only [sampleMean]
    exact (Finset.measurable_sum _ fun t _ => hmeas _).const_mul _
  simp only [sampleACVF]
  refine Measurable.const_mul (Finset.measurable_sum _ fun t _ => ?_) _
  rcases eq_or_ne (decide ((t : ℕ) + m < T)) true with hlt | hlt
  · have hlt' : (t : ℕ) + m < T := of_decide_eq_true hlt
    simpa [dite_eq_left hlt'] using! ((hmeas _).sub hmean).mul ((hmeas _).sub hmean)
  · have hlt' : ¬ ((t : ℕ) + m < T) := by simpa using hlt
    simp [dite_eq_right hlt']

end PACF

/-! ### The frozen `ls_yw_mle_equivalent_debt` statement is FALSE — a formalized witness

The statement quantifies over an
**arbitrary measurable** `bMLE`: no hypothesis ties it to the Gaussian likelihood, to
least squares, or to the data at all (and no least-squares estimator appears anywhere,
despite the name). It therefore asserts `√T · dist(b̂_YW, bMLE) →p 0` for *every*
measurable sequence `bMLE`, which fails for the constant translate
`bMLE := b̂_YW + 1` as soon as `p ≥ 1`.

In the witness below, the instance is the causal AR(1) with zero coefficient
(`b(z) = 1`, so `X = ε`) driven by the coordinate white noise on `(ℤ → ℝ, ⊗ N(0,1))`,
and `bMLE` is the translate, whose measurability comes from `measurable_inv_mulVec` /
`measurable_sampleACVF` above.

**Repair.** B&D Thm 10.8.2 compares three *estimators*, so `bMLE` (and a least-squares
sequence `bLS`, currently absent) must carry their defining hypotheses — for `bMLE` the
`hargmin`/`hδTfast` pair of `hannan_mle_clt`, for `bLS` the normal equations. With those
in place the statement becomes a genuine `√T`-equivalence and the residue is the one
recorded at `armaMLE_linearization`.

This witness is kept verbatim, quantified over the *frozen* shape `H`, as the permanent
record. -/

private noncomputable def wnMeasure : Measure (ℤ → ℝ) :=
  Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)

private instance : IsProbabilityMeasure wnMeasure := by
  unfold wnMeasure; infer_instance

private def wnCoord (t : ℤ) (ω : ℤ → ℝ) : ℝ := ω t

private lemma wnCoord_measurable (t : ℤ) : Measurable (wnCoord t) := measurable_pi_apply t

private lemma wnMeasure_map_coord (t : ℤ) : wnMeasure.map (wnCoord t) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval _ t

private lemma wnCoord_identDistrib (t : ℤ) :
    IdentDistrib (wnCoord t) (id : ℝ → ℝ) wnMeasure (gaussianReal 0 1) :=
  ⟨(wnCoord_measurable t).aemeasurable, aemeasurable_id, by
    rw [Measure.map_id, wnMeasure_map_coord t]⟩

private lemma wn_isIIDNoise : IsIIDNoise wnCoord 1 wnMeasure := by
  refine ⟨wnCoord_measurable, ?_, ?_, ?_, ?_, ?_⟩
  · exact iIndepFun_infinitePi (X := fun _ : ℤ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  · exact fun s t => (wnCoord_identDistrib s).trans (wnCoord_identDistrib t).symm
  · exact (wnCoord_identDistrib 0).memLp_iff.2 (memLp_id_gaussianReal 2)
  · rw [(wnCoord_identDistrib 0).integral_eq]
    simp only [id_eq]
    exact (integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)))
  · rw [(wnCoord_identDistrib 0).variance_eq, variance_id_gaussianReal]
    simp

/-- The zero AR(1) coefficient vector: `b(z) = 1`, so `X = ε` is a causal AR(1). -/
private def wnB : Fin 1 → ℝ := fun _ => 0

private lemma arPoly_wnB : arPoly wnB = 1 := by
  simp [arPoly, wnB]

private lemma wn_noRoot : NoRootClosedDisc wnB := by
  intro z _
  rw [arPoly_wnB]
  simp

private lemma armaPsi_wnB (n : ℕ) :
    armaPsi wnB (Fin.elim0 : Fin 0 → ℝ) n = if n = 0 then 1 else 0 := by
  have hma : (maPoly (Fin.elim0 : Fin 0 → ℝ)) = 1 := by simp [maPoly]
  unfold armaPsi
  rw [hma, arPoly_wnB]
  simp [PowerSeries.coeff_one]

private lemma wn_isAR : IsAR wnB 1 wnCoord wnCoord wnMeasure := by
  refine ⟨wnCoord_measurable, wn_isIIDNoise.isWhiteNoise, ?_⟩
  intro t
  filter_upwards with ω
  simp [wnB]

private lemma wn_isLinearProcess :
    IsLinearProcessOf (armaPsi wnB (Fin.elim0 : Fin 0 → ℝ)) wnCoord wnCoord wnMeasure := by
  intro t
  refine Tendsto.congr' ?_ tendsto_const_nhds (f₁ := fun _ : ℕ => (0 : ENNReal))
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hsum : ∀ ω : ℤ → ℝ,
      ∑ j ∈ Finset.range N, armaPsi wnB (Fin.elim0 : Fin 0 → ℝ) j * wnCoord (t - (j : ℕ)) ω
        = wnCoord t ω := by
    intro ω
    rw [Finset.sum_eq_single 0]
    · simp [armaPsi_wnB]
    · intro j _ hj; simp [armaPsi_wnB, hj]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have : (fun ω => wnCoord t ω -
      ∑ j ∈ Finset.range N, armaPsi wnB (Fin.elim0 : Fin 0 → ℝ) j * wnCoord (t - (j : ℕ)) ω)
      = fun _ => (0 : ℝ) := by
    funext ω; rw [hsum ω]; ring
  rw [this]
  simp only [← Pi.zero_def, eLpNorm'_zero (by norm_num : (0 : ℝ) < 2)]


/-- The Yule-Walker estimator of the frozen statement, at the white-noise instance. -/
private noncomputable def wnYW (T : ℕ) (ω : ℤ → ℝ) : Fin 1 → ℝ :=
  ((Matrix.of fun i' j : Fin 1 =>
      sampleACVF (fun t : Fin T => wnCoord (((t : ℕ) : ℤ) + 1) ω)
        ((i' : ℤ) - (j : ℤ)).natAbs)⁻¹) *ᵥ
    fun i' : Fin 1 => sampleACVF (fun t : Fin T => wnCoord (((t : ℕ) : ℤ) + 1) ω)
      ((i' : ℕ) + 1)

private lemma wnYW_measurable (T : ℕ) : Measurable (wnYW T) := by
  refine Measurable.of_eval fun i => ?_
  exact measurable_inv_mulVec (fun _ _ => measurable_sampleACVF wnCoord_measurable _)
    (fun _ => measurable_sampleACVF wnCoord_measurable _) i

private theorem ls_yw_mle_equivalent_debt_false
    (H : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℕ}
      {b0 : Fin p → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ},
      IsAR b0 σ2 X ε μ → IsIIDNoise ε σ2 μ → 0 < σ2 → NoRootClosedDisc b0 →
      IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) X ε μ →
      (∀ t, Measurable (X t)) →
      ∀ bYW : (T : ℕ) → Ω → Fin p → ℝ,
      (∀ (T : ℕ) (ω : Ω) (i : Fin p),
        bYW T ω i = (((Matrix.of fun i' j : Fin p =>
            sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
              ((i' : ℤ) - (j : ℤ)).natAbs)⁻¹) *ᵥ
          fun i' : Fin p => sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
            ((i' : ℕ) + 1)) i) →
      ∀ bMLE : (T : ℕ) → Ω → Fin p → ℝ, (∀ T, Measurable (bMLE T)) →
      ∀ {δ : ℝ}, 0 < δ →
      Tendsto (fun T : ℕ => (μ {ω | δ ≤
        Real.sqrt T * dist (bYW T ω) (bMLE T ω)}).toReal) atTop (𝓝 0)) :
    False := by
  classical
  have hmle : ∀ T : ℕ, Measurable (fun ω : ℤ → ℝ => fun i : Fin 1 => wnYW T ω i + 1) :=
    fun T => Measurable.of_eval fun i =>
      ((measurable_pi_apply i).comp (wnYW_measurable T)).add measurable_const
  have key := H wn_isAR wn_isIIDNoise one_pos wn_noRoot wn_isLinearProcess
    wnCoord_measurable wnYW (fun _ _ _ => rfl)
    (fun T ω => fun i : Fin 1 => wnYW T ω i + 1) hmle (δ := 1) one_pos
  -- the two estimator sequences are at distance `≥ 1`, so the event is everything
  have hset : ∀ T : ℕ, 1 ≤ T → {ω : ℤ → ℝ | (1 : ℝ) ≤
      Real.sqrt T * dist (wnYW T ω) (fun i : Fin 1 => wnYW T ω i + 1)} = Set.univ := by
    intro T hT
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have hd : (1 : ℝ) ≤ dist (wnYW T ω) (fun i : Fin 1 => wnYW T ω i + 1) := by
      have := dist_le_pi_dist (wnYW T ω) (fun i : Fin 1 => wnYW T ω i + 1) 0
      rw [Real.dist_eq] at this
      simpa using this
    have hs : (1 : ℝ) ≤ Real.sqrt T := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hT)
    nlinarith [Real.sqrt_nonneg (T : ℝ)]
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    refine key.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    rw [hset T hT]
    simp
  have := tendsto_nhds_unique hconst tendsto_const_nhds
  norm_num at this

end StatLean.TimeSeries
