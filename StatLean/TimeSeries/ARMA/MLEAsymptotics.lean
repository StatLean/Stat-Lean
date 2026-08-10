import StatLean.TimeSeries.ARMA.Consistency
import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.BrownCLT
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
-- Consumed only by the falsity witness `ls_yw_mle_equivalent_debt_false` below: the
-- coordinate white noise on `(ℤ → ℝ, ⊗ N(0,1))`.
import Mathlib.Probability.Independence.InfinitePi

/-!
# Hannan's theorem: asymptotic normality of the ARMA Gaussian MLE (FY Theorem 3.2)

The head of the commissioned Hannan program (ledger (a), batches C–D): for a
stationary causal invertible ARMA(p, q) with **iid** noise and coprime minimal orders,
any measurable approximate-MLE sequence over a compact identifiable region satisfies

`√T (θ̂_T − θ₀) →d N(0, W)`, `W = (hannanVarZBack b₀ a₀)⁻¹` (FY eq. (3.14)),

where `hannanVarZBack` is the covariance of the score vector `Z_t = (U_{t−1−i},
V_{t−1−j})` — see FINDING 26 at `hannanScore_brownInputs` and the orientation repair
recorded there (wave `ts/f1c-hannan-orientation`): the file used to write the *forward*
Gram `hannanVarZ` here, which is a different quadratic form as soon as `p, q ≥ 1` and
`max (p, q) ≥ 2`.

Stated in Cramér–Wold/charFun form, together with `σ̂² →p σ²`. FY's remarks are
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

**Status of the assembly** (wave `ts/d-hannan-assembly`). All three headline theorems
are *assembled*: their proofs run end to end over named `private` debts, which are
listed here with their exact blockers.

* Proved outright: the charFun bricks (`tendsto_charFun_of_tendstoInProb_sub`, the
  charFun form of Slutsky), `exists_adapted_isLinearProcessOf` (conditional expectation
  turns a linear process into an *adapted* one — `exists_isLinearProcessOf` alone does
  not, and Brown's CLT needs adaptedness), `hannanScore_clt` (the Brown CLT genuinely
  wired along the noise filtration), the padding lemmas and measurability of
  `samplePACF`, and the three assemblies.
* The **variance algebra** of the sandwich is carried out symbolically in the
  `ScoreCLT` section docstring; it collapses to `W⁻¹ = (hannanVarZBack b₀ a₀)⁻¹`.
* Debts (after wave `ts/f1c-hannan-orientation`, 2026-08-09): `armaMLE_linearization`,
  `samplePACF_linearization`. **`hannanScore_brownInputs` is CLOSED** (see below).
  **FINDING 26 (wave `ts/f1b-arma-deep`, 2026-08-09): `hannanVarZ` is the covariance of
  the FORWARD auxiliary vector, while the score contracts the BACKWARD one `Z_t =
  (U_{t−1−i}, V_{t−1−j})`; the two Grams read the AR–MA cross-block at opposite lags and
  differ whenever `p, q ≥ 1` and `max (p, q) ≥ 2`** (machine witness:
  `ScoreAnalysis.hannanVarZ_quadForm_ne_back`, at ARMA(2,1)).
  **ORIENTATION REPAIR APPLIED (wave `ts/f1c-hannan-orientation`, 2026-08-09).** Every
  statement in the chain that asserted a `hannanVarZ` covariance for the score now
  asserts the `hannanVarZBack` one: `hannanScore_brownInputs`(2), `hannanScore_clt`,
  `armaMLE_linearization`, `samplePACF_linearization`, and the headline
  `hannan_mle_clt`, whose asymptotic covariance is now `(hannanVarZBack b₀ a₀)⁻¹`.
  `hannanVarZ` itself is untouched (it is a correct object — the forward Gram — and
  `hannanVarZ_posDef` stands); what the repair supplies is its twin
  `ScoreAnalysis.hannanVarZBack_posDef`, proved by re-running the Bézout/degree argument
  at the score's shifts. The pure-AR and pure-MA instantiations are unaffected either way
  (`hannanVarZ_eq_back_of_pure_ar`, `..._of_pure_ma`).
  **`hannanScore_brownInputs` is now PROVED**: items (1) and (2) are
  `hannanScore_brownInputs_back`, item (3) is the new `hannanScore_lindeberg`.
  **CLOSED**: `armaProfileS_atTruth_tendstoInProb` (a two-line corollary of Consistency's
  now-public `armaProfileS_tendstoInProb`) and `armaProfileS_equicontinuous` (a one-line
  corollary of `Consistency.armaProfileS_locallyEquicontinuous`).
  `ARMA/Consistency.lean` is now `sorry`-free — `mle_consistent` is PROVED — and it
  exports the generic one-filter LLN `linearProcess_avgSq_tendstoInProb`, which is the
  analytic brick all three remaining debts were blocked on. Each of them now carries a
  status note naming exactly what is left; the short version is: an `L²`-limit
  past-measurability step (score `L²` and the conditional-variance identity), the
  `private` `hannanVec`/`hannanVarZ_quadForm` chain in `ARMA/ScoreAnalysis.lean` (a new
  scope blocker), an identical-distribution transfer for the Lindeberg input, and the
  Taylor/delta-method bookkeeping of the last two debts.
  The "**pointwise ergodic theorem**" diagnosis is **WITHDRAWN** (2026-08-08/09):
  `ARMA/Consistency.lean`'s `armaResidualSS_tendstoInProb` proved the pointwise LLN
  ergodic-theorem-free, and the *uniform* half is a deterministic θ-modulus estimate,
  not an ergodic statement — see `armaProfileS_equicontinuous` below, where the
  geometric-bound brick and the `ℓ¹` modulus of `π` are now available as
  `Consistency.exists_uniform_geometric_bound_arma` and
  `Consistency.exists_armaPi_l1_modulus`.
  The scope blocker that used to sit here — `ARMA/ScoreAnalysis.lean`'s
  `indep_noise_sigmaLT`, `private` and hence not citeable — is **gone**: wave
  `ts/s1b-arma-finish` made it public. (Its replacement, narrower, is the still-`private`
  `hannanVarZ_quadForm` chain; see `hannanScore_brownInputs`.)

**Two findings reported by this wave.**
1. `criterion_tendsto_contrast` is *strictly weaker* than the `S_T/T`-level LLN the
   variance part needs: `Real.log 0 = 0`, so at `σ² = 1` the degenerate event
   `{S_T = 0}` is invisible at the `log` level and the `exp`-transfer fails. The
   project-level fix is to un-`private` Consistency's `armaProfileS_tendstoInProb`.
2. The commissioned Bartlett route to `samplePACF_clt` is **closed**:
   `sampleACF_bartlett_clt_debt` carries `MemLp (ε 0) 4 μ`, which `samplePACF_clt` —
   correctly, FY Prop 3.1 needs two moments — does not assume. The martingale route
   taken instead is documented in the `PACF` section.

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

section ScoreCLT

/-! ### The score martingale and its CLT

**The variance algebra, done symbolically first** (this is what forces the frozen
`W = (hannanVarZBack b₀ a₀)⁻¹`). Write `Q_T(θ) = T⁻¹ Σ_t r_t(θ)²` for the residual sum of
squares (`S_T(θ)/T` up to the edge effect) and `θ₀ = (b₀, a₀)`.

*Score.* With `b(z) = 1 − Σ b_i z^{i+1}`, `a(z) = 1 + Σ a_j z^{j+1}` and
`r_t(θ) = (b(B)/a(B)) X_t`:
`∂r_t/∂b_i = −(1/a(B)) X_{t−1−i}`, which at `θ₀` (where `X = (a₀/b₀) ε`) is `−U_{t−1−i}`
for the auxiliary AR process `b₀(B) U = ε`; and `∂r_t/∂a_j = −(1/a(B)) r_{t−1−j}`, which
at `θ₀` is `−V_{t−1−j}` for `a₀(B) V = ε`. So with
`Z_t = (U_{t−1−i})_{i<p} ⌢ (V_{t−1−j})_{j<q}`,

  `∇Q_T(θ₀) = −2 T⁻¹ Σ_t ε_t Z_t`.

*Information.* `Cov(Z_t) = σ² · hannanVarZBack b₀ a₀`.

**This is the sentence FINDING 26 corrected.** It used to read `hannanVarZ b₀ a₀`, with
the parenthetical "the backward `Z_t` used here has the transposed cross-blocks, and a
covariance matrix is symmetric, so the two coincide". That is **false**, and it is the
whole error: transposing the cross-blocks of a Gram matrix is *not* the same as
symmetrising it — `hannanVarZ` and `hannanVarZBack` are both symmetric, and they still
differ, because their `(inl i, inr j)` entries are the cross-covariance read at the
opposite lags `j − i` and `i − j`, and a cross-covariance is not even. The ARMA(2,1)
witness is `ScoreAnalysis.hannanVarZ_quadForm_ne_back`.

Hence `H := ∇²Q_T(θ₀) →p 2 σ² · hannanVarZBack` (the `ε_t ∂²r_t` part is itself a
martingale difference and vanishes), and
`√T ∇Q_T(θ₀) →d N(0, 4·Var(ε Z)) = N(0, 4 σ⁴ · hannanVarZBack)` by independence of `ε_t`
from its past.

*Sandwich.* `√T(θ̂ − θ₀) = −H⁻¹ √T ∇Q_T(θ₀) + o_p(1)` has limit variance

  `(2σ²W)⁻¹ (4σ⁴ W) (2σ²W)⁻¹ = W⁻¹`,  `W := hannanVarZBack b₀ a₀`,

exactly the frozen `cᵀ W⁻¹ c`. Coordinate-wise, with `d := W⁻¹ c`,

  `cᵀ √T(θ̂ − θ₀) = σ⁻² · T^{−1/2} Σ_t ε_t ⟨d, Z_t⟩ + o_p(1)`,

and `Var(ε_t ⟨d, Z_t⟩) = σ² · dᵀ(σ² W)d = σ⁴ · cᵀW⁻¹c`, so the scalar multiplier `σ⁻²`
turns the score's limit `N(0, σ⁴ cᵀW⁻¹c)` into `N(0, cᵀW⁻¹c)`. The multiplier is applied
to the *Gaussian scale* through `charFun_map_mul_comp`, so no multiplier-Slutsky lemma is
needed; only the additive `tendsto_charFun_of_tendstoInProb_sub` above. -/

omit [MeasurableSpace Ω] in
private lemma comap_le_sigmaLT' {Z : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    MeasurableSpace.comap (Z s) inferInstance ≤ sigmaLT Z t :=
  le_iSup₂ (f := fun s (_ : s ∈ Set.Iio t) => MeasurableSpace.comap (Z s) inferInstance) s hst

private lemma sigmaLT_le' {Z : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (Z t)) (t : ℤ) :
    sigmaLT Z t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun _ _ => (hm _).comap_le

omit [MeasurableSpace Ω] in
private lemma measurable_sigmaLT' {Z : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    Measurable[sigmaLT Z t] (Z s) :=
  (Measurable.of_comap_le (le_refl (MeasurableSpace.comap (Z s) inferInstance))).mono
    (comap_le_sigmaLT' hst) le_rfl

/-- The AR polynomial of the negated MA coefficients is the MA polynomial (the two sign
conventions of `arPoly`/`maPoly` differ exactly by the sign of the coefficients). -/
private lemma arPoly_neg' {q : ℕ} (a : Fin q → ℝ) : arPoly (fun j => -a j) = maPoly a := by
  simp only [maPoly, arPoly, map_neg, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- Invertibility of `a` is root-freeness of the AR polynomial of `−a`. -/
private lemma noRootClosedDisc_neg' {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) : NoRootClosedDisc (fun j => -a j) := by
  intro z hz
  rw [arPoly_neg']
  exact hB.2 z hz

/-- **Adapted version of a linear process.** `IsLinearProcessOf` only constrains `L²`
distances, so replacing `U_t` by `E[U_t | σ(ε_s : s ≤ t)]` — which is adapted by
construction — preserves it: conditional expectation fixes the (adapted) partial sums
and is an `L²` contraction. This is what lets the Brown CLT see the auxiliary AR
processes as a *filtered* martingale-difference sequence, which
`exists_isLinearProcessOf` alone does not provide. -/
private lemma exists_adapted_isLinearProcessOf [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {ε U : ℤ → Ω → ℝ} (hψ : Summable fun n => |ψ n|) (hε : IsWhiteNoise ε σ2 μ)
    (hUmeas : ∀ t, Measurable (U t)) (hU : IsLinearProcessOf ψ U ε μ) :
    ∃ U' : ℤ → Ω → ℝ, (∀ t, Measurable (U' t)) ∧
      (∀ t, Measurable[sigmaLT ε (t + 1)] (U' t)) ∧ IsLinearProcessOf ψ U' ε μ := by
  classical
  refine ⟨fun t => μ[U t | sigmaLT ε (t + 1)],
    fun t => (stronglyMeasurable_condExp.mono (sigmaLT_le' hε.measurable _)).measurable,
    fun _ => stronglyMeasurable_condExp.measurable, fun t => ?_⟩
  have hle : sigmaLT ε (t + 1) ≤ (inferInstance : MeasurableSpace Ω) :=
    sigmaLT_le' hε.measurable _
  have hUint : Integrable (U t) μ := (hU.memLp hψ hε hUmeas t).integrable one_le_two
  have hbd : ∀ N : ℕ,
      eLpNorm (fun ω => (μ[U t | sigmaLT ε (t + 1)]) ω
          - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ
        ≤ eLpNorm (fun ω => U t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ := by
    intro N
    have hpsm : StronglyMeasurable[sigmaLT ε (t + 1)]
        (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) :=
      Finset.stronglyMeasurable_fun_sum _ fun j _ =>
        ((measurable_sigmaLT' (Z := ε) (by omega : t - (j : ℕ) < t + 1)).const_mul
          (ψ j)).stronglyMeasurable
    have hpint : Integrable (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) μ :=
      integrable_finset_sum _ fun j _ => ((hε.memLp _).integrable one_le_two).const_mul _
    have h2 : μ[(fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) | sigmaLT ε (t + 1)]
        = fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω :=
      condExp_of_stronglyMeasurable hle hpsm hpint
    have hcond : (fun ω => (μ[U t | sigmaLT ε (t + 1)]) ω
          - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω)
        =ᵐ[μ] μ[U t - (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω)
          | sigmaLT ε (t + 1)] := by
      filter_upwards [condExp_sub hUint hpint (sigmaLT ε (t + 1))] with ω e1
      rw [e1, Pi.sub_apply, h2]
    calc eLpNorm (fun ω => (μ[U t | sigmaLT ε (t + 1)]) ω
            - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ
        = eLpNorm (μ[U t - (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω)
            | sigmaLT ε (t + 1)]) 2 μ := eLpNorm_congr_ae hcond
      _ ≤ _ := eLpNorm_condExp_le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hU t)
    (fun N => zero_le _) hbd

omit [MeasurableSpace Ω] in
private lemma sigmaLT_mono' {Z : ℤ → Ω → ℝ} {s t : ℤ} (hst : s ≤ t) :
    sigmaLT Z s ≤ sigmaLT Z t :=
  iSup₂_le fun _ hr => comap_le_sigmaLT' (lt_of_lt_of_le hr hst)

/-- The **scalar score sequence** at the truth, `ξ_t = ε_t ⟨d, Z_t⟩` with
`Z_t = (U_{t−1−i})_{i<p} ⌢ (V_{t−1−j})_{j<q}`: the martingale difference whose partial
sums carry the whole asymptotic distribution of the MLE (see the variance algebra
above). -/
private noncomputable def scoreSeq {p q : ℕ} (ε U V : ℤ → Ω → ℝ)
    (d : Fin p ⊕ Fin q → ℝ) (t : ℤ) (ω : Ω) : ℝ :=
  ε t ω * ((∑ i : Fin p, d (.inl i) * U (t - 1 - (i : ℕ)) ω)
    + ∑ j : Fin q, d (.inr j) * V (t - 1 - (j : ℕ)) ω)

/-! ### The three Brown inputs, built (finding 26)

The machinery below discharges items (1) and (2) of `hannanScore_brownInputs`, and
overturns two of the three residual sub-items its status note records — at the cost of a
new finding about the *constant* in item (2). In order:

* `isLinearProcessOf_unique` — two linear processes of the **same** coefficient sequence
  over the same noise agree a.e. (the `L²` limit is unique). Combined with the file's own
  `exists_adapted_isLinearProcessOf`, this **dissolves residual item 1** ("the `L²`-limit
  past-measurability"): `U t` is a.e. equal to the *adapted* copy `μ[U t | σ(ε_s : s<t+1)]`,
  which is past-measurable by construction. No subsequence extraction, no
  `aestronglyMeasurable_of_tendsto_ae` for a sub-σ-algebra, and no strengthening of the
  frozen statement is needed. The status note's "it is not free" is correct only in the
  sense that one has to notice the adapted copy is *the same process*.
* `isLinearProcessOf_comb` — **closure of linear processes under finite linear
  combinations of shifts**, with `hannanShiftSeq` bookkeeping. This is residual item 2's
  "mechanical" half, and it really is mechanical: the `N`-term partial sum of the combined
  filter is exactly the combination of the `(N − m_s)`-term partial sums of the pieces.
* `hannanVarZBack` and its quadratic form (`ARMA/ScoreAnalysis.lean`, un-`private`d by
  this wave, which also removes the *scope* blocker residual item 2 records).

**FINDING 26, recorded at `hannanScore_brownInputs` below.** Carrying (1) and (2) through
shows that the constant in the frozen item (2) is **wrong**: the limit is
`σ² · (σ² · dᵀ Σ_back d)` with `Σ_back = hannanVarZBack b₀ a₀`, the covariance of the
**backward** score vector `Z_t = (U_{t−1−i}, V_{t−1−j})`, and not `hannanVarZ b₀ a₀`,
which is the covariance of the *forward* vector. See the section docstring at
`ScoreAnalysis.hannanVarZBack` for why the two differ, and
`ScoreAnalysis.hannanVarZ_quadForm_ne_back` for an ARMA(2,1) witness. -/


/-- Reindexing a shifted filter's partial sum. -/
private lemma sum_range_shiftSeq_mul (ψ : ℕ → ℝ) (m : ℕ) (ε : ℤ → Ω → ℝ) (t : ℤ) (ω : Ω) (N : ℕ) :
    ∑ j ∈ Finset.range N, hannanShiftSeq ψ m j * ε (t - (j : ℕ)) ω
      = ∑ k ∈ Finset.range (N - m), ψ k * ε (t - (m : ℕ) - (k : ℕ)) ω := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rcases lt_or_ge N m with h | h
    · rw [hannanShiftSeq_of_lt h, zero_mul, add_zero]
      have h1 : N - m = 0 := by omega
      have h2 : N + 1 - m = 0 := by omega
      rw [h1, h2]
    · have h2 : N + 1 - m = (N - m) + 1 := by omega
      have harg : t - ((N : ℕ) : ℤ) = t - ((m : ℕ) : ℤ) - (((N - m : ℕ) : ℤ)) := by
        have hc : ((N - m : ℕ) : ℤ) = (N : ℤ) - (m : ℤ) := by
          rw [Nat.cast_sub h]
        omega
      rw [h2, Finset.sum_range_succ, hannanShiftSeq, if_pos h, harg]

/-- **Closure of linear processes under finite linear combinations of shifts.** -/
private lemma isLinearProcessOf_comb [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {σ2 : ℝ} {ε : ℤ → Ω → ℝ} (hε : IsWhiteNoise ε σ2 μ)
    (x : ι → ℝ) (m : ι → ℕ) (ψ : ι → ℕ → ℝ) (W : ι → ℤ → Ω → ℝ)
    (hWmeas : ∀ s t, Measurable (W s t))
    (hW : ∀ s, IsLinearProcessOf (ψ s) (W s) ε μ) :
    IsLinearProcessOf (fun n => ∑ s, x s * hannanShiftSeq (ψ s) (m s) n)
      (fun t ω => ∑ s, x s * W s (t - (m s : ℕ)) ω) ε μ := by
  classical
  intro t
  set g : ι → ℕ → Ω → ℝ := fun s M ω =>
    W s (t - (m s : ℕ)) ω - ∑ k ∈ Finset.range M, ψ s k * ε (t - (m s : ℕ) - (k : ℕ)) ω with hg
  have hgmeas : ∀ s M, Measurable (g s M) := by
    intro s M
    exact (hWmeas s _).sub (Finset.measurable_sum _ fun k _ => measurable_const.mul (hε.measurable _))
  -- the defect of the combination is the combination of the defects
  have hkey : ∀ N : ℕ, (fun ω => (∑ s, x s * W s (t - (m s : ℕ)) ω)
        - ∑ j ∈ Finset.range N,
            (∑ s, x s * hannanShiftSeq (ψ s) (m s) j) * ε (t - (j : ℕ)) ω)
      = fun ω => ∑ s, x s * g s (N - m s) ω := by
    intro N
    funext ω
    have h1 : ∑ j ∈ Finset.range N,
          (∑ s, x s * hannanShiftSeq (ψ s) (m s) j) * ε (t - (j : ℕ)) ω
        = ∑ s, x s * ∑ k ∈ Finset.range (N - m s),
            ψ s k * ε (t - (m s : ℕ) - (k : ℕ)) ω := by
      calc ∑ j ∈ Finset.range N,
              (∑ s, x s * hannanShiftSeq (ψ s) (m s) j) * ε (t - (j : ℕ)) ω
          = ∑ j ∈ Finset.range N, ∑ s,
              x s * (hannanShiftSeq (ψ s) (m s) j * ε (t - (j : ℕ)) ω) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ = ∑ s, ∑ j ∈ Finset.range N,
              x s * (hannanShiftSeq (ψ s) (m s) j * ε (t - (j : ℕ)) ω) := Finset.sum_comm
        _ = ∑ s, x s * ∑ k ∈ Finset.range (N - m s),
              ψ s k * ε (t - (m s : ℕ) - (k : ℕ)) ω := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [← Finset.mul_sum, sum_range_shiftSeq_mul]
    rw [h1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by rw [hg]; ring
  -- and its `L²` norm is dominated by the sum of the individual defects
  have hbd : ∀ N : ℕ, eLpNorm (fun ω => ∑ s, x s * g s (N - m s) ω) 2 μ
      ≤ ∑ s, ‖x s‖ₑ * eLpNorm (g s (N - m s)) 2 μ := by
    intro N
    have hsm : ∀ s ∈ (Finset.univ : Finset ι),
        AEStronglyMeasurable (fun ω => x s * g s (N - m s) ω) μ :=
      fun s _ => ((hgmeas s _).const_mul (x s)).aestronglyMeasurable
    have hfun : (fun ω => ∑ s, x s * g s (N - m s) ω)
        = ∑ s : ι, (x s • (g s (N - m s)) : Ω → ℝ) := by
      funext ω
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun s _ => rfl
    rw [hfun]
    refine (eLpNorm_sum_le (p := 2) (fun s _ =>
      ((hgmeas s (N - m s)).const_smul (x s)).aestronglyMeasurable) one_le_two).trans_eq ?_
    exact Finset.sum_congr rfl fun s _ => eLpNorm_const_smul (x s) (g s (N - m s)) 2 μ
  -- each individual defect vanishes
  have htend : ∀ s : ι, Tendsto (fun N : ℕ => eLpNorm (g s (N - m s)) 2 μ) atTop (𝓝 0) := by
    intro s
    have hsub : Tendsto (fun N : ℕ => N - m s) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b + m s, fun a ha => by omega⟩
    exact (hW s (t - (m s : ℕ))).comp hsub
  have hmul : ∀ s : ι,
      Tendsto (fun N : ℕ => ‖x s‖ₑ * eLpNorm (g s (N - m s)) 2 μ) atTop (𝓝 0) := by
    intro s
    have h0 : ‖x s‖ₑ * (0 : ENNReal) = 0 := by simp
    have hc := ENNReal.Tendsto.const_mul (a := ‖x s‖ₑ) (htend s) (Or.inr enorm_ne_top)
    rwa [h0] at hc
  have hsum : Tendsto (fun N : ℕ => ∑ s, ‖x s‖ₑ * eLpNorm (g s (N - m s)) 2 μ) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset ι) (fun s _ => hmul s)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun N => zero_le _) (fun N => ?_)
  rw [hkey N]
  exact hbd N

/-- **`L²`-limit uniqueness for linear processes.** -/
private lemma isLinearProcessOf_unique [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {ε U U' : ℤ → Ω → ℝ}
    (hU : IsLinearProcessOf ψ U ε μ) (hU' : IsLinearProcessOf ψ U' ε μ)
    (hUm : ∀ t, Measurable (U t)) (hU'm : ∀ t, Measurable (U' t))
    (hεm : ∀ t, Measurable (ε t)) (t : ℤ) : U t =ᵐ[μ] U' t := by
  have hSm : ∀ N : ℕ, Measurable fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω :=
    fun N => Finset.measurable_sum _ fun j _ => measurable_const.mul (hεm _)
  have hle : ∀ N : ℕ, eLpNorm (fun ω => U t ω - U' t ω) 2 μ
      ≤ eLpNorm (fun ω => U t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ
        + eLpNorm (fun ω => U' t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ := by
    intro N
    have hfun : (fun ω => U t ω - U' t ω)
        = (fun ω => U t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω)
          + fun ω => (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) - U' t ω := by
      funext ω; simp only [Pi.add_apply]; ring
    have hswap : (fun ω => (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) - U' t ω)
        = -fun ω => U' t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω := by
      funext ω; simp only [Pi.neg_apply]; ring
    rw [hfun]
    refine (eLpNorm_add_le ((hUm t).sub (hSm N)).aestronglyMeasurable
      ((hSm N).sub (hU'm t)).aestronglyMeasurable one_le_two).trans ?_
    rw [hswap, eLpNorm_neg]
  have hlim : Tendsto (fun N : ℕ =>
      eLpNorm (fun ω => U t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ
        + eLpNorm (fun ω => U' t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ)
      atTop (𝓝 0) := by
    simpa using (hU t).add (hU' t)
  have hzero : eLpNorm (fun ω => U t ω - U' t ω) 2 μ ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall hle)
  have heq0 := le_antisymm hzero (zero_le _)
  have hae := (eLpNorm_eq_zero_iff ((hUm t).sub (hU'm t)).aestronglyMeasurable two_ne_zero).1 heq0
  filter_upwards [hae] with ω hω
  have h0 : U t ω - U' t ω = 0 := hω
  linarith

/-- `E[ε_t²] = σ²` for i.i.d. noise. -/
private lemma integral_noise_sq [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (t : ℤ) : ∫ ω, ε t ω ^ 2 ∂μ = σ2 := by
  have hid := hiid.identDistrib t 0
  have hmem : MemLp (ε t) 2 μ := (hid.memLp_iff).2 hiid.memLp
  have hmean : ∫ ω, ε t ω ∂μ = 0 := by rw [hid.integral_eq, hiid.integral_eq_zero]
  have hvar : variance (ε t) μ = σ2 := by rw [hid.variance_eq, hiid.variance_eq]
  rw [variance_eq_integral hmem.aestronglyMeasurable.aemeasurable, hmean] at hvar
  simpa using hvar

/-- **The conditional-variance identity for the score.** -/
private lemma condExp_noise_mul_sq [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (t : ℤ) {Y : Ω → ℝ} (hYmem : MemLp Y 2 μ)
    (hYmeas : Measurable[sigmaLT ε t] Y) :
    μ[fun ω => (ε t ω * Y ω) ^ 2 | sigmaLT ε t] =ᵐ[μ] fun ω => σ2 * Y ω ^ 2 := by
  have hle : sigmaLT ε t ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup₂_le fun _ _ => (hiid.measurable _).comap_le
  have hεmem : MemLp (ε t) 2 μ := ((hiid.identDistrib t 0).memLp_iff).2 hiid.memLp
  -- independence of `ε_t²` from the past
  have hind : Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT ε t) μ :=
    indep_noise_sigmaLT hiid.measurable hiid.iIndep t
  have hIF : IndepFun (fun ω => ε t ω ^ 2) (fun ω => Y ω ^ 2) μ := by
    have h0 : IndepFun (ε t) Y μ := indep_of_indep_of_le_right hind hYmeas.comap_le
    exact h0.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hεsq : Integrable (fun ω => ε t ω ^ 2) μ := by
    simpa [sq] using hεmem.integrable_mul hεmem
  have hYsq : Integrable (fun ω => Y ω ^ 2) μ := by
    simpa [sq] using hYmem.integrable_mul hYmem
  have hprod : Integrable ((fun ω => ε t ω ^ 2) * fun ω => Y ω ^ 2) μ :=
    hIF.integrable_mul hεsq hYsq
  have hfun : (fun ω => (ε t ω * Y ω) ^ 2)
      = (fun ω => ε t ω ^ 2) * fun ω => Y ω ^ 2 := by
    funext ω; simp [Pi.mul_apply, mul_pow]
  rw [hfun]
  have hpull := condExp_mul_of_stronglyMeasurable_right
    (hYmeas.pow_const 2).stronglyMeasurable hprod hεsq
  have hconst := condExp_indep_eq (hiid.measurable t).comap_le hle
    (Measurable.stronglyMeasurable
      ((Measurable.of_comap_le
        (le_refl (MeasurableSpace.comap (ε t) inferInstance))).pow_const 2))
    hind
  filter_upwards [hpull, hconst] with ω h1 h2
  rw [h1, Pi.mul_apply, h2, integral_noise_sq hiid t]

/-- The score's auxiliary vector, contracted against `d`. -/
private noncomputable def scoreVec {p q : ℕ} (U V : ℤ → Ω → ℝ) (d : Fin p ⊕ Fin q → ℝ)
    (t : ℤ) (ω : Ω) : ℝ :=
  (∑ i : Fin p, d (.inl i) * U (t - 1 - (i : ℕ)) ω)
    + ∑ j : Fin q, d (.inr j) * V (t - 1 - (j : ℕ)) ω

private lemma scoreVec_eq_comb {p q : ℕ} (U V : ℤ → Ω → ℝ) (d : Fin p ⊕ Fin q → ℝ) (t : ℤ) (ω : Ω) :
    scoreVec U V d t ω
      = ∑ s : Fin p ⊕ Fin q, d s *
          (Sum.elim (fun _ : Fin p => U) (fun _ : Fin q => V) s)
            (t - ((hannanShiftBack p q s : ℕ) : ℤ)) ω := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hannanShiftBack, scoreVec]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    push_cast
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    push_cast
    ring

private lemma measurable_scoreVec {p q : ℕ} {U V : ℤ → Ω → ℝ} (hUmeas : ∀ t, Measurable (U t))
    (hVmeas : ∀ t, Measurable (V t)) (d : Fin p ⊕ Fin q → ℝ) (t : ℤ) :
    Measurable (scoreVec U V d t) :=
  (Finset.measurable_sum _ fun i _ => measurable_const.mul (hUmeas _)).add
    (Finset.measurable_sum _ fun j _ => measurable_const.mul (hVmeas _))

/-- The contracted score vector is a linear process with the **backward** coefficients. -/
private lemma isLinearProcessOf_scoreVec [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {ε U V : ℤ → Ω → ℝ}
    (hε : IsWhiteNoise ε σ2 μ)
    (hU : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) U ε μ)
    (hV : IsLinearProcessOf (armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ)) V ε μ)
    (hUmeas : ∀ t, Measurable (U t)) (hVmeas : ∀ t, Measurable (V t))
    (d : Fin p ⊕ Fin q → ℝ) :
    IsLinearProcessOf (fun n => ∑ s, d s * hannanVecBack b0 a0 s n) (scoreVec U V d) ε μ := by
  have hcomb := isLinearProcessOf_comb (μ := μ) hε d (hannanShiftBack p q)
    (fun s => hannanSeq b0 a0 s)
    (Sum.elim (fun _ : Fin p => U) (fun _ : Fin q => V))
    (by rintro (i | j) t; exacts [hUmeas t, hVmeas t])
    (by rintro (i | j); exacts [hU, hV])
  have hfun : scoreVec U V d
      = fun t ω => ∑ s, d s *
          (Sum.elim (fun _ : Fin p => U) (fun _ : Fin q => V) s)
            (t - ((hannanShiftBack p q s : ℕ) : ℤ)) ω := by
    funext t ω
    exact scoreVec_eq_comb U V d t ω
  rw [hfun]
  exact hcomb

/-- **The corrected conditional-variance LLN** — item (2) of `hannanScore_brownInputs`,
with the **backward** Gram `hannanVarZBack` in place of the frozen `hannanVarZ`. -/
private theorem hannanScore_condVar_lln [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {ε U V U' V' : ℤ → Ω → ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2) (hB0 : ARMAInvertibleParams b0 a0)
    (hU : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) U ε μ)
    (hV : IsLinearProcessOf (armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ)) V ε μ)
    (hUmeas : ∀ t, Measurable (U t)) (hVmeas : ∀ t, Measurable (V t))
    (hU' : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) U' ε μ)
    (hV' : IsLinearProcessOf (armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ)) V' ε μ)
    (hU'meas : ∀ t, Measurable (U' t)) (hV'meas : ∀ t, Measurable (V' t))
    (hU'adapt : ∀ t, Measurable[sigmaLT ε (t + 1)] (U' t))
    (hV'adapt : ∀ t, Measurable[sigmaLT ε (t + 1)] (V' t))
    (d : Fin p ⊕ Fin q → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (μ {ω | δ ≤ |(n : ℝ)⁻¹ *
        (∑ i ∈ Finset.range n,
          μ[fun ω' => (ε ((i : ℤ) + 1) ω' * scoreVec U V d ((i : ℤ) + 1) ω') ^ 2
            | sigmaLT ε ((i : ℤ) + 1)] ω)
        - σ2 * (σ2 * (d ⬝ᵥ (hannanVarZBack b0 a0 *ᵥ d)))|}).toReal) atTop (𝓝 0) := by
  classical
  have hwn := hiid.isWhiteNoise
  have hc : Summable fun n => |∑ s, d s * hannanVecBack b0 a0 s n| :=
    summable_abs_hannanComboBack hB0 d
  have hY := isLinearProcessOf_scoreVec hwn hU hV hUmeas hVmeas d
  have hY2 := isLinearProcessOf_scoreVec hwn hU' hV' hU'meas hV'meas d
  have hYm := measurable_scoreVec hUmeas hVmeas d
  have hY2m := measurable_scoreVec hU'meas hV'meas d
  have hae : ∀ t : ℤ, scoreVec U V d t =ᵐ[μ] scoreVec U' V' d t :=
    fun t => isLinearProcessOf_unique hY hY2 hYm hY2m hiid.measurable t
  -- the adapted copy is past-measurable
  have hadapt : ∀ i : ℕ,
      Measurable[sigmaLT ε ((i : ℤ) + 1)] (scoreVec U' V' d ((i : ℤ) + 1)) := by
    intro i
    refine Measurable.add (Finset.measurable_sum _ fun k _ => measurable_const.mul ?_)
      (Finset.measurable_sum _ fun k _ => measurable_const.mul ?_)
    · exact (hU'adapt _).mono (sigmaLT_mono' (by push_cast; omega)) le_rfl
    · exact (hV'adapt _).mono (sigmaLT_mono' (by push_cast; omega)) le_rfl
  -- the quadratic form
  have hQ : ∑' n : ℕ, (∑ s, d s * hannanVecBack b0 a0 s n) ^ 2
      = d ⬝ᵥ (hannanVarZBack b0 a0 *ᵥ d) := by
    rw [← hannanVarZBack_quadForm hB0 d]
    simp only [dotProduct, Matrix.mulVec]
  -- the conditional-variance identity
  have hcond : ∀ i : ℕ,
      μ[fun ω' => (ε ((i : ℤ) + 1) ω' * scoreVec U V d ((i : ℤ) + 1) ω') ^ 2
        | sigmaLT ε ((i : ℤ) + 1)]
      =ᵐ[μ] fun ω => σ2 * scoreVec U V d ((i : ℤ) + 1) ω ^ 2 := by
    intro i
    have h1 : (fun ω' => (ε ((i : ℤ) + 1) ω' * scoreVec U V d ((i : ℤ) + 1) ω') ^ 2)
        =ᵐ[μ] fun ω' => (ε ((i : ℤ) + 1) ω' * scoreVec U' V' d ((i : ℤ) + 1) ω') ^ 2 := by
      filter_upwards [hae ((i : ℤ) + 1)] with ω hω
      rw [hω]
    have h2 := condExp_noise_mul_sq hiid ((i : ℤ) + 1)
      (hY2.memLp hc hwn hY2m ((i : ℤ) + 1)) (hadapt i)
    have h3 := condExp_congr_ae (m := sigmaLT ε ((i : ℤ) + 1)) h1
    filter_upwards [h3, h2, hae ((i : ℤ) + 1)] with ω e1 e2 e3
    rw [e1, e2, e3]
  -- the running average collapses to `σ² ·` the average of the squares
  have hsum_ae : ∀ n : ℕ,
      (fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
          μ[fun ω' => (ε ((i : ℤ) + 1) ω' * scoreVec U V d ((i : ℤ) + 1) ω') ^ 2
            | sigmaLT ε ((i : ℤ) + 1)] ω)
        =ᵐ[μ] fun ω => σ2 * ((n : ℝ)⁻¹ *
          ∑ i ∈ Finset.range n, scoreVec U V d ((i : ℤ) + 1) ω ^ 2) := by
    intro n
    have hall : ∀ᵐ ω ∂μ, ∀ i ∈ (Finset.range n : Finset ℕ),
        μ[fun ω' => (ε ((i : ℤ) + 1) ω' * scoreVec U V d ((i : ℤ) + 1) ω') ^ 2
          | sigmaLT ε ((i : ℤ) + 1)] ω = σ2 * scoreVec U V d ((i : ℤ) + 1) ω ^ 2 := by
      rw [Filter.eventually_all_finset]
      intro i _
      exact hcond i
    filter_upwards [hall] with ω hω
    rw [Finset.sum_congr rfl fun i hi => hω i hi, ← Finset.mul_sum]
    ring
  -- and the two bad events coincide up to a null set
  have hset : ∀ n : ℕ,
      μ {ω | δ ≤ |(n : ℝ)⁻¹ * (∑ i ∈ Finset.range n,
          μ[fun ω' => (ε ((i : ℤ) + 1) ω' * scoreVec U V d ((i : ℤ) + 1) ω') ^ 2
            | sigmaLT ε ((i : ℤ) + 1)] ω)
          - σ2 * (σ2 * (d ⬝ᵥ (hannanVarZBack b0 a0 *ᵥ d)))|}
        = μ {ω | δ / σ2 ≤ |(n : ℝ)⁻¹ *
            ∑ i ∈ Finset.range n, scoreVec U V d ((i : ℤ) + 1) ω ^ 2
            - σ2 * ∑' m : ℕ, (∑ s, d s * hannanVecBack b0 a0 s m) ^ 2|} := by
    intro n
    refine measure_congr ?_
    filter_upwards [hsum_ae n] with ω hω
    have habs : |σ2 * ((n : ℝ)⁻¹ *
          ∑ i ∈ Finset.range n, scoreVec U V d ((i : ℤ) + 1) ω ^ 2)
          - σ2 * (σ2 * (d ⬝ᵥ (hannanVarZBack b0 a0 *ᵥ d)))|
        = σ2 * |(n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, scoreVec U V d ((i : ℤ) + 1) ω ^ 2
            - σ2 * (d ⬝ᵥ (hannanVarZBack b0 a0 *ᵥ d))| := by
      rw [← mul_sub, abs_mul, abs_of_pos hσ]
    have hiff : (δ ≤ |(n : ℝ)⁻¹ * (∑ i ∈ Finset.range n,
          μ[fun ω' => (ε ((i : ℤ) + 1) ω' * scoreVec U V d ((i : ℤ) + 1) ω') ^ 2
            | sigmaLT ε ((i : ℤ) + 1)] ω)
          - σ2 * (σ2 * (d ⬝ᵥ (hannanVarZBack b0 a0 *ᵥ d)))|)
        ↔ (δ / σ2 ≤ |(n : ℝ)⁻¹ *
            ∑ i ∈ Finset.range n, scoreVec U V d ((i : ℤ) + 1) ω ^ 2
            - σ2 * ∑' m : ℕ, (∑ s, d s * hannanVecBack b0 a0 s m) ^ 2|) := by
      rw [hQ, hω, habs, div_le_iff₀ hσ]
      constructor
      · intro h; linarith
      · intro h; linarith
    exact propext hiff
  have hlln := linearProcess_avgSq_tendstoInProb hiid hc hY hYm
    (show (0 : ℝ) < δ / σ2 by positivity)
  exact hlln.congr fun n => congrArg ENNReal.toReal (hset n).symm

/-- **Item (1)**: the score is in `L²`, by noise/past independence (Hölder is unavailable
— only two moments are assumed). -/
private lemma memLp_noise_mul_of_adapted [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (t : ℤ) {Y : Ω → ℝ} (hYmem : MemLp Y 2 μ)
    (hYmeas : Measurable[sigmaLT ε t] Y) :
    MemLp (fun ω => ε t ω * Y ω) 2 μ := by
  have hεmem : MemLp (ε t) 2 μ := ((hiid.identDistrib t 0).memLp_iff).2 hiid.memLp
  have hind : Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT ε t) μ :=
    indep_noise_sigmaLT hiid.measurable hiid.iIndep t
  have hIF : IndepFun (fun ω => ε t ω ^ 2) (fun ω => Y ω ^ 2) μ := by
    have h0 : IndepFun (ε t) Y μ := indep_of_indep_of_le_right hind hYmeas.comap_le
    exact h0.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hεsq : Integrable (fun ω => ε t ω ^ 2) μ := by
    simpa [sq] using hεmem.integrable_mul hεmem
  have hYsq : Integrable (fun ω => Y ω ^ 2) μ := by
    simpa [sq] using hYmem.integrable_mul hYmem
  have hprod : Integrable ((fun ω => ε t ω ^ 2) * fun ω => Y ω ^ 2) μ :=
    hIF.integrable_mul hεsq hYsq
  refine (memLp_two_iff_integrable_sq
    (hεmem.aestronglyMeasurable.mul hYmem.aestronglyMeasurable)).2 ?_
  refine hprod.congr ?_
  filter_upwards with ω
  simp [Pi.mul_apply, mul_pow]

/-- **Item (1) for the score sequence**, stated for the given (not necessarily adapted)
`U`, `V`: the adapted copies carry the independence and `L²` membership transfers along
the a.e. equality of `L²` limits. -/
private lemma memLp_scoreSeqS [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {ε U V U' V' : ℤ → Ω → ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (hB0 : ARMAInvertibleParams b0 a0)
    (hU : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) U ε μ)
    (hV : IsLinearProcessOf (armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ)) V ε μ)
    (hUmeas : ∀ t, Measurable (U t)) (hVmeas : ∀ t, Measurable (V t))
    (hU' : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) U' ε μ)
    (hV' : IsLinearProcessOf (armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ)) V' ε μ)
    (hU'meas : ∀ t, Measurable (U' t)) (hV'meas : ∀ t, Measurable (V' t))
    (hU'adapt : ∀ t, Measurable[sigmaLT ε (t + 1)] (U' t))
    (hV'adapt : ∀ t, Measurable[sigmaLT ε (t + 1)] (V' t))
    (d : Fin p ⊕ Fin q → ℝ) (i : ℕ) :
    MemLp (fun ω => ε ((i : ℤ) + 1) ω * scoreVec U V d ((i : ℤ) + 1) ω) 2 μ := by
  have hwn := hiid.isWhiteNoise
  have hc : Summable fun n => |∑ s, d s * hannanVecBack b0 a0 s n| :=
    summable_abs_hannanComboBack hB0 d
  have hY := isLinearProcessOf_scoreVec hwn hU hV hUmeas hVmeas d
  have hY2 := isLinearProcessOf_scoreVec hwn hU' hV' hU'meas hV'meas d
  have hYm := measurable_scoreVec hUmeas hVmeas d
  have hY2m := measurable_scoreVec hU'meas hV'meas d
  have hadapt : Measurable[sigmaLT ε ((i : ℤ) + 1)] (scoreVec U' V' d ((i : ℤ) + 1)) := by
    refine Measurable.add (Finset.measurable_sum _ fun k _ => measurable_const.mul ?_)
      (Finset.measurable_sum _ fun k _ => measurable_const.mul ?_)
    · exact (hU'adapt _).mono (sigmaLT_mono' (by push_cast; omega)) le_rfl
    · exact (hV'adapt _).mono (sigmaLT_mono' (by push_cast; omega)) le_rfl
  have hmem := memLp_noise_mul_of_adapted hiid ((i : ℤ) + 1)
    (hY2.memLp hc hwn hY2m ((i : ℤ) + 1)) hadapt
  refine hmem.ae_eq ?_
  filter_upwards [isLinearProcessOf_unique hY hY2 hYm hY2m hiid.measurable ((i : ℤ) + 1)]
    with ω hω
  rw [hω]


/-! ### Item (3): the averaged Lindeberg condition

The recipe the status note at `hannanScore_brownInputs` predicts, carried out. Everything
is phrased through the **Lindeberg truncation as a function of the value**,
`lindTrunc l y = y² · 1{|y| ≥ l}`, which turns every set integral in sight into an
ordinary integral of a fixed measurable function of one random variable — so the two
transfers the argument needs (the a.e. swap to the adapted copy, and identical
distribution along `t`) are both just `integral_congr_ae` / `IdentDistrib.integral_eq`.

**FINDING 30 (wave `ts/f1c-hannan-orientation`, 2026-08-09).** Two things the residual
note at `hannanScore_brownInputs` does not say. First, the set-splitting it prescribes
(`{|ε Y| ≥ λ} ⊆ {|ε| ≥ √λ} ∪ {|Y| ≥ √λ}`) never has to be done at the level of sets: it is
a *pointwise real inequality* between three values of `lindTrunc`, after which the whole
argument is `integral_mono` plus two independence factorisations, with no measure-theoretic
set algebra at all. Second, item (3) is the only one of the three Brown inputs that
consumes **identical distribution** of the score vector, hence the only one that needs
`IsLinearProcessOf.isStrictlyStationary` and therefore the *iid* (not merely white-noise)
hypothesis on `ε`; items (1) and (2) use only noise/past independence and the one-filter
LLN. Anyone weakening `IsIIDNoise` to a martingale-difference assumption — FY's stated
future direction — will hit item (3) first, and will need a uniform-integrability
substitute for stationarity there.

The estimate itself is the pointwise inequality

  `lindTrunc l (e·y) ≤ lindTrunc √l e · y² + e² · lindTrunc √l y`

(if `|e·y| ≥ l` then at least one of `|e|, |y|` is `≥ √l`), integrated and factorised by
noise/past independence into `E[ε² 1{|ε|≥√l}]·E[Y²] + σ²·E[Y² 1{|Y|≥√l}]`. Both factors
are free of the time index by identical distribution — for `ε` from `IsIIDNoise`, for `Y`
from `IsLinearProcessOf.isStrictlyStationary`, which applies because
`isLinearProcessOf_comb` exhibits `⟨d, Z_t⟩` as a linear process of a summable filter.
With `l = η√n → ∞` both vanish by dominated convergence, and the average of `n` terms
each bounded by the same vanishing quantity vanishes. -/

/-- Lindeberg truncation, as a function of the value. -/
private noncomputable def lindTrunc (l y : ℝ) : ℝ := if l ≤ |y| then y ^ 2 else 0

private lemma lindTrunc_nonneg (l y : ℝ) : 0 ≤ lindTrunc l y := by
  unfold lindTrunc; split_ifs
  · positivity
  · exact le_rfl

private lemma lindTrunc_le_sq (l y : ℝ) : lindTrunc l y ≤ y ^ 2 := by
  unfold lindTrunc; split_ifs
  · exact le_rfl
  · positivity

private lemma measurable_lindTrunc (l : ℝ) : Measurable (lindTrunc l) := by
  unfold lindTrunc
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  exact measurableSet_le measurable_const measurable_norm

private lemma lindTrunc_mul_le {l : ℝ} (hl : 0 ≤ l) (e y : ℝ) :
    lindTrunc l (e * y)
      ≤ lindTrunc (Real.sqrt l) e * y ^ 2 + e ^ 2 * lindTrunc (Real.sqrt l) y := by
  have h1 : 0 ≤ lindTrunc (Real.sqrt l) e * y ^ 2 :=
    mul_nonneg (lindTrunc_nonneg _ _) (sq_nonneg _)
  have h2 : 0 ≤ e ^ 2 * lindTrunc (Real.sqrt l) y :=
    mul_nonneg (sq_nonneg _) (lindTrunc_nonneg _ _)
  by_cases hcase : l ≤ |e * y|
  · have hL : lindTrunc l (e * y) = e ^ 2 * y ^ 2 := by
      unfold lindTrunc; rw [if_pos hcase]; ring
    rcases le_or_gt (Real.sqrt l) |e| with h | h
    · have he : lindTrunc (Real.sqrt l) e = e ^ 2 := if_pos h
      rw [hL, he]
      nlinarith
    · have hy : Real.sqrt l ≤ |y| := by
        by_contra hy
        push Not at hy
        have hs : Real.sqrt l * Real.sqrt l = l := Real.mul_self_sqrt hl
        have hab : |e * y| = |e| * |y| := abs_mul e y
        nlinarith [abs_nonneg e, abs_nonneg y, Real.sqrt_nonneg l]
      have hey : lindTrunc (Real.sqrt l) y = y ^ 2 := if_pos hy
      rw [hL, hey]
      nlinarith
  · have hL : lindTrunc l (e * y) = 0 := if_neg hcase
    rw [hL]
    linarith

private lemma setIntegral_sq_eq_integral_lindTrunc {Z : Ω → ℝ} (hZ : Measurable Z) (l : ℝ) :
    ∫ ω in {ω | l ≤ |Z ω|}, (Z ω) ^ 2 ∂μ = ∫ ω, lindTrunc l (Z ω) ∂μ := by
  have hs : MeasurableSet {ω | l ≤ |Z ω|} :=
    measurableSet_le measurable_const hZ.norm
  rw [← integral_indicator hs]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [Set.indicator_apply, Set.mem_setOf_eq, lindTrunc]

private lemma tendsto_integral_lindTrunc {Z : Ω → ℝ} (hZ : Measurable Z)
    (hint : Integrable (fun ω => Z ω ^ 2) μ) {l : ℕ → ℝ} (hl : Tendsto l atTop atTop) :
    Tendsto (fun n : ℕ => ∫ ω, lindTrunc (l n) (Z ω) ∂μ) atTop (𝓝 0) := by
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => lindTrunc (l n) (Z ω)) atTop (𝓝 0) := by
    filter_upwards with ω
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hl.eventually_gt_atTop (|Z ω|)] with n hn
    exact (if_neg (not_le.2 hn)).symm
  have := tendsto_integral_of_dominated_convergence (F := fun n ω => lindTrunc (l n) (Z ω))
    (f := fun _ : Ω => (0 : ℝ)) (bound := fun ω => Z ω ^ 2)
    (fun n => ((measurable_lindTrunc (l n)).comp hZ).aestronglyMeasurable)
    hint
    (fun n => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (lindTrunc_nonneg _ _)]
      exact lindTrunc_le_sq _ _)
    hlim
  simpa using this

private lemma identDistrib_of_isStrictlyStationary {Y : ℤ → Ω → ℝ}
    (hstat : IsStrictlyStationary Y μ) (hmeas : ∀ t, Measurable (Y t)) (s t : ℤ) :
    IdentDistrib (Y s) (Y t) μ μ := by
  refine ⟨(hmeas s).aemeasurable, (hmeas t).aemeasurable, ?_⟩
  have h := hstat 1 (fun _ => t) (s - t)
  have hts : t + (s - t) = s := by ring
  rw [hts] at h
  have hmap : ∀ u : ℤ, μ.map (Y u)
      = (μ.map fun ω (_ : Fin 1) => Y u ω).map (fun f : Fin 1 → ℝ => f 0) := by
    intro u
    rw [Measure.map_map (measurable_pi_apply 0)
      (measurable_pi_lambda _ fun _ => hmeas u)]
    rfl
  rw [hmap s, hmap t, h]

/-- **The averaged Lindeberg condition for a noise-times-past product.** -/
private theorem lindeberg_noise_mul [IsProbabilityMeasure μ] {ε Y : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hYmeas : ∀ t, Measurable (Y t))
    (hYadapt : ∀ t, Measurable[sigmaLT ε t] (Y t))
    (hYmem : ∀ t, MemLp (Y t) 2 μ)
    (hprodmem : ∀ t, MemLp (fun ω => ε t ω * Y t ω) 2 μ)
    (hstat : IsStrictlyStationary Y μ)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ∫ ω in {ω | η * Real.sqrt n ≤ |ε ((i : ℤ) + 1) ω * Y ((i : ℤ) + 1) ω|},
          (ε ((i : ℤ) + 1) ω * Y ((i : ℤ) + 1) ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  classical
  -- ## notation: the truncation level, and the three `i`-free constants
  set r : ℕ → ℝ := fun n => Real.sqrt (η * Real.sqrt n) with hr
  set M : ℝ := ∫ ω, Y 1 ω ^ 2 ∂μ with hM
  set A : ℕ → ℝ := fun n => ∫ ω, lindTrunc (r n) (ε 0 ω) ∂μ with hA
  set B : ℕ → ℝ := fun n => ∫ ω, lindTrunc (r n) (Y 1 ω) ∂μ with hB
  -- ## integrability facts
  have hεmem : ∀ t : ℤ, MemLp (ε t) 2 μ :=
    fun t => ((hiid.identDistrib t 0).memLp_iff).2 hiid.memLp
  have hεsq : ∀ t : ℤ, Integrable (fun ω => ε t ω ^ 2) μ := by
    intro t; simpa [sq] using (hεmem t).integrable_mul (hεmem t)
  have hYsq : ∀ t : ℤ, Integrable (fun ω => Y t ω ^ 2) μ := by
    intro t; simpa [sq] using (hYmem t).integrable_mul (hYmem t)
  have hprodsq : ∀ t : ℤ, Integrable (fun ω => (ε t ω * Y t ω) ^ 2) μ := by
    intro t
    have := (hprodmem t).integrable_mul (hprodmem t)
    simpa [sq] using this
  have hMnn : 0 ≤ M := integral_nonneg fun ω => sq_nonneg _
  have hAnn : ∀ n, 0 ≤ A n := fun n => integral_nonneg fun ω => lindTrunc_nonneg _ _
  have hBnn : ∀ n, 0 ≤ B n := fun n => integral_nonneg fun ω => lindTrunc_nonneg _ _
  -- ## the identically-distributed transfer
  have hidY : ∀ i : ℕ, IdentDistrib (Y ((i : ℤ) + 1)) (Y 1) μ μ :=
    fun i => identDistrib_of_isStrictlyStationary hstat hYmeas _ _
  -- ## the per-index bound
  have hterm : ∀ (n : ℕ) (i : ℕ),
      ∫ ω in {ω | η * Real.sqrt n ≤ |ε ((i : ℤ) + 1) ω * Y ((i : ℤ) + 1) ω|},
        (ε ((i : ℤ) + 1) ω * Y ((i : ℤ) + 1) ω) ^ 2 ∂μ ≤ A n * M + σ2 * B n := by
    intro n i
    set t : ℤ := (i : ℤ) + 1 with ht
    have hmul : Measurable fun ω => ε t ω * Y t ω := (hiid.measurable t).mul (hYmeas t)
    rw [setIntegral_sq_eq_integral_lindTrunc hmul]
    -- independence of the noise from the past
    have hind : Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT ε t) μ :=
      indep_noise_sigmaLT hiid.measurable hiid.iIndep t
    have hIF : IndepFun (ε t) (Y t) μ :=
      indep_of_indep_of_le_right hind (hYadapt t).comap_le
    -- the two products, and their integrability
    have hIF1 : IndepFun (fun ω => lindTrunc (r n) (ε t ω)) (fun ω => Y t ω ^ 2) μ :=
      hIF.comp (measurable_lindTrunc (r n)) (measurable_id.pow_const 2)
    have hIF2 : IndepFun (fun ω => ε t ω ^ 2) (fun ω => lindTrunc (r n) (Y t ω)) μ :=
      hIF.comp (measurable_id.pow_const 2) (measurable_lindTrunc (r n))
    have hint1 : Integrable (fun ω => lindTrunc (r n) (ε t ω)) μ := by
      refine Integrable.mono' (hεsq t)
        ((measurable_lindTrunc (r n)).comp (hiid.measurable t)).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (lindTrunc_nonneg _ _)]
      exact lindTrunc_le_sq _ _
    have hint2 : Integrable (fun ω => lindTrunc (r n) (Y t ω)) μ := by
      refine Integrable.mono' (hYsq t)
        ((measurable_lindTrunc (r n)).comp (hYmeas t)).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (lindTrunc_nonneg _ _)]
      exact lindTrunc_le_sq _ _
    have hg1 : Integrable (fun ω => lindTrunc (r n) (ε t ω) * Y t ω ^ 2) μ :=
      hIF1.integrable_mul hint1 (hYsq t)
    have hg2 : Integrable (fun ω => ε t ω ^ 2 * lindTrunc (r n) (Y t ω)) μ :=
      hIF2.integrable_mul (hεsq t) hint2
    have hf : Integrable (fun ω => lindTrunc (η * Real.sqrt n) (ε t ω * Y t ω)) μ := by
      refine Integrable.mono' (hprodsq t)
        ((measurable_lindTrunc _).comp hmul).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (lindTrunc_nonneg _ _)]
      exact lindTrunc_le_sq _ _
    -- the pointwise truncation inequality, integrated
    have hle : ∫ ω, lindTrunc (η * Real.sqrt n) (ε t ω * Y t ω) ∂μ
        ≤ (∫ ω, lindTrunc (r n) (ε t ω) * Y t ω ^ 2 ∂μ)
          + ∫ ω, ε t ω ^ 2 * lindTrunc (r n) (Y t ω) ∂μ := by
      rw [← integral_add hg1 hg2]
      refine integral_mono hf (hg1.add hg2) fun ω => ?_
      have := lindTrunc_mul_le (l := η * Real.sqrt n)
        (by positivity) (ε t ω) (Y t ω)
      simpa [hr, Pi.add_apply] using this
    -- factorisation by independence
    have hfac1 : ∫ ω, lindTrunc (r n) (ε t ω) * Y t ω ^ 2 ∂μ
        = (∫ ω, lindTrunc (r n) (ε t ω) ∂μ) * ∫ ω, Y t ω ^ 2 ∂μ :=
      hIF1.integral_fun_mul_eq_mul_integral hint1.aestronglyMeasurable
        (hYsq t).aestronglyMeasurable
    have hfac2 : ∫ ω, ε t ω ^ 2 * lindTrunc (r n) (Y t ω) ∂μ
        = (∫ ω, ε t ω ^ 2 ∂μ) * ∫ ω, lindTrunc (r n) (Y t ω) ∂μ :=
      hIF2.integral_fun_mul_eq_mul_integral (hεsq t).aestronglyMeasurable
        hint2.aestronglyMeasurable
    -- and the transfer to time `0` / time `1`
    have he0 : ∫ ω, lindTrunc (r n) (ε t ω) ∂μ = A n :=
      ((hiid.identDistrib t 0).comp (measurable_lindTrunc (r n))).integral_eq
    have hy1 : ∫ ω, lindTrunc (r n) (Y t ω) ∂μ = B n :=
      ((hidY i).comp (measurable_lindTrunc (r n))).integral_eq
    have hy2 : ∫ ω, Y t ω ^ 2 ∂μ = M :=
      ((hidY i).comp (measurable_id.pow_const 2)).integral_eq
    rw [hfac1, hfac2, he0, hy1, hy2, integral_noise_sq hiid t] at hle
    exact hle
  -- ## the average is squeezed between `0` and the `i`-free bound
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      ∫ ω in {ω | η * Real.sqrt n ≤ |ε ((i : ℤ) + 1) ω * Y ((i : ℤ) + 1) ω|},
        (ε ((i : ℤ) + 1) ω * Y ((i : ℤ) + 1) ω) ^ 2 ∂μ := by
    intro n
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    exact setIntegral_nonneg (measurableSet_le measurable_const
      (((hiid.measurable _).mul (hYmeas _)).norm)) fun ω _ => sq_nonneg _
  have hub : ∀ n : ℕ, (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
      (∫ ω in {ω | η * Real.sqrt n ≤ |ε ((i : ℤ) + 1) ω * Y ((i : ℤ) + 1) ω|},
        (ε ((i : ℤ) + 1) ω * Y ((i : ℤ) + 1) ω) ^ 2 ∂μ) ≤ A n * M + σ2 * B n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, _root_.inv_zero, Finset.range_zero, Finset.sum_empty, mul_zero]
      exact add_nonneg (mul_nonneg (hAnn 0) hMnn) (mul_nonneg hσ.le (hBnn 0))
    have hsum : (∑ i ∈ Finset.range n,
        ∫ ω in {ω | η * Real.sqrt n ≤ |ε ((i : ℤ) + 1) ω * Y ((i : ℤ) + 1) ω|},
          (ε ((i : ℤ) + 1) ω * Y ((i : ℤ) + 1) ω) ^ 2 ∂μ)
        ≤ (n : ℝ) * (A n * M + σ2 * B n) := by
      calc (∑ i ∈ Finset.range n, _) ≤ ∑ _i ∈ Finset.range n, (A n * M + σ2 * B n) :=
            Finset.sum_le_sum fun i _ => hterm n i
        _ = (n : ℝ) * (A n * M + σ2 * B n) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    calc (n : ℝ)⁻¹ * _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * (A n * M + σ2 * B n)) := by
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = A n * M + σ2 * B n := by field_simp
  -- ## the bound vanishes
  have hrtop : Tendsto r atTop atTop := by
    refine Real.tendsto_sqrt_atTop.comp ?_
    exact Filter.Tendsto.const_mul_atTop hη
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hA0 : Tendsto A atTop (𝓝 0) :=
    tendsto_integral_lindTrunc (hiid.measurable 0) (hεsq 0) hrtop
  have hB0 : Tendsto B atTop (𝓝 0) :=
    tendsto_integral_lindTrunc (hYmeas 1) (hYsq 1) hrtop
  have hbound : Tendsto (fun n => A n * M + σ2 * B n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => A n * M) atTop (𝓝 0) := by
      simpa using hA0.mul_const M
    have h2 : Tendsto (fun n => σ2 * B n) atTop (𝓝 0) := by
      simpa using hB0.const_mul σ2
    simpa using h1.add h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound hnn hub

/-- **Item (3) of `hannanScore_brownInputs`, PROVED**: the averaged Lindeberg condition
for the ARMA score, obtained from `lindeberg_noise_mul` at the adapted copy of the score
vector and transferred back along `isLinearProcessOf_unique`. -/
private theorem hannanScore_lindeberg [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {ε U V U' V' : ℤ → Ω → ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2) (hB0 : ARMAInvertibleParams b0 a0)
    (hU : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) U ε μ)
    (hV : IsLinearProcessOf (armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ)) V ε μ)
    (hUmeas : ∀ t, Measurable (U t)) (hVmeas : ∀ t, Measurable (V t))
    (hU' : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) U' ε μ)
    (hV' : IsLinearProcessOf (armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ)) V' ε μ)
    (hU'meas : ∀ t, Measurable (U' t)) (hV'meas : ∀ t, Measurable (V' t))
    (hU'adapt : ∀ t, Measurable[sigmaLT ε (t + 1)] (U' t))
    (hV'adapt : ∀ t, Measurable[sigmaLT ε (t + 1)] (V' t))
    (d : Fin p ⊕ Fin q → ℝ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ∫ ω in {ω | η * Real.sqrt n ≤ |scoreSeq ε U V d ((i : ℤ) + 1) ω|},
          (scoreSeq ε U V d ((i : ℤ) + 1) ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hwn := hiid.isWhiteNoise
  have hc : Summable fun n => |∑ s, d s * hannanVecBack b0 a0 s n| :=
    summable_abs_hannanComboBack hB0 d
  have hY := isLinearProcessOf_scoreVec hwn hU hV hUmeas hVmeas d
  have hY2 := isLinearProcessOf_scoreVec hwn hU' hV' hU'meas hV'meas d
  have hYm := measurable_scoreVec hUmeas hVmeas d
  have hY2m := measurable_scoreVec hU'meas hV'meas d
  have hae : ∀ t : ℤ, scoreVec U V d t =ᵐ[μ] scoreVec U' V' d t :=
    fun t => isLinearProcessOf_unique hY hY2 hYm hY2m hiid.measurable t
  -- the adapted copy of the score vector is measurable for the *strict* past
  have hadapt : ∀ t : ℤ, Measurable[sigmaLT ε t] (scoreVec U' V' d t) := by
    intro t
    refine Measurable.add (Finset.measurable_sum _ fun k _ => measurable_const.mul ?_)
      (Finset.measurable_sum _ fun k _ => measurable_const.mul ?_)
    · exact (hU'adapt _).mono (sigmaLT_mono' (by omega)) le_rfl
    · exact (hV'adapt _).mono (sigmaLT_mono' (by omega)) le_rfl
  have hmem : ∀ t : ℤ, MemLp (scoreVec U' V' d t) 2 μ := fun t => hY2.memLp hc hwn hY2m t
  have hprod : ∀ t : ℤ, MemLp (fun ω => ε t ω * scoreVec U' V' d t ω) 2 μ :=
    fun t => memLp_noise_mul_of_adapted hiid t (hmem t) (hadapt t)
  have hstat : IsStrictlyStationary (scoreVec U' V' d) μ :=
    hY2.isStrictlyStationary hc hiid hY2m
  have hbase := lindeberg_noise_mul hiid hσ hY2m hadapt hmem hprod hstat hη
  refine hbase.congr fun n => ?_
  refine congrArg (fun z => (n : ℝ)⁻¹ * z) (Finset.sum_congr rfl fun i _ => ?_)
  have h1 : Measurable fun ω => ε ((i : ℤ) + 1) ω * scoreVec U V d ((i : ℤ) + 1) ω :=
    (hiid.measurable _).mul (hYm _)
  have h2 : Measurable fun ω => ε ((i : ℤ) + 1) ω * scoreVec U' V' d ((i : ℤ) + 1) ω :=
    (hiid.measurable _).mul (hY2m _)
  show ∫ ω in {ω | η * Real.sqrt n ≤
        |ε ((i : ℤ) + 1) ω * scoreVec U' V' d ((i : ℤ) + 1) ω|},
      (ε ((i : ℤ) + 1) ω * scoreVec U' V' d ((i : ℤ) + 1) ω) ^ 2 ∂μ
    = ∫ ω in {ω | η * Real.sqrt n ≤
        |ε ((i : ℤ) + 1) ω * scoreVec U V d ((i : ℤ) + 1) ω|},
      (ε ((i : ℤ) + 1) ω * scoreVec U V d ((i : ℤ) + 1) ω) ^ 2 ∂μ
  rw [setIntegral_sq_eq_integral_lindTrunc h1, setIntegral_sq_eq_integral_lindTrunc h2]
  refine integral_congr_ae ?_
  filter_upwards [hae ((i : ℤ) + 1)] with ω hω
  rw [hω]

/-- **Items (1) and (2) of `hannanScore_brownInputs`, PROVED — with the CORRECTED
constant.** The `L²` membership of the score and the conditional-variance LLN, over
i.i.d. noise, with no adaptedness hypothesis on `U`, `V` (the adapted copies are produced
internally by `exists_adapted_isLinearProcessOf` and are a.e. equal to `U`, `V` by
`isLinearProcessOf_unique`).

The limit is `σ² · (σ² · dᵀ Σ_back d)` with `Σ_back = hannanVarZBack b₀ a₀` — **not**
`hannanVarZ b₀ a₀`. See finding 26 at `hannanScore_brownInputs` below. -/
private theorem hannanScore_brownInputs_back [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {ε U V : ℤ → Ω → ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2) (hB0 : ARMAInvertibleParams b0 a0)
    (hU : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) U ε μ)
    (hV : IsLinearProcessOf (armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ)) V ε μ)
    (hUmeas : ∀ t, Measurable (U t)) (hVmeas : ∀ t, Measurable (V t))
    (d : Fin p ⊕ Fin q → ℝ) :
    (∀ i : ℕ, MemLp (scoreSeq ε U V d ((i : ℤ) + 1)) 2 μ) ∧
    (∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => (μ {ω | δ ≤ |(n : ℝ)⁻¹ *
        (∑ i ∈ Finset.range n,
          μ[fun ω' => scoreSeq ε U V d ((i : ℤ) + 1) ω' ^ 2 | sigmaLT ε ((i : ℤ) + 1)] ω)
        - σ2 * (σ2 * (d ⬝ᵥ (hannanVarZBack b0 a0 *ᵥ d)))|}).toReal) atTop (𝓝 0)) := by
  have hψb : Summable fun n => |armaPsi b0 (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) hB0.1
  have hψa : Summable fun n => |armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) (noRootClosedDisc_neg' hB0)
  obtain ⟨U', hU'meas, hU'adapt, hU'⟩ :=
    exists_adapted_isLinearProcessOf hψb hiid.isWhiteNoise hUmeas hU
  obtain ⟨V', hV'meas, hV'adapt, hV'⟩ :=
    exists_adapted_isLinearProcessOf hψa hiid.isWhiteNoise hVmeas hV
  refine ⟨fun i => ?_, fun δ hδ => ?_⟩
  · exact memLp_scoreSeqS hiid hB0 hU hV hUmeas hVmeas hU' hV' hU'meas hV'meas
      hU'adapt hV'adapt d i
  · exact hannanScore_condVar_lln hiid hσ hB0 hU hV hUmeas hVmeas hU' hV' hU'meas hV'meas
      hU'adapt hV'adapt d hδ

/-- **DEBT — the three analytic inputs Brown's CLT needs for the ARMA score.**

Given the martingale-difference property (which is PROVED upstream:
`armaScore_condexp_zero`), `mds_clt_sequence` additionally requires

1. `ξ_t = ε_t ⟨d, Z_t⟩ ∈ L²`. This does **not** follow from `ε ∈ L²` and `Z ∈ L²` by
   Hölder — FY assumes only two moments, so `ε_t²` need not be integrable against
   `Z_t²` term by term. It holds because `ε_t` is *independent* of `σ(ε_s : s < t)` and
   `Z_t` is (a.e. equal to) a `σ(ε_s : s < t)`-measurable variable, whence
   `E[ε_t² ⟨d, Z_t⟩²] = σ² E⟨d, Z_t⟩² < ∞`. The independence brick is
   `indep_noise_sigmaLT`, `private` to `ARMA/ScoreAnalysis.lean`.
2. The **conditional-variance LLN** `n⁻¹ Σ_{i<n} E[ξ_i² | 𝓕_i] →p σ²·(σ² dᵀ W d)`. By
   the same independence, `E[ξ_i² | 𝓕_i] = σ² ⟨d, Z_i⟩²` a.e., so this is the time
   average of the stationary sequence `⟨d, Z_t⟩²`. **The diagnosis "this is the
   pointwise-ergodic gap, absent from Mathlib" is WITHDRAWN** (2026-08-08): it is the
   *same shape* as `ARMA/Consistency.lean`'s residual item (C), and (C) is now known to
   be ergodic-theorem-free — and (C) has since been **PROVED** there
   (`armaResidualSS_tendstoInProb`, axiom-clean). The construction to copy, and the two
   places the original sketch was wrong, are:
   - the truncation must be **double**. Truncating only the filter at lag `m` leaves each
     truncated square a function of the *entire* noise past, so the progressions are
     **not** independent; one must also truncate the linear processes `U`, `V` at `m`,
     and then the window is `[t−m, t+m]` and the progression step is `2m`, not `m`;
   - the `m → ∞` transfer is **not** the two-factor Cauchy–Schwarz of the sketch but the
     term-by-term one, `∫|u² − z²| ≤ ‖u − z‖₂(‖u‖₂ + ‖z‖₂)`, followed by one Markov
     inequality. (The `L²` route really does need fourth cumulants; that part of the note
     stands, and it is exactly why the route goes through `L¹` + a.e. convergence.)
   **Scope blocker DISSOLVED (2026-08-09, wave `ts/s1b-arma-finish`).** The relocation
   this note asked for is unnecessary: the reusable core has been used, inside
   `ARMA/Consistency.lean`, to prove the *generic one-filter* statement

     `Consistency.linearProcess_avgSq_tendstoInProb` (public, axiom-clean):
     for i.i.d. noise and any absolutely summable `c` with `W` a linear process of `c`,
     `T⁻¹ Σ_{t<T} W_{t+1}² →p σ² Σ_n c_n²`,

   which is exactly what (2) consumes. Two predictions of the note above are
   **overturned**: (a) the *bilinear* Parseval identity is **not** needed — one collapses
   `U` and `V` into a **single** coefficient sequence *first*, namely
   `c_n = Σ_s d_s · hannanVec b₀ a₀ s n` (`ScoreAnalysis`), after which only the
   one-filter LLN is used; (b) with `π = δ` the `min(T − i, m)` edge term of
   `integral_defect_le` disappears, so the transfer is `O(T · tail_m)` with no `O(m)`
   correction — the generic statement is strictly *simpler* than (C), not a duplicate
   of it.
3. The **averaged Lindeberg condition**. Under stationarity the average collapses to the
   single term `E[ξ_0² 1{|ξ_0| ≥ η√n}] → 0`, which is dominated convergence once (1) is
   available; it is bundled here because it shares (1)'s independence input.

Recorded as one named debt rather than three, since (1)–(3) all reduce to the same two
inputs: noise/past independence and the `m`-dependent LLN described in (2).

**STATUS after wave `ts/s1b-arma-finish` (2026-08-09).** Both recorded blockers are gone:

* `ScoreAnalysis.indep_noise_sigmaLT` is now **public** (un-`private`d by this wave), so
  the independence input is citeable here;
* the LLN of (2) is now **proved and public** as
  `Consistency.linearProcess_avgSq_tendstoInProb`.

The residue is therefore three *new*, precisely identified sub-items, none of which the
original sketch names:

1. **The `L²`-limit past-measurability.** `Z_t` is only given as an `L²` limit of the
   `σ(ε_s : s < t)`-measurable partial sums `Σ_{n<N} ψ_n ε_{t−1−i−n}`; it is **not**
   assumed measurable for the past (`hannanScore_brownInputs` deliberately does not carry
   `hUadapt`/`hVadapt` — those appear only in `hannanScore_clt`). Every use of "by the
   same independence" in (1) and (2) silently needs an a.e.-equal `σ(ε_s : s < t)`-
   measurable representative of `Z_t`, i.e. a subsequence-a.e. extraction from the `L²`
   convergence plus `aestronglyMeasurable_of_tendsto_ae` **for the sub-σ-algebra**. This
   is the real obstacle in (1) and in the identity `E[ξ_i²|𝓕_i] = σ²⟨d, Z_i⟩²`, and it is
   not free. (Alternatively: strengthen the statement with `hUadapt`/`hVadapt`, which
   `hannanScore_clt` already has available — but the statement is frozen.)
2. **Linear-process closure plus the variance identity.** `⟨d, Z_t⟩ = Σ_n c_n ε_{t−n}`
   with `c_n = Σ_s d_s · hannanVec b₀ a₀ s n` needs "a finite combination of shifted
   linear processes is a linear process" (an `L²` triangle inequality; mechanical), and
   then `Σ_n c_n² = dᵀ (hannanVarZ b₀ a₀) d` is **exactly**
   `ScoreAnalysis.hannanVarZ_quadForm`. That lemma — and the whole
   `hannanVec`/`hannanSeq`/`hannanShiftSeq` chain appearing in its *statement* — is still
   `private` to `ARMA/ScoreAnalysis.lean`: a **new, sharper scope blocker** than the one
   this note originally recorded, and the only one left for (2).
3. **Identical distribution for the Lindeberg input.** (3)'s collapse "under stationarity
   the average is the single term `E[ξ_0² 1{|ξ_0| ≥ η√n}]`" needs the `ξ_i` to be
   identically distributed. Finite-block shift invariance is available
   (`Consistency`'s `map_noise_block'` device), but transferring it through the `L²`
   limit defining `U`, `V` is a separate step, with the same flavour as item 1.

**STATUS after wave `ts/f1-arma-finale` (2026-08-09): NOT attempted; the three-item residue
above is unchanged and remains accurate.** One brick built elsewhere by this wave is worth
naming because it is the *moment* half of items 1-2 and is now available in the import
closure: `Stationarity/ARMAExistence.lean`'s new (private) `integral_lin_mul_noise` gives
`E[W_t ε_s] = σ² ψ_{t−s}` for `s ≤ t` and `0` for `s > t`, for any linear process `W` of
`ψ` over white noise — i.e. exactly the orthogonality that turns an `L²`-limit filter into
its coefficient sequence, with no past-measurability input. It does **not** dissolve item 1:
the obstacle there is the *conditional* identity `E[ξ_i²|𝓕_i] = σ²⟨d, Z_i⟩²`, which needs an
a.e.-equal `σ(ε_s : s < i)`-measurable representative of `Z_i`, not a moment identity. It is
`private`, so a relocation would be needed to cite it.

**STATUS after wave `ts/f1b-arma-deep` (2026-08-09): items (1) and (2) are PROVED — but
this statement is FALSE as frozen, because its item (2) carries the wrong matrix. That is
FINDING 26 of the campaign.**

*What was built.* `hannanScore_brownInputs_back` above proves items (1) and (2) verbatim
except for the matrix, over the machinery inserted after `scoreSeq`. Two of the three
residual sub-items recorded above are **overturned**:

1. Residual item 1 (the `L²`-limit past-measurability) is **not** an obstacle and needs no
   subsequence extraction. `exists_adapted_isLinearProcessOf` — already in this file —
   produces an *adapted* linear process `U'` of the same coefficient sequence, and
   `isLinearProcessOf_unique` (new; the `L²` limit of a fixed sequence of partial sums is
   unique) gives `U t =ᵐ U' t`. So `Z_i` **does** have an a.e.-equal past-measurable
   representative, for free, and the frozen statement needs no `hUadapt`/`hVadapt`.
2. Residual item 2's scope blocker is gone (`ScoreAnalysis`'s Gram chain is now public),
   and its "mechanical" half is `isLinearProcessOf_comb` (new): a finite linear
   combination of shifted linear processes is a linear process, because the `N`-term
   partial sum of the combined filter is exactly the combination of the `(N − m_s)`-term
   partial sums of the pieces. With it, item (2) is a direct instance of
   `Consistency.linearProcess_avgSq_tendstoInProb`, as the note predicted.
3. Residual item 3 (the Lindeberg input) is **not** attempted. Its recorded blocker — an
   identical-distribution transfer through the `L²` limit — is now much cheaper than the
   note suggests, because `Process/LinearProcess.lean`'s
   `IsLinearProcessOf.isStrictlyStationary` gives strict stationarity of the *combined*
   process `⟨d, Z_t⟩` directly from `isLinearProcessOf_comb`. The remaining step is the
   split `{|ε_t Y_t| ≥ λ} ⊆ {|ε_t| ≥ √λ} ∪ {|Y_t| ≥ √λ}` followed by the same
   independence factorisation used in (1)–(2): the two resulting terms are
   `E[ε² 1_{|ε|≥√λ}]·E[Y²]` and `σ²·E[Y² 1_{|Y|≥√λ}]`, both independent of `i` and both
   `→ 0` by dominated convergence. That is a bounded amount of work, not a gap.

*FINDING 26 — the frozen constant is wrong.* Item (2)'s limit is
`σ² · (σ² · dᵀ Σ_back d)` with `Σ_back = hannanVarZBack b₀ a₀`, and **not** with
`hannanVarZ b₀ a₀`. The reason is a shift-alignment error in `hannanVarZ`, not an
arithmetic slip:

* `ScoreAnalysis.hannanVarZ` is proved (`hannanVarZ_gram`) to be the Gram matrix of the
  filter family with shifts `p + q − i`, which **decrease** in `i`: it is the covariance
  matrix of the *forward* vector `(U_{t−(p+q)+i}, V_{t−(p+q)+j})`, whose two blocks are
  right-aligned;
* the vector `scoreSeq` actually contracts is `Z_t = (U_{t−1−i})_{i<p} ⌢ (V_{t−1−j})_{j<q}`,
  with shifts `1 + i`, which **increase** in `i`: left-aligned blocks. Its Gram matrix is
  `hannanVarZBack`.
* Both Grams have the same diagonal blocks (an autocovariance is even) but read the AR–MA
  cross-block at **opposite** lags, `i − j` versus `j − i`, and a cross-covariance is not
  even. They coincide when `p = 0`, when `q = 0`, and (up to the block-wise reversal
  permutation, which the frozen statement's free vector `c` does not apply) when `p = q`.
  They differ for `p, q ≥ 1` with `max (p, q) ≥ 2`.
* `ScoreAnalysis.hannanVarZ_quadForm_ne_back` is a formalized ARMA(2,1) witness:
  `b(z) = 1 − z/2`, `a(z) = 1`, `x = (0, 1) ⌢ (1)`, where the two quadratic forms differ by
  exactly `1`. The parameter point satisfies `ARMAInvertibleParams`.

*Scope of the finding.* The wrong matrix propagates: `hannanScore_clt` (proved *from* this
debt), `armaMLE_linearization`, and the frozen headline `hannan_mle_clt` — whose asymptotic
variance is `cᵀ (hannanVarZ b₀ a₀)⁻¹ c` — all carry it. The correct variance is
`cᵀ (hannanVarZBack b₀ a₀)⁻¹ c`. `hannan_mle_clt` is therefore expected to be FALSE as
stated for `p, q ≥ 1` with `max (p, q) ≥ 2`; ARMA(1,1), pure AR and pure MA are unaffected,
which is presumably how the error survived, ARMA(1,1) being the case textbooks print. A
*complete* refutation of the headline would additionally need a formalized instance
carrying the MLE asymptotics themselves, which is out of reach here; what is formalized is
the matrix identity together with the corrected item (2), which pin the error to
`hannanVarZ`'s shift convention and nothing else.

*What wave `ts/f1b-arma-deep` deliberately did NOT do* was change the statement: with the
lane owner's call outstanding, the debt was left at a `sorry` carrying the wrong matrix,
with the corrected version proved beside it as `hannanScore_brownInputs_back`.

**REPAIR APPLIED and DEBT CLOSED (wave `ts/f1c-hannan-orientation`, 2026-08-09).** The
laptop authorized re-stating the frozen Hannan chain with the object the score actually
contracts. Item (2) below now reads `hannanVarZBack b₀ a₀`, and with that the whole
statement is **PROVED**: items (1) and (2) are `hannanScore_brownInputs_back`, and item
(3) — the averaged Lindeberg condition, the one piece wave `ts/f1b-arma-deep` did not
attempt — is `hannanScore_lindeberg` above, exactly along the route its residual note
predicted (split the level set, factorise by noise/past independence, kill both halves by
dominated convergence, uniformly in the time index by strict stationarity of `⟨d, Z_t⟩`).

Note what the repair is *not*: it is not a change to `hannanVarZ`, which stays exactly as
FY prints it, and not a re-typographing of Hannan's paper. `hannanVarZ` is a correct
object — the Gram matrix of the forward auxiliary vector, proved as such by
`hannanVarZ_gram` — and Hannan's own convention is stated for a vector whose alignment
matches it. What was wrong was the *pairing*: the Lean score process `scoreSeq` contracts
`Z_t = (U_{t−1−i}, V_{t−1−j})`, whose Gram is `hannanVarZBack`, and the machine witness
`ScoreAnalysis.hannanVarZ_quadForm_ne_back` shows at ARMA(2,1) that these are different
quadratic forms. The repair aligns the statements with the process in the file, and the
witness — not a reading of the paper's typography — is what forces it. Invertibility of
the replacement is `ScoreAnalysis.hannanVarZBack_posDef` (new; proved by re-running the
Bézout/degree argument at the score's shifts, since the two Grams are conjugate by a
permutation only when `p = q`). -/
private theorem hannanScore_brownInputs [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε U V : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hU : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) U ε μ)
    (hV : IsLinearProcessOf (armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ)) V ε μ)
    (hUmeas : ∀ t, Measurable (U t)) (hVmeas : ∀ t, Measurable (V t))
    (d : Fin p ⊕ Fin q → ℝ) :
    (∀ i : ℕ, MemLp (scoreSeq ε U V d ((i : ℤ) + 1)) 2 μ) ∧
    (∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => (μ {ω | δ ≤ |(n : ℝ)⁻¹ *
        (∑ i ∈ Finset.range n,
          μ[fun ω' => scoreSeq ε U V d ((i : ℤ) + 1) ω' ^ 2 | sigmaLT ε ((i : ℤ) + 1)] ω)
        - σ2 * (σ2 * (d ⬝ᵥ (hannanVarZBack b0 a0 *ᵥ d)))|}).toReal) atTop (𝓝 0)) ∧
    (∀ η : ℝ, 0 < η → Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        ∫ ω in {ω | η * Real.sqrt n ≤ |scoreSeq ε U V d ((i : ℤ) + 1) ω|},
          (scoreSeq ε U V d ((i : ℤ) + 1) ω) ^ 2 ∂μ) atTop (𝓝 0)) := by
  have hψb : Summable fun n => |armaPsi b0 (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) hB0.1
  have hψa : Summable fun n => |armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) (noRootClosedDisc_neg' hB0)
  obtain ⟨U', hU'meas, hU'adapt, hU'⟩ :=
    exists_adapted_isLinearProcessOf hψb hiid.isWhiteNoise hUmeas hU
  obtain ⟨V', hV'meas, hV'adapt, hV'⟩ :=
    exists_adapted_isLinearProcessOf hψa hiid.isWhiteNoise hVmeas hV
  obtain ⟨h1, h2⟩ := hannanScore_brownInputs_back hiid hσ hB0 hU hV hUmeas hVmeas d
  exact ⟨h1, h2, fun η hη => hannanScore_lindeberg hiid hσ hB0 hU hV hUmeas hVmeas
    hU' hV' hU'meas hV'meas hU'adapt hV'adapt d hη⟩

/-- **The score CLT** (step 3 of the assembly): the normalized partial sums of the
score martingale are asymptotically `N(0, σ⁴ dᵀ W d)`, `W = hannanVarZBack b₀ a₀` (the
score's own Gram; finding 26). Proved by
feeding `armaScore_condexp_zero` (the martingale-difference property) and
`hannanScore_brownInputs` into Brown's martingale CLT `mds_clt_sequence`, along the
noise filtration `𝓕_t = σ(ε_s : s < t)`. -/
private theorem hannanScore_clt [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε U V : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    (hU : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) U ε μ)
    (hV : IsLinearProcessOf (armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ)) V ε μ)
    (hUmeas : ∀ t, Measurable (U t)) (hVmeas : ∀ t, Measurable (V t))
    (hUadapt : ∀ t, Measurable[sigmaLT ε (t + 1)] (U t))
    (hVadapt : ∀ t, Measurable[sigmaLT ε (t + 1)] (V t))
    (d : Fin p ⊕ Fin q → ℝ) (hnn : 0 ≤ d ⬝ᵥ (hannanVarZBack b0 a0 *ᵥ d)) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, scoreSeq ε U V d ((i : ℤ) + 1) ω) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (σ2 * (σ2 * (d ⬝ᵥ (hannanVarZBack b0 a0 *ᵥ d)))))) u)) := by
  obtain ⟨hL2, hvar, hlind⟩ :=
    hannanScore_brownInputs h hiid hσ hB0 hU hV hUmeas hVmeas d
  refine mds_clt_sequence (G := fun i : ℕ => sigmaLT ε ((i : ℤ) + 1))
    (fun i => sigmaLT_le' hiid.measurable _)
    (fun i j hij => sigmaLT_mono' (by
      have : (i : ℤ) ≤ (j : ℤ) := Int.ofNat_le.2 hij
      omega))
    (fun i => ?_) hL2 (fun i => ?_) (by positivity) hvar hlind u
  · -- adaptedness: `ξ_i` is `σ(ε_s : s ≤ i + 1)`-measurable
    have hunfold : scoreSeq ε U V d ((i : ℤ) + 1)
        = fun ω => ε ((i : ℤ) + 1) ω *
          ((∑ k : Fin p, d (.inl k) * U (((i : ℤ) + 1) - 1 - (k : ℕ)) ω)
            + ∑ k : Fin q, d (.inr k) * V (((i : ℤ) + 1) - 1 - (k : ℕ)) ω) := rfl
    rw [hunfold]
    refine (measurable_sigmaLT' (Z := ε) (by push_cast; omega)).mul (Measurable.add ?_ ?_)
    · exact Finset.measurable_sum _ fun k _ => measurable_const.mul
        ((hUadapt _).mono (sigmaLT_mono' (by push_cast; omega)) le_rfl)
    · exact Finset.measurable_sum _ fun k _ => measurable_const.mul
        ((hVadapt _).mono (sigmaLT_mono' (by push_cast; omega)) le_rfl)
  · exact armaScore_condexp_zero h hiid hB0 hcausal hmeas hU hV hUmeas hVmeas d ((i : ℤ) + 1)

/-- **DEBT — the Taylor/sandwich linearization** (steps 2, 4 and 5 of the assembly).

On the event `θ̂_T ∈ ball(θ₀, ρ)` (which has probability `→ 1` by `mle_consistent`, since
`θ₀ ∈ interior K`), the `o(1/T)`-approximate minimality `hargmin` gives a near-first-order
condition `∇Q_T(θ̂_T) = o_p(T^{−1/2})`; a coordinatewise mean-value expansion of `∇Q_T`
around `θ₀` then yields `0 = ∇Q_T(θ₀) + H_T(θ̄_T)(θ̂_T − θ₀) + o_p(T^{−1/2})` with
`θ̄_T` between `θ̂_T` and `θ₀`, and `H_T(θ̄_T) →p 2σ² W` uniformly on `ball(θ₀, ρ)`
(continuity of the second-derivative filters plus the same ergodic average as
`hannanScore_brownInputs`(2)). Inverting `H` and reading off the `c`-coordinate gives

  `√T·cᵀ(θ̂_T − θ₀) = σ⁻²·T^{−1/2} Σ_t ε_t ⟨W⁻¹c, Z_t⟩ + o_p(1)`,

which is the statement below (the constant is fixed by the variance algebra recorded at
the head of this section; `hannanVarZ_posDef` is what makes `W⁻¹` meaningful, whence the
`hcop`/`hbdeg`/`hadeg` hypotheses — and it is **PROVED** upstream, contrary to the
now-stale remark that it was an open `sorry`).

**STATUS after wave `ts/s1b-arma-finish` (2026-08-09).** Two of the three recorded
blockers are gone: `Consistency.mle_consistent` is **PROVED** (0-sorry, axiom-clean), and
so is the local stochastic equicontinuity `armaProfileS_equicontinuous` above. The
"pointwise ergodic theorem" diagnosis stays withdrawn. What is left is genuinely the
Taylor/sandwich analysis itself, whose two inputs are:

* `hannanScore_brownInputs` above (see its own status note for the three residual items);
* the **Hessian ULLN** `H_T(θ̄_T) →p 2σ²W` uniformly on a ball. Its pointwise half is now
  a direct instance of `Consistency.linearProcess_avgSq_tendstoInProb` applied to the
  first/second-derivative filters of the residual (each is again a linear process of the
  noise, with an absolutely summable coefficient sequence by
  `Consistency.exists_uniform_geometric_bound_arma`); its uniform half is the same
  `ℓ¹`-modulus argument as `Consistency.armaProfileS_locallyEquicontinuous`, applied to
  the derivative filters instead of `π` itself. Neither is attempted here.

Not attempted in this wave: the first-order condition from `hδTfast` (the
`o(1/T)`-approximate minimality) and the mean-value expansion, which are the substance.

**STATUS after wave `ts/f1-arma-finale` (2026-08-09): NOT attempted; the two-input residue
above is unchanged.**

**STATUS after wave `ts/f1b-arma-deep` (2026-08-09): NOT attempted, and this statement
carries FINDING 26** — its `(hannanVarZ b0 a0)⁻¹ *ᵥ c` is the *forward* Gram, whereas the
score direction the sandwich produces is `(hannanVarZBack b0 a0)⁻¹ *ᵥ c`; see the finding
paragraph at `hannanScore_brownInputs`. For `p, q ≥ 1` with `max (p, q) ≥ 2` the two differ,
so the statement is expected to be FALSE as frozen; for `q = 0` (the instantiation used by
`ls_yw_mle_equivalent_debt`) it is unaffected, by
`ScoreAnalysis.hannanVarZ_eq_back_of_pure_ar`.

Of the two recorded inputs, the first is now discharged in its corrected form
(`hannanScore_brownInputs_back`: items (1) and (2)), so the honest residue here is
(a) the Hessian ULLN, (b) the first-order condition from `hδTfast` and the mean-value
expansion, and (c) the matrix repair. Note that (a)'s pointwise half now has a second
route besides the one recorded above: the derivative filters are finite combinations of
shifted linear processes, so `isLinearProcessOf_comb` puts them in the exact shape
`Consistency.linearProcess_avgSq_tendstoInProb` consumes, with no ad-hoc coefficient
bookkeeping.

**STATUS after wave `ts/f1c-hannan-orientation` (2026-08-09): item (c) DONE, items (a)
and (b) NOT closed — this remains the one substantive debt of the Hannan chain.** The
statement above now reads `(hannanVarZBack b0 a0)⁻¹ *ᵥ c`, so it is no longer expected to
be false, and its score input `hannanScore_brownInputs` is fully PROVED (item (3), the
averaged Lindeberg condition, closed by `hannanScore_lindeberg`). What is left is exactly
the deterministic-analysis half of the sandwich, and this wave sharpens the ledger for it:

* **(a) Hessian ULLN.** Pointwise: an instance of
  `Consistency.linearProcess_avgSq_tendstoInProb` per second-derivative filter, via
  `isLinearProcessOf_comb` (no new brick). Uniform: the `ℓ¹`-modulus argument of
  `Consistency.armaProfileS_locallyEquicontinuous` applied to the derivative filters —
  the modulus brick `Consistency.exists_armaPi_l1_modulus` is stated for `π` itself, so
  its `∂π/∂θ` analogue is the *one genuinely missing input* of (a). This wave did not
  build it; note the amendment recorded at `armaProfileS_equicontinuous` ("no `∂π/∂θ`
  companion is needed") applies to the *criterion*, not to the Hessian, so it does not
  dissolve this item.
* **(b) First-order condition + mean-value expansion.** Untouched, and it is the part
  that needs a genuine `o(1/T)`-to-`o_p(T^{−1/2})` argument on `hδTfast`; nothing in the
  score layer bears on it.

The two are independent of each other and of the orientation repair; neither is blocked
on a missing analytic theory, both are bounded but substantial formalization.

**STATUS after wave `ts/f4a-arma-last` (2026-08-09): NOT attempted; items (a) and (b)
stand.** Two entries for the ledger, both produced while closing
`Diagnostics.residual_acf_transfer_residue` (which is now PROVED) and both bearing on (a):

* the search region of (a)'s uniform half no longer has to be assumed: invertibility is an
  **open** condition, `Diagnostics.exists_ball_invertible` (`private` there; it is four
  short lemmas — a uniform Lipschitz bound of `z ↦ b(z)` in the coefficients against the
  minimum of `|b(z)|` over the closed disc — and should be relocated next to
  `Consistency.exists_uniform_geometric_bound_arma` when a wave needs it here). This is what
  lets a `√T`-consistency hypothesis alone produce the compact `K` the `ℓ¹` bricks want; the
  present statement carries its own `K`, so it does not need this, but the Hessian ULLN's
  *pointwise* half at a moving `θ̄_T` does;
* **FINDING 35 (this wave).** The note above says (a)'s missing input is "the `∂π/∂θ`
  analogue of `Consistency.exists_armaPi_l1_modulus`". For the part of the argument that
  compares filters at two parameter values, that is **not** what is needed: the `ℓ¹`
  *Lipschitz* bound `Consistency.exists_armaPi_l1_lipschitz` plus Young's inequality on the
  triangular convolution (`Diagnostics.sum_sq_truncConv_le`, proved this wave) already
  converts a parameter difference into an `ℓ²` bound on the *window* of fitted residuals,
  with no derivative of `π` anywhere. What genuinely needs `∂π/∂θ` is only the *second*
  derivative filter appearing in `H_T` itself, i.e. the object being averaged — not the
  modulus that controls its oscillation. A next wave should re-scope item (a) accordingly:
  the oscillation half is now brick-complete, the missing input is the identification of
  `∂²/∂θ²` of the residual as a finite combination of shifted linear processes. -/
private theorem armaMLE_linearization [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε U V : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    (hbdeg : (arPoly b0).natDegree = p) (hadeg : (maPoly a0).natDegree = q)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    (hU : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) U ε μ)
    (hV : IsLinearProcessOf (armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ)) V ε μ)
    (hUmeas : ∀ t, Measurable (U t)) (hVmeas : ∀ t, Measurable (V t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))}
    (hK : IsCompact K) (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
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
    (c : Fin p ⊕ Fin q → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ => (μ {ω | δ ≤
        |Real.sqrt T *
            ((∑ i : Fin p, c (.inl i) * ((θ T ω).1 i - b0 i)) +
              ∑ j : Fin q, c (.inr j) * ((θ T ω).2 j - a0 j))
          - σ2⁻¹ * ((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T,
              scoreSeq ε U V ((hannanVarZBack b0 a0)⁻¹ *ᵥ c) ((i : ℤ) + 1) ω)|}).toReal)
      atTop (𝓝 0) := by
  sorry

end ScoreCLT

/-- **FY Theorem 3.2 (Hannan), Cramér–Wold/charFun form**: under the `mle_consistent`
setting, every linear combination of `√T (θ̂_T − θ₀)` is asymptotically
`N(0, cᵀ W c)` with `W = (hannanVarZBack b₀ a₀)⁻¹` — the inverse of the covariance of the
score vector `Z_t = (U_{t−1−i}, V_{t−1−j})`.

**Statement repaired (wave `ts/f1c-hannan-orientation`, 2026-08-09).** The frozen form
wrote the *forward* Gram `hannanVarZ b₀ a₀` here and was FALSE for `p, q ≥ 1` with
`max (p, q) ≥ 2`; see FINDING 26 and the repair paragraph at `hannanScore_brownInputs`.
ARMA(1,1), pure AR and pure MA are unaffected by the change (`hannanVarZ_eq_back_of_pure_ar`,
`..._of_pure_ma`, and the reversal permutation at `p = q`), which is why the error
survived: those are the cases textbooks print. -/
theorem hannan_mle_clt [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ)
    -- USER-INPUT: iid innovations; FY Thm 3.2 (no 4th moment required)
    (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    -- USER-INPUT: (b₀, a₀) ∈ 𝓑; FY eq. (3.11)
    (hB0 : ARMAInvertibleParams b0 a0)
    -- USER-INPUT: coprime minimal orders; Hannan 1973 (FY implicit)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    -- USER-INPUT: exact orders (see `hannanVarZBack_posDef`'s docstring — coprimality
    -- alone does not make the information matrix invertible); Hannan 1973 §2
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
        (c ⬝ᵥ ((hannanVarZBack b0 a0)⁻¹ *ᵥ c)))) u)) := by
  classical
  -- ## The information matrix, the sandwich direction `d = W⁻¹c`, and the limit variance
  have hWpd : (hannanVarZBack b0 a0).PosDef := hannanVarZBack_posDef hB0 hcop hbdeg hadeg
  have hWdet : IsUnit (hannanVarZBack b0 a0).det := Matrix.isUnit_iff_isUnit_det _ |>.1 hWpd.isUnit
  have hWd : hannanVarZBack b0 a0 *ᵥ ((hannanVarZBack b0 a0)⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hWdet, Matrix.one_mulVec]
  -- `dᵀ W d = cᵀ W⁻¹ c` — the collapse `(2σ²W)⁻¹(4σ⁴W)(2σ²W)⁻¹ = W⁻¹` in coordinates
  have hdv : ((hannanVarZBack b0 a0)⁻¹ *ᵥ c) ⬝ᵥ
      (hannanVarZBack b0 a0 *ᵥ ((hannanVarZBack b0 a0)⁻¹ *ᵥ c))
        = c ⬝ᵥ ((hannanVarZBack b0 a0)⁻¹ *ᵥ c) := by
    rw [hWd, dotProduct_comm]
  have hvnn : 0 ≤ c ⬝ᵥ ((hannanVarZBack b0 a0)⁻¹ *ᵥ c) := by
    have := hWpd.inv.posSemidef.dotProduct_mulVec_nonneg c
    simpa using this
  -- ## The auxiliary AR processes `b₀(B)U = ε`, `a₀(B)V = ε`, in adapted form
  have hψb : Summable fun n => |armaPsi b0 (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) hB0.1
  have hψa : Summable fun n => |armaPsi (fun j => -a0 j) (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) (noRootClosedDisc_neg' hB0)
  obtain ⟨U0, hU0meas, hU0⟩ := exists_isLinearProcessOf hψb h.whiteNoise
  obtain ⟨V0, hV0meas, hV0⟩ := exists_isLinearProcessOf hψa h.whiteNoise
  obtain ⟨U, hUmeas, hUadapt, hU⟩ :=
    exists_adapted_isLinearProcessOf hψb h.whiteNoise hU0meas hU0
  obtain ⟨V, hVmeas, hVadapt, hV⟩ :=
    exists_adapted_isLinearProcessOf hψa h.whiteNoise hV0meas hV0
  -- ## Step 3: the score CLT
  have hscore := hannanScore_clt h hiid hσ hB0 hcausal hmeas hU hV hUmeas hVmeas
    hUadapt hVadapt ((hannanVarZBack b0 a0)⁻¹ *ᵥ c) (hdv ▸ hvnn) (σ2⁻¹ * u)
  rw [hdv] at hscore
  -- ## The multiplier `σ⁻²` acts on the Gaussian scale, not on the random variable
  have hgauss : charFun (gaussianReal 0 (Real.toNNReal
        (σ2 * (σ2 * (c ⬝ᵥ ((hannanVarZBack b0 a0)⁻¹ *ᵥ c)))))) (σ2⁻¹ * u)
      = charFun (gaussianReal 0 (Real.toNNReal (c ⬝ᵥ ((hannanVarZBack b0 a0)⁻¹ *ᵥ c)))) u := by
    rw [charFun_gaussianReal, charFun_gaussianReal,
      Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hvnn]
    congr 1
    have hneC : (σ2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hσ)
    push_cast
    field_simp
    ring
  rw [hgauss] at hscore
  -- ## The two sequences of the Slutsky step, and their measurability
  have hUVmeas : ∀ (T : ℕ), Measurable
      (fun ω => σ2⁻¹ * ((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T,
        scoreSeq ε U V ((hannanVarZBack b0 a0)⁻¹ *ᵥ c) ((i : ℤ) + 1) ω)) := by
    intro T
    refine measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_))
    exact (hiid.measurable _).mul
      ((Finset.measurable_sum _ fun k _ => measurable_const.mul (hUmeas _)).add
        (Finset.measurable_sum _ fun k _ => measurable_const.mul (hVmeas _)))
  have hZmeas : ∀ (T : ℕ), Measurable
      (fun ω => Real.sqrt T *
        ((∑ i : Fin p, c (.inl i) * ((θ T ω).1 i - b0 i)) +
          ∑ j : Fin q, c (.inr j) * ((θ T ω).2 j - a0 j))) := by
    intro T
    refine measurable_const.mul (Measurable.add ?_ ?_)
    · exact Finset.measurable_sum _ fun i _ => measurable_const.mul
        (((measurable_pi_apply i).comp (hθmeas T).fst).sub measurable_const)
    · exact Finset.measurable_sum _ fun j _ => measurable_const.mul
        (((measurable_pi_apply j).comp (hθmeas T).snd).sub measurable_const)
  -- ## Steps 2/4/5 (the sandwich) + charFun Slutsky
  refine tendsto_charFun_of_tendstoInProb_sub hUVmeas hZmeas ?_ (fun η hη =>
    armaMLE_linearization h hiid hσ hB0 hcop hbdeg hadeg hcausal hmeas hU hV hUmeas hVmeas
      hK hKB hcopK hK0 θ hθmeas hδT0 hδTfast hargmin c hη)
  refine hscore.congr fun T => ?_
  exact (charFun_map_mul_comp
    (((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        (hiid.measurable _).mul
          ((Finset.measurable_sum _ fun k _ => measurable_const.mul (hUmeas _)).add
            (Finset.measurable_sum _ fun k _ => measurable_const.mul (hVmeas _))))) :
      Measurable _)).aemeasurable σ2⁻¹ u).symm

section Sigma2

/-! ### The two inputs of the variance part

`S(θ̂_T)/T = (S(θ̂_T)/T − S(θ₀)/T) + S(θ₀)/T`: the second term is the quadratic-form
LLN at the truth, the first is killed by consistency plus a local equicontinuity
estimate. Both are recorded as named debts below; everything else is proved. -/

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
  simpa using tsum_ite_eq (0 : ℕ) (1 : ℝ)

/-- **The quadratic-form LLN at the truth**: `T⁻¹ xᵀ Γ_T(θ₀)⁻¹ x →p σ²`.

This is **not a second copy** of Consistency's debt: it is exactly that lane's
`armaProfileS_tendstoInProb` specialised to `θ = θ₀`, where the contrast variance is
`1` (`armaContrastVar_self`, above — the coprimality-free half of
`armaContrastVar_eq_one_iff`). The public `criterion_tendsto_contrast` is **strictly
weaker** than what is needed here: it controls `log(S_T/T) + T⁻¹ log det Γ_T`, and
`Real.log` is not injective at Lean's junk value (`Real.log 0 = 0`), so at `σ² = 1` the
degenerate event `{S_T = 0}` is invisible at the `log` level and the `exp`-transfer back
to `S_T/T` fails.

The lemma cited was `private` to `ARMA/Consistency.lean` when this debt was recorded;
the project-level fix that note asked for — making it public — has now been applied, so
this statement is a two-line corollary and no longer carries any debt of its own. -/
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
  simp only [Set.mem_setOf_eq, armaContrastVar_self, mul_one, div_eq_inv_mul]

/-- **Local stochastic equicontinuity of the profiled sum of squares — PROVED**
(2026-08-09, wave `ts/s1b-arma-finish`): the oscillation of `θ ↦ T⁻¹ S_T(θ)` over a small
ball around `θ₀` is uniformly (in `T`) negligible in probability. It is a one-line
corollary of `Consistency.armaProfileS_locallyEquicontinuous`, where the estimate is
carried out; the note below is kept because two of its predictions were **overturned**
there (see the last paragraph).

Hannan's ergodic route proves this together with the pointwise LLN: `T⁻¹ S_T(θ)` is,
up to the `O(1/T)` edge effect controlled by `logdet_armaToeplitz_vanishes`'s
whitened-Toeplitz factorisation, the time average `T⁻¹ Σ_t r_t(θ)²` of the squared
`θ`-residual process, and `θ ↦ r_t(θ)` is Lipschitz in `θ` on the compact `K ⊆ 𝓑`
with an `L²`-integrable Lipschitz constant (geometric decay of `∂π_j/∂θ`, uniform on
`K` by `exists_geometric_bound_armaPi`). The claim that the missing ingredient is "the
pointwise ergodic theorem, absent from Mathlib" is **WITHDRAWN** (2026-08-08): the
pointwise LLN it is paired with is now reduced, in Consistency, to the single
ergodic-theorem-free item (C) (`armaProfileS_tendstoInProb`'s `hCLLN`), and the
finite-`T` half of the *oscillation* statement is not an ergodic statement at all — it
is the `θ`-Lipschitz estimate above, uniform in `T`, which needs a locally uniform
geometric bound on `π(θ)` and on `∂π(θ)` over the compact `K`.

**The brick itself is now PROVED** (2026-08-09, wave `ts/s1-arma-endgame`):
`Consistency.exists_uniform_geometric_bound_arma` (public) gives, for any compact
`K ⊆ 𝓑`, one `(C, r)` with `r < 1` bounding `|armaPi θ n|` *and* `|armaPsi θ n|` by
`C rⁿ` uniformly in `θ ∈ K`. Two amendments to the recipe recorded above:

* the Lipschitz-in-`z` step is **unnecessary**. Pushing the radius past `1` is done by
  the polar parametrisation `z = s · w` (`‖w‖ ≤ 1`, `s ∈ [1, 2]`): the zero set of
  `(θ, w, s) ↦ aeval (s·w) (maPoly θ.2)` is compact, so the minimum of its
  `s`-coordinate is already `> 1`. The rest is `IsCompact.exists_isMinOn` /
  `exists_isMaxOn` for `inf |den|` and `sup |num|` on `K × closedBall 0 R`;
* the diagnosis that `exists_geometric_bound_armaPsi` cannot be used as a black box was
  correct — its Cauchy estimate is redone carrying the radius and the sup-bound
  (`Consistency.abs_armaPsi_le_of_disc_bounds`, via `norm_cauchyPowerSeries_le` plus
  uniqueness of power series).

**No `∂π/∂θ` companion is needed.** What the oscillation estimate actually consumes is a
*modulus of continuity*, `∀ ε > 0, ∃ ρ > 0, ∀ θ θ' ∈ K, dist θ θ' < ρ →
∑' n, |π_n(θ) − π_n(θ')| < ε`, and that is free from the brick plus compactness of
`K × K`: it is PROVED as `Consistency.exists_armaPi_l1_modulus` (public).

**AMENDMENT (2026-08-09).** The Gram-tail *difference* modulus asked for below is **not
needed**, and the two "shortcuts" declared dead below are indeed dead but irrelevant.
What the oscillation estimate actually consumes is a bound on the correction term
`T⁻¹uᵀG_T(θ)u` that is `o_p(1)` *uniformly over `θ ∈ K`* — and that is available from the
entrywise bound `|G_{ij}| ≤ (1−r²)⁻¹h_ih_j`, which factorises the quadratic form into a
square of a **`θ`-free** envelope (`Consistency.quadForm_gramTail_le_env`). One Markov
inequality then covers the whole supremum at rate `O(1/T)`. The superseded plan follows.

**What was thought to be left here** was the matching modulus for the Gram tail. Writing
`Γ_T(θ)⁻¹ = Π_Tᵀ(1 + G_T)⁻¹Π_T` and splitting

  `[Π−Π′]ᵀ(1+G)⁻¹Π  +  Π′ᵀ[(1+G)⁻¹−(1+G′)⁻¹]Π  +  Π′ᵀ(1+G′)⁻¹[Π−Π′]`,

the outer two terms are handled by `exists_armaPi_l1_modulus`, `(1+G)⁻¹ ⪯ 1` and the
Schur test (`rowSum_kernel_le`); the middle term needs
`∑_j |G_T(θ)_{ij} − G_T(θ′)_{ij}| ≤ L(ρ)` uniformly in `T` and `i`, i.e.
`trace_gramTail_le`'s estimate redone in difference form off the same modulus. The two
apparent shortcuts do not work: the pathwise bound `T⁻¹uᵀG u ≤ K P² · T⁻¹‖x‖²` is
`O_p(1)`, not `o_p(1)`, and using `(1+K)⁻¹ ⪯ (1+G)⁻¹` in the sandwich costs an additive
`O(1)` term `log(1+K)` in the criterion. -/
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

section PACF

/-! ### The sample PACF (FY Proposition 3.1)

**A blocker on the commissioned route, reported.** The lane plan routed this through
Bartlett's formula (`sampleACF_bartlett_clt_debt`, FY Thm 2.8(iii)) plus a delta method.
That is **not available for the frozen statement**: the Bartlett debt carries a
`MemLp (ε 0) 4 μ` hypothesis (FY assumes a finite fourth moment throughout Thm 2.8),
whereas `samplePACF_clt` — correctly, since FY Prop 3.1 needs only two moments — does
not. There is no way to manufacture the fourth moment, so the Bartlett route is closed.

The route taken instead is the martingale one, which is also the one that explains the
`N(0, 1)`: for `k > p` the population Yule–Walker solution at order `k` is `(b₀, 0…0)`,
so the AR(k) fit is *exact*, and

  `√T π̂(k) = σ⁻² · T^{−1/2} Σ_t ε_t ⟨d, (X_{t−1}, …, X_{t−k})⟩ + o_p(1)`,

where `d` is the last row of the order-`k` information matrix's inverse. The instrument
`ε_t ⟨d, past⟩` is a martingale difference against the noise filtration, so the *same*
Brown CLT wiring as `hannanScore_clt` applies verbatim once the AR(p) coefficient vector
is padded with zeros to length `k`. FY's reciprocal-variance identity
`(Γ_k⁻¹)_{kk} = 1/ν_{k−1} = σ⁻²` for `k > p` (Schur complement plus exactness of the
AR(p) predictor beyond lag `p`) is exactly the normalisation `dᵀ W_k d = 1` that turns
the limit into `N(0, 1)`; it is carried by the single named debt below. -/

/-- Padding a coefficient vector with zeros beyond its length changes no induced sum. -/
private lemma sum_padCoeff {p k : ℕ} {M : Type*} [AddCommMonoid M] (hk : p ≤ k)
    (b0 : Fin p → ℝ) (f : ℕ → ℝ → M) (hf : ∀ n, f n 0 = 0) :
    ∑ i : Fin k, f (i : ℕ) (if hi : (i : ℕ) < p then b0 ⟨i, hi⟩ else 0)
      = ∑ i : Fin p, f (i : ℕ) (b0 i) := by
  classical
  have h1 : ∑ i : Fin k, f (i : ℕ) (if hi : (i : ℕ) < p then b0 ⟨i, hi⟩ else 0)
      = ∑ n ∈ Finset.range k, f n (if hn : n < p then b0 ⟨n, hn⟩ else 0) :=
    Fin.sum_univ_eq_sum_range (fun n => f n (if hn : n < p then b0 ⟨n, hn⟩ else 0)) k
  have h2 : ∑ n ∈ Finset.range p, f n (if hn : n < p then b0 ⟨n, hn⟩ else 0)
      = ∑ n ∈ Finset.range k, f n (if hn : n < p then b0 ⟨n, hn⟩ else 0) :=
    Finset.sum_subset (fun x hx => Finset.mem_range.2
        (lt_of_lt_of_le (Finset.mem_range.1 hx) hk))
      (fun n _ hn => by rw [dif_neg (by simpa using hn), hf])
  have h3 : ∑ n ∈ Finset.range p, f n (if hn : n < p then b0 ⟨n, hn⟩ else 0)
      = ∑ i : Fin p, f (i : ℕ) (b0 i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => f n (if hn : n < p then b0 ⟨n, hn⟩ else 0)) p]
    exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt]
  rw [h1, ← h2, h3]

/-- Padding does not change the AR lag polynomial. -/
private lemma arPoly_pad {p k : ℕ} (hk : p ≤ k) (b0 : Fin p → ℝ) :
    arPoly (fun i : Fin k => if hi : (i : ℕ) < p then b0 ⟨i, hi⟩ else 0) = arPoly b0 := by
  simp only [arPoly]
  exact congrArg (fun z => 1 - z)
    (sum_padCoeff hk b0 (fun n r => Polynomial.C r * Polynomial.X ^ (n + 1)) (by simp))

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
    simpa [dif_pos hlt'] using ((hmeas _).sub hmean).mul ((hmeas _).sub hmean)
  · have hlt' : ¬ ((t : ℕ) + m < T) := by simpa using hlt
    simp [dif_neg hlt']

/-- The sample PACF of the observation window is measurable. -/
private lemma measurable_samplePACF {T : ℕ} {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (k : ℕ) :
    Measurable fun ω => samplePACF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) k := by
  classical
  simp only [samplePACF]
  split
  · exact measurable_inv_mulVec (fun i j => measurable_sampleACVF hmeas _)
      (fun i => measurable_sampleACVF hmeas _) _
  · exact measurable_const

/-- **DEBT — the delta-method linearization of the sample PACF, with its variance
normalisation** (FY Prop 3.1's "can be proved").

Two classical facts are bundled, because they are proved together (B&D §8.10, §10.8):

* the **linearization**: for `k > p` the sample Yule–Walker map `γ̂ ↦ (Γ̂_k⁻¹ γ̂_k)_k` is
  differentiable at the population point, where the solution is `(b₀, 0, …, 0)` with last
  coordinate `pacf X μ k = 0` (PROVED upstream as `pacf_eq_zero_of_isAR`), so no centring
  term appears; propagating the derivative through the exact AR(k) recursion
  `X_t = Σ_{j<k} φ_j X_{t−1−j} + ε_t` turns `√T π̂(k)` into the normalized score
  `σ⁻² T^{−1/2} Σ_t ε_t ⟨d, (X_{t−1−j})_{j<k}⟩` up to `o_p(1)`;
* the **reciprocal-variance identity** `dᵀ W_k d = 1`, i.e. `(Γ_k⁻¹)_{kk} = 1/ν_{k−1}`
  (Schur complement / partitioned inverse) together with `ν_{k−1} = σ²` for `k > p`
  (the AR(p) one-step predictor is already exact from `p` lags, so no further lag reduces
  the prediction variance).

**STATUS after wave `ts/s1b-arma-finish` (2026-08-09).** The recorded blocker — "the
ergodic LLN for `Γ̂_k →p Γ_k`" — is **available**. Each entry of `Γ̂_k` is a sample
autocovariance `T⁻¹ Σ_t X_t X_{t+m}`, and polarization
`X_t X_{t+m} = ¼((X_t + X_{t+m})² − (X_t − X_{t+m})²)` writes it as a difference of two
instances of `Consistency.linearProcess_avgSq_tendstoInProb`, since `X_· ± X_{·+m}` is
again a linear process of the noise with coefficient sequence
`ψ_n ± ψ_{n−m}1{n ≥ m}` (absolutely summable). The sample-mean centring in `sampleACVF`
costs one further application of the same brick plus a Markov step.

What is left here is therefore the delta-method bookkeeping itself: the differentiability
of `γ̂ ↦ (Γ̂_k⁻¹ γ̂_k)_k` at the population point (Cramer's rule plus `Γ_k` invertible),
the propagation through the exact AR(k) recursion, and the reciprocal-variance identity
`(Γ_k⁻¹)_{kk} = σ⁻²` for `k > p`. Not attempted in this wave.

**STATUS after wave `ts/f1-arma-finale` (2026-08-09): NOT attempted; the residue above is
unchanged.**

**STATUS after wave `ts/f1b-arma-deep` (2026-08-09): NOT attempted, but this statement is
IMMUNE to finding 26** — it instantiates the MA order at `0`, and
`ScoreAnalysis.hannanVarZ_eq_back_of_pure_ar` proves `hannanVarZ b elim0 = hannanVarZBack b
elim0` (only the AR–AR block survives, and an autocovariance is even). So its
`d ⬝ᵥ (hannanVarZ … *ᵥ d) = 1` normalization is the right one and the residue is exactly
the three delta-method items listed above, with none of the matrix repair
`armaMLE_linearization` needs.

One brick the residue list does not name is now available and is the right entry point for
the `√T` half: `hannanScore_brownInputs_back` supplies items (1) and (2) of the Brown
inputs (in the pure-AR case with the correct matrix, by the immunity just quoted), so what
is left really is only the delta-method bookkeeping — the Jacobian of
`γ̂ ↦ (Γ̂_k⁻¹ γ̂_k)_k`, the AR(k) recursion, and `(Γ_k⁻¹)_{kk} = σ⁻²`. The brief's suggestion
to cite `sampleACF_bartlett_clt_debt` remains available but is not needed for the *matrix*
side of the statement; it is needed only to feed the joint CLT of `γ̂`.

**STATUS after wave `ts/f1c-hannan-orientation` (2026-08-09): NOT closed; statement
re-stated with `hannanVarZBack`, which changes nothing here.** The normalisation now reads
`d ⬝ᵥ (hannanVarZBack (pad b₀) elim0 *ᵥ d) = 1`. By `hannanVarZ_eq_back_of_pure_ar` the two
matrices are *literally equal* at `q = 0`, so this is the same statement as before; it is
re-stated only so that the whole chain speaks about the object the score contracts, and so
that the repaired `hannanScore_clt` (which now consumes the backward Gram) can be applied
to it verbatim — as `samplePACF_clt` below in fact does, unchanged. The residue is
unchanged: the three delta-method items above.

**STATUS after wave `ts/f4a-arma-last` (2026-08-09): NOT attempted; the three delta-method
items stand, and one of them is now cheaper than the note suggests.** The wave closed
`Diagnostics.residual_acf_transfer_residue`, whose machinery covers the *first* half of
item 1's "propagating the derivative through the exact AR(k) recursion": the passage from a
perturbation of the filter to a perturbation of the sample autocovariance is now a named
deterministic brick (`Diagnostics.abs_sampleACVF_sub_le`, an `ℓ²`-modulus bound on
`|γ̂_y(k) − γ̂_z(k)|`, together with Young's inequality
`Diagnostics.sum_sq_truncConv_le` for the triangular convolution). Both are `private` to
`ARMA/Diagnostics.lean` and would have to be relocated — they use nothing from that file.

What that does **not** touch, and what remains the substance here, is the Jacobian of
`γ̂ ↦ (Γ̂_k⁻¹ γ̂_k)_k` (Cramer's rule at the population point) and the reciprocal-variance
identity `(Γ_k⁻¹)_{kk} = σ⁻²`; the second is pure linear algebra (Schur complement) and is
the one item of this debt that needs no probability at all. -/
private theorem samplePACF_linearization [IsProbabilityMeasure μ] {p k : ℕ}
    {b0 : Fin p → ℝ} {σ2 : ℝ} {X ε U V : ℤ → Ω → ℝ}
    (h : IsAR b0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hroot : NoRootClosedDisc b0)
    (hcausal : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) X ε μ)
    (hmeas : ∀ t, Measurable (X t)) (hk : p < k)
    (hU : IsLinearProcessOf (armaPsi
      (fun i : Fin k => if hi : (i : ℕ) < p then b0 ⟨i, hi⟩ else 0)
      (Fin.elim0 : Fin 0 → ℝ)) U ε μ)
    (hV : IsLinearProcessOf (armaPsi (fun j => -(Fin.elim0 : Fin 0 → ℝ) j)
      (Fin.elim0 : Fin 0 → ℝ)) V ε μ)
    (hUmeas : ∀ t, Measurable (U t)) (hVmeas : ∀ t, Measurable (V t)) :
    ∃ d : Fin k ⊕ Fin 0 → ℝ,
      d ⬝ᵥ (hannanVarZBack (fun i : Fin k => if hi : (i : ℕ) < p then b0 ⟨i, hi⟩ else 0)
        (Fin.elim0 : Fin 0 → ℝ) *ᵥ d) = 1 ∧
      ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ => (μ {ω | δ ≤
        |Real.sqrt T * samplePACF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) k
          - σ2⁻¹ * ((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T,
              scoreSeq ε U V d ((i : ℤ) + 1) ω)|}).toReal) atTop (𝓝 0) := by
  sorry

end PACF

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
  classical
  -- ## Pad the AR(p) coefficients with zeros to length `k`: the same process is an AR(k)
  set bk : Fin k → ℝ := fun i => if hi : (i : ℕ) < p then b0 ⟨i, hi⟩ else 0 with hbkdef
  have hpoly : arPoly bk = arPoly b0 := arPoly_pad hk.le b0
  have hrootk : NoRootClosedDisc bk := by
    intro z hz; rw [hpoly]; exact hroot z hz
  have hBk : ARMAInvertibleParams bk (Fin.elim0 : Fin 0 → ℝ) :=
    ⟨hrootk, fun z _ => by simp [maPoly]⟩
  have hpsi : armaPsi bk (Fin.elim0 : Fin 0 → ℝ) = armaPsi b0 (Fin.elim0 : Fin 0 → ℝ) := by
    funext n; simp only [armaPsi, hpoly]
  have hcausalk : IsLinearProcessOf (armaPsi bk (Fin.elim0 : Fin 0 → ℝ)) X ε μ := by
    rw [hpsi]; exact hcausal
  have hARk : IsARMA bk (Fin.elim0 : Fin 0 → ℝ) σ2 X ε μ := by
    refine ⟨h.measurableX, h.whiteNoise, fun t => ?_⟩
    filter_upwards [h.recurrence t] with ω hω
    rw [hω]
    exact congrArg (fun z => z + ε t ω + ∑ j : Fin 0, (Fin.elim0 : Fin 0 → ℝ) j *
        ε (t - 1 - (j : ℕ)) ω)
      (sum_padCoeff hk.le b0 (fun n r => r * X (t - 1 - (n : ℕ)) ω) (by simp)).symm
  -- ## The auxiliary processes of the order-`k` score, in adapted form
  have hψb : Summable fun n => |armaPsi bk (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) hBk.1
  have hψa : Summable fun n =>
      |armaPsi (fun j => -(Fin.elim0 : Fin 0 → ℝ) j) (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) (noRootClosedDisc_neg' hBk)
  obtain ⟨U0, hU0meas, hU0⟩ := exists_isLinearProcessOf hψb h.whiteNoise
  obtain ⟨V0, hV0meas, hV0⟩ := exists_isLinearProcessOf hψa h.whiteNoise
  obtain ⟨U, hUmeas, hUadapt, hU⟩ :=
    exists_adapted_isLinearProcessOf hψb h.whiteNoise hU0meas hU0
  obtain ⟨V, hVmeas, hVadapt, hV⟩ :=
    exists_adapted_isLinearProcessOf hψa h.whiteNoise hV0meas hV0
  -- ## The delta-method debt supplies the direction `d` and its unit normalisation
  obtain ⟨d, hd1, hlin⟩ :=
    samplePACF_linearization h hiid hσ hroot hcausal hmeas hk hU hV hUmeas hVmeas
  -- ## The score CLT at order `k`, then the `σ⁻²` multiplier on the Gaussian scale
  have hscore := hannanScore_clt hARk hiid hσ hBk hcausalk h.measurableX hU hV hUmeas hVmeas
    hUadapt hVadapt d (by rw [hd1]; norm_num) (σ2⁻¹ * u)
  rw [hd1] at hscore
  have hgauss : charFun (gaussianReal 0 (Real.toNNReal (σ2 * (σ2 * 1)))) (σ2⁻¹ * u)
      = charFun (gaussianReal 0 1) u := by
    rw [charFun_gaussianReal, charFun_gaussianReal, Real.coe_toNNReal _ (by positivity)]
    have hneC : (σ2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hσ)
    congr 1
    push_cast
    field_simp
    ring
  rw [hgauss] at hscore
  -- ## charFun Slutsky
  refine tendsto_charFun_of_tendstoInProb_sub (Y := fun T ω =>
      σ2⁻¹ * ((Real.sqrt T)⁻¹ * ∑ i ∈ Finset.range T, scoreSeq ε U V d ((i : ℤ) + 1) ω))
    (fun T => ?_) (fun T => measurable_const.mul (measurable_samplePACF hmeas k)) ?_ hlin
  · refine measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_))
    exact (hiid.measurable _).mul
      ((Finset.measurable_sum _ fun l _ => measurable_const.mul (hUmeas _)).add
        (Finset.measurable_sum _ fun l _ => measurable_const.mul (hVmeas _)))
  · refine hscore.congr fun T => ?_
    exact (charFun_map_mul_comp
      (((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
          (hiid.measurable _).mul
            ((Finset.measurable_sum _ fun l _ => measurable_const.mul (hUmeas _)).add
              (Finset.measurable_sum _ fun l _ => measurable_const.mul (hVmeas _))))) :
        Measurable _)).aemeasurable σ2⁻¹ u).symm

/-! ### The frozen `ls_yw_mle_equivalent_debt` statement is FALSE — a formalized witness

Found in wave `ts/s12-model-selection` (2026-08-09). The statement quantifies over an
**arbitrary measurable** `bMLE`: no hypothesis ties it to the Gaussian likelihood, to
least squares, or to the data at all (and no least-squares estimator appears anywhere,
despite the name). It therefore asserts `√T · dist(b̂_YW, bMLE) →p 0` for *every*
measurable sequence `bMLE`, which fails for the constant translate
`bMLE := b̂_YW + 1` as soon as `p ≥ 1`.

The witness below is axiom-clean: the instance is the causal AR(1) with zero coefficient
(`b(z) = 1`, so `X = ε`) driven by the coordinate white noise on `(ℤ → ℝ, ⊗ N(0,1))`,
and `bMLE` is the translate, whose measurability comes from `measurable_inv_mulVec` /
`measurable_sampleACVF` above.

**Repair.** B&D Thm 10.8.2 compares three *estimators*, so `bMLE` (and a least-squares
sequence `bLS`, currently absent) must carry their defining hypotheses — for `bMLE` the
`hargmin`/`hδTfast` pair of `hannan_mle_clt`, for `bLS` the normal equations. With those
in place the statement becomes a genuine `√T`-equivalence and the residue is the one
recorded at `armaMLE_linearization`.

**The repair is applied** to `ls_yw_mle_equivalent_debt` below (wave
`ts/s12b-model-repairs`, 2026-08-09); see the Statement-strengthening paragraph there.
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
  simp


/-- The Yule-Walker estimator of the frozen statement, at the white-noise instance. -/
private noncomputable def wnYW (T : ℕ) (ω : ℤ → ℝ) : Fin 1 → ℝ :=
  ((Matrix.of fun i' j : Fin 1 =>
      sampleACVF (fun t : Fin T => wnCoord (((t : ℕ) : ℤ) + 1) ω)
        ((i' : ℤ) - (j : ℤ)).natAbs)⁻¹) *ᵥ
    fun i' : Fin 1 => sampleACVF (fun t : Fin T => wnCoord (((t : ℕ) : ℤ) + 1) ω)
      ((i' : ℕ) + 1)

private lemma wnYW_measurable (T : ℕ) : Measurable (wnYW T) := by
  refine measurable_pi_lambda _ fun i => ?_
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
    fun T => measurable_pi_lambda _ fun i =>
      ((measurable_pi_apply i).comp (wnYW_measurable T)).add measurable_const
  have key := H wn_isAR wn_isIIDNoise one_pos wn_noRoot wn_isLinearProcess
    wnCoord_measurable wnYW (fun _ _ _ => rfl)
    (fun T ω => fun i : Fin 1 => wnYW T ω i + 1) hmle (δ := 1) one_pos
  -- the two estimator sequences are at distance `≥ 1`, so the event is everything
  have hset : ∀ T : ℕ, 1 ≤ T → {ω : ℤ → ℝ | (1 : ℝ) ≤
      Real.sqrt T * dist (wnYW T ω) (fun i : Fin 1 => wnYW T ω i + 1)} = Set.univ := by
    intro T hT
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
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

/-- **DEBT (B&D Thm 10.8.2; FY §3.3.2 remark)**: least-squares, Yule–Walker, and
Gaussian-MLE estimator sequences of a causal AR(p) are asymptotically equivalent
(`√T`-differences vanish in probability). Statement recorded at the coarse level FY
cites.

**Statement strengthening (wave `ts/s12b-model-repairs`, 2026-08-09).** The frozen form
was FALSE — see `ls_yw_mle_equivalent_debt_false` above, kept verbatim as the record: it
quantified over an *arbitrary measurable* `bMLE`, so the constant translate
`bMLE := b̂_YW + 1` refuted it, and no least-squares sequence appeared at all despite the
name. Two repairs, exactly the ones that witness's docstring prescribes:

1. **`bMLE` is an MLE.** It carries `hannan_mle_clt`'s defining package verbatim: a
   compact identifiable search region `K` of invertible parameters with `θ₀` interior, and
   `o(1/T)`-approximate minimization `hargmin`/`hδTfast` of the profiled criterion
   (`q = 0`, so the parameter is the pair `(b, Fin.elim0)`). Exact minimizers qualify
   (`δT = 0`). This is what makes the statement citable against `hannan_mle_clt` and
   `armaMLE_linearization`.
2. **The least-squares sequence is present**, introduced through its **normal equations**
   `hLS`: for each coordinate `i`, the regressor `X_{s−i}` is orthogonal to the fitted
   residual over the usable window `p ≤ s < T`. This is B&D's third estimator, the one the
   theorem's name promises.

The conclusion is correspondingly the pair of `√T`-equivalences LS ↔ YW and YW ↔ MLE;
LS ↔ MLE follows from them by the triangle inequality. The residue is the one recorded at
`armaMLE_linearization` (for the MLE leg) together with the standard YW-vs-LS edge-effect
bookkeeping (the two differ only by the `O_p(1)` boundary terms of the two windows).

**STATUS after wave `ts/f1-arma-finale` (2026-08-09): NOT attempted, but the repair was
audited for NON-VACUITY, since a repair that adds hypotheses can silently make a statement
unsatisfiable.** It is not vacuous: `hLS` asks for a solution of the *normal equations* of
the regression of `X_{s+1}` on `(X_{s−i})_{i<p}` over `s ∈ [p, T)`, and normal equations
`Aβ = c` with `A` the (symmetric positive-semidefinite) design Gram matrix always have a
solution, since `c` is the vector of inner products of the response with the columns and
therefore lies in the range of `A`; a *measurable* selection exists as the pointwise limit
`lim_{ε↓0} (A + εI)⁻¹ c` (the Moore-Penrose solution), each term being measurable in `ω` by
`measurable_inv_mulVec` above. So `hLSmeas`/`hLS` are jointly satisfiable, and the a.s.
nonsingularity of `A` for large `T` makes the selection a.s. unique. The two remaining
mathematical items are unchanged: the MLE leg (via `armaMLE_linearization`) and the YW-vs-LS
edge-effect bookkeeping, where note the two windows genuinely differ — `hLS` reaches back to
`X_0`, one step outside the `X_1, …, X_T` window that `sampleACVF` sees, an `O_p(1)`
boundary term that dies after `√T`-scaling but must be discarded explicitly.

**STATUS after wave `ts/f1b-arma-deep` (2026-08-09): NOT attempted; IMMUNE to finding 26.**
The MLE leg goes through `armaMLE_linearization`, which finding 26 shows carries the wrong
information matrix in general — but only for genuinely mixed models. Here the MA order is
`0`, and `ScoreAnalysis.hannanVarZ_eq_back_of_pure_ar` gives
`hannanVarZ b₀ elim0 = hannanVarZBack b₀ elim0`, so the instantiation this debt needs is
unaffected and the two mathematical items recorded above stand verbatim. In particular this
debt does **not** have to wait on the `hannanVarZ` repair; it waits only on the
Taylor/sandwich analysis and on the `X_0` boundary discard.

**STATUS after wave `ts/f1c-hannan-orientation` (2026-08-09): NOT attempted; audit of the
two items refreshed.** The orientation repair is applied upstream, and as predicted it
changes nothing here (`q = 0`). The two items stand, and the second is the one this wave
can sharpen from the audit it did of the first:

* **MLE leg.** Blocked on `armaMLE_linearization`, whose residue is now precisely (a) the
  Hessian ULLN and (b) the first-order condition/mean-value expansion — the score input is
  PROVED. Nothing else stands between this debt and that one.
* **YW-vs-LS leg — FINDING 33 (wave `ts/f1c-hannan-orientation`, 2026-08-09).** The `X_0`
  boundary discard recorded above is correct but is not the only window mismatch, and the
  second one is easy to miss: `bYW` is built from
  `sampleACVF`, which is **mean-corrected** (`Process/Defs.lean`), whereas `hLS`'s normal
  equations are *uncentered*. So the two systems differ by the sample-mean terms as well as
  by the endpoints. Both differences are `O_p(1/T)` after the LLN — `X̄_T = O_p(T^{−1/2})`
  and it enters quadratically — so the leg is still `o_p(T^{−1/2})` as claimed, but a proof
  has to discard *three* things, not one: the `X_0` endpoint, the `s = T−1` endpoint, and
  the centring. The same remark applies to any future comparison of `samplePACF` (also
  `sampleACVF`-based, hence centred) with a normal-equation estimator.

**STATUS after wave `ts/f4a-arma-last` (2026-08-09): NOT attempted. Note the two legs are
now of very different maturity**, which a next wave should exploit rather than treating the
conjunction as one item:

* the **YW-vs-LS** leg (second conjunct) is independent of `armaMLE_linearization`
  altogether. Its three discards are exactly the `O_p(1/T)` bookkeeping this wave carried
  out for the residual-vs-innovation transfer, and the missing input it does *not* share
  with that transfer is the **invertibility of the sample Gram in probability** — the
  population Toeplitz `Γ_p` is positive definite, so `Γ̂_p⁻¹ = O_p(1)`, but nothing in the
  project turns `Γ̂_p →p Γ_p` plus `Γ_p ≻ 0` into a statement about `Γ̂_p⁻¹`. That is the
  honest cost of the second conjunct and it is a self-contained item;
* the **YW-vs-MLE** leg is still blocked on `armaMLE_linearization` items (a) and (b), for
  which see finding 35 recorded there.

A wave that wants partial credit here should prove the second conjunct first: it closes
half of the statement over one new brick, whereas the first conjunct closes over the whole
of the Hannan sandwich. -/
theorem ls_yw_mle_equivalent_debt [IsProbabilityMeasure μ] {p : ℕ}
    {b0 : Fin p → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsAR b0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hroot : NoRootClosedDisc b0)
    (hcausal : IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: the Yule–Walker estimator (sample-YW solution); B&D Thm 10.8.2
    (bYW : (T : ℕ) → Ω → Fin p → ℝ)
    (hYW : ∀ (T : ℕ) (ω : Ω) (i : Fin p),
      bYW T ω i = (((Matrix.of fun i' j : Fin p =>
          sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
            ((i' : ℤ) - (j : ℤ)).natAbs)⁻¹) *ᵥ
        fun i' : Fin p => sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          ((i' : ℕ) + 1)) i)
    -- USER-INPUT: the least-squares estimator, through its normal equations on the
    -- usable window `p ≤ s < T`; B&D Thm 10.8.2 (absent from the frozen statement)
    (bLS : (T : ℕ) → Ω → Fin p → ℝ) (hLSmeas : ∀ T, Measurable (bLS T))
    (hLS : ∀ (T : ℕ) (ω : Ω) (i : Fin p),
      ∑ s ∈ Finset.Ico p T, X ((s : ℤ) - (i : ℕ)) ω *
          (X ((s : ℤ) + 1) ω
            - ∑ j : Fin p, bLS T ω j * X ((s : ℤ) - (j : ℕ)) ω) = 0)
    -- USER-INPUT: the Gaussian-MLE sequence, with `hannan_mle_clt`'s defining package
    -- (compact identifiable region, θ₀ interior, o(1/T)-approximate minimization);
    -- B&D Thm 10.8.2 / Hannan 1973 §2
    (bMLE : (T : ℕ) → Ω → Fin p → ℝ) (hMLEmeas : ∀ T, Measurable (bMLE T))
    {K : Set ((Fin p → ℝ) × (Fin 0 → ℝ))}
    (hK : IsCompact K) (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
    (hcopK : ∀ ba ∈ K, IsCoprime (arPoly ba.1) (maPoly ba.2))
    (hK0 : (b0, (Fin.elim0 : Fin 0 → ℝ)) ∈ interior K)
    {δT : ℕ → ℝ} (hδT0 : ∀ T, 0 ≤ δT T)
    (hδTfast : Tendsto (fun T : ℕ => (T : ℝ) * δT T) atTop (𝓝 0))
    (hargmin : ∀ (T : ℕ) (ω : Ω),
      (bMLE T ω, (Fin.elim0 : Fin 0 → ℝ)) ∈ K ∧ ∀ ba ∈ K,
        armaProfileCriterion (bMLE T ω) (Fin.elim0 : Fin 0 → ℝ)
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          ≤ armaProfileCriterion ba.1 ba.2
              (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) + δT T)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ => (μ {ω | δ ≤
        Real.sqrt T * dist (bYW T ω) (bMLE T ω)}).toReal) atTop (𝓝 0) ∧
    Tendsto (fun T : ℕ => (μ {ω | δ ≤
        Real.sqrt T * dist (bYW T ω) (bLS T ω)}).toReal) atTop (𝓝 0) := by
  sorry

end StatLean.TimeSeries
