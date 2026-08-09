import StatLean.TimeSeries.ARMA.ScoreAnalysis
import StatLean.TimeSeries.Process.SampleACF

/-!
# Diagnostic checking of fitted ARMA models (FY §3.5)

* **Standardized residuals** (FY eq. (3.29)): the fitted-model residuals scaled by the
  estimated innovation standard deviation (`standardizedResiduals`; finite-sample
  object, defined through the AR(∞) inversion `armaPi` truncated to the sample);
* the **residual correlogram validity** claim (FY §3.5.2): for a correctly specified
  model with `√T`-consistent parameter estimates, the residual sample ACF at a fixed
  lag admits the same `±1.96/√T` bands as white noise — recorded as a literature
  DEBT at the granularity FY asserts it ("approximate validity from
  √T-consistency"; the exact Box–Pierce correction is cited only).

FY §3.5.3's formal whiteness tests live in ch. 7 (outside the current scope); no
portmanteau statistic appears in ch. 3, so none is stated here.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.5,
eq. (3.29) (pp. 110–113). (`FY §3.5`.)

**Bibliographic comments.** Residual correlogram bands: Box & Jenkins (1970) §8.2;
the residual-ACF distribution correction is Box & Pierce (1970), refined by
Ljung & Box (1978) — both cited by FY without statements.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-- **Truncated sample residuals** of a fitted ARMA model (FY eq. (3.29) numerators):
`ε̂_t = Σ_{j<t} π_j(b̂, â) x_{t−j}` (the AR(∞) inversion truncated at the sample
start; `t` is 0-based over the data vector). -/
noncomputable def sampleResiduals {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) (t : Fin T) : ℝ :=
  ∑ j ∈ Finset.range ((t : ℕ) + 1),
    armaPi b a j * x ⟨(t : ℕ) - j, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩

/-- **Standardized residuals** (FY eq. (3.29)): residuals scaled by the plugged-in
innovation standard deviation `σ̂ = √(S/T)` (junk when `S ≤ 0`). -/
noncomputable def standardizedResiduals {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) (t : Fin T) : ℝ :=
  sampleResiduals b a x t / Real.sqrt (armaProfileS b a x / T)

/-! ### Sanity checks on the finite-sample residual definitions

Three consistency facts that exercise `sampleResiduals`/`standardizedResiduals` on
concrete data: the leading residual is the leading observation (`π₀ = 1`), the AR(1)
residual is the explicit one-step prediction error `x_t − b₁ x_{t−1}`, and the
standardization really removes the scale of the data. -/

private lemma coeff_arPoly_aux {p : ℕ} (b : Fin p → ℝ) (m : ℕ) :
    (arPoly b).coeff m
      = (if m = 0 then 1 else 0) - ∑ i : Fin p, if m = (i : ℕ) + 1 then b i else 0 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]

private lemma coeff_maPoly_zero_aux {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  simp [maPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

/-- `π₀ = 1`: the AR(∞) inversion is normalized, since `b(0) = a(0) = 1`. -/
private lemma armaPi_zero {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) : armaPi b a 0 = 1 := by
  have ha : PowerSeries.constantCoeff (R := ℝ) ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)
      = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, coeff_maPoly_zero_aux]
  have hb : PowerSeries.constantCoeff (R := ℝ) ((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
      = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe, coeff_arPoly_aux]
    simp
  unfold armaPi
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_inv, ha, hb]
  norm_num

/-- **Sanity check 1**: the truncated residual at the sample start is the first
observation itself (nothing is available to predict it with). -/
private lemma sampleResiduals_at_zero {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) (h0 : 0 < T) :
    sampleResiduals b a x ⟨0, h0⟩ = x ⟨0, h0⟩ := by
  simp [sampleResiduals, armaPi_zero]

/-- With no MA part the inversion coefficients are just the AR polynomial's. -/
private lemma armaPi_ma_nil {p : ℕ} (b : Fin p → ℝ) (n : ℕ) :
    armaPi b (Fin.elim0 : Fin 0 → ℝ) n = (arPoly b).coeff n := by
  have h : (maPoly (Fin.elim0 : Fin 0 → ℝ)) = 1 := by simp [maPoly]
  unfold armaPi
  rw [h]
  simp [Polynomial.coeff_coe]

/-- **Sanity check 2**: for a realized AR(1) sample the truncated residual is the
explicit one-step prediction error `ε̂_t = x_t − b₁ x_{t−1}` (the sum in
`sampleResiduals` collapses to its first two terms because `π_j = 0` for `j ≥ 2`). -/
private lemma sampleResiduals_ar_one {T : ℕ} (b : Fin 1 → ℝ) (x : Fin T → ℝ)
    (t : Fin T) (ht : 1 ≤ (t : ℕ)) :
    sampleResiduals b (Fin.elim0 : Fin 0 → ℝ) x t
      = x t - b 0 * x ⟨(t : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩ := by
  have hsub : Finset.range 2 ⊆ Finset.range ((t : ℕ) + 1) := fun y hy =>
    Finset.mem_range.mpr (by have := Finset.mem_range.mp hy; omega)
  unfold sampleResiduals
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_range_succ, Finset.sum_range_one, armaPi_ma_nil, armaPi_ma_nil,
      coeff_arPoly_aux, coeff_arPoly_aux]
    simp only [Fin.isValue]
    norm_num
    ring
  · intro j _ hj
    have h2 : 2 ≤ j := by simpa using hj
    rw [armaPi_ma_nil, coeff_arPoly_aux]
    simp [show j ≠ 0 by omega, show j ≠ 1 by omega]

private lemma sampleResiduals_const_mul {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (c : ℝ) (x : Fin T → ℝ) (t : Fin T) :
    sampleResiduals b a (fun i => c * x i) t = c * sampleResiduals b a x t := by
  unfold sampleResiduals
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma armaProfileS_const_mul {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (c : ℝ) (x : Fin T → ℝ) :
    armaProfileS b a (fun i => c * x i) = c ^ 2 * armaProfileS b a x := by
  unfold armaProfileS
  have h : (fun i => c * x i) = c • x := by funext i; simp
  rw [h, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp [smul_eq_mul]
  ring

/-- **Sanity check 3**: the standardization does its job — rescaling the data by a
positive constant leaves the standardized residuals unchanged (the numerator scales by
`c`, the plugged-in `σ̂ = √(S/T)` by `c` as well, since `S` is quadratic). -/
private lemma standardizedResiduals_const_mul {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} {c : ℝ} (hc : 0 < c) (x : Fin T → ℝ) (t : Fin T) :
    standardizedResiduals b a (fun i => c * x i) t = standardizedResiduals b a x t := by
  have hs : Real.sqrt (c ^ 2 * armaProfileS b a x / T)
      = c * Real.sqrt (armaProfileS b a x / T) := by
    rw [mul_div_assoc, Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
  unfold standardizedResiduals
  rw [sampleResiduals_const_mul, armaProfileS_const_mul, hs,
    mul_div_mul_left _ _ (ne_of_gt hc)]

/-! ### Assembly of the residual correlogram claim over two named residues

`√T ρ̂_{ε̂}(k) = √T ρ̂_ε(k) + √T (ρ̂_{ε̂}(k) − ρ̂_ε(k))`: the first term is the
innovation-side CLT (residue (A)), the second vanishes in probability (residue (B)), and
charFun-Slutsky glues them. The glue and the measurability of the innovation-side
statistic are **proved** here; `MLEAsymptotics`' copy of the Slutsky lemma is `private`
on the far side of the `Consistency` import edge, so it is replayed. -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- charFun of a pushforward, as an integral on the base space. -/
private lemma charFun_map_eq_integral₂ {f : Ω → ℝ} (hf : AEMeasurable f μ) (u : ℝ) :
    charFun (μ.map f) u = ∫ ω, Complex.exp (Complex.I * (u * f ω : ℝ)) ∂μ := by
  rw [charFun_apply_real, integral_map hf (by fun_prop)]
  simp only [Complex.ofReal_mul]
  congr 1 with ω
  ring_nf

private lemma integrable_cexp_mul_I₂ [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) :
    Integrable (fun ω => Complex.exp (Complex.I * (f ω : ℝ))) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (Complex.measurable_exp.comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with ω
  simp [Complex.norm_exp]

/-- The elementary two-point bound `‖e^{ix} − e^{iy}‖ ≤ min(|x − y|, 2)`. -/
private lemma norm_cexp_sub_cexp_le₂ (x y : ℝ) :
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

/-- **Slutsky's theorem at the charFun level** (the copy of `MLEAsymptotics`'
`tendsto_charFun_of_tendstoInProb_sub`, which is `private` on the far side of the
`Consistency` import edge). -/
private lemma tendsto_charFun_of_tendstoInProb_sub₂ [IsProbabilityMeasure μ]
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
    rw [charFun_map_eq_integral₂ (hZ T).aemeasurable, charFun_map_eq_integral₂ (hY T).aemeasurable,
      ← integral_sub (integrable_cexp_mul_I₂ ((hZ T).const_mul u))
        (integrable_cexp_mul_I₂ ((hY T).const_mul u))]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ ω, ‖Complex.exp (Complex.I * ((u * Z T ω : ℝ)))
          - Complex.exp (Complex.I * ((u * Y T ω : ℝ)))‖
        ≤ |u| * δ + 2 * Set.indicator {ω | δ ≤ |Z T ω - Y T ω|} (1 : Ω → ℝ) ω := by
      intro ω
      refine (norm_cexp_sub_cexp_le₂ _ _).trans ?_
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
    · exact ((integrable_cexp_mul_I₂ ((hZ T).const_mul u)).sub
        (integrable_cexp_mul_I₂ ((hY T).const_mul u))).norm
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

/-- The sample autocovariance of an observation window is measurable. -/
private lemma measurable_sampleACVF₂ {T : ℕ} {Z : ℤ → Ω → ℝ} (hZ : ∀ t, Measurable (Z t))
    (m : ℕ) :
    Measurable fun ω => sampleACVF (fun t : Fin T => Z (((t : ℕ) : ℤ) + 1) ω) m := by
  classical
  have hmean : Measurable fun ω => sampleMean (fun t : Fin T => Z (((t : ℕ) : ℤ) + 1) ω) := by
    simp only [sampleMean]
    exact (Finset.measurable_sum _ fun t _ => hZ _).const_mul _
  simp only [sampleACVF]
  refine Measurable.const_mul (Finset.measurable_sum _ fun t _ => ?_) _
  rcases eq_or_ne (decide ((t : ℕ) + m < T)) true with hlt | hlt
  · have hlt' : (t : ℕ) + m < T := of_decide_eq_true hlt
    simpa [dif_pos hlt'] using ((hZ _).sub hmean).mul ((hZ _).sub hmean)
  · have hlt' : ¬ ((t : ℕ) + m < T) := by simpa using hlt
    simp [dif_neg hlt']

/-- The sample autocorrelation of an observation window is measurable. -/
private lemma measurable_sampleACF₂ {T : ℕ} {Z : ℤ → Ω → ℝ} (hZ : ∀ t, Measurable (Z t))
    (m : ℕ) :
    Measurable fun ω => sampleACF (fun t : Fin T => Z (((t : ℕ) : ℤ) + 1) ω) m := by
  simp only [sampleACF]
  exact (measurable_sampleACVF₂ hZ m).div (measurable_sampleACVF₂ hZ 0)


/-! ### The two named residues

The residual-correlogram statement splits, by charFun-Slutsky, into an innovation-side
CLT and a residual-vs-innovation transfer. Both are recorded as named residues; the
assembly between them is proved. -/

/-- **RESIDUE (A) — the white-noise sample-ACF CLT under two moments.**

`√T ρ̂_ε(k) →d N(0, 1)` for i.i.d. `ε` with `0 < σ² < ∞` and `k ≥ 1`.

**Why it is not citable from what exists.** `Process/SampleACF.lean` has two statements
of this shape — `sampleACF_bartlett_clt_debt` (FY Thm 2.8(iii)) and `IsMA.sampleACF_clt`
(eq. (2.27), whose `q = 0` case is exactly this) — but **both require a finite fourth
moment** (`MemLp (ε 0) 4 μ`), and the frozen residual-correlogram statement supplies only
`IsIIDNoise ε σ2 μ`, i.e. two moments. The fourth moment is genuinely unnecessary here,
which is why this is a separate residue rather than a citation:

* the numerator `T^{-1/2} Σ_t ε_t ε_{t−k}` is a **martingale-difference** sum for
  `𝓕_t = σ(ε_s : s ≤ t)` (`E[ε_t ε_{t−k} | 𝓕_{t−1}] = ε_{t−k} E ε_t = 0`), and
  `E[(ε_0 ε_k)²] = σ⁴ < ∞` by independence — no fourth moment of `ε` itself;
* the conditional variance is `σ² · T^{-1} Σ_t ε_{t−k}²  →p σ⁴` (LLN for i.i.d. `ε²`);
* Lindeberg is `E[ξ² 1{|ξ| ≥ η√T}] → 0` for the single variable `ξ = ε_0 ε_k`, which is
  dominated convergence off `E ξ² < ∞`;
* the denominator `γ̂(0) →p σ²` and the mean correction cost one Slutsky step each.

So the route is Brown's martingale CLT (`mds_clt_sequence`, `ForMathlib/.../BrownCLT`),
which is **not** in this file's import closure — a scope item, not a mathematical one. -/
private theorem sampleACF_whiteNoise_clt_residue [IsProbabilityMeasure μ] {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2) {k : ℕ} (hk : 1 ≤ k) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * sampleACF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k) u)
      atTop (𝓝 (charFun (gaussianReal 0 1) u)) := by
  sorry

/-- **RESIDUE (B) — the residual-vs-innovation transfer**, bundled with the
measurability of the residual statistic (the two are the same plumbing).

`√T (ρ̂_{ε̂}(k) − ρ̂_ε(k)) →p 0`, where `ε̂_t = Σ_{j≤t} π_j(θ̂_T) x_{t−j}`.

**What the frozen hypothesis really gives.** `hcons` reads
`∀ δ > 0, μ{δ ≤ √T · dist(θ̂_T, θ₀)} → 0`, i.e. `√T(θ̂_T − θ₀) →p 0` — **super**-
consistency, `θ̂_T − θ₀ = o_p(T^{−1/2})`, *not* the `O_p(T^{−1/2})` that the docstring's
phrase "√T-consistent" names. The distinction is exactly what makes the frozen statement
TRUE: under genuine `O_p(T^{−1/2})` the conclusion is **FALSE** — the Box–Pierce (1970)
variance deflation makes the limit variance strictly less than one at small lags (for a
fitted AR(1) the lag-1 residual ACF has asymptotic variance `φ²`, not `1`), and moreover
the limit is not even determined by the rate alone, since it depends on the joint limit
law of `√T(θ̂_T − θ₀)`. Under `o_p(T^{−1/2})` the deflation term vanishes and the
innovation-side limit survives unchanged.

**The route, and the one brick it is missing.** Split
`ε̂_t − ε_t = Σ_{j≤t} (π_j(θ̂) − π_j(θ₀)) x_{t−j} − Σ_{j>t} π_j(θ₀) x_{t−j}`. The second
(truncation) piece is geometric in `t` by `Consistency.exists_uniform_geometric_bound_arma`,
so it contributes `O_p(1/T)` to `γ̂` and dies after `√T`-scaling. The first needs
`‖π(θ̂) − π(θ₀)‖_{ℓ¹} = O_p(dist(θ̂, θ₀)) = o_p(T^{−1/2})`, i.e. a **Lipschitz** bound for
`θ ↦ π(θ)` in `ℓ¹` on a neighbourhood of `θ₀`. The project has only
`Consistency.exists_armaPi_l1_modulus` (a *modulus of continuity*, from compactness),
which converts `o_p(T^{−1/2})` into `o_p(1)` — one full factor of `√T` short. The
Lipschitz brick is true (each `π_n` is a polynomial in `θ`, and Cauchy estimates in `θ`
on a complex polydisc give `|∂π_n/∂θ| ≤ C rⁿ` uniformly on a compact `K ⊆ 𝓑`), but it
does not exist yet; `exists_uniform_geometric_bound_arma` bounds `π` and `ψ`, not their
`θ`-derivatives.

**Scope items** (neither mathematical): `Consistency.continuous_armaPi` and
`maPoly_conv_armaPi` are `private`, so the measurability half must be re-derived here or
they must be un-`private`d; and `Consistency` is not in this file's import closure. -/
private theorem residual_acf_transfer_residue [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    (θ : (T : ℕ) → Ω → (Fin p → ℝ) × (Fin q → ℝ)) (hθmeas : ∀ T, Measurable (θ T))
    (hcons : ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ =>
      (μ {ω | δ ≤ Real.sqrt T * dist (θ T ω) (b0, a0)}).toReal) atTop (𝓝 0))
    {k : ℕ} (hk : 1 ≤ k) :
    (∀ T : ℕ, Measurable fun ω => Real.sqrt T * sampleACF
        (fun t : Fin T => sampleResiduals (θ T ω).1 (θ T ω).2
          (fun s : Fin T => X (((s : ℕ) : ℤ) + 1) ω) t) k) ∧
    (∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ => (μ {ω | δ ≤
        |Real.sqrt T * sampleACF (fun t : Fin T => sampleResiduals (θ T ω).1 (θ T ω).2
            (fun s : Fin T => X (((s : ℕ) : ℤ) + 1) ω) t) k
          - Real.sqrt T * sampleACF (fun t : Fin T => ε (((t : ℕ) : ℤ) + 1) ω) k|}).toReal)
      atTop (𝓝 0)) := by
  sorry

end Assembly

/-- **DEBT (FY §3.5.2; Box–Jenkins folklore made precise by Box–Pierce 1970)**: for a
correctly specified stationary causal invertible ARMA with iid noise and any
`√T`-consistent estimator sequence, the lag-`k` sample ACF of the fitted residuals is
asymptotically `N(0, 1)` after `√T`-scaling — the basis of the `±1.96/√T` residual
correlogram bands. (The exact Box–Pierce variance deflation at small lags is a
strictly finer statement, cited only.)

**STATUS after wave `ts/s12-model-selection` (2026-08-09).** This is no longer a
monolithic debt: the statement is **PROVED over the two named residues**
`sampleACF_whiteNoise_clt_residue` (A) and `residual_acf_transfer_residue` (B) above,
glued by the charFun-Slutsky lemma replayed in the `Assembly` section. Two corrections
to the reading recorded above, both detailed at the residues:

* the formal `hcons` is `√T(θ̂_T − θ₀) →p 0`, i.e. `o_p(T^{−1/2})` **super**-consistency,
  not the `O_p(T^{−1/2})` that "√T-consistent estimator sequence" names. That is what
  makes the conclusion true: under mere `O_p(T^{−1/2})` it is FALSE, and not by the
  "strictly finer" Box–Pierce correction alone — the limit law is then not determined by
  the rate at all, since it depends on the limit law of `√T(θ̂_T − θ₀)`;
* residue (A) cannot cite `sampleACF_bartlett_clt_debt` or `IsMA.sampleACF_clt`: both
  demand a finite fourth moment, which `IsIIDNoise` does not supply and which the
  martingale-difference route does not need. -/
theorem residual_acf_asymptotically_standard_debt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    (θ : (T : ℕ) → Ω → (Fin p → ℝ) × (Fin q → ℝ)) (hθmeas : ∀ T, Measurable (θ T))
    -- USER-INPUT: √T-consistency of the fitted parameters; FY §3.5.2
    (hcons : ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℕ =>
      (μ {ω | δ ≤ Real.sqrt T * dist (θ T ω) (b0, a0)}).toReal) atTop (𝓝 0))
    {k : ℕ} (hk : 1 ≤ k) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * sampleACF
          (fun t : Fin T => sampleResiduals (θ T ω).1 (θ T ω).2
            (fun s : Fin T => X (((s : ℕ) : ℤ) + 1) ω) t) k) u)
      atTop (𝓝 (charFun (gaussianReal 0 1) u)) := by
  obtain ⟨hZmeas, hsub⟩ :=
    residual_acf_transfer_residue h hiid hσ hB0 hcop hcausal hmeas θ hθmeas hcons hk
  exact tendsto_charFun_of_tendstoInProb_sub₂
    (fun T => (measurable_sampleACF₂ hiid.measurable k).const_mul _) hZmeas
    (sampleACF_whiteNoise_clt_residue hiid hσ hk u) hsub

end StatLean.TimeSeries
