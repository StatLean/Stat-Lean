import StatLean.TimeSeries.Models.Defs
import StatLean.TimeSeries.Process.LinearProcess
import StatLean.TimeSeries.Process.SecondOrder
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Stochastic volatility models (FY §4.2.9, eqs. (4.60)–(4.62))

The SV model `X_t = ε_t g(h_t)` with latent AR(1) log-volatility
`h_t = a₀ + a₁ h_{t−1} + e_t` is `Models/Defs.lean`'s `IsSV`. This file carries the
three in-text results, all elementary once the AR(1) facts and the lognormal moment
formula are available:

* **eq. (4.60)**: `|a₁| < 1` ⇒ the latent process is (strictly) stationary with
  `μ_h = a₀/(1 − a₁)` and `γ_h(k) = σ_e²a₁^{|k|}/(1 − a₁²)`, hence `X` is strictly
  stationary;
* **eq. (4.61)** (Taylor's lognormal SV, `g = exp(·/2)` and Gaussian `ε`): the even
  moments `E X_t^{2k} = (2k)!·exp(kμ_h + k²σ_h²/2)/(2^k k!)`, and in particular the
  kurtosis `κ_x = 3e^{σ_h²} > 3` — SV is always leptokurtic;
* **eq. (4.62)**: `log X_t² = h_t + log ε_t²`, an ARMA(1,1) in its first two moments
  (compare Example 2.7), together with the squared-process autocorrelation
  `Corr(X_t², X_{t−k}²) = (exp(σ_h² a₁^{|k|}) − 1)/(exp(σ_h²) − 1)`.

Estimation for SV models (GMM, Kalman filtering on (4.62), MCMC) is citation-only in
FY §4.2.9 and is not formalized.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.2.9,
eqs. (4.60)–(4.62) (pp. 179–181). (`FY §4.2.9`.)

**Bibliographic comments.** The lognormal SV model is S. J. Taylor, *Modelling Financial
Time Series* (Wiley, 1986); the ARMA(1,1) representation of `log X_t²` and the
quasi-likelihood/Kalman route are Harvey, Ruiz & Shephard (1994).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A linear process over mean-zero (white) noise has mean zero: the mean is the limit
of the (vanishing) means of the `L²`-approximating partial sums, the `L¹` defect being
dominated by the `L²` defect on a probability space. -/
private lemma integral_eq_zero_of_isLinearProcessOf [IsProbabilityMeasure μ]
    {ψ : ℕ → ℝ} {σ2 : ℝ} {Y ε : ℤ → Ω → ℝ} (hY : IsLinearProcessOf ψ Y ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsWhiteNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (Y t)) (t : ℤ) : ∫ ω, Y t ω ∂μ = 0 := by
  have hmem : MemLp (Y t) 2 μ := hY.memLp hψ hε hmeas t
  have hint : Integrable (Y t) μ := hmem.integrable one_le_two
  have hεint : ∀ s : ℤ, Integrable (ε s) μ := fun s => (hε.memLp s).integrable one_le_two
  have hSmem : ∀ N : ℕ,
      MemLp (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ := by
    intro N
    have := memLp_finset_sum (μ := μ) (p := 2) (Finset.range N)
      (f := fun (j : ℕ) ω => ψ j * ε (t - (j : ℕ)) ω)
      (fun j _ => (hε.memLp (t - (j : ℕ))).const_mul (ψ j))
    simpa using this
  have hSint : ∀ (N : ℕ),
      Integrable (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) μ :=
    fun N => (hSmem N).integrable one_le_two
  have hS0 : ∀ N : ℕ, ∫ ω, (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) ∂μ = 0 := by
    intro N
    rw [integral_finset_sum _ fun j _ => (hεint _).const_mul _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, hε.integral_eq_zero, mul_zero]
  have hbound : ∀ N : ℕ, |∫ ω, Y t ω ∂μ|
      ≤ (eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ).toReal := by
    intro N
    have hfmem : MemLp (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ :=
      hmem.sub (hSmem N)
    have hfint : Integrable (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) μ :=
      hint.sub (hSint N)
    have hval : ∫ ω, (Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) ∂μ
        = ∫ ω, Y t ω ∂μ := by
      rw [integral_sub hint (hSint N), hS0 N, sub_zero]
    have h1 : |∫ ω, (Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) ∂μ|
        ≤ ∫ ω, |Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω| ∂μ :=
      abs_integral_le_integral_abs
    have h2 : ∫ ω, |Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω| ∂μ
        = (eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      rw [← integral_norm_eq_lintegral_enorm hfint.aestronglyMeasurable]
      simp [Real.norm_eq_abs]
    have h3 : eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 1 μ
        ≤ eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ :=
      eLpNorm_le_eLpNorm_of_exponent_le one_le_two hfmem.aestronglyMeasurable
    rw [hval] at h1
    refine h1.trans ?_
    rw [h2]
    exact ENNReal.toReal_mono hfmem.eLpNorm_ne_top h3
  have htend : Tendsto
      (fun N => (eLpNorm (fun ω => Y t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ).toReal)
      atTop (𝓝 0) := by
    simpa using (ENNReal.continuousAt_toReal (by simp)).tendsto.comp (hY t)
  exact abs_eq_zero.mp (le_antisymm (ge_of_tendsto' htend hbound) (abs_nonneg _))

/-- **FY eq. (4.60)**: with `|a₁| < 1` the latent log-volatility is second-order
stationary with mean `a₀/(1 − a₁)` and autocovariance `σ_e² a₁^{|k|}/(1 − a₁²)`. -/
theorem IsSV.latent_stationary [IsProbabilityMeasure μ] {g : ℝ → ℝ} {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ)
    -- USER-INPUT: causal AR(1) latent process; FY eq. (4.60)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    (hmeas : ∀ t, Measurable (h t)) :
    IsStationary h μ ∧ (∀ t, ∫ ω, h t ω ∂μ = a0 / (1 - a1)) ∧
      ∀ k : ℤ, acvf h μ k = σe2 * a1 ^ k.natAbs / (1 - a1 ^ 2) := by
  have hWN : IsWhiteNoise e σe2 μ := hSV.iidLatent.isWhiteNoise
  have hψ : Summable fun j : ℕ => |a1 ^ j| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg a1) ha1
  have hYm : ∀ t : ℤ, Measurable (fun ω => h t ω - a0 / (1 - a1)) :=
    fun t => (hmeas t).sub_const _
  obtain ⟨hstatY, hacvfY⟩ := hcausal.isStationary hψ hWN hYm
  -- the centred process has vanishing mean, so `E h_t = a₀/(1 − a₁)`
  have hYint : ∀ t : ℤ, Integrable (fun ω => h t ω - a0 / (1 - a1)) μ :=
    fun t => (hstatY.memLp t).integrable one_le_two
  have heq : ∀ t : ℤ,
      ((fun ω => h t ω - a0 / (1 - a1)) + fun _ : Ω => a0 / (1 - a1)) = h t := by
    intro t; funext ω; simp
  have hhint : ∀ t : ℤ, Integrable (h t) μ := by
    intro t
    have h1 := (hYint t).add (integrable_const (a0 / (1 - a1)))
    rwa [heq t] at h1
  have hmean : ∀ t : ℤ, ∫ ω, h t ω ∂μ = a0 / (1 - a1) := by
    intro t
    have h0 := integral_eq_zero_of_isLinearProcessOf hcausal hψ hWN hYm t
    rw [integral_sub (hhint t) (integrable_const _)] at h0
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h0
    linarith
  -- covariances are unchanged by centring
  have hcov : ∀ s t : ℤ, cov[fun ω => h s ω - a0 / (1 - a1),
      fun ω => h t ω - a0 / (1 - a1); μ] = cov[h s, h t; μ] := by
    intro s t
    rw [covariance_sub_const_left (hhint s), covariance_sub_const_right (hhint t)]
  -- the geometric autocovariance
  have hgeo : ∀ n : ℕ, (∑' j : ℕ, a1 ^ j * a1 ^ (j + n)) = a1 ^ n / (1 - a1 ^ 2) := by
    intro n
    have hterm : ∀ j : ℕ, a1 ^ j * a1 ^ (j + n) = a1 ^ n * (a1 ^ 2) ^ j := by
      intro j; ring
    have hsq : a1 ^ 2 < 1 := by nlinarith [abs_nonneg a1, sq_abs a1, abs_lt.mp ha1]
    calc (∑' j : ℕ, a1 ^ j * a1 ^ (j + n)) = ∑' j : ℕ, a1 ^ n * (a1 ^ 2) ^ j :=
          tsum_congr hterm
      _ = a1 ^ n * ∑' j : ℕ, (a1 ^ 2) ^ j := tsum_mul_left
      _ = a1 ^ n / (1 - a1 ^ 2) := by
          rw [tsum_geometric_of_lt_one (sq_nonneg a1) hsq, div_eq_mul_inv]
  refine ⟨⟨fun t => ?_, fun s t => by rw [hmean s, hmean t], fun t k => ?_⟩, hmean, fun k => ?_⟩
  · have h1 := (hstatY.memLp t).add (memLp_const (μ := μ) (p := 2) (a0 / (1 - a1)))
    rwa [heq t] at h1
  · have h1 := hstatY.cov_shift t k
    rw [hcov (t + k) t, hcov k 0] at h1
    exact h1
  · have h1 := hacvfY k
    rw [acvf, hcov k 0] at h1
    rw [acvf, h1, hgeo k.natAbs, mul_div_assoc]

/-- **NAMED DEBT — a missing hypothesis, not a gap in the mathematics.** The observation
noise family `{ε_t}` is independent of the latent family `{h_t}`.

This is *not* derivable from `IsSV` alone. The structure carries `indep_families`
(`σ{ε_t} ⟂ σ{e_t}`) together with the pointwise recursion `h_t = a₀ + a₁h_{t−1} + e_t`,
and the recursion does not tie `h` to `σ{e_t}`: it is satisfied by every solution,
including ones whose "initial condition at `−∞`" is built out of `ε`. Witness: take
`a₀ = 0`, `a₁ = 1`, `h_0 := μ_h + √σ_h² ε_0`, `h_t := h_0 + Σ_{0<s≤t} e_s` for `t > 0`
and `h_t := h_0 − Σ_{t<s≤0} e_s` for `t < 0`. Every field of `IsSV` holds, `h_0` is
`N(μ_h, σ_h²)` and `ε_0` is `N(0,1)`, so all hypotheses of (4.61) hold, yet
`E X_0² = e^{μ_h+σ_h²/2}(1+σ_h²) ≠ e^{μ_h+σ_h²/2}`.

In FY the latent chain *is* the causal solution `h_t − a₀/(1−a₁) = Σ_{j≥0} a₁^j e_{t−j}`
of (4.60) — the hypothesis `hcausal` carried by `IsSV.latent_stationary` and
`IsSV.isStrictlyStationary` — and then `h_t` is `σ{e_s}`-measurable up to a null set, so
`indep_families` yields the conclusion. The frozen statements of (4.61)–(4.62) do not
carry `hcausal`, so the missing input is recorded here as a single brick. -/
private lemma indep_noise_latent [IsProbabilityMeasure μ] {g : ℝ → ℝ} {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ) :
    Indep (⨆ t : ℤ, MeasurableSpace.comap (ε t) inferInstance)
      (⨆ t : ℤ, MeasurableSpace.comap (h t) inferInstance) μ := by
  sorry

private lemma indepFun_noise_latent [IsProbabilityMeasure μ] {g : ℝ → ℝ} {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ) (s t : ℤ) :
    IndepFun (ε s) (h t) μ :=
  indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_noise_latent hSV)
      (le_iSup (fun s : ℤ => MeasurableSpace.comap (ε s) inferInstance) s))
    (le_iSup (fun t : ℤ => MeasurableSpace.comap (h t) inferInstance) t)

/-- **NAMED DEBT — a missing `LEAN-ONLY` hypothesis.** The volatility transform `g` is
measurable.

`IsSV` requires only `g_pos`. Strict stationarity of `X_t = ε_t g(h_t)` is proved by
pushing the shift through the joint law of the pair of windows
`((ε_{t_i+k})_i, (h_{t_i+k})_i)` and then composing with the fixed map
`(a, b) ↦ (a_i g(b_i))_i`; that last step is a `Measure.map` composition and needs the
map to be measurable. `hSV.measurableX` gives measurability of each `X_t`, which pins
`g` down only on `{ε_t ≠ 0}` and only through `h_t` (`g(h_t) = X_t/ε_t` there); recovering
a measurable `g` from that is a descriptive-set-theoretic statement about the fibres of
`(ε_t, h_t)`, not available for an abstract measurable space `Ω`. Every concrete FY
instance (`g = exp(·/2)` in (4.61)–(4.62)) is continuous, so this is a bookkeeping
hypothesis the frozen `IsSV` omits. -/
private lemma measurable_g_brick [IsProbabilityMeasure μ] {g : ℝ → ℝ} {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ) : Measurable g := by
  sorry

private lemma comap_window_le {ι : Type*} (f : ℤ → Ω → ℝ) (u : ι → ℤ) :
    MeasurableSpace.comap (fun ω (i : ι) => f (u i) ω) inferInstance
      ≤ ⨆ s : ℤ, MeasurableSpace.comap (f s) inferInstance := by
  have h1 : (inferInstance : MeasurableSpace (ι → ℝ))
      = ⨆ i : ι, MeasurableSpace.comap (fun v : ι → ℝ => v i) inferInstance := rfl
  rw [h1, MeasurableSpace.comap_iSup]
  refine iSup_le fun i => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup (fun s : ℤ => MeasurableSpace.comap (f s) inferInstance) (u i)

private lemma map_noise_block' [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    {A : Type*} [Finite A] (hε : IsIIDNoise ε σ2 μ) (u : A → ℤ) (k : ℤ) :
    μ.map (fun ω a => ε (u a + k) ω) = μ.map (fun ω a => ε (u a) ω) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  set S : Finset ℤ := Finset.image u Finset.univ with hS
  set ρ : A → {x // x ∈ S} :=
    fun a => ⟨u a, Finset.mem_image_of_mem u (Finset.mem_univ a)⟩ with hρ
  have hlaw : ∀ c : ℤ, μ.map (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω)
      = Measure.pi (fun _ : {x // x ∈ S} => μ.map (ε 0)) := by
    intro c
    have hinj : Function.Injective (fun b : {x // x ∈ S} => (b : ℤ) + c) := by
      intro b1 b2 h
      exact Subtype.ext (by simpa using h)
    have hindep : iIndepFun (fun b : {x // x ∈ S} => ε ((b : ℤ) + c)) μ :=
      hε.iIndep.precomp hinj
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun b => (hε.measurable _).aemeasurable).1 hindep]
    exact congrArg Measure.pi (funext fun b => (hε.identDistrib _ 0).map_eq)
  have hmb : ∀ c : ℤ, Measurable (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω) :=
    fun c => measurable_pi_lambda _ fun b => hε.measurable _
  have hcomp : Measurable (fun v : {x // x ∈ S} → ℝ => v ∘ ρ) :=
    measurable_pi_lambda _ fun a => measurable_pi_apply (ρ a)
  have hfac : ∀ c : ℤ, (fun ω a => ε (u a + c) ω)
      = (fun v : {x // x ∈ S} → ℝ => v ∘ ρ) ∘ (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω) :=
    fun c => rfl
  have hzero : (fun ω a => ε (u a) ω)
      = (fun v : {x // x ∈ S} → ℝ => v ∘ ρ)
        ∘ (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + 0) ω) := by
    funext ω a
    simp only [Function.comp_apply, add_zero, hρ]
  rw [hfac k, hzero, ← Measure.map_map hcomp (hmb k), ← Measure.map_map hcomp (hmb 0),
    hlaw k, hlaw 0]

/-- **FY eq. (4.60), conclusion**: a stationary latent process makes the observed SV
process strictly stationary. -/
theorem IsSV.isStrictlyStationary [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    {a0 a1 σe2 : ℝ} {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ)
    (ha1 : |a1| < 1)
    (hcausal : IsLinearProcessOf (fun j => a1 ^ j) (fun t ω => h t ω - a0 / (1 - a1))
      e μ)
    -- USER-INPUT: strict stationarity of the latent chain (from the AR(1) causal
    -- representation over iid noise); FY eq. (4.60)
    (hstath : IsStrictlyStationary h μ) :
    IsStrictlyStationary X μ := by
  classical
  intro n tt k
  have hg : Measurable g := measurable_g_brick hSV
  have hmε : ∀ s : ℤ, Measurable (ε s) := hSV.iidNoise.measurable
  have hmh : ∀ s : ℤ, Measurable (h s) := hSV.measurableH
  set Φ : ((Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) := fun p i => p.1 i * g (p.2 i) with hΦdef
  have hΦ : Measurable Φ := measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp measurable_fst).mul
      (hg.comp ((measurable_pi_apply i).comp measurable_snd))
  have hEm : ∀ c : ℤ, Measurable (fun ω (i : Fin n) => ε (tt i + c) ω) :=
    fun c => measurable_pi_lambda _ fun i => hmε _
  have hHm : ∀ c : ℤ, Measurable (fun ω (i : Fin n) => h (tt i + c) ω) :=
    fun c => measurable_pi_lambda _ fun i => hmh _
  -- the noise window and the latent window are independent
  have hindep : ∀ c : ℤ, IndepFun (fun ω (i : Fin n) => ε (tt i + c) ω)
      (fun ω (i : Fin n) => h (tt i + c) ω) μ := by
    intro c
    exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (indep_noise_latent hSV)
        (comap_window_le ε fun i : Fin n => tt i + c))
      (comap_window_le h fun i : Fin n => tt i + c)
  have hpair : ∀ c : ℤ,
      μ.map (fun ω => ((fun (i : Fin n) => ε (tt i + c) ω), (fun (i : Fin n) => h (tt i + c) ω)))
        = (μ.map fun ω (i : Fin n) => ε (tt i + c) ω).prod
          (μ.map fun ω (i : Fin n) => h (tt i + c) ω) :=
    fun c => (indepFun_iff_map_prod_eq_prod_map_map (hEm c).aemeasurable
      (hHm c).aemeasurable).1 (hindep c)
  -- every window of `X` is the same measurable function of the pair of windows
  have hX : ∀ c : ℤ, μ.map (fun ω (i : Fin n) => X (tt i + c) ω)
      = (μ.map (fun ω => ((fun (i : Fin n) => ε (tt i + c) ω),
          (fun (i : Fin n) => h (tt i + c) ω)))).map Φ := by
    intro c
    have hall : ∀ᵐ ω ∂μ, ∀ i : Fin n, X (tt i + c) ω = ε (tt i + c) ω * g (h (tt i + c) ω) :=
      ae_all_iff.2 fun i => hSV.recX (tt i + c)
    have hae : (fun ω (i : Fin n) => X (tt i + c) ω)
        =ᵐ[μ] fun ω (i : Fin n) => ε (tt i + c) ω * g (h (tt i + c) ω) := by
      filter_upwards [hall] with ω hω
      funext i
      exact hω i
    rw [Measure.map_congr hae, Measure.map_map hΦ ((hEm c).prodMk (hHm c))]
    rfl
  have hh : (μ.map fun ω (i : Fin n) => h (tt i + k) ω)
      = μ.map fun ω (i : Fin n) => h (tt i + 0) ω := by
    simpa using hstath n tt k
  have hgoal0 : (fun ω (i : Fin n) => X (tt i) ω) = fun ω (i : Fin n) => X (tt i + 0) ω := by
    simp
  rw [hgoal0, hX k, hX 0, hpair k, hpair 0, hh,
    map_noise_block' hSV.iidNoise tt k, map_noise_block' hSV.iidNoise tt 0]


/-! ### Gaussian even moments -/

private noncomputable def gexp : ℝ → ℝ := fun y => Real.exp (y ^ 2 / 2)

private lemma contDiff_gexp : ContDiff ℝ (⊤ : ℕ∞) gexp :=
  Real.contDiff_exp.comp ((contDiff_id.pow 2).div_const 2)

private lemma differentiable_iteratedDeriv_gexp (m : ℕ) :
    Differentiable ℝ (iteratedDeriv m gexp) :=
  contDiff_gexp.differentiable_iteratedDeriv m (by exact_mod_cast lt_top_iff_ne_top.2 (by simp))

private lemma deriv_gexp : deriv gexp = fun y => y * gexp y := by
  funext y
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) y y := by
    simpa using (hasDerivAt_pow 2 y).div_const 2
  have := (Real.hasDerivAt_exp (y ^ 2 / 2)).comp y h1
  simpa [gexp, Function.comp_def, mul_comm] using this.deriv

private lemma iteratedDeriv_id_mul {g : ℝ → ℝ} (hg : ∀ m : ℕ, Differentiable ℝ (iteratedDeriv m g))
    (n : ℕ) : iteratedDeriv n (fun y => y * g y)
      = fun y => y * iteratedDeriv n g y + (n : ℝ) * iteratedDeriv (n - 1) g y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : ∀ y : ℝ, HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g y) y := by
      intro y
      have := (hg n y).hasDerivAt
      rwa [← iteratedDeriv_succ] at this
    have hB : ∀ y : ℝ, HasDerivAt (iteratedDeriv (n - 1) g) (iteratedDeriv (n - 1 + 1) g y) y := by
      intro y
      have := (hg (n - 1) y).hasDerivAt
      rwa [← iteratedDeriv_succ] at this
    rw [iteratedDeriv_succ, ih]
    funext y
    have hd : HasDerivAt (fun y : ℝ => y * iteratedDeriv n g y + (n : ℝ) * iteratedDeriv (n - 1) g y)
        (1 * iteratedDeriv n g y + y * iteratedDeriv (n + 1) g y
          + (n : ℝ) * iteratedDeriv (n - 1 + 1) g y) y :=
      ((hasDerivAt_id y).mul (hA y)).add ((hB y).const_mul (n : ℝ))
    rw [hd.deriv]
    cases n with
    | zero => simp; ring
    | succ m =>
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

private lemma iteratedDeriv_gexp_recur (n : ℕ) :
    iteratedDeriv (n + 1) gexp 0 = (n : ℝ) * iteratedDeriv (n - 1) gexp 0 := by
  rw [iteratedDeriv_succ', deriv_gexp,
    iteratedDeriv_id_mul differentiable_iteratedDeriv_gexp n]
  simp

private lemma iteratedDeriv_gexp_even (k : ℕ) :
    iteratedDeriv (2 * k) gexp 0
      = (Nat.factorial (2 * k) : ℝ) / (2 ^ k * Nat.factorial k) := by
  induction k with
  | zero => simp [gexp]
  | succ k ih =>
    have hstep : iteratedDeriv (2 * (k + 1)) gexp 0
        = (2 * k + 1 : ℝ) * iteratedDeriv (2 * k) gexp 0 := by
      have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [h1, iteratedDeriv_gexp_recur (2 * k + 1)]
      simp
    rw [hstep, ih]
    have h2 : Nat.factorial (2 * (k + 1)) = (2 * k + 2) * ((2 * k + 1) * Nat.factorial (2 * k)) := by
      have : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [this, Nat.factorial_succ, Nat.factorial_succ]
    rw [h2, Nat.factorial_succ]
    have hk : (0:ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    push_cast
    field_simp
    ring

private lemma integral_pow_even_gaussianReal (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂(gaussianReal 0 1)
      = (Nat.factorial (2 * k) : ℝ) / (2 ^ k * Nat.factorial k) := by
  have hmgf : mgf id (gaussianReal 0 1) = gexp := by
    rw [mgf_id_gaussianReal]
    funext t
    norm_num [gexp]
  have hint : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by simp
  have hkey := iteratedDeriv_mgf_zero (X := (id : ℝ → ℝ)) (μ := gaussianReal 0 1) hint (2 * k)
  rw [hmgf, iteratedDeriv_gexp_even k] at hkey
  have hpi : ((gaussianReal 0 1)[(id : ℝ → ℝ) ^ (2 * k)])
      = ∫ x, x ^ (2 * k) ∂(gaussianReal 0 1) := by simp
  rw [hpi] at hkey
  exact hkey.symm

/-- **NAMED DEBT — a missing hypothesis.** The noise does not charge `0`.

`IsIIDNoise ε 1` constrains only the first two moments, and a mean-zero unit-variance law
may well have an atom at `0` (e.g. `P(ε = ±√2) = 1/4`, `P(ε = 0) = 1/2`). On `{ε_t = 0}`
one has `log X_t² = log 0 = 0` while `h_t + log ε_t² = h_t + 0 = h_t`, so (4.62) fails
there unless `h_t = 0`: with such noise the frozen statement of `log_sq_decomposition` is
false (take `a₁ = 0`, `h_t = e_t` standard normal). It holds in FY's setting because the
observation noise is Gaussian (`hgauss` plus `noAtoms_gaussianReal`), a hypothesis this
statement does not carry. -/
private lemma noise_ne_zero_ae [IsProbabilityMeasure μ] {g : ℝ → ℝ} {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ} (hSV : IsSV g a0 a1 σe2 X h ε e μ) (t : ℤ) :
    μ {ω | ε t ω = 0} = 0 := by
  sorry

/-- **FY eq. (4.61)** (Taylor's lognormal SV): with `g(x) = e^{x/2}`, standard normal
`ε`, and a stationary Gaussian latent process with mean `μ_h` and variance `σ_h²`,
`E X_t^{2k} = (2k)! · exp(k μ_h + k²σ_h²/2) / (2^k k!)`. -/
theorem IsSV.moment_even_lognormal [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    -- USER-INPUT: standard normal observation noise; FY eq. (4.61)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    -- USER-INPUT: stationary Gaussian latent law; FY eq. (4.61)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2)
    (k : ℕ) :
    (∫ ω, X 0 ω ^ (2 * k) ∂μ)
      = (Nat.factorial (2 * k) : ℝ) * Real.exp (k * μh + (k : ℝ) ^ 2 * σh2 / 2)
        / (2 ^ k * Nat.factorial k) := by
  have hmε : Measurable (ε 0) := hSV.iidNoise.measurable 0
  have hmh : Measurable (h 0) := hSV.measurableH 0
  -- (a) the standard-normal even moment `(2k)!/(2^k k!)`
  have hA : ∫ ω, ε 0 ω ^ (2 * k) ∂μ
      = (Nat.factorial (2 * k) : ℝ) / (2 ^ k * Nat.factorial k) := by
    rw [← integral_pow_even_gaussianReal k, ← hgauss,
      integral_map hmε.aemeasurable
        (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ (2 * k)) _)]
  -- (b) the lognormal moment: the Gaussian m.g.f. at `t = k`
  have hB : ∫ ω, Real.exp ((k : ℝ) * h 0 ω) ∂μ
      = Real.exp ((k : ℝ) * μh + (k : ℝ) ^ 2 * σh2 / 2) := by
    have hm := mgf_gaussianReal hlatent (k : ℝ)
    rw [Real.coe_toNNReal σh2 hσh.le] at hm
    rw [show (∫ ω, Real.exp ((k : ℝ) * h 0 ω) ∂μ) = mgf (h 0) μ (k : ℝ) from rfl, hm]
    ring_nf
  -- (c) split the product along `ε ⟂ h`
  have hindep : IndepFun (fun ω => ε 0 ω ^ (2 * k)) (fun ω => Real.exp ((k : ℝ) * h 0 ω)) μ :=
    (indepFun_noise_latent hSV 0 0).comp (measurable_id.pow_const (2 * k))
      ((measurable_id.const_mul (k : ℝ)).exp)
  have hprod : ∫ ω, (ε 0 ω ^ (2 * k) * Real.exp ((k : ℝ) * h 0 ω)) ∂μ
      = (∫ ω, ε 0 ω ^ (2 * k) ∂μ) * ∫ ω, Real.exp ((k : ℝ) * h 0 ω) ∂μ :=
    hindep.integral_fun_mul_eq_mul_integral
      (hmε.pow_const (2 * k)).aestronglyMeasurable
      ((hmh.const_mul (k : ℝ)).exp).aestronglyMeasurable
  -- (d) the model equation, squared `k` times
  have hae : (fun ω => X 0 ω ^ (2 * k))
      =ᵐ[μ] fun ω => ε 0 ω ^ (2 * k) * Real.exp ((k : ℝ) * h 0 ω) := by
    filter_upwards [hSV.recX 0] with ω hω
    rw [hω, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [integral_congr_ae hae, hprod, hA, hB]
  ring


/-- **FY eq. (4.61), kurtosis**: the lognormal SV kurtosis is `3e^{σ_h²} > 3` — SV is
strictly leptokurtic (stated multiplicatively to avoid division). -/
theorem IsSV.kurtosis_lognormal [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2) :
    (∫ ω, X 0 ω ^ 4 ∂μ) = 3 * Real.exp σh2 * (∫ ω, X 0 ω ^ 2 ∂μ) ^ 2 ∧
      3 < 3 * Real.exp σh2 := by
  have h4 := hSV.moment_even_lognormal hgauss hlatent hσh 2
  have h2 := hSV.moment_even_lognormal hgauss hlatent hσh 1
  norm_num at h4 h2
  refine ⟨?_, ?_⟩
  · rw [h4, h2, sq]
    have he : Real.exp σh2 * (Real.exp (μh + σh2 / 2) * Real.exp (μh + σh2 / 2))
        = Real.exp (2 * μh + 4 * σh2 / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
    linarith
  · nlinarith [Real.add_one_lt_exp (ne_of_gt hσh)]


/-- **FY eq. (4.62)**: the log-squared observation decomposes as `log X_t² = h_t +
log ε_t²` (for `g = exp(·/2)`), the identity behind the ARMA(1,1)-in-two-moments
representation and the Kalman-filter estimation route. -/
theorem IsSV.log_sq_decomposition [IsProbabilityMeasure μ] {a0 a1 σe2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ) (t : ℤ) :
    (fun ω => Real.log (X t ω ^ 2)) =ᵐ[μ] fun ω => h t ω + Real.log (ε t ω ^ 2) := by
  have hne : ∀ᵐ ω ∂μ, ε t ω ≠ 0 := by
    rw [ae_iff]
    simpa using noise_ne_zero_ae hSV t
  filter_upwards [hSV.recX t, hne] with ω hω hε0
  rw [hω, mul_pow, Real.log_mul (pow_ne_zero 2 hε0)
      (ne_of_gt (pow_pos (Real.exp_pos _) 2)), ← Real.exp_nat_mul, Real.log_exp]
  push_cast
  ring


/-- **FY eq. (4.62), squared-process ACF** (lognormal algebra):
`Corr(X_t², X_{t−k}²) = (exp(σ_h² a₁^{|k|}) − 1)/(exp(σ_h²) − 1)`. -/
theorem IsSV.acf_sq_lognormal [IsProbabilityMeasure μ] {a0 a1 σe2 μh σh2 : ℝ}
    {X h ε e : ℤ → Ω → ℝ}
    (hSV : IsSV (fun x => Real.exp (x / 2)) a0 a1 σe2 X h ε e μ)
    (hgauss : μ.map (ε 0) = gaussianReal 0 1)
    (hlatent : μ.map (h 0) = gaussianReal μh (Real.toNNReal σh2)) (hσh : 0 < σh2)
    (ha1 : |a1| < 1)
    -- USER-INPUT: the stationary latent autocovariance structure; FY eq. (4.60)
    (hacvf : ∀ k : ℤ, acvf h μ k = σh2 * a1 ^ k.natAbs)
    (hstat : IsStrictlyStationary X μ) (hL4 : ∀ t, MemLp (X t) 4 μ) (k : ℤ) :
    acf (fun t ω => X t ω ^ 2) μ k
      = (Real.exp (σh2 * a1 ^ k.natAbs) - 1) / (Real.exp σh2 - 1) := by
  sorry

end StatLean.TimeSeries
