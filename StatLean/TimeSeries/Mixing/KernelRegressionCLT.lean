import StatLean.TimeSeries.Mixing.Inequalities
import StatLean.TimeSeries.Mixing.Relations
import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# CLT for kernel-localized sums under α-mixing (FY §2.6.4, Theorem 2.22)

The triangular-array CLT behind kernel regression with dependent data: for a strictly
stationary bivariate series `(X_t, e_t)` with `E(e|X) = 0`, the localized sums
`S_n(x) = Σ_{t=1}^n e_t W((X_t − x)/h_n)` satisfy
`(n h_n)^{-1/2} S_n(x) →d N(0, σ²(x) p(x) ∫ W²)` under (C1)–(C5). This is FY's
template for Theorem 6.3 (local-polynomial fitting) and the ch. 10 results.

**Conditions, as formalized.**
* (C1) joint strict stationarity (finite-dimensional-distribution form);
  `E(e_1 | X_1) = 0`, `E(e_1² | X_1) = σ²(X_1)`, `E|e_1|^δ < ∞` (δ > 2); the marginal
  `X_1` has a Lebesgue density `p`; `σ²`, `p` continuous at `x`, `p(x) > 0`.
* (C2) stated in its **operative integrated form**: uniformly in the lag `j ≠ 0`,
  `E[|e_0 e_j| g(X_0, X_j)] ≤ B · E[e_0²] · ∫∫ g` for nonnegative test functions `g` —
  this is exactly what FY's "conditional density of `(X_1, X_{j})` given `(e_1, e_j)`
  bounded uniformly in `j`" is used for (small-lag variance bound (2.76)), combined
  with Cauchy–Schwarz on `E|e_1 e_j|`.
* (C3) α-mixing of the bivariate series (`pairAlphaCoeff`) with
  `Σ_t t^λ α(t)^{1−2/δ} < ∞` for some `λ > 1 − 2/δ`.
* (C4) `W` bounded and measurable with `∫|W| < ∞`, `∫ W² < ∞`.
* (C5) **as corrected**: the printed display is inverted; we take the endorsed
  sufficient form `h_n → 0`, `h_n > 0`, `n h_n³ → ∞` (which implies the intended
  polynomial lower bound `n h_n^{(λ+2−2/δ)/(λ+2/δ)} → ∞`).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.4,
conditions (C1)–(C5) and Theorem 2.22 (pp. 76–77); proof §2.7.7 (pp. 85–87).
(`FY §2.6.4 Thm 2.22`.)

**Proof route (§2.7.7, for the closure session).** (a) variance asymptotics
(2.73)–(2.76): main diagonal term by continuity of `σ²·p` + substitution; small lags
`j ≤ m_n = [1/(h|log h|)]` by (C2'); large lags by Davydov (`abs_covariance_le_davydov`
with `p = q = δ`) + (C3). (b) Bernstein blocks `l_n = [√(nh)/log n]`,
`s_n = [(√(n/h) log n)^{(1−2/δ)/(λ+1)}]`; negligibility (2.79)–(2.81) via the variance
part. (c) truncation of `e` at level `L`; variance split (2.82)–(2.83).
(d) 4-term charFun telescope: truncation tail + Volkonskii–Rozanov
(`norm_integral_prod_sub_prod_integral_le`; `16(k_n − 1)α(s_n) → 0` by (2.78)) +
degenerate Lindeberg (`tendsto_charFun_rowSum_gaussian_of_uniformly_small`; the
truncated block summands have envelope `l_n L sup|W| / √(nh) → 0`) + `ν_L → ν`.
Sub-steps may be left as **named ledger-(a) debts** if the wave budget is hit.
[Print slips (recorded in the inventory): Term-1 of the telescope is missing a `½`
exponent; the final "(2.83)" should read "(2.84)".]

**Bibliographic comments.** Theorem 2.22 descends from Masry & Fan, *Local polynomial
estimation of regression functions for mixing processes* (Scand. J. Statist. 1997) and
Fan & Gijbels (1996) §6.5; the Bernstein-block scheme under (C3) follows Bosq (1998).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **bivariate past/future α-coefficient** (FY §2.6.4's mixing condition is on the
pair series `(X_t, e_t)`): α between `σ{(X_s, e_s) : s ≤ 0}` and
`σ{(X_s, e_s) : s ≥ n}`. -/
noncomputable def pairAlphaCoeff (X e : ℤ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  alphaMixCoeff μ
    (⨆ s ∈ Set.Iic (0 : ℤ),
      MeasurableSpace.comap (X s) inferInstance ⊔
        MeasurableSpace.comap (e s) inferInstance)
    (⨆ s ∈ Set.Ici (n : ℤ),
      MeasurableSpace.comap (X s) inferInstance ⊔
        MeasurableSpace.comap (e s) inferInstance)

/-! ### Elementary properties of `pairAlphaCoeff`

Transported from the `alphaMixCoeff` lemmas of `Mixing/Relations.lean`; the pair
σ-algebras are `⨆`-sups, so `iSup_le`/`le_iSup` do the monotonicity transport. -/

section PairAlpha

variable {X e : ℤ → Ω → ℝ}

/-- `pairAlphaCoeff` is nonnegative (FY §2.6.4). -/
theorem pairAlphaCoeff_nonneg [IsProbabilityMeasure μ] (X e : ℤ → Ω → ℝ) (n : ℕ) :
    0 ≤ pairAlphaCoeff X e μ n :=
  alphaMixCoeff_nonneg (mΩ := inferInstance)

/-- `pairAlphaCoeff ≤ 1` (FY §2.6.4). -/
theorem pairAlphaCoeff_le_one [IsProbabilityMeasure μ] (X e : ℤ → Ω → ℝ) (n : ℕ) :
    pairAlphaCoeff X e μ n ≤ 1 :=
  alphaMixCoeff_le_one (mΩ := inferInstance)

/-- `pairAlphaCoeff` is antitone in the lag: the future σ-algebra shrinks as the gap
grows, so the sup defining `α` is taken over a smaller set. -/
theorem pairAlphaCoeff_antitone [IsProbabilityMeasure μ] (X e : ℤ → Ω → ℝ) :
    Antitone (pairAlphaCoeff X e μ) := by
  intro m n hmn
  refine alphaMixCoeff_mono (mΩ := inferInstance) le_rfl ?_
  refine iSup₂_le fun s hs => le_iSup₂_of_le s ?_ le_rfl
  simp only [Set.mem_Ici] at hs ⊢
  exact le_trans (by exact_mod_cast hmn) hs

end PairAlpha

/-! ### Analytic bricks for the variance asymptotics (a)

Four reusable identities/limits behind FY (2.73): the affine change of variables
`v = x + h u`, the substitution of the `X`-marginal density `p`, the conditional
(tower) elimination of the errors against a bounded `X`-measurable weight, and the
dominated-convergence localization. All four are **proved**. -/

section Bricks

/-- **Affine change of variables** `v = x + h u` on Lebesgue measure:
`∫ F(u) g(x + h u) du = h⁻¹ ∫ F((v − x)/h) g(v) dv` for `h > 0`.
(Both sides use Mathlib's junk value `0` for non-integrable integrands, and the
identity holds regardless — `Measure.integral_comp_mul_left` is unconditional.) -/
theorem integral_dilate_translate (F g : ℝ → ℝ) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ u, F u * g (x + h * u) = h⁻¹ * ∫ v, F ((v - x) / h) * g v := by
  set G : ℝ → ℝ := fun v => F ((v - x) / h) * g v with hG
  have h1 : ∫ u, G (x + h * u) = |h⁻¹| • ∫ w, G (x + w) :=
    MeasureTheory.Measure.integral_comp_mul_left (fun w => G (x + w)) h
  have h2 : ∫ w, G (x + w) = ∫ v, G v := integral_add_left_eq_self G x
  have h3 : ∀ u : ℝ, G (x + h * u) = F u * g (x + h * u) := by
    intro u
    simp [hG, add_sub_cancel_left, mul_div_cancel_left₀ _ hh.ne']
  calc ∫ u, F u * g (x + h * u) = ∫ u, G (x + h * u) := by simp_rw [h3]
    _ = |h⁻¹| • ∫ w, G (x + w) := h1
    _ = h⁻¹ * ∫ v, G v := by rw [h2, abs_of_pos (by positivity), smul_eq_mul]

/-- **Density substitution for the `X`-marginal** (FY (C1)): if `X` has Lebesgue
density `p`, then `E[F(X)] = ∫ p(v) F(v) dv`. -/
theorem integral_comp_eq_integral_density {Y : Ω → ℝ} (hY : Measurable Y)
    {p : ℝ → ℝ} (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map Y = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (F : ℝ → ℝ) (hF : Measurable F) :
    ∫ ω, F (Y ω) ∂μ = ∫ v, p v * F v := by
  rw [← integral_map hY.aemeasurable hF.aestronglyMeasurable, hpd,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun v => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hp0 v)]

/-- **Tower elimination against a bounded `σ(Y)`-measurable weight**: if
`μ[ζ | σ(Y)] =ᵐ Z` and `G` is bounded measurable, then `E[G(Y) ζ] = E[G(Y) Z]`.
Used twice: with `ζ = e₀` (giving mean zero of each localized summand, FY (C1)
`E(e|X) = 0`) and with `ζ = e₀²` (giving the `σ²(X)` form of the diagonal term). -/
theorem integral_bdd_comp_mul_eq_of_condExp [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : Measurable Y) {Z ζ : Ω → ℝ} (hζ : Integrable ζ μ)
    (hce : μ[ζ | MeasurableSpace.comap Y inferInstance] =ᵐ[μ] Z)
    (G : ℝ → ℝ) (hG : Measurable G) {C : ℝ} (hGb : ∀ v, |G v| ≤ C) :
    ∫ ω, G (Y ω) * ζ ω ∂μ = ∫ ω, G (Y ω) * Z ω ∂μ := by
  have hmle : MeasurableSpace.comap Y inferInstance ≤ ‹MeasurableSpace Ω› := hY.comap_le
  have hYm : Measurable[MeasurableSpace.comap Y inferInstance] Y :=
    Measurable.of_comap_le le_rfl
  have hf : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] (fun ω => G (Y ω)) :=
    (hG.comp hYm).stronglyMeasurable
  have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ)
    (m := MeasurableSpace.comap Y inferInstance) hmle hf hζ C
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hGb (Y ω))
  have h1 : ∫ ω, G (Y ω) * ζ ω ∂μ
      = ∫ ω, (μ[(fun ω => G (Y ω)) * ζ | MeasurableSpace.comap Y inferInstance]) ω ∂μ :=
    (integral_condExp hmle).symm
  rw [h1]
  refine integral_congr_ae ?_
  filter_upwards [hpull, hce] with ω h1 h2
  simp only [Pi.mul_apply] at h1 ⊢
  rw [h1, h2]

/-- **Dominated-convergence localization**: for `g` measurable, globally bounded and
continuous at `x`, and a nonnegative integrable weight `Φ`,
`∫ g(x + h_n u) Φ(u) du → g(x) ∫ Φ` whenever `h_n → 0`.
This is the analytic core of FY (2.73). -/
theorem tendsto_integral_dilate_of_bounded {g : ℝ → ℝ} (hg : Measurable g) {x : ℝ}
    (hgc : ContinuousAt g x) {M : ℝ} (hgM : ∀ v, |g v| ≤ M)
    {Φ : ℝ → ℝ} (hΦm : Measurable Φ) (hΦ0 : ∀ u, 0 ≤ Φ u)
    (hΦ : Integrable Φ MeasureTheory.volume)
    {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ u, g (x + h n * u) * Φ u) atTop (𝓝 (g x * ∫ u, Φ u)) := by
  have hlim : ∫ u, g x * Φ u = g x * ∫ u, Φ u := integral_const_mul _ _
  rw [← hlim]
  refine tendsto_integral_of_dominated_convergence (fun u => M * Φ u)
    (fun n => ((hg.comp (by fun_prop)).mul hΦm).aestronglyMeasurable)
    (hΦ.const_mul M) (fun n => Eventually.of_forall fun u => ?_)
    (Eventually.of_forall fun u => ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΦ0 u)]
    exact mul_le_mul_of_nonneg_right (hgM _) (hΦ0 u)
  · exact ((hgc.tendsto.comp (by simpa using (hh.mul_const u).const_add x)).mul
      tendsto_const_nhds)

/-- **FY (2.73), diagonal term — the TRUE form.** Under a *global bound* on `σ² · p`
(which FY's (C1) implicitly carries, and which the formalized (C1)–(C5) do **not**
supply — see `tendsto_localized_second_moment_debt`),
`h⁻¹ E[e₀² W²((X₀ − x)/h)] → σ²(x) p(x) ∫ W²`. -/
theorem tendsto_localized_second_moment_of_bounded [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hX : Measurable (X 0))
    {σsq p : ℝ → ℝ} (hmσ : Measurable σsq) (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {x : ℝ}
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (he2 : Integrable (fun ω => e 0 ω ^ 2) μ)
    (hgc : ContinuousAt (fun v => σsq v * p v) x)
    {M : ℝ} (hgM : ∀ v, |σsq v * p v| ≤ M)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
        (h n)⁻¹ * ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ) atTop
      (𝓝 (σsq x * p x * ∫ v, W v ^ 2)) := by
  -- The `n`-th term equals `∫ (σ²·p)(x + h u) W²(u) du`.
  have hkey : ∀ n : ℕ, (h n)⁻¹ * ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ
      = ∫ u, (fun v => σsq v * p v) (x + h n * u) * W u ^ 2 := by
    intro n
    -- (i) tower: replace `e₀²` by `σ²(X₀)`.
    have hstep1 : ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ
        = ∫ ω, (fun v => W ((v - x) / h n) ^ 2) (X 0 ω) * σsq (X 0 ω) ∂μ := by
      rw [← integral_bdd_comp_mul_eq_of_condExp hX he2 hcv
        (fun v => W ((v - x) / h n) ^ 2) (by fun_prop) (C := CW ^ 2)
        (fun v => by
          have hb := hWb ((v - x) / h n)
          rw [abs_pow]
          nlinarith [abs_nonneg (W ((v - x) / h n))])]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    -- (ii) density substitution.
    have hstep2 : ∫ ω, (fun v => W ((v - x) / h n) ^ 2) (X 0 ω) * σsq (X 0 ω) ∂μ
        = ∫ v, W ((v - x) / h n) ^ 2 * (σsq v * p v) := by
      rw [integral_comp_eq_integral_density hX hmp hp0 hpd
        (fun v => W ((v - x) / h n) ^ 2 * σsq v) (by fun_prop)]
      exact integral_congr_ae (Eventually.of_forall fun v => by ring)
    -- (iii) affine change of variables.
    have hstep3 := integral_dilate_translate (fun u => W u ^ 2)
      (fun v => σsq v * p v) x (hh0 n)
    rw [hstep1, hstep2, ← hstep3]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  simp only [hkey]
  have := tendsto_integral_dilate_of_bounded (g := fun v => σsq v * p v) (by fun_prop) hgc hgM
    (Φ := fun u => W u ^ 2) (by fun_prop) (fun u => sq_nonneg _) hW2 hh
  simpa [mul_assoc] using this

end Bricks

/-! ### The §2.7.7 ledger

The proof apparatus of FY §2.7.7, as named private declarations. `locSum` is the
statistic of Theorem 2.22 itself; `locTruncSum` is its truncated-and-recentred
companion of step (c); `bigBlockLen`/`smallBlockLen`/`blockCount`/`smallLagCut` are
FY's `l_n`, `s_n`, `k_n`, `m_n`.

**What is proved here**: the small-lag covariance bound (2.76) — the one ledger-(a)
item that the formalized (C2) delivers outright — and the abstract diagonal-limit
device that the four-term telescope of step (d) is squeezed through. The remaining
items are named debts, one per FY display. -/

section Ledger

/-- FY's localized statistic `(n h_n)^{-1/2} Σ_{t=1}^n e_t W((X_t − x)/h_n)`. -/
private noncomputable def locSum (X e : ℤ → Ω → ℝ) (W : ℝ → ℝ) (x : ℝ) (h : ℕ → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (Real.sqrt ((n : ℝ) * h n))⁻¹ *
    ∑ t ∈ Finset.range n, e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)

/-- Two-sided clamp at level `L`. -/
private noncomputable def clampAt (L z : ℝ) : ℝ := max (-L) (min L z)

/-- FY's truncated, conditionally recentred error `e^L_t = e_t^{(L)} − E(e_t^{(L)}|X_t)`
(step (c), (2.82)); the recentring keeps `E(e^L | X) = 0`, hence keeps every summand
of `locTruncSum` centred. -/
private noncomputable def truncErr (X e : ℤ → Ω → ℝ) (μ : Measure Ω) (L : ℝ) (t : ℤ)
    (ω : Ω) : ℝ :=
  clampAt L (e t ω) -
    (μ[fun ω' => clampAt L (e t ω') | MeasurableSpace.comap (X t) inferInstance]) ω

/-- The truncated statistic of step (c). -/
private noncomputable def locTruncSum (X e : ℤ → Ω → ℝ) (μ : Measure Ω) (W : ℝ → ℝ)
    (x : ℝ) (h : ℕ → ℝ) (L : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Real.sqrt ((n : ℝ) * h n))⁻¹ *
    ∑ t ∈ Finset.range n,
      truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)

/-- FY's big-block length `l_n = [√(n h_n) / log n]` (step (b), (2.77)). -/
private noncomputable def bigBlockLen (h : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌈Real.sqrt ((n : ℝ) * h n) / Real.log n⌉₊

/-- FY's small-block length `s_n = [(√(n/h_n) log n)^{(1−2/δ)/(λ+1)}]` (step (b)). -/
private noncomputable def smallBlockLen (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) : ℕ :=
  ⌈(Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1))⌉₊

/-- FY's number of block pairs `k_n = [n / (l_n + s_n)]` (step (b)). -/
private noncomputable def blockCount (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) : ℕ :=
  n / (bigBlockLen h n + smallBlockLen h δ lam n)

/-- FY's small/large lag cut `m_n = [1 / (h_n |log h_n|)]` (step (a), before (2.75)). -/
private noncomputable def smallLagCut (h : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌈(h n * |Real.log (h n)|)⁻¹⌉₊

/-! #### Ledger (a): variance asymptotics (2.73)–(2.76) -/

/-- **FY (2.76), small-lag covariance bound — PROVED.** For every nonzero lag,
`|E[ξ_0 ξ_j]| ≤ B · E[e_0²] · (∫|W|)² · h²`, where `ξ_t = e_t W((X_t − x)/h)`. This is
exactly the operative content of (C2): bound `|ξ_0 ξ_j|` by `|e_0 e_j| g(X_0, X_j)`
with `g(v,w) = |W((v−x)/h)| |W((w−x)/h)|`, apply (C2), and evaluate
`∫∫ g = (h ∫|W|)²` by the affine change of variables. -/
private theorem small_lag_covariance_bound {X e : ℤ → Ω → ℝ} {W : ℝ → ℝ} {x : ℝ}
    (hWm : Measurable W) {B : ℝ}
    (hC2 : ∀ j : ℤ, j ≠ 0 → ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |e 0 ω * e j ω| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {hn : ℝ} (hhn : 0 < hn) (j : ℤ) (hj : j ≠ 0) :
    |∫ ω, (e 0 ω * W ((X 0 ω - x) / hn)) * (e j ω * W ((X j ω - x) / hn)) ∂μ|
      ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) * ((∫ v, |W v|) * hn) ^ 2 := by
  -- Step 1: pass to absolute values and factor the integrand as `|e₀ e_j| · g(X₀, X_j)`.
  have h0 := norm_integral_le_integral_norm (μ := μ)
    fun ω => (e 0 ω * W ((X 0 ω - x) / hn)) * (e j ω * W ((X j ω - x) / hn))
  simp only [Real.norm_eq_abs] at h0
  have hcongr : ∫ ω, |(e 0 ω * W ((X 0 ω - x) / hn)) * (e j ω * W ((X j ω - x) / hn))| ∂μ
      = ∫ ω, |e 0 ω * e j ω| *
          (fun z : ℝ × ℝ => |W ((z.1 - x) / hn)| * |W ((z.2 - x) / hn)|) (X 0 ω, X j ω) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by simp only [abs_mul]; ring)
  have h1 : |∫ ω, (e 0 ω * W ((X 0 ω - x) / hn)) * (e j ω * W ((X j ω - x) / hn)) ∂μ|
      ≤ ∫ ω, |e 0 ω * e j ω| *
          (fun z : ℝ × ℝ => |W ((z.1 - x) / hn)| * |W ((z.2 - x) / hn)|) (X 0 ω, X j ω) ∂μ :=
    hcongr ▸ h0
  -- Step 2: (C2) with that test function.
  refine h1.trans ((hC2 j hj
    (fun z : ℝ × ℝ => |W ((z.1 - x) / hn)| * |W ((z.2 - x) / hn)|)
    (by fun_prop) (fun z => by positivity)).trans (le_of_eq ?_))
  -- Step 3: the product integral factorizes, and each factor is `hn ∫|W|`.
  have hprod : ∫ z : ℝ × ℝ, |W ((z.1 - x) / hn)| * |W ((z.2 - x) / hn)|
        ∂(MeasureTheory.volume.prod MeasureTheory.volume)
      = (∫ v, |W ((v - x) / hn)|) * ∫ w, |W ((w - x) / hn)| :=
    integral_prod_mul (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
      (f := fun v => |W ((v - x) / hn)|) (g := fun w => |W ((w - x) / hn)|)
  have hone : ∫ v, |W ((v - x) / hn)| = hn * ∫ v, |W v| := by
    have := integral_dilate_translate (fun u => |W u|) (fun _ => (1 : ℝ)) x hhn
    simp only [mul_one] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ hhn.ne', one_mul]
  rw [hprod, hone]
  ring

/-- **FY (2.73), diagonal term — DEBT, and FALSE as frozen.**
`h⁻¹ E[e_0² W²((X_0 − x)/h)] = ∫ (σ²·p)(x + h u) W²(u) du` (an *identity*, proved
inside `tendsto_localized_second_moment_of_bounded`), and FY asserts the limit
`σ²(x) p(x) ∫ W²`.

**Status.** The limit needs more than the formalized (C1)–(C5) supply. Continuity of
`σ²·p` at `x` controls the window `|u| ≤ M` (there `|h u| ≤ M h → 0`), but the tail
`|u| > M` is left uncontrolled: `(C2)` forces only `σ·p` to be bounded (take
`g = g₁ ⊗ g₂` in (C2) and let `g` concentrate), **not** `σ²·p`, and `σ²·p ∈ L¹` alone
(`= E e_0² < ∞`) is not enough against a merely-`L¹` weight `W²`. Concretely: with
`σ p ≡ B` on a sequence of spikes escaping to `v ≈ x + 1`, `σ²p = (σp)²/p` is
unbounded, and choosing `W² = 1` on intervals `J_k ≈ 2^k` of length `2^{-k}`
(so `W` is bounded, `∫|W| < ∞`, `∫W² < ∞`) makes
`∫ (σ²p)(x + h_k u) W²(u) du ≥ σ²(x)p(x)∫W² + 1` along `h_k = 2^{-k}` while `σ²`, `p`
stay continuous at `x`. Sparsifying the spike sequence keeps `h_n → 0` compatible with
`n h_n³ → ∞`, so (C5) does not rescue it.

**Repair.** Either strengthen (C4) to compactly supported `W` (then continuity at `x`
suffices and this lemma is `tendsto_localized_second_moment_of_bounded`'s window
argument), or strengthen (C1) to `σ²·p` bounded — which is what the textbook's
"(C1) with `σ²` and `p` bounded" silently supplies. `tendsto_localized_second_moment_of_bounded`
is the repaired statement, and it is **proved**.

Note also that the frozen (C1) carries no measurability hypothesis on `σsq`; only
`hcv` constrains it, and only `μ.map (X 0)`-a.e. -/
private theorem tendsto_localized_second_moment_debt [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hX : Measurable (X 0)) {σsq p : ℝ → ℝ}
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {x : ℝ}
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (he2 : Integrable (fun ω => e 0 ω ^ 2) μ)
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
        (h n)⁻¹ * ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ) atTop
      (𝓝 (σsq x * p x * ∫ v, W v ^ 2)) := by
  sorry

/-- **FY (2.75), large-lag covariance bound — DEBT.** For lags beyond the cut `m_n`,
Davydov (`abs_covariance_le_davydov` with `p = q = δ`) against the pair α-coefficient:
`|Cov(ξ_0, ξ_j)| ≤ 8 α_pair(j)^{1−2/δ} ‖ξ_0‖_δ ‖ξ_j‖_δ`, where the σ-algebra transport
is `σ(X_0, e_0) ≤ ⨆_{s ≤ 0}` and `σ(X_j, e_j) ≤ ⨆_{s ≥ j}`. The remaining work is the
kernel-localization estimate `‖ξ_0‖_δ² ≤ C h^{2/δ}` and the summation
`Σ_{j > m_n} α^{1−2/δ}(j) ≤ m_n^{−λ} Σ_j j^λ α^{1−2/δ}(j)` from (C3), whose `h`-powers
close against (C5). -/
private theorem large_lag_covariance_bound [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    {δ : ℝ} (hδ : 2 < δ) {W : ℝ → ℝ} {x : ℝ} (hWm : Measurable W)
    {hn : ℝ} (hhn : 0 < hn) (j : ℕ) (hj : 1 ≤ j)
    (hL0 : MemLp (fun ω => e 0 ω * W ((X 0 ω - x) / hn)) (ENNReal.ofReal δ) μ)
    (hLj : MemLp (fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / hn)) (ENNReal.ofReal δ) μ) :
    |cov[fun ω => e 0 ω * W ((X 0 ω - x) / hn),
        fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / hn); μ]|
      ≤ 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ)
        * (eLpNorm (fun ω => e 0 ω * W ((X 0 ω - x) / hn)) (ENNReal.ofReal δ) μ).toReal
        * (eLpNorm (fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / hn))
            (ENNReal.ofReal δ) μ).toReal := by
  sorry

/-! #### Ledger (b)–(c): Bernstein blocks and truncation -/

/-- **FY (2.78) — DEBT.** The Volkonskii–Rozanov error of step (d) vanishes:
`k_n · α_pair(s_n) → 0`, from (C3)'s summability and (C5). -/
private theorem tendsto_blockCount_mul_pairAlpha [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} {δ lam : ℝ} (hδ : 2 < δ) (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) :
    Tendsto (fun n : ℕ =>
        (blockCount h δ lam n : ℝ) * pairAlphaCoeff X e μ (smallBlockLen h δ lam n))
      atTop (𝓝 0) := by
  sorry

/-- **FY (2.79)–(2.81) — DEBT.** The small blocks (and the terminal remainder) are
`L²`-negligible: their contribution to `locTruncSum` has variance `→ 0`. Proved from
ledger (a) applied to the small-block index sets, whose total length is
`k_n s_n / n → 0` by the choice of `l_n`, `s_n`. -/
private theorem tendsto_smallBlock_variance [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} {W : ℝ → ℝ} {x : ℝ} {δ lam : ℝ} {h : ℕ → ℝ} {L : ℝ} :
    Tendsto (fun n : ℕ =>
        ((n : ℝ) * h n)⁻¹ *
          ∫ ω, (∑ i ∈ Finset.range (blockCount h δ lam n),
              ∑ t ∈ Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n)
                    + bigBlockLen h n)
                ((i + 1) * (bigBlockLen h n + smallBlockLen h δ lam n)),
              truncErr X e μ L ((t : ℤ) + 1) ω *
                W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  sorry

/-! #### Ledger (d): the four-term telescope -/

/-- **Abstract diagonal-limit device — PROVED.** If `f` is approximated uniformly in
`n` by a family `g L ·` indexed by a level `L → ∞`, each `g L ·` converges to `a L`,
and `a L → A`, then `f n → A`. This is the outer skeleton of FY's four-term telescope:
`L` is the truncation level, the uniform approximation is the truncation tail (2.82),
`a L` is the level-`L` Gaussian charFun, and `a L → A` is the variance continuity in
`L` (2.84). -/
private theorem tendsto_of_uniform_approx {f : ℕ → ℂ} {g : ℝ → ℕ → ℂ} {a : ℝ → ℂ} {A : ℂ}
    (happrox : ∀ ε : ℝ, 0 < ε → ∀ᶠ L in atTop, ∀ n, ‖f n - g L n‖ ≤ ε)
    (hg : ∀ L, Tendsto (g L) atTop (𝓝 (a L)))
    (ha : Tendsto a atTop (𝓝 A)) :
    Tendsto f atTop (𝓝 A) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨L, hL1, hL2⟩ :=
    ((happrox (ε / 3) hε3).and (ha.eventually (Metric.ball_mem_nhds A hε3))).exists
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hg L) (ε / 3) hε3
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ‖f n - g L n‖ ≤ ε / 3 := hL1 n
  have h2 : ‖g L n - a L‖ < ε / 3 := by simpa [dist_eq_norm] using hN n hn
  have h3 : ‖a L - A‖ < ε / 3 := by simpa [Metric.mem_ball, dist_eq_norm] using hL2
  have hsplit : f n - A = f n - g L n + (g L n - a L) + (a L - A) := by ring
  rw [dist_eq_norm, hsplit]
  calc ‖f n - g L n + (g L n - a L) + (a L - A)‖
      ≤ ‖f n - g L n + (g L n - a L)‖ + ‖a L - A‖ := norm_add_le _ _
    _ ≤ ‖f n - g L n‖ + ‖g L n - a L‖ + ‖a L - A‖ := by
        gcongr; exact norm_add_le _ _
    _ < ε := by linarith

/-- **FY (2.82)–(2.83), truncation tail — DEBT.** Uniformly in `n`, the charFun of the
localized sum is within `ε` of the charFun of its truncated companion once the
truncation level `L` is large. Proof: `|e^{iuS} − e^{iuS^L}| ≤ |u| E|S − S^L|`, and the
variance of `S − S^L` obeys the ledger-(a) bound with the factor `E[e²1_{|e|>L}]`,
which vanishes as `L → ∞` by `δ`-moment uniform integrability (`heLδ`, `δ > 2`). -/
private theorem charFun_locSum_sub_locTruncSum_le [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    {δ : ℝ} (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {x : ℝ} {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) (u : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ L in atTop, ∀ n : ℕ,
      ‖charFun (μ.map (locSum X e W x h n)) u
        - charFun (μ.map (locTruncSum X e μ W x h L n)) u‖ ≤ ε := by
  sorry

/-- **FY (2.77)–(2.81) + (2.84), the fixed-level limit — DEBT.** For each truncation
level `L` the truncated statistic is asymptotically `N(0, ν_L)`, and `ν_L → σ²(x) p(x) ∫W²`.

This is the Bernstein-block core of §2.7.7: split `locTruncSum` into `k_n` big blocks
of length `l_n`, `k_n` small blocks of length `s_n` and a remainder; the small blocks
and remainder are `L²`-negligible (`tendsto_smallBlock_variance`); the big blocks
factorize up to `16 (k_n − 1) α_pair(s_n) → 0` by Volkonskii–Rozanov
(`norm_integral_prod_sub_prod_integral_le` with `tendsto_blockCount_mul_pairAlpha`);
and the resulting product of block charFuns converges by the degenerate-Lindeberg
corollary `tendsto_charFun_rowSum_gaussian_of_uniformly_small` — applicable because the
truncated block summands carry the envelope `l_n L CW / √(n h_n) → 0`, which is exactly
why `l_n = [√(n h_n)/log n]` is chosen. The block-variance input is ledger (a). -/
private theorem tendsto_charFun_locTruncSum [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {σsq p : ℝ → ℝ} {δ : ℝ} {x : ℝ}
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    (hC2 : ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℤ, j ≠ 0 → ∀ g : ℝ × ℝ → ℝ, Measurable g →
      (∀ v, 0 ≤ g v) →
      ∫ ω, |e 0 ω * e j ω| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) (u : ℝ) :
    ∃ vT : ℝ → ℝ,
      (∀ L : ℝ, Tendsto (fun n : ℕ => charFun (μ.map (locTruncSum X e μ W x h L n)) u)
          atTop (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (vT L))) u)))
      ∧ Tendsto (fun L : ℝ => charFun (gaussianReal 0 (Real.toNNReal (vT L))) u) atTop
          (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
            (σsq x * p x * ∫ v, W v ^ 2 ∂MeasureTheory.volume))) u)) := by
  sorry

end Ledger

/-- **FY Theorem 2.22** (charFun form): under (C1)–(C5),
`(n h_n)^{-1/2} Σ_{t=1}^n e_t W((X_t − x)/h_n) →d N(0, σ²(x) p(x) ∫ W²)`. -/
theorem kernel_localized_clt [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    -- (C1) USER-INPUT: joint strict stationarity (fdd form); FY (C1)
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {σsq p : ℝ → ℝ} {δ : ℝ} {x : ℝ}
    -- (C1) USER-INPUT: E(e₁ | X₁) = 0; FY (C1)
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    -- (C1) USER-INPUT: E(e₁² | X₁) = σ²(X₁); FY (C1)
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    -- (C1) USER-INPUT: δ-moment of the errors, δ > 2; FY (C1)
    (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    -- (C1) USER-INPUT: X₁ has Lebesgue density p; FY (C1)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    -- (C1) USER-INPUT: continuity at x and positivity; FY (C1)
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    -- (C2) USER-INPUT: operative integrated form of the bounded conditional density
    -- of (X₁, X_j) given the errors; FY (C2), see the module docstring
    (hC2 : ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℤ, j ≠ 0 → ∀ g : ℝ × ℝ → ℝ, Measurable g →
      (∀ v, 0 ≤ g v) →
      ∫ ω, |e 0 ω * e j ω| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ}
    -- (C3) USER-INPUT: α-mixing rate of the pair series; FY (C3)
    (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ}
    -- (C4) USER-INPUT: bounded, integrable kernel with square-integrability; FY (C4)
    (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ}
    -- (C5) USER-INPUT (corrected form — printed display inverted): bandwidths
    -- positive, h → 0, n h³ → ∞; FY (C5)
    (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop)
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt ((n : ℝ) * h n))⁻¹ *
          ∑ t ∈ Finset.range n, e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (σsq x * p x * ∫ v, W v ^ 2 ∂MeasureTheory.volume))) u)) := by
  -- Step (d): the four-term telescope, run through the abstract diagonal device.
  -- `L` is the truncation level; the uniform-in-`n` approximation is the truncation
  -- tail (2.82)–(2.83), the fixed-`L` limits are the Bernstein-block core
  -- (2.77)–(2.81), and their `L → ∞` limit is the variance continuity (2.84).
  obtain ⟨vT, hvT1, hvT2⟩ :=
    tendsto_charFun_locTruncSum hmeasX hmeasE hstat (σsq := σsq) (p := p) hce hcv hδ heLδ
      hmp hp0 hpd hσc hpc hpx hC2 hlam hα hWm hWb hW1 hW2 hh0 hh hnh u
  exact tendsto_of_uniform_approx
    (charFun_locSum_sub_locTruncSum_le hmeasX hmeasE hδ heLδ hWm hWb hW1 hW2
      (x := x) hh0 hh hnh u)
    hvT1 hvT2

end StatLean.TimeSeries
