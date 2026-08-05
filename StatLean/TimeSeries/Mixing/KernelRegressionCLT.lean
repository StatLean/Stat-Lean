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

**Status of the ledger.** `kernel_localized_clt` is assembled (no `sorry` of its own)
from the two step-(d) inputs through the proved `tendsto_of_uniform_approx`. Proved in
full: the four analytic bricks (`integral_dilate_translate`,
`integral_comp_eq_integral_density`, `integral_bdd_comp_mul_eq_of_condExp`,
`tendsto_integral_dilate_of_bounded`), the repaired diagonal
`tendsto_localized_second_moment_of_bounded`, the small-lag bound (2.76)
`small_lag_covariance_bound`, the large-lag Davydov bound (2.75)
`large_lag_covariance_bound`, the pair-σ-algebra transport, and the `pairAlphaCoeff`
basics; and, under the authorized (C1) repair, the diagonal (2.73) itself
(`tendsto_localized_second_moment_debt`, with `nonneg_of_continuousAt_of_ae_nonneg`).
and the Volkonskii–Rozanov rate (2.78) `tendsto_blockCount_mul_pairAlpha`, with its
(C3) input `tendsto_weighted_antitone_of_summable`.
Open, as named debts:
`var_localized_sum` (the (a) headline — see its docstring for this wave's sharp
obstruction: FY's route needs `E|ξ_0|^δ = O(h)`, a *third* silent reading of (C1)),
`tendsto_smallBlock_variance` (2.79)–(2.81), `charFun_locSum_sub_locTruncSum_le`
(2.82)–(2.83), `tendsto_charFun_locTruncSum` ((b) + (d) at fixed `L`, and (2.84)).

**FALSE AS FROZEN (verified) — REPAIR APPLIED.** FY (2.73) — hence Theorem 2.22 itself —
does not follow from (C1)–(C5) *as formalized here*. The counterexample below stands; the
laptop-authorized amendment of (C1) has been applied to `kernel_localized_clt`,
`tendsto_localized_second_moment_debt`, `var_localized_sum` and
`tendsto_charFun_locTruncSum`, in the form of the two extra hypotheses
`(hσm : Measurable σsq)` and `(hσpb : ∃ C, ∀ v, σsq v * p v ≤ C)`. Under them the
diagonal (2.73) is now **proved** (`tendsto_localized_second_moment_debt`); note that only
the *upper* half of the bound is assumed — the lower half is derived from `σ²` being a
conditional second moment. The record of the failure as frozen:

The diagonal term equals, identically,
`∫ (σ²·p)(x + h u) W²(u) du` (this identity is proved, inside
`tendsto_localized_second_moment_of_bounded`), and its convergence to `σ²(x)p(x)∫W²`
needs control of the range `|u| > M`, which continuity of `σ²·p` **at `x`** does not
give. (C2) forces only `σ·p` bounded, never `σ²·p`; and `σ²·p ∈ L¹` (`= E e_0² < ∞`) is
too weak against a merely-`L¹` weight `W²`. See
`tendsto_localized_second_moment_debt`'s docstring for the explicit spike/kernel
counterexample and the two possible repairs (compactly supported `W`, or `σ²·p`
bounded — the latter is the textbook's silent reading of (C1)). Note also that (C1) as
frozen carries **no measurability hypothesis on `σsq`**; only `hcv` constrains it, and
only `μ.map (X 0)`-a.e.

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

/-! #### σ-algebra transport for the pair series

The past/future σ-algebras of `pairAlphaCoeff` are `⨆`-sups over index sets; these three
lemmas are all the transport the Davydov step needs. -/

/-- Every pair σ-algebra sits below the ambient one. -/
private theorem pairSigma_le {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t))
    (hmeasE : ∀ t, Measurable (e t)) (S : Set ℤ) :
    (⨆ s ∈ S, MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance) ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun s _ => sup_le (hmeasX s).comap_le (hmeasE s).comap_le

omit [MeasurableSpace Ω] in
/-- `X t` is measurable for the pair σ-algebra of any index set containing `t`. -/
private theorem measurable_X_pairSigma {X e : ℤ → Ω → ℝ} {S : Set ℤ} {t : ℤ} (ht : t ∈ S) :
    Measurable[⨆ s ∈ S, MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance] (X t) :=
  (Measurable.of_comap_le le_rfl).mono (le_iSup₂_of_le t ht le_sup_left) le_rfl

omit [MeasurableSpace Ω] in
/-- `e t` is measurable for the pair σ-algebra of any index set containing `t`. -/
private theorem measurable_e_pairSigma {X e : ℤ → Ω → ℝ} {S : Set ℤ} {t : ℤ} (ht : t ∈ S) :
    Measurable[⨆ s ∈ S, MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance] (e t) :=
  (Measurable.of_comap_le le_rfl).mono (le_iSup₂_of_le t ht le_sup_right) le_rfl

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

/-- **Continuity at a point upgrades an a.e. lower bound to a pointwise one.** If `g` is
continuous at `x` and `0 ≤ g` Lebesgue-a.e., then `0 ≤ g x`: otherwise `g < 0` on a whole
ball around `x`, which has positive Lebesgue measure. Used to evaluate the repaired
diagonal limit at the point `x` itself, where `σ²` is *not* pinned down by `hcv` (which
constrains it only `μ.map (X 0)`-a.e.). -/
private theorem nonneg_of_continuousAt_of_ae_nonneg {g : ℝ → ℝ} {x : ℝ}
    (hgc : ContinuousAt g x)
    (hae : ∀ᵐ v ∂(MeasureTheory.volume : Measure ℝ), 0 ≤ g v) : 0 ≤ g x := by
  by_contra hx
  push_neg at hx
  have hlt : ∀ᶠ v in 𝓝 x, g v < 0 := hgc (Iio_mem_nhds hx)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hlt
  have hsub : Metric.ball x ε ⊆ {v : ℝ | 0 ≤ g v}ᶜ := fun v hv => not_le.2 (hball v hv)
  exact (Metric.measure_ball_pos MeasureTheory.volume x hε).ne'
    (measure_mono_null hsub (mem_ae_iff.1 hae))

/-- **FY (2.73), diagonal term — REPAIRED AND PROVED.**
`h⁻¹ E[e_0² W²((X_0 − x)/h)] = ∫ (σ²·p)(x + h u) W²(u) du` (an *identity*, proved
inside `tendsto_localized_second_moment_of_bounded`), and FY asserts the limit
`σ²(x) p(x) ∫ W²`.

**Status: PROVED, under the authorized repair** — the two hypotheses `hσm`/`hσpb` below
are the laptop-authorized amendment of (C1) (the textbook's silent reading; see the
module docstring's FALSE-AS-FROZEN section). The record of *why* the amendment is
necessary is kept verbatim below.

Note that `hσpb` is only a **one-sided** (upper) bound: the matching lower bound is not
assumed but *derived*, since `σ²` is a conditional second moment, hence `≥ 0` a.e. for
the law of `X_0`, hence `σ²·p ≥ 0` Lebesgue-a.e. (this is where `hσm` is spent — it makes
`{v | 0 ≤ σ²(v)}` measurable, so the a.e. statement transports through
`ae_map_iff`/`ae_withDensity_iff`). The proof then runs
`tendsto_localized_second_moment_of_bounded` on the clipped `max σ² 0`, which agrees with
`σ²` a.e.-`μ` under the conditional expectation, and agrees with it *at the point* `x` by
`nonneg_of_continuousAt_of_ae_nonneg`.

**Why the repair is needed.** The limit needs more than the formalized (C1)–(C5) supply
(this was verified in the previous wave). Continuity of
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

**Repair (APPLIED).** Either strengthen (C4) to compactly supported `W` (then continuity
at `x` suffices and this lemma is `tendsto_localized_second_moment_of_bounded`'s window
argument), or strengthen (C1) to `σ²·p` bounded — which is what the textbook's
"(C1) with `σ²` and `p` bounded" silently supplies. The second route is the one taken:
`hσpb` below, together with the measurability `hσm` that the frozen (C1) also omitted
(only `hcv` constrains `σsq`, and only `μ.map (X 0)`-a.e.). -/
private theorem tendsto_localized_second_moment_debt [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hX : Measurable (X 0)) {σsq p : ℝ → ℝ}
    -- USER-INPUT: σ² measurable (the frozen (C1) omits it); FY §2.6.4
    (hσm : Measurable σsq)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {x : ℝ}
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (he2 : Integrable (fun ω => e 0 ω ^ 2) μ)
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x)
    -- USER-INPUT: σ²·p bounded (the textbook's silent reading of (C1)); FY §2.6.4
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
        (h n)⁻¹ * ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ) atTop
      (𝓝 (σsq x * p x * ∫ v, W v ^ 2)) := by
  obtain ⟨C, hC⟩ := hσpb
  -- (1) `σ²` is a conditional second moment, hence `≥ 0` a.e.-`μ` along `X 0`.
  have hcond0 : (0 : Ω → ℝ)
      ≤ᵐ[μ] μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance] :=
    condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
  have hσ0 : ∀ᵐ ω ∂μ, 0 ≤ σsq (X 0 ω) := by
    filter_upwards [hcond0, hcv] with ω h1 h2
    simpa [h2] using h1
  -- (2) hence `σ²·p ≥ 0` Lebesgue-a.e. (transport through the density of `X 0`).
  have hlaw : ∀ᵐ v ∂(μ.map (X 0)), 0 ≤ σsq v := by
    rw [ae_map_iff hX.aemeasurable (measurableSet_le measurable_const hσm)]
    exact hσ0
  rw [hpd, ae_withDensity_iff (by fun_prop)] at hlaw
  have hae : ∀ᵐ v ∂(MeasureTheory.volume : Measure ℝ), 0 ≤ σsq v * p v := by
    filter_upwards [hlaw] with v hv
    rcases (hp0 v).eq_or_lt with hz | hz
    · rw [← hz, mul_zero]
    · exact mul_nonneg (hv (ENNReal.ofReal_pos.2 hz).ne') (hp0 v)
  -- (3) the clipped `max σ² 0` satisfies the *two-sided* bound of the proved brick,
  -- and agrees with `σ²` both a.e.-`μ` (under `hcv`) and at the point `x`.
  have hcv' : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => max (σsq (X 0 ω)) 0 := by
    filter_upwards [hcv, hσ0] with ω h1 h2
    rw [h1, max_eq_left h2]
  have hbound : ∀ v : ℝ, |max (σsq v) 0 * p v| ≤ max C 0 := by
    intro v
    rw [abs_of_nonneg (mul_nonneg (le_max_right _ _) (hp0 v))]
    rcases le_or_gt 0 (σsq v) with hs | hs
    · rw [max_eq_left hs]; exact (hC v).trans (le_max_left _ _)
    · rw [max_eq_right hs.le, zero_mul]; exact le_max_right _ _
  have hend : max (σsq x) 0 * p x = σsq x * p x := by
    rcases le_or_gt 0 (σsq x) with hs | hs
    · rw [max_eq_left hs]
    · have hgx : 0 ≤ σsq x * p x :=
        nonneg_of_continuousAt_of_ae_nonneg (g := fun v => σsq v * p v)
          (hσc.mul hpc) hae
      have hpx0 : p x = 0 := by
        rcases (hp0 x).eq_or_lt with hz | hz
        · exact hz.symm
        · nlinarith
      rw [hpx0, mul_zero, mul_zero]
  have hmain := tendsto_localized_second_moment_of_bounded (X := X) (e := e) hX
    (σsq := fun v => max (σsq v) 0) (p := p) (hσm.max measurable_const) hmp hp0 hpd
    (x := x) hcv' he2 ((hσc.max continuousAt_const).mul hpc) (M := max C 0) hbound
    hWm hWb hW2 hh0 hh
  rw [hend] at hmain
  exact hmain

/-- **FY (2.75), large-lag covariance bound — PROVED.** Davydov
(`abs_covariance_le_davydov` at `p = q = δ`, so the exponent is `1 − 2/δ`) against the
pair α-coefficient: `|Cov(ξ_0, ξ_j)| ≤ 8 α_pair(j)^{1−2/δ} ‖ξ_0‖_δ ‖ξ_j‖_δ`. The
σ-algebra transport is `σ(X_0, e_0) ≤ ⨆_{s ≤ 0}` and `σ(X_j, e_j) ≤ ⨆_{s ≥ j}`.

What remains for ledger (a) — and is *not* part of this lemma — is the kernel
localization of the δ-norms, `‖ξ_0‖_δ² ≤ C h^{2/δ}`, and the summation
`Σ_{j > m_n} α^{1−2/δ}(j) ≤ m_n^{−λ} Σ_j j^λ α^{1−2/δ}(j)` from (C3), whose `h`-powers
close against (C5); those live in `var_localized_sum`'s assembly. -/
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
  have hpq : 1 / δ + 1 / δ < 1 := by
    have h2d : 1 / δ + 1 / δ = 2 / δ := by ring
    rw [h2d, div_lt_one (by linarith : (0 : ℝ) < δ)]; linarith
  have hf : Measurable[⨆ s ∈ Set.Iic (0 : ℤ), MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance]
      (fun ω => e 0 ω * W ((X 0 ω - x) / hn)) :=
    (measurable_e_pairSigma (X := X) (e := e) (Set.mem_Iic.2 (le_refl (0 : ℤ)))).mul
      (hWm.comp (((measurable_X_pairSigma (X := X) (e := e)
        (Set.mem_Iic.2 (le_refl (0 : ℤ)))).sub measurable_const).div measurable_const))
  have hg : Measurable[⨆ s ∈ Set.Ici (j : ℤ), MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance]
      (fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / hn)) :=
    (measurable_e_pairSigma (X := X) (e := e) (Set.mem_Ici.2 (le_refl (j : ℤ)))).mul
      (hWm.comp (((measurable_X_pairSigma (X := X) (e := e)
        (Set.mem_Ici.2 (le_refl (j : ℤ)))).sub measurable_const).div measurable_const))
  have hdav := abs_covariance_le_davydov (pairSigma_le hmeasX hmeasE (Set.Iic (0 : ℤ)))
    (pairSigma_le hmeasX hmeasE (Set.Ici (j : ℤ))) hf hg (p := δ) (q := δ)
    (by linarith) (by linarith) hpq hL0 hLj
  have hexp : (1 : ℝ) - 1 / δ - 1 / δ = 1 - 2 / δ := by ring
  rw [hexp] at hdav
  exact hdav

/-- **FY (2.73)–(2.76), the ledger-(a) headline — DEBT, with a *sharp* missing input.**
`(n h_n)⁻¹ Var(S_n(x)) → σ²(x) p(x) ∫ W²`.

Assembled from three inputs: the diagonal (`tendsto_localized_second_moment_debt`, now
**proved** under the authorized (C1) repair), the small lags `1 ≤ j ≤ smallLagCut h n`
via `small_lag_covariance_bound` (total `m_n · h² / h = h/|log h| → 0`), and the large
lags `j > smallLagCut h n` via `large_lag_covariance_bound` + (C3)'s weighted summability
(`Σ_{j>m} α^{1−2/δ}(j) ≤ m^{−λ} Σ j^λ α^{1−2/δ}(j)`). Stationarity (`hstat`) turns the
double sum over `1 ≤ s, t ≤ n` into `n` times a single lag sum. Mean-zero of each summand
(from `hce` through `integral_bdd_comp_mul_eq_of_condExp`) is what lets the variance be
read off the second moment.

**BLOCKED AS FROZEN (this wave's finding; a *separate* gap from the one the authorized
repair fixes).** The large-lag half does not close under (C1)–(C5) as formalized here,
for any `λ ≤ 1`. FY's step is `|Cov(ξ_0, ξ_j)| ≤ 8 α(j)^{1−2/δ} ‖ξ_0‖_δ ‖ξ_j‖_δ` with the
**kernel-localized δ-norm** `‖ξ_0‖_δ² = O(h^{2/δ})`, i.e. `E|ξ_0|^δ = O(h)`; then
`h⁻¹ · h^{2/δ} · m_n^{−λ} = h^{λ + 2/δ − 1} |log h|^λ → 0`, which is *exactly* (C3)'s
`λ > 1 − 2/δ`. But `E|ξ_0|^δ = E[|e_0|^δ |W((X_0−x)/h)|^δ]` factorizes only through a
**conditional** δ-moment `E(|e_0|^δ | X_0) ≤ M` (with `p` bounded), and the frozen (C1)
supplies only the *unconditional* `MemLp (e 0) δ` (`heLδ`), which gives merely
`‖ξ_0‖_δ ≤ CW ‖e_0‖_δ = O(1)` — no `h`-gain at all.

The gap is not repairable by interpolating the inputs that *are* available. Writing
`β = 1 − 2/δ`, what the file has is `‖ξ_0‖_2 = O(√h)` (this **is** new, and comes from the
authorized repair: `E ξ_0² = ∫ (σ²p)(x+hu)W(u)²du ≤ C h ∫W²`), `‖ξ_0‖_δ = O(1)`, and the
`(C2)` bound `|E[ξ_0 ξ_j]| = O(h²)` valid at *every* lag. Hölder interpolation at
`2 < q ≤ δ` gives `‖ξ_0‖_q = O(h^{θ/2})` with `1/q = θ/2 + (1−θ)/δ`, and the Davydov
exponent is then `1 − 2/q = β(1−θ)`, so the large-lag total is
`h^{θ−1} Σ_{j>m} α(j)^{β(1−θ)}`. With `s := 1 − θ`, `(C3)` gives only
`α(j)^β = o(j^{−λ})`, hence `α(j)^{βs} = o(j^{−λs})`, whose tail converges only when
`λ s > 1`; since `s ≤ 1` this forces `λ > 1`. Taking instead the `(C2)` bound on the same
range costs `n h → ∞`. So for `λ ∈ (1 − 2/δ, 1]` — the range (C3) actually allows —
every combination of the frozen inputs diverges.

**Missing input, precisely.** FY's implicit (2.74): `E|ξ_0|^δ ≤ K h` (equivalently:
`E(|e_0|^δ | X_0) ≤ M` a.e. together with `p` bounded). This is a *third* silent reading
of (C1), independent of the two authorized here (`hσm`, `hσpb` bound `σ²·p`, i.e. the
**second** conditional moment; they do not bound the δ-th). It is not in this wave's
authorization, so the item stays a named debt rather than being repaired. -/
private theorem var_localized_sum [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {σsq p : ℝ → ℝ} {δ x : ℝ}
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    -- USER-INPUT (authorized (C1) repair): σ² measurable; FY §2.6.4
    (hσm : Measurable σsq)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    -- USER-INPUT: σ²·p bounded (the textbook's silent reading of (C1)); FY §2.6.4
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
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
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) :
    Tendsto (fun n : ℕ => ((n : ℝ) * h n)⁻¹ *
        ∫ ω, (∑ t ∈ Finset.range n,
          e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ)
      atTop (𝓝 (σsq x * p x * ∫ v, W v ^ 2 ∂MeasureTheory.volume)) := by
  sorry

/-! #### Ledger (b)–(c): Bernstein blocks and truncation -/

/-- **Antitone weighted summability gains one power — PROVED.** If `a` is nonnegative and
antitone and `Σ t^λ a(t)^β < ∞` (`λ, β > 0`), then `t^{λ+1} a(t)^β → 0`. Summability alone
gives only `t^λ a(t)^β → 0`; the extra power comes from the dyadic block
`Σ_{j ∈ [T/2, T)} j^λ a(j)^β ≥ (T/2)^{λ+1} a(T)^β`, whose left side is a difference of two
partial sums and hence vanishes. This is the form of (C3) that FY's (2.78) actually
uses. -/
private theorem tendsto_weighted_antitone_of_summable {a : ℕ → ℝ} {lam beta : ℝ}
    (hlam : 0 < lam) (hbeta : 0 < beta)
    (ha0 : ∀ t, 0 ≤ a t) (hanti : Antitone a)
    (hsum : Summable fun t : ℕ => (t : ℝ) ^ lam * a t ^ beta) :
    Tendsto (fun t : ℕ => (t : ℝ) ^ (lam + 1) * a t ^ beta) atTop (𝓝 0) := by
  set f : ℕ → ℝ := fun t => (t : ℝ) ^ lam * a t ^ beta with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _) (Real.rpow_nonneg (ha0 t) _)
  have hS : Tendsto (fun k => ∑ j ∈ Finset.range k, f j) atTop (𝓝 (∑' j, f j)) :=
    hsum.hasSum.tendsto_sum_nat
  have hdiv : Tendsto (fun T : ℕ => T / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun a ha => by omega⟩
  have hg : Tendsto (fun T : ℕ =>
      (∑ j ∈ Finset.range T, f j) - ∑ j ∈ Finset.range (T / 2), f j) atTop (𝓝 0) := by
    have := hS.sub (hS.comp hdiv)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun t =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _) (Real.rpow_nonneg (ha0 t) _)) ?_
    (by simpa using hg.const_mul ((4 : ℝ) ^ (lam + 1)))
  filter_upwards [eventually_ge_atTop 2] with T hT
  set m : ℕ := T / 2 with hm
  have hmT : m ≤ T := Nat.div_le_self _ _
  have hm1 : 1 ≤ m := Nat.one_le_div_iff (by norm_num) |>.2 hT
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  -- each term of the block dominates `m ^ lam * a T ^ beta`
  have hterm : ∀ j ∈ Finset.Ico m T, (m : ℝ) ^ lam * a T ^ beta ≤ f j := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have h1 : (m : ℝ) ^ lam ≤ (j : ℝ) ^ lam :=
      Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hj.1) hlam.le
    have h2 : a T ^ beta ≤ a j ^ beta :=
      Real.rpow_le_rpow (ha0 T) (hanti hj.2.le) hbeta.le
    exact mul_le_mul h1 h2 (Real.rpow_nonneg (ha0 T) _)
      (Real.rpow_nonneg (Nat.cast_nonneg j) _)
  have hcard : m ≤ (Finset.Ico m T).card := by
    rw [Nat.card_Ico]
    omega
  have hblock : (m : ℝ) ^ (lam + 1) * a T ^ beta
      ≤ ∑ j ∈ Finset.Ico m T, f j := by
    have hcast : (m : ℝ) ≤ ((Finset.Ico m T).card : ℝ) := by exact_mod_cast hcard
    have hnn : (0 : ℝ) ≤ (m : ℝ) ^ lam * a T ^ beta :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _) (Real.rpow_nonneg (ha0 T) _)
    calc (m : ℝ) ^ (lam + 1) * a T ^ beta
        = (m : ℝ) * ((m : ℝ) ^ lam * a T ^ beta) := by
          rw [Real.rpow_add hmpos, Real.rpow_one, mul_comm ((m:ℝ)^lam), mul_assoc]
      _ ≤ ((Finset.Ico m T).card : ℝ) * ((m : ℝ) ^ lam * a T ^ beta) :=
          mul_le_mul_of_nonneg_right hcast hnn
      _ = (Finset.Ico m T).card • ((m : ℝ) ^ lam * a T ^ beta) := (nsmul_eq_mul _ _).symm
      _ ≤ ∑ j ∈ Finset.Ico m T, f j := Finset.card_nsmul_le_sum _ _ _ hterm
  -- and `T ≤ 4 m`
  have hT4 : (T : ℝ) ≤ 4 * (m : ℝ) := by
    have : T ≤ 4 * m := by omega
    exact_mod_cast this
  have hTle : (T : ℝ) ^ (lam + 1) ≤ (4 : ℝ) ^ (lam + 1) * (m : ℝ) ^ (lam + 1) := by
    calc (T : ℝ) ^ (lam + 1) ≤ (4 * (m : ℝ)) ^ (lam + 1) :=
          Real.rpow_le_rpow (Nat.cast_nonneg T) hT4 (by linarith)
      _ = (4 : ℝ) ^ (lam + 1) * (m : ℝ) ^ (lam + 1) :=
          Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)
  calc (T : ℝ) ^ (lam + 1) * a T ^ beta
      ≤ ((4 : ℝ) ^ (lam + 1) * (m : ℝ) ^ (lam + 1)) * a T ^ beta :=
        mul_le_mul_of_nonneg_right hTle (Real.rpow_nonneg (ha0 T) _)
    _ = (4 : ℝ) ^ (lam + 1) * ((m : ℝ) ^ (lam + 1) * a T ^ beta) := by ring
    _ ≤ (4 : ℝ) ^ (lam + 1) * ∑ j ∈ Finset.Ico m T, f j :=
        mul_le_mul_of_nonneg_left hblock (Real.rpow_nonneg (by norm_num) _)
    _ = (4 : ℝ) ^ (lam + 1) *
          ((∑ j ∈ Finset.range T, f j) - ∑ j ∈ Finset.range m, f j) := by
        rw [Finset.sum_Ico_eq_sub _ hmT]

/-- **FY (2.78) — PROVED.** The Volkonskii–Rozanov error of step (d) vanishes:
`k_n · α_pair(s_n) → 0`.

The exponent arithmetic, with `β = 1 − 2/δ` and `A_n = √(n/h_n) log n`: the block count
obeys `k_n ≤ n/l_n ≤ A_n` (that is what `l_n = [√(n h_n)/log n]` is for), while
`s_n = [A_n^{β/(λ+1)}]` gives `A_n ≤ s_n^{(λ+1)/β}`. Hence
`(k_n α(s_n))^β ≤ A_n^β α(s_n)^β ≤ s_n^{λ+1} α(s_n)^β → 0`
by `tendsto_weighted_antitone_of_summable` (`s_n → ∞`), and `k_n α(s_n) → 0` follows by
continuity of `y ↦ y^{1/β}` at `0`.

Note that (C5) (`hnh`) is **not needed**: (2.78) holds for any bandwidth sequence with
`h_n → 0`. (C5) is what makes `s_n = o(l_n)`, which is used elsewhere in step (b), not
here. -/
private theorem tendsto_blockCount_mul_pairAlpha [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} {δ lam : ℝ} (hδ : 2 < δ) (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) :
    Tendsto (fun n : ℕ =>
        (blockCount h δ lam n : ℝ) * pairAlphaCoeff X e μ (smallBlockLen h δ lam n))
      atTop (𝓝 0) := by
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by
    rw [sub_pos, div_lt_one hδ0]; linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  have hlam1 : (0 : ℝ) < lam + 1 := by linarith
  -- `A n = √(n/h n) · log n`, the upper bound for the block count `k_n`
  have hA : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) / h n) * Real.log n) atTop atTop := by
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hq : Tendsto (fun n : ℕ => (n : ℝ) / h n) atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
      filter_upwards [hh.eventually_le_const (by norm_num : (0:ℝ) < 1)] with n hn
      calc (n : ℝ) = (n : ℝ) / 1 := by ring
        _ ≤ (n : ℝ) / h n := div_le_div_of_nonneg_left (Nat.cast_nonneg n) (hh0 n) hn
    exact (Real.tendsto_sqrt_atTop.comp hq).atTop_mul_atTop₀ hlog
  -- the small block length tends to infinity
  have hs_top : Tendsto (fun n : ℕ => smallBlockLen h δ lam n) atTop atTop := by
    refine tendsto_nat_ceil_atTop.comp ?_
    exact (tendsto_rpow_atTop (div_pos hβ0 hlam1)).comp hA
  -- `k_n ≤ A n`
  have hk_le : ∀ᶠ n : ℕ in atTop, (blockCount h δ lam n : ℝ)
      ≤ Real.sqrt ((n : ℝ) / h n) * Real.log n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogpos : 0 < Real.log n := Real.log_pos hn1
    have hbig : 0 < Real.sqrt ((n : ℝ) * h n) / Real.log n :=
      div_pos (Real.sqrt_pos.2 (mul_pos hnpos (hh0 n))) hlogpos
    have hl : Real.sqrt ((n : ℝ) * h n) / Real.log n ≤ (bigBlockLen h n : ℝ) :=
      Nat.le_ceil _
    have hlpos : (0 : ℝ) < (bigBlockLen h n : ℝ) := lt_of_lt_of_le hbig hl
    have hkey : (n : ℝ) / (Real.sqrt ((n : ℝ) * h n) / Real.log n)
        = Real.sqrt ((n : ℝ) / h n) * Real.log n := by
      have h1 : Real.sqrt ((n : ℝ) * h n) = Real.sqrt n * Real.sqrt (h n) :=
        Real.sqrt_mul hnpos.le _
      have h2 : Real.sqrt ((n : ℝ) / h n) = Real.sqrt n / Real.sqrt (h n) :=
        Real.sqrt_div hnpos.le _
      have h3 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt hnpos.le
      have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnpos
      have hsh : (0 : ℝ) < Real.sqrt (h n) := Real.sqrt_pos.2 (hh0 n)
      rw [h1, h2]
      field_simp
      nlinarith [h3, hsn, hsh, hlogpos]
    calc (blockCount h δ lam n : ℝ)
        ≤ (n : ℝ) / ((bigBlockLen h n + smallBlockLen h δ lam n : ℕ) : ℝ) :=
          Nat.cast_div_le
      _ ≤ (n : ℝ) / (bigBlockLen h n : ℝ) := by
          rw [Nat.cast_add]
          exact div_le_div_of_nonneg_left hnpos.le hlpos
            (le_add_of_nonneg_right (Nat.cast_nonneg _))
      _ ≤ (n : ℝ) / (Real.sqrt ((n : ℝ) * h n) / Real.log n) :=
          div_le_div_of_nonneg_left hnpos.le hbig hl
      _ = Real.sqrt ((n : ℝ) / h n) * Real.log n := hkey
  -- the main pointwise bound
  have hmain : ∀ᶠ n : ℕ in atTop,
      (blockCount h δ lam n : ℝ) * pairAlphaCoeff X e μ (smallBlockLen h δ lam n)
        ≤ (((smallBlockLen h δ lam n : ℝ)) ^ (lam + 1) *
            pairAlphaCoeff X e μ (smallBlockLen h δ lam n) ^ (1 - 2 / δ)) ^ (1 / (1 - 2 / δ)) := by
    filter_upwards [hk_le, hA.eventually_gt_atTop 0] with n hk hA0
    have ha0 : 0 ≤ pairAlphaCoeff X e μ (smallBlockLen h δ lam n) :=
      pairAlphaCoeff_nonneg X e _
    have hspos : (0 : ℝ) ≤ (smallBlockLen h δ lam n : ℝ) := Nat.cast_nonneg _
    -- `A n ≤ s_n ^ ((lam+1)/β)`
    have hsge : (Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1))
        ≤ (smallBlockLen h δ lam n : ℝ) := Nat.le_ceil _
    have hs1 : Real.sqrt ((n : ℝ) / h n) * Real.log n
        ≤ (smallBlockLen h δ lam n : ℝ) ^ ((lam + 1) / (1 - 2 / δ)) := by
      have hd2 : δ - 2 ≠ 0 := (by linarith : (0:ℝ) < δ - 2).ne'
      have hpq : ((1 - 2 / δ) / (lam + 1)) * ((lam + 1) / (1 - 2 / δ)) = 1 := by
        field_simp [hd2, hlam1.ne']
      have hid : ((Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1)))
            ^ ((lam + 1) / (1 - 2 / δ)) = Real.sqrt ((n : ℝ) / h n) * Real.log n := by
        rw [← Real.rpow_mul hA0.le, hpq, Real.rpow_one]
      calc Real.sqrt ((n : ℝ) / h n) * Real.log n
          = ((Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1)))
              ^ ((lam + 1) / (1 - 2 / δ)) := hid.symm
        _ ≤ (smallBlockLen h δ lam n : ℝ) ^ ((lam + 1) / (1 - 2 / δ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hA0.le _) hsge (div_pos hlam1 hβ0).le
    -- the right-hand side splits
    have hrhs : (((smallBlockLen h δ lam n : ℝ)) ^ (lam + 1) *
          pairAlphaCoeff X e μ (smallBlockLen h δ lam n) ^ (1 - 2 / δ)) ^ (1 / (1 - 2 / δ))
        = (smallBlockLen h δ lam n : ℝ) ^ ((lam + 1) / (1 - 2 / δ)) *
            pairAlphaCoeff X e μ (smallBlockLen h δ lam n) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hspos _) (Real.rpow_nonneg ha0 _),
        ← Real.rpow_mul hspos, ← Real.rpow_mul ha0, mul_one_div, mul_one_div,
        div_self hβ0.ne', Real.rpow_one]
    rw [hrhs]
    exact mul_le_mul (hk.trans hs1) le_rfl ha0 (Real.rpow_nonneg hspos _)
  refine squeeze_zero' ?_ hmain ?_
  · filter_upwards with n
    exact mul_nonneg (Nat.cast_nonneg _) (pairAlphaCoeff_nonneg X e _)
  · have hcomp := (tendsto_weighted_antitone_of_summable (a := pairAlphaCoeff X e μ) hlam0 hβ0
      (fun t => pairAlphaCoeff_nonneg X e t) (pairAlphaCoeff_antitone X e) hα).comp hs_top
    have hcont : Tendsto (fun y : ℝ => y ^ (1 / (1 - 2 / δ))) (𝓝 0) (𝓝 0) := by
      have hpos : (0 : ℝ) < 1 / (1 - 2 / δ) := one_div_pos.2 hβ0
      have hz : (0 : ℝ) ^ (1 / (1 - 2 / δ)) = 0 := Real.zero_rpow hpos.ne'
      have ht := (Real.continuousAt_rpow_const (0 : ℝ) (1 / (1 - 2 / δ))
        (Or.inr hpos.le)).tendsto
      rw [hz] at ht
      exact ht
    exact hcont.comp hcomp

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
    -- USER-INPUT (authorized (C1) repair): σ² measurable; FY §2.6.4
    (hσm : Measurable σsq)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    -- USER-INPUT: σ²·p bounded (the textbook's silent reading of (C1)); FY §2.6.4
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
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
    -- (C1) USER-INPUT: σ² measurable (the frozen (C1) omits it); FY (C1)
    (hσm : Measurable σsq)
    -- (C1) USER-INPUT: X₁ has Lebesgue density p; FY (C1)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    -- (C1) USER-INPUT: continuity at x and positivity; FY (C1)
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    -- USER-INPUT: σ²·p bounded (the textbook's silent reading of (C1)); FY §2.6.4
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
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
      hσm hmp hp0 hpd hσc hpc hpx hσpb hC2 hlam hα hWm hWb hW1 hW2 hh0 hh hnh u
  exact tendsto_of_uniform_approx
    (charFun_locSum_sub_locTruncSum_le hmeasX hmeasE hδ heLδ hWm hWb hW1 hW2
      (x := x) hh0 hh hnh u)
    hvT1 hvT2

end StatLean.TimeSeries
