import StatLean.Bayesian.BernsteinVonMises.Defs
import StatLean.Bayesian.BernsteinVonMises.Basic

/-!
# Prior small-ball bounds and the exponential tail split

Quantitative consequences of the prior condition of vdV Theorem 10.1 (`HasLocalDensity`):

* `prior_ball_inv_sqrt_lower` — the small-ball lower bound
  `π(B(θ₀, u/√n)) ≳ n^{-k/2}` (continuity and positivity of the density at `θ₀`);
* `prior_smallBall_upper` / `prior_smallBall_lower` — two-sided volume comparison of `π`
  with Lebesgue measure on a small ball around `θ₀`;
* `prior_tail_split` — the Step-A tail estimate (vdV p. 142, last display):
  `√nᵏ · ∫_{‖θ−θ₀‖ ≥ Mₙ/√n} exp(−c n (‖θ−θ₀‖² ∧ 1)) dπ(θ) → 0` for every `Mₙ → ∞`,
  by splitting at a fixed radius `D` where the density is bounded (moderate zone: Gaussian
  integral; far zone: `√nᵏ e^{−cn} → 0`).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Theorem 10.1, p. 142 (the displays following "Combining the preceding displays").

**Proof formalization notes.** All statements are about the prior alone — no sampling model
appears. The `n^{-k/2}` normalizations are kept explicit (no rescaled-prior object is
introduced); `volume` is Lebesgue measure on `EuclideanSpace ℝ (Fin k)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Pointwise

namespace StatLean.Bayesian

variable {k : ℕ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- Continuity and positivity of `f` at `θ₀` give a radius `D ≤ r₀` on which the density is
squeezed between `f θ₀ / 2` and `2 f θ₀`. -/
private lemma exists_density_envelope (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∃ D : ℝ, 0 < D ∧ D ≤ r₀ ∧
      (∀ θ ∈ Metric.ball θ₀ D, f θ ≤ 2 * f θ₀) ∧
      (∀ θ ∈ Metric.ball θ₀ D, f θ₀ / 2 ≤ f θ) := by
  have hpos := hπ.pos
  obtain ⟨δ, hδ, hδf⟩ :=
    Metric.continuousAt_iff.1 hπ.continuousAt (f θ₀ / 2) (by linarith)
  refine ⟨min δ r₀, lt_min hδ hπ.rad_pos, min_le_right _ _, ?_, ?_⟩ <;>
    intro θ hθ
  · have h1 : dist θ θ₀ < δ := lt_of_lt_of_le (Metric.mem_ball.1 hθ) (min_le_left _ _)
    have := hδf h1
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).2
    linarith
  · have h1 : dist θ θ₀ < δ := lt_of_lt_of_le (Metric.mem_ball.1 hθ) (min_le_left _ _)
    have := hδf h1
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).1
    linarith

/-- The prior integral over a small measurable subset of `B(θ₀, r₀)` unfolds to a Lebesgue
integral of the density. -/
private lemma prior_setLIntegral_eq (hπ : HasLocalDensity π θ₀ r₀ f)
    {s : Set (EuclideanSpace ℝ (Fin k))} (hs : s ⊆ Metric.ball θ₀ r₀) (hsm : MeasurableSet s) :
    π s = ∫⁻ θ in s, ENNReal.ofReal (f θ) ∂volume := by
  have h1 : π s = π.restrict (Metric.ball θ₀ r₀) s := by
    rw [Measure.restrict_apply hsm, Set.inter_eq_self_of_subset_left hs]
  rw [h1, hπ.restrict_eq, withDensity_apply _ hsm, Measure.restrict_restrict hsm,
    Set.inter_eq_self_of_subset_left hs]

/-- Volume of a ball in `ℝᵏ` in terms of the unit ball (stated without `[Nontrivial]`, so that
the degenerate case `k = 0` is covered). -/
private lemma volume_ball_eq_ofReal_pow (x : EuclideanSpace ℝ (Fin k)) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball x r)
      = ENNReal.ofReal (r ^ k) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) := by
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) r
      = r • Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    rw [smul_ball hr.ne' (0 : EuclideanSpace ℝ (Fin k)) 1, smul_zero,
      Real.norm_eq_abs, abs_of_pos hr, mul_one]
  rw [Measure.addHaar_ball_center, hball,
    Measure.addHaar_smul_of_nonneg (volume : Measure (EuclideanSpace ℝ (Fin k))) hr.le,
    finrank_euclideanSpace_fin]

/-- The lower volume comparison, extracted so that both `prior_ball_inv_sqrt_lower` and
`prior_smallBall_lower` can use it. -/
private lemma prior_smallBall_lower_aux (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∃ D : ℝ, 0 < D ∧ D ≤ r₀ ∧ ∃ cb : ℝ≥0∞, 0 < cb ∧
      ∀ s : Set (EuclideanSpace ℝ (Fin k)), s ⊆ Metric.ball θ₀ D → MeasurableSet s →
        cb * volume s ≤ π s := by
  obtain ⟨D, hD, hDr, _, hlow⟩ := exists_density_envelope hπ
  refine ⟨D, hD, hDr, ENNReal.ofReal (f θ₀ / 2), ?_, ?_⟩
  · exact ENNReal.ofReal_pos.2 (by linarith [hπ.pos])
  intro s hs hsm
  have hsr : s ⊆ Metric.ball θ₀ r₀ := hs.trans (Metric.ball_subset_ball hDr)
  rw [prior_setLIntegral_eq hπ hsr hsm, ← setLIntegral_const s (ENNReal.ofReal (f θ₀ / 2))]
  exact setLIntegral_mono hπ.measurable.ennreal_ofReal fun θ hθ =>
    ENNReal.ofReal_le_ofReal (hlow θ (hs hθ))

/-- **Prior small-ball lower bound** (vdV p. 142: `Π_n(U) ≳ (1/√n)ᵏ`): under the prior
condition, for every fixed `u > 0` there is `c > 0` with
`c · (√n)⁻ᵏ ≤ π(B(θ₀, u/√n))` for all large `n`. -/
theorem prior_ball_inv_sqrt_lower
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {u : ℝ}
    -- LEAN-ONLY: nontrivial ball radius
    (hu : 0 < u) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k) ≤ π (Metric.ball θ₀ (u / Real.sqrt n)) := by
  obtain ⟨D, hD, _, cb, hcb, hbound⟩ := prior_smallBall_lower_aux hπ
  set V₁ := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1) with hV₁
  have hV₁pos : 0 < V₁ := Metric.measure_ball_pos _ _ one_pos
  refine ⟨cb * ENNReal.ofReal (u ^ k) * V₁, ?_, ?_⟩
  · exact ENNReal.mul_pos
      (ENNReal.mul_pos hcb.ne' (ENNReal.ofReal_pos.2 (by positivity)).ne').ne' hV₁pos.ne'
  -- eventually `u / √n ≤ D` and `n ≥ 1`
  have hsq : Tendsto (fun n : ℕ => u / Real.sqrt n) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa using h.const_div_atTop u
  filter_upwards [hsq.eventually (eventually_le_nhds hD), eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hrpos : 0 < u / Real.sqrt n := div_pos hu hsqrt
  have hsub : Metric.ball θ₀ (u / Real.sqrt n) ⊆ Metric.ball θ₀ D := Metric.ball_subset_ball hn
  have hvol := volume_ball_eq_ofReal_pow θ₀ hrpos
  have hkey : ENNReal.ofReal ((u / Real.sqrt n) ^ k)
      = ENNReal.ofReal (u ^ k) * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow, inv_pow]
    ring
  calc cb * ENNReal.ofReal (u ^ k) * V₁ * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k)
      = cb * (ENNReal.ofReal ((u / Real.sqrt n) ^ k) * V₁) := by rw [hkey]; ring
    _ = cb * volume (Metric.ball θ₀ (u / Real.sqrt n)) := by rw [hvol]
    _ ≤ π (Metric.ball θ₀ (u / Real.sqrt n)) :=
        hbound _ hsub Metric.isOpen_ball.measurableSet

/-- **Local volume upper comparison**: near `θ₀` the prior is dominated by a multiple of
Lebesgue measure (density bounded by continuity at `θ₀`). Returns a radius `D ≤ r₀` on which
the comparison holds. -/
theorem prior_smallBall_upper
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∃ D : ℝ, 0 < D ∧ D ≤ r₀ ∧ ∃ Cb : ℝ≥0∞, Cb ≠ ∞ ∧
      ∀ s : Set (EuclideanSpace ℝ (Fin k)), s ⊆ Metric.ball θ₀ D → MeasurableSet s →
        π s ≤ Cb * volume s := by
  obtain ⟨D, hD, hDr, hup, _⟩ := exists_density_envelope hπ
  refine ⟨D, hD, hDr, ENNReal.ofReal (2 * f θ₀), ENNReal.ofReal_ne_top, ?_⟩
  intro s hs hsm
  have hsr : s ⊆ Metric.ball θ₀ r₀ := hs.trans (Metric.ball_subset_ball hDr)
  rw [prior_setLIntegral_eq hπ hsr hsm, ← setLIntegral_const s (ENNReal.ofReal (2 * f θ₀))]
  exact setLIntegral_mono measurable_const fun θ hθ =>
    ENNReal.ofReal_le_ofReal (hup θ (hs hθ))

/-- **Local volume lower comparison**: near `θ₀` the prior dominates a positive multiple of
Lebesgue measure (density positive by continuity at `θ₀`). -/
theorem prior_smallBall_lower
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∃ D : ℝ, 0 < D ∧ D ≤ r₀ ∧ ∃ cb : ℝ≥0∞, 0 < cb ∧
      ∀ s : Set (EuclideanSpace ℝ (Fin k)), s ⊆ Metric.ball θ₀ D → MeasurableSet s →
        cb * volume s ≤ π s :=
  prior_smallBall_lower_aux hπ

/-- **The Step-A tail split** (vdV p. 142, final display of the concentration step): for every
exponent `c > 0` and every `Mₙ → ∞`,
`(√n)ᵏ · ∫_{‖θ−θ₀‖ ≥ Mₙ/√n} exp(−c n (‖θ−θ₀‖² ∧ 1)) dπ(θ) → 0`.
Split at a radius `D` from `prior_smallBall_upper`: on the moderate zone substitute the
density bound and compare with the Gaussian integral `∫_{‖h‖ ≥ Mₙ} e^{−c‖h‖²} dh → 0`; on
the far zone bound by `(√n)ᵏ e^{−c n D²} · π(univ) → 0`. -/
theorem prior_tail_split
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {c : ℝ}
    -- LEAN-ONLY: positive exponential rate (supplied by Lemma 10.3)
    (hc : 0 < c) {Mseq : ℕ → ℝ}
    -- USER-INPUT: the localization radii diverge; vdV §10.2, p. 141 (`Mₙ → ∞`)
    (hM : Tendsto Mseq atTop atTop) :
    Tendsto (fun n : ℕ =>
        ENNReal.ofReal (Real.sqrt n ^ k) *
          ∫⁻ θ in {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖},
            ENNReal.ofReal (Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
      atTop (𝓝 0) := by
  sorry

end StatLean.Bayesian
