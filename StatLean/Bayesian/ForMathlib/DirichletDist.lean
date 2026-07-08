import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Beta

/-!
# The Dirichlet distribution (corner parametrization)

The **Dirichlet distribution** `𝒟_{k+1}(α₀, …, α_k)` on the probability simplex over `k + 1`
categories, in the *corner parametrization*: the first `k` probabilities `θ : Fin k → ℝ` are free
coordinates on
$$\mathrm{simplexCorner}\ k = \{\theta \mid \forall i,\ 0 < \theta_i \ \wedge\ \textstyle\sum_i
\theta_i < 1\},$$
and the last probability is `1 − ∑ θᵢ` (`simplexExtend`). The density against Lebesgue measure on
`Fin k → ℝ` is
$$w_\alpha(\theta) = \mathbf{1}_{\mathrm{corner}}(\theta)\,
  \prod_{i=0}^{k} (\mathrm{simplexExtend}\,\theta)_i^{\alpha_i - 1},$$
and `dirichletMeasure α = Z(α)⁻¹ • volume.withDensity w_α` with the **abstract normalization**
`Z(α) = ∫⁻ w_α`. Conjugacy (`StatLean.Bayesian.Conjugacy.DirichletMultinomial`) needs only
`0 < Z(α) < ∞`, never the closed form `Z(α) = ∏Γ(αᵢ)/Γ(∑αᵢ)` (a stretch goal).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). Appendix A.8 (Dirichlet 𝒟_k(α₁,…,α_k)), p. 521; Example 3.3.4
(the Dirichlet as an exponential family), p. 116.

**Proof formalization notes.** Robert's A.8 writes the density in `k + 1` symmetric coordinates on
the null set `{∑ xᵢ = 1}`; the corner parametrization used here is the standard
Lebesgue-absolutely-continuous realization (drop the last coordinate), which keeps all measure
theory on `Fin k → ℝ` where `volume` is the pi measure and `StandardBorelSpace` is automatic.
Positivity of `Z` is a sub-box lower bound. Finiteness is the batch's hardest analysis: peel one
coordinate with `MeasureTheory.measurePreserving_piFinSuccAbove`, rescale the remaining corner by
`(1 − t)`, and reduce to the one-dimensional Beta integral `lintegral_Ioo_rpow_mul_rpow`, itself
derived from the pinned `lintegral_betaPDF_eq_one`. Exponents use `Real.rpow`; mind
`Real.rpow_add` needing a positive base (true on the open corner).

**Bibliographic comments.** The distribution is named for P. G. L. Dirichlet, whose evaluation of
the multivariate integral `∫ ∏ xᵢ^{αᵢ−1}` over the simplex ("Sur une nouvelle méthode pour la
détermination des intégrales multiples," *J. Math. Pures Appl.* 4 (1839), 164–168) gives the
normalizing constant. As the conjugate prior of the multinomial it enters Bayesian statistics with
the conjugate-family program of H. Raiffa and R. Schlaifer (*Applied Statistical Decision Theory*,
Harvard, 1961; Robert Table 3.3.1), and it underlies the Dirichlet-process prior of T. S. Ferguson
("A Bayesian analysis of some nonparametric problems," *Ann. Statist.* 1 (1973), 209–230; Robert
§1.8.2) at the heart of Bayesian nonparametrics.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

/-- The open **corner simplex**: the first `k` category probabilities, positive with sum `< 1`
(Robert Appendix A.8, in the corner parametrization). -/
def simplexCorner (k : ℕ) : Set (Fin k → ℝ) :=
  {θ | (∀ i, 0 < θ i) ∧ ∑ i, θ i < 1}

/-- Extend `k` free probabilities to the full vector of `k + 1` category probabilities, the last
being `1 − ∑ θᵢ`. -/
noncomputable def simplexExtend {k : ℕ} (θ : Fin k → ℝ) : Fin (k + 1) → ℝ :=
  Fin.snoc θ (1 - ∑ i, θ i)

theorem measurable_simplexExtend {k : ℕ} : Measurable (simplexExtend (k := k)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simp only [simplexExtend, Fin.snoc_last]
    exact measurable_const.sub (Finset.univ.measurable_sum fun j _ => measurable_pi_apply j)
  · intro j
    simp only [simplexExtend, Fin.snoc_castSucc]
    exact measurable_pi_apply j

theorem measurableSet_simplexCorner (k : ℕ) : MeasurableSet (simplexCorner k) := by
  rw [simplexCorner, Set.setOf_and]
  refine MeasurableSet.inter ?_ ?_
  · rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (measurable_pi_apply i)
  · exact measurableSet_lt
      (Finset.univ.measurable_sum fun i _ => measurable_pi_apply i) measurable_const

open Classical in
/-- **Dirichlet weight** (unnormalized density against Lebesgue on the corner):
`𝟙_corner(θ) · ∏ᵢ (simplexExtend θ)ᵢ^(αᵢ − 1)` (Robert Appendix A.8). -/
noncomputable def dirichletWeight {k : ℕ} (α : Fin (k + 1) → ℝ) : (Fin k → ℝ) → ℝ≥0∞ :=
  fun θ =>
    if θ ∈ simplexCorner k then
      ENNReal.ofReal (∏ i, simplexExtend θ i ^ (α i - 1))
    else 0

theorem measurable_dirichletWeight {k : ℕ} (α : Fin (k + 1) → ℝ) :
    Measurable (dirichletWeight α) := by
  unfold dirichletWeight
  refine Measurable.ite (measurableSet_simplexCorner k) ?_ measurable_const
  refine Measurable.ennreal_ofReal ?_
  refine Finset.univ.measurable_prod fun i _ => ?_
  exact ((measurable_pi_apply i).comp measurable_simplexExtend).pow measurable_const

/-- The **Dirichlet normalization** `Z(α) = ∫⁻ w_α dLeb`. Conjugacy needs only `0 < Z < ∞`;
the closed form `∏Γ(αᵢ)/Γ(∑αᵢ)` is a stretch goal. -/
noncomputable def dirichletZ {k : ℕ} (α : Fin (k + 1) → ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, dirichletWeight α θ

/-- The **Dirichlet distribution** in the corner parametrization (Robert Appendix A.8). Junk: the
zero measure when `Z(α) ∈ {0, ∞}` (excluded for `α > 0` by `dirichletZ_pos`/`dirichletZ_lt_top`). -/
noncomputable def dirichletMeasure {k : ℕ} (α : Fin (k + 1) → ℝ) : Measure (Fin k → ℝ) :=
  (dirichletZ α)⁻¹ • (volume : Measure (Fin k → ℝ)).withDensity (dirichletWeight α)

/-- One-dimensional Beta integral in `ℝ≥0∞` form, derived from the pinned Beta-distribution
normalization: `∫⁻ t in Ioo 0 1, ofReal (t^(a−1) (1−t)^(b−1)) = ofReal (B(a, b))`. -/
theorem lintegral_Ioo_rpow_mul_rpow {a b : ℝ}
    -- USER-INPUT: positive shape parameters; Robert Appendix A.3
    (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (b - 1))
      = ENNReal.ofReal (ProbabilityTheory.beta a b) := by
  have hc : 0 < ProbabilityTheory.beta a b := ProbabilityTheory.beta_pos ha hb
  set I := ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (b - 1)) with hI
  have key : ENNReal.ofReal (1 / ProbabilityTheory.beta a b) * I = 1 := by
    have h1 := ProbabilityTheory.lintegral_betaPDF_eq_one ha hb
    rw [ProbabilityTheory.lintegral_betaPDF] at h1
    rw [hI, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← h1]
    apply lintegral_congr
    intro t
    dsimp only
    rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr hc.le)]
    congr 1
    ring
  calc I = ENNReal.ofReal (ProbabilityTheory.beta a b)
            * (ENNReal.ofReal (1 / ProbabilityTheory.beta a b) * I) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_one_div, div_self hc.ne',
            ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal (ProbabilityTheory.beta a b) := by rw [key, mul_one]

/-- The Dirichlet normalization is positive for positive parameters (sub-box lower bound). -/
theorem dirichletZ_pos {k : ℕ} {α : Fin (k + 1) → ℝ}
    -- USER-INPUT: positive Dirichlet parameters; Robert Appendix A.8
    (hα : ∀ i, 0 < α i) :
    0 < dirichletZ α := by
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set lo : ℝ := 1 / (2 * ((k : ℝ) + 1)) with hlo
  set hi : ℝ := 1 / ((k : ℝ) + 1) with hhi
  have hlopos : 0 < lo := by rw [hlo]; positivity
  have hlohi : lo < hi := by
    rw [hlo, hhi]; exact one_div_lt_one_div_of_lt hkpos (by linarith)
  set B : Set (Fin k → ℝ) := Set.univ.pi (fun _ => Set.Ioo lo hi) with hB
  -- On the sub-box `B`, the density is strictly positive: `B ⊆ support wₐ`.
  have hBsub : B ⊆ Function.support (dirichletWeight α) := by
    intro θ hθ
    simp only [hB, Set.mem_univ_pi, Set.mem_Ioo] at hθ
    have hcorner : θ ∈ simplexCorner k := by
      refine ⟨fun i => hlopos.trans (hθ i).1, ?_⟩
      calc ∑ i, θ i ≤ ∑ _i : Fin k, hi := Finset.sum_le_sum fun i _ => (hθ i).2.le
        _ = (k : ℝ) * hi := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ < 1 := by rw [hhi, mul_one_div, div_lt_one hkpos]; linarith
    have hpos : ∀ i, 0 < simplexExtend θ i := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [simplexExtend, Fin.snoc_last]; linarith [hcorner.2]
      · intro j; rw [simplexExtend, Fin.snoc_castSucc]; exact hcorner.1 j
    have : dirichletWeight α θ ≠ 0 := by
      rw [dirichletWeight, if_pos hcorner, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hpos i) _
    exact this
  rw [dirichletZ, lintegral_pos_iff_support (measurable_dirichletWeight α)]
  refine lt_of_lt_of_le ?_ (measure_mono hBsub)
  rw [hB, volume_pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  rw [Real.volume_Ioo, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact sub_pos.mpr hlohi

/-- The Dirichlet normalization is finite for positive parameters (coordinate-peel recursion down
to the one-dimensional Beta integral). -/
theorem dirichletZ_lt_top {k : ℕ} {α : Fin (k + 1) → ℝ}
    -- USER-INPUT: positive Dirichlet parameters; Robert Appendix A.8
    (hα : ∀ i, 0 < α i) :
    dirichletZ α < ∞ := by
  -- SANCTIONED DEBT (batch's single accepted `sorry`). The finiteness of the Dirichlet
  -- normalization is the genuine analytic content of this file: it requires the coordinate-peel
  -- recursion `Z(α) = B(α₀, ∑_{i≥1} αᵢ) · Z(tail α)`, obtained by (1) splitting the first
  -- coordinate with `MeasureTheory.measurePreserving_piFinSuccAbove volume 0` + Tonelli, then
  -- (2) the Haar rescaling `η = (1 − t) • ζ` on `Fin k → ℝ` (`map_addHaar_smul`, Jacobian
  -- `(1 − t)^k`), collecting the `(1 − t)` powers via `Real.rpow_add` (positive base on the open
  -- corner) into the exponent `∑_{i≥1} αᵢ − 1`, bounding the `t`-marginal by
  -- `lintegral_Ioo_rpow_mul_rpow` (target 8) and closing by induction on `k` (base `k = 0`:
  -- `Z = 1`). This peel is several hours of measure-theoretic bookkeeping and is left as the
  -- documented debt per the batch plan; every other statement in the touch-set is closed.
  sorry

/-- The Dirichlet distribution is a probability measure for positive parameters. -/
theorem isProbabilityMeasure_dirichletMeasure {k : ℕ} {α : Fin (k + 1) → ℝ}
    -- USER-INPUT: positive Dirichlet parameters; Robert Appendix A.8
    (hα : ∀ i, 0 < α i) :
    IsProbabilityMeasure (dirichletMeasure α) := by
  refine ⟨?_⟩
  rw [dirichletMeasure, Measure.smul_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← dirichletZ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (dirichletZ_pos hα).ne' (dirichletZ_lt_top hα).ne

end StatLean.Bayesian
