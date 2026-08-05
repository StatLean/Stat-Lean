import StatLean.StatisticalModels.Survival.Cox.Defs
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Convex.Basic

/-!
# The Cox partial likelihood — definition and the discrete conditional theorem

Cox's partial likelihood on right-censored covariate data
`dz : Fin n → (ℝ × Bool) × ℝᵖ` (observed time, event indicator, covariate):

* `coxRiskSet dz t` — the risk set at `t`; `HasNoTies dz` — the no-ties condition;
* `coxPartialLikelihood β dz = ∏_{i : Δᵢ=1} e^{⟪β,zᵢ⟫} / ∑_{j ∈ R(tᵢ)} e^{⟪β,zⱼ⟫}`
  (`Cox72 §5` Eq. (12)) and `coxPartialLogLik`;
* **S5.5, the discrete conditional theorem** (`Cox72 §6`): in Cox's discrete logistic model
  — independent Bernoulli failures over a risk set with odds proportional to `e^{⟪β,z⟫}` —
  the conditional probability that subject `i` is the failure, given exactly one failure,
  is `e^{⟪β,zᵢ⟫} / ∑_{j∈R} e^{⟪β,zⱼ⟫}`: an exact, finite theorem identifying the partial-
  likelihood factor as a genuine conditional probability;
* **S5.7** concavity of the partial log-likelihood (via the `convexOn_logSumExp` brick) —
  the optimization-friendliness of Cox estimation.

*Deliberate non-theorems, documented:* the continuous-time version of S5.5 (the conditional
*density* of the failing subject given the risk set) needs conditional-density calculus for
order statistics — named future debt, `Cox75` / S. A. Murphy and A. W. van der Vaart, "On
profile likelihood," *JASA* **95** (2000), 449–465. The factor-by-factor assembly of the
product over event times as iterated conditioning (Cox's own §5 narrative) is a modeling
bridge with no additional mathematical content beyond S5.5 — narrated here, not formalized.

**Reference.** `Cox72` §5 (Eq. (12)), §6 (the discrete logistic conditional); D. R. Cox,
"Partial likelihood," *Biometrika* **62** (1975), 269–276 (`Cox75`); ABGK §VII.2 (verify §).

**Proof formalization notes.** S5.5 is a finite computation over Bernoulli cubes:
`Measure.pi` of `PMF.bernoulli`s, `ProbabilityTheory.cond`, and `Finset` algebra — the
one-failure event probability factorizes as `p_i ∏_{j≠i}(1−p_j)`; dividing by the sum and
substituting the odds `p_j/(1−p_j) = θ₀ e^{⟪β,z_j⟫}` cancels `θ₀` and the common
`∏(1−p_j)` factor (needs `p_j < 1`, USER-INPUT). Denominator positivity of the partial
likelihood: each subject is in its own risk set.

**Bibliographic comments.** The interpretation controversy (is the partial likelihood a
likelihood?) is settled operationally by `Cox75` and the martingale/profile-likelihood
readings (ABGK VII.2; Murphy–van der Vaart 2000).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal InnerProductSpace NNReal

namespace StatLean.StatisticalModels.Survival

variable {p n : ℕ}

/-- The **risk set** at time `t`: subjects still under observation, `R(t) = {j : t ≤ T̃ⱼ}`
(`Cox72 §5`). -/
noncomputable def coxRiskSet (dz : Fin n → (ℝ × Bool) × EuclideanSpace ℝ (Fin p)) (t : ℝ) :
    Finset (Fin n) :=
  univ.filter fun j => t ≤ (dz j).1.1

/-- **No ties** among observed event times (`Cox72 §5` treats the untied case; tie
corrections are future work). -/
def HasNoTies (dz : Fin n → (ℝ × Bool) × EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ i j, (dz i).1.2 = true → (dz j).1.2 = true → (dz i).1.1 = (dz j).1.1 → i = j

/-- The **Cox partial likelihood** (`Cox72 §5` Eq. (12)):
`∏_{i : Δᵢ=1} e^{⟪β,zᵢ⟫} / ∑_{j ∈ R(tᵢ)} e^{⟪β,zⱼ⟫}`. -/
noncomputable def coxPartialLikelihood (β : EuclideanSpace ℝ (Fin p))
    (dz : Fin n → (ℝ × Bool) × EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∏ i ∈ univ.filter fun i => (dz i).1.2 = true,
    Real.exp ⟪β, (dz i).2⟫_ℝ / ∑ j ∈ coxRiskSet dz (dz i).1.1, Real.exp ⟪β, (dz j).2⟫_ℝ

/-- The Cox partial log-likelihood. -/
noncomputable def coxPartialLogLik (β : EuclideanSpace ℝ (Fin p))
    (dz : Fin n → (ℝ × Bool) × EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i ∈ univ.filter fun i => (dz i).1.2 = true,
    (⟪β, (dz i).2⟫_ℝ - Real.log (∑ j ∈ coxRiskSet dz (dz i).1.1, Real.exp ⟪β, (dz j).2⟫_ℝ))

/-- Each event subject belongs to its own risk set — partial-likelihood denominators are
positive. -/
theorem sum_exp_riskSet_pos (β : EuclideanSpace ℝ (Fin p))
    (dz : Fin n → (ℝ × Bool) × EuclideanSpace ℝ (Fin p)) (i : Fin n) :
    0 < ∑ j ∈ coxRiskSet dz (dz i).1.1, Real.exp ⟪β, (dz j).2⟫_ℝ :=
  Finset.sum_pos' (fun _ _ => (Real.exp_pos _).le) ⟨i, by simp [coxRiskSet], Real.exp_pos _⟩

/-- The partial likelihood is positive. -/
theorem coxPartialLikelihood_pos (β : EuclideanSpace ℝ (Fin p))
    (dz : Fin n → (ℝ × Bool) × EuclideanSpace ℝ (Fin p)) :
    0 < coxPartialLikelihood β dz :=
  Finset.prod_pos fun i _ => div_pos (Real.exp_pos _) (sum_exp_riskSet_pos β dz i)

/-- log of the partial likelihood is the partial log-likelihood. -/
theorem log_coxPartialLikelihood (β : EuclideanSpace ℝ (Fin p))
    (dz : Fin n → (ℝ × Bool) × EuclideanSpace ℝ (Fin p)) :
    Real.log (coxPartialLikelihood β dz) = coxPartialLogLik β dz := by
  rw [coxPartialLikelihood, coxPartialLogLik,
    Real.log_prod fun i _ => (div_pos (Real.exp_pos _) (sum_exp_riskSet_pos β dz i)).ne']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_div (Real.exp_ne_zero _) (sum_exp_riskSet_pos β dz i).ne', Real.log_exp]

/-- **S5.5, the discrete conditional theorem** (`Cox72 §6`): in the discrete logistic model —
independent Bernoulli failure indicators over the risk set `R`, with odds
`pⱼ/(1−pⱼ) = θ₀·e^{⟪β,zⱼ⟫}` — the conditional probability that subject `i` fails, given
exactly one failure in `R`, is the partial-likelihood factor
`e^{⟪β,zᵢ⟫}/∑_{j∈R} e^{⟪β,zⱼ⟫}`. Exact and finite; `θ₀` cancels. -/
theorem cond_single_failure (R : Finset (Fin n)) (z : Fin n → EuclideanSpace ℝ (Fin p))
    (β : EuclideanSpace ℝ (Fin p)) (prob : Fin n → ℝ≥0)
    -- LEAN-ONLY: Bernoulli parameters are probabilities
    (h1 : ∀ j, prob j ≤ 1) {θ₀ : ℝ}
    -- USER-INPUT: positive common odds factor; Cox72 §6
    (hθ : 0 < θ₀)
    -- USER-INPUT: proportional odds on the risk set; Cox72 §6
    (hodds : ∀ j ∈ R, (prob j : ℝ) / (1 - (prob j : ℝ)) = θ₀ * Real.exp ⟪β, z j⟫_ℝ)
    -- USER-INPUT: no sure failures (odds finite); Cox72 §6
    (hlt : ∀ j ∈ R, (prob j : ℝ) < 1)
    {i : Fin n} (hi : i ∈ R) :
    (Measure.pi fun j => (PMF.bernoulli (prob j) (h1 j)).toMeasure)[|{ω |
        (R.filter fun j => ω j = true).card = 1}] {ω | ω i = true}
      = ENNReal.ofReal
          (Real.exp ⟪β, z i⟫_ℝ / ∑ j ∈ R, Real.exp ⟪β, z j⟫_ℝ) := by
  sorry

/-- The one-failure events partition: conditioning on "exactly one failure" and asking which
subject failed sums the S5.5 factors to one (sanity identity for the conditional family). -/
theorem sum_partialFactor_eq_one (R : Finset (Fin n)) (z : Fin n → EuclideanSpace ℝ (Fin p))
    (β : EuclideanSpace ℝ (Fin p))
    -- USER-INPUT: nonempty risk set; Cox72 §6
    (hR : R.Nonempty) :
    ∑ i ∈ R, Real.exp ⟪β, z i⟫_ℝ / ∑ j ∈ R, Real.exp ⟪β, z j⟫_ℝ = 1 := by
  rw [← Finset.sum_div, div_self (Finset.sum_pos (fun _ _ => Real.exp_pos _) hR).ne']

/-- **`convexOn_logSumExp` brick**: `β ↦ log ∑_{j∈R} e^{⟪β, zⱼ⟫}` is convex (Hölder;
Boyd–Vandenberghe §3.1.5). -/
theorem convexOn_logSumExp (R : Finset (Fin n)) (z : Fin n → EuclideanSpace ℝ (Fin p))
    -- USER-INPUT: nonempty index set (log of a positive sum); Boyd–Vandenberghe §3.1.5
    (hR : R.Nonempty) :
    ConvexOn ℝ Set.univ
      (fun β : EuclideanSpace ℝ (Fin p) => Real.log (∑ j ∈ R, Real.exp ⟪β, z j⟫_ℝ)) := by
  refine ⟨convex_univ, fun β₁ _ β₂ _ a b ha hb hab => ?_⟩
  have hX : (0 : ℝ) < ∑ j ∈ R, Real.exp ⟪β₁, z j⟫_ℝ :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) hR
  have hY : (0 : ℝ) < ∑ j ∈ R, Real.exp ⟪β₂, z j⟫_ℝ :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) hR
  -- Hölder in normalized form: `(x/X)^a (y/Y)^b ≤ a(x/X) + b(y/Y)`, summed over the risk set
  have hterm : ∀ j ∈ R, Real.exp ⟪a • β₁ + b • β₂, z j⟫_ℝ
      / ((∑ k ∈ R, Real.exp ⟪β₁, z k⟫_ℝ) ^ a * (∑ k ∈ R, Real.exp ⟪β₂, z k⟫_ℝ) ^ b)
      ≤ a * (Real.exp ⟪β₁, z j⟫_ℝ / ∑ k ∈ R, Real.exp ⟪β₁, z k⟫_ℝ)
        + b * (Real.exp ⟪β₂, z j⟫_ℝ / ∑ k ∈ R, Real.exp ⟪β₂, z k⟫_ℝ) := by
    intro j _
    -- the numerator splits into the two rpow factors (`exp` of a convex combination)
    have hnum : Real.exp ⟪a • β₁ + b • β₂, z j⟫_ℝ
        = Real.exp ⟪β₁, z j⟫_ℝ ^ a * Real.exp ⟪β₂, z j⟫_ℝ ^ b := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, Real.exp_add,
        mul_comm a ⟪β₁, z j⟫_ℝ, mul_comm b ⟪β₂, z j⟫_ℝ, Real.exp_mul, Real.exp_mul]
    have hsplit : Real.exp ⟪a • β₁ + b • β₂, z j⟫_ℝ
        / ((∑ k ∈ R, Real.exp ⟪β₁, z k⟫_ℝ) ^ a * (∑ k ∈ R, Real.exp ⟪β₂, z k⟫_ℝ) ^ b)
        = (Real.exp ⟪β₁, z j⟫_ℝ / ∑ k ∈ R, Real.exp ⟪β₁, z k⟫_ℝ) ^ a
          * (Real.exp ⟪β₂, z j⟫_ℝ / ∑ k ∈ R, Real.exp ⟪β₂, z k⟫_ℝ) ^ b := by
      rw [Real.div_rpow (Real.exp_pos _).le hX.le, Real.div_rpow (Real.exp_pos _).le hY.le,
        div_mul_div_comm, hnum]
    rw [hsplit]
    exact Real.geom_mean_le_arith_mean2_weighted ha hb (by positivity) (by positivity) hab
  have hsum : (∑ j ∈ R, Real.exp ⟪a • β₁ + b • β₂, z j⟫_ℝ)
      ≤ (∑ k ∈ R, Real.exp ⟪β₁, z k⟫_ℝ) ^ a * (∑ k ∈ R, Real.exp ⟪β₂, z k⟫_ℝ) ^ b := by
    have hpos : (0 : ℝ) < (∑ k ∈ R, Real.exp ⟪β₁, z k⟫_ℝ) ^ a
        * (∑ k ∈ R, Real.exp ⟪β₂, z k⟫_ℝ) ^ b := by positivity
    rw [← div_le_one hpos, Finset.sum_div]
    calc ∑ j ∈ R, Real.exp ⟪a • β₁ + b • β₂, z j⟫_ℝ
          / ((∑ k ∈ R, Real.exp ⟪β₁, z k⟫_ℝ) ^ a * (∑ k ∈ R, Real.exp ⟪β₂, z k⟫_ℝ) ^ b)
        ≤ ∑ j ∈ R, (a * (Real.exp ⟪β₁, z j⟫_ℝ / ∑ k ∈ R, Real.exp ⟪β₁, z k⟫_ℝ)
            + b * (Real.exp ⟪β₂, z j⟫_ℝ / ∑ k ∈ R, Real.exp ⟪β₂, z k⟫_ℝ)) :=
          Finset.sum_le_sum hterm
      _ = 1 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div,
            ← Finset.sum_div, div_self hX.ne', div_self hY.ne', mul_one, mul_one, hab]
  calc Real.log (∑ j ∈ R, Real.exp ⟪a • β₁ + b • β₂, z j⟫_ℝ)
      ≤ Real.log ((∑ k ∈ R, Real.exp ⟪β₁, z k⟫_ℝ) ^ a
          * (∑ k ∈ R, Real.exp ⟪β₂, z k⟫_ℝ) ^ b) :=
        Real.log_le_log (Finset.sum_pos (fun _ _ => Real.exp_pos _) hR) hsum
    _ = a * Real.log (∑ k ∈ R, Real.exp ⟪β₁, z k⟫_ℝ)
        + b * Real.log (∑ k ∈ R, Real.exp ⟪β₂, z k⟫_ℝ) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hX, Real.log_rpow hY,
        mul_comm a, mul_comm b]

/-- A finite sum of functions concave on the whole space is concave. -/
private theorem concaveOn_univ_sum {E ι : Type*} [AddCommMonoid E] [Module ℝ E]
    (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, ConcaveOn ℝ (Set.univ : Set E) (f i)) :
    ConcaveOn ℝ (Set.univ : Set E) fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using concaveOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E))
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- **S5.7, concavity of the Cox partial log-likelihood** (`Cox72 §5`): a sum of linear
terms minus log-sum-exps. -/
theorem concaveOn_coxPartialLogLik (dz : Fin n → (ℝ × Bool) × EuclideanSpace ℝ (Fin p)) :
    ConcaveOn ℝ Set.univ (fun β => coxPartialLogLik β dz) := by
  simp only [coxPartialLogLik]
  refine concaveOn_univ_sum _ _ fun i _ => ?_
  have hlin : ConcaveOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin p)))
      fun β => ⟪β, (dz i).2⟫_ℝ := by
    have he : (fun β : EuclideanSpace ℝ (Fin p) => ⟪β, (dz i).2⟫_ℝ)
        = fun β => (innerSL ℝ ((dz i).2)).toLinearMap β := by
      funext β; exact real_inner_comm _ _
    rw [he]
    exact LinearMap.concaveOn _ convex_univ
  have hlog := convexOn_logSumExp (coxRiskSet dz (dz i).1.1) (fun j => (dz j).2)
    ⟨i, by simp [coxRiskSet]⟩ (p := p)
  have hcongr : (fun β : EuclideanSpace ℝ (Fin p) => ⟪β, (dz i).2⟫_ℝ
      - Real.log (∑ j ∈ coxRiskSet dz (dz i).1.1, Real.exp ⟪β, (dz j).2⟫_ℝ))
      = (fun β : EuclideanSpace ℝ (Fin p) => ⟪β, (dz i).2⟫_ℝ)
        + -fun β : EuclideanSpace ℝ (Fin p) =>
            Real.log (∑ j ∈ coxRiskSet dz (dz i).1.1, Real.exp ⟪β, (dz j).2⟫_ℝ) := by
    funext β; simp [sub_eq_add_neg]
  rw [hcongr]
  exact hlin.add hlog.neg

end StatLean.StatisticalModels.Survival
