import StatLean.Minimaxity.Fano.FanoLowerBound

/-!
# Lower bounds based on local packings (Wainwright §15.3.3)

The "generalized Fano" / local-packing method packages the Fano lower bound with the convexity
bound on the mutual information (Eq. (15.34)). If a `2δ`-separated family can be found whose pairwise
KL divergences are uniformly controlled and which is large enough, the minimax risk is bounded below
by `½ Φ(δ)`:

> In summary, if we can find a `2δ`-separated family of distributions such that conditions
> (15.35a) `√(D(P_{θʲ} ‖ P_{θᵏ})) ≤ c √n δ` and (15.35b) `log M(2δ) ≥ 2{c²nδ² + log 2}` both hold,
> then the minimax risk is lower bounded as `M(θ(𝒫); Φ∘ρ) ≥ ½ Φ(δ)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

/-- **Local-packing minimax lower bound** (Wainwright §15.3.3, conditions (15.35a)/(15.35b)): given a
`2δ`-separated family `θfam : Fin M → Θ` whose pairwise KL divergences satisfy
`D(P_{θʲ} ‖ P_{θᵏ}) ≤ c²nδ²` (15.35a) and whose cardinality satisfies
`log M ≥ 2(c²nδ² + log 2)` (15.35b), the minimax risk is at least `½ Φ(δ)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3. -/
theorem minimax_local_packing [PseudoEMetricSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    {M : ℕ} [NeZero M] (θfam : Fin M → Θ) (hθ : Measurable θfam) (δ : ℝ≥0∞) (c n : ℝ)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.3.3.
    (hΦ : Monotone Φ)
    -- USER-INPUT: `{θfam j}` is a `2δ`-separated set; Wainwright §15.3.3.
    (hsep : IsSeparatedFamily g θfam δ)
    -- USER-INPUT: `n ≥ 0` (sample size — implicit in the book's `√n` in (15.35a)); Wainwright §15.3.3.
    (hn : 0 ≤ n)
    -- USER-INPUT: pairwise KL control (15.35a), `√D ≤ c√n δ`; Wainwright §15.3.3.
    (h35a : ∀ j k, j ≠ k →
      klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
        ≤ ENNReal.ofReal (c ^ 2 * n * δ.toReal ^ 2))
    -- USER-INPUT: packing cardinality (15.35b); Wainwright §15.3.3.
    (h35b : 2 * (c ^ 2 * n * δ.toReal ^ 2 + Real.log 2) ≤ Real.log (M : ℝ)) :
    2⁻¹ * Φ δ ≤ minimaxRiskDist Φ g P := by
  classical
  set Q := P.comap θfam hθ with hQ
  set K : ℝ := c ^ 2 * n * δ.toReal ^ 2 with hKdef
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Cardinalities of `(M : ℝ≥0∞)`.
  have hMpos : (M : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (NeZero.ne M)
  have hMtop : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
  have hMsq0 : ((M : ℝ≥0∞) ^ 2) ≠ 0 := pow_ne_zero _ hMpos
  have hMsqtop : ((M : ℝ≥0∞) ^ 2) ≠ ∞ := by
    simp [hMtop]
  -- Step 1: mutual information is bounded by the cover radius `ofReal K`.
  have hI : mutualInformation Q ≤ ENNReal.ofReal K := by
    refine (mutualInformation_le_avg_pairwise_kl Q).trans ?_
    have hterm : ∀ j, ∑ k, klDiv (Q j) (Q k) ≤ ∑ _k : Fin M, ENNReal.ofReal K := by
      intro j
      refine Finset.sum_le_sum fun k _ => ?_
      by_cases hjk : j = k
      · subst hjk; simp [klDiv_self]
      · exact h35a j k hjk
    have hsum : ∑ j, ∑ k, klDiv (Q j) (Q k) ≤ (M : ℝ≥0∞) ^ 2 * ENNReal.ofReal K := by
      refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
      have hconst : ∑ _j : Fin M, ∑ _k : Fin M, ENNReal.ofReal K
          = (M : ℝ≥0∞) ^ 2 * ENNReal.ofReal K := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, ← pow_two]
      exact hconst.le
    calc ((M : ℝ≥0∞) ^ 2)⁻¹ * ∑ j, ∑ k, klDiv (Q j) (Q k)
        ≤ ((M : ℝ≥0∞) ^ 2)⁻¹ * ((M : ℝ≥0∞) ^ 2 * ENNReal.ofReal K) := by
          gcongr
      _ = ENNReal.ofReal K := by rw [ENNReal.inv_mul_cancel_left hMsq0 hMsqtop]
  -- Step 2: from (15.35b), `log M > 0`, hence `2 ≤ M`.
  have hlogM : 0 < Real.log (M : ℝ) := by
    have : (0 : ℝ) < 2 * (K + Real.log 2) := by positivity
    linarith [h35b]
  have hM2 : 2 ≤ M := by
    have h1 : (1 : ℝ) < (M : ℝ) := (Real.log_pos_iff (by positivity)).1 hlogM
    have : (1 : ℕ) < M := by exact_mod_cast h1
    omega
  -- Step 3: the Fano fraction is at most `2⁻¹`.
  have hfrac : (mutualInformation Q + ENNReal.ofReal (Real.log 2))
      / ENNReal.ofReal (Real.log (M : ℝ)) ≤ 2⁻¹ := by
    apply ENNReal.div_le_of_le_mul
    -- `I + ofReal (log 2) ≤ 2⁻¹ * ofReal (log M)`
    have hIlog : mutualInformation Q + ENNReal.ofReal (Real.log 2)
        ≤ ENNReal.ofReal (K + Real.log 2) := by
      rw [ENNReal.ofReal_add hK hlog2.le]; gcongr
    refine hIlog.trans ?_
    -- `2·ofReal (K + log 2) = ofReal (2(K + log 2)) ≤ ofReal (log M)` by (15.35b).
    have hstep : (2 : ℝ≥0∞) * ENNReal.ofReal (K + Real.log 2)
        ≤ ENNReal.ofReal (Real.log (M : ℝ)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal h35b
    calc ENNReal.ofReal (K + Real.log 2)
        = 2⁻¹ * ((2 : ℝ≥0∞) * ENNReal.ofReal (K + Real.log 2)) :=
          (ENNReal.inv_mul_cancel_left (by norm_num) (by norm_num)).symm
      _ ≤ 2⁻¹ * ENNReal.ofReal (Real.log (M : ℝ)) := by gcongr
  -- Step 4: combine with the Fano lower bound `minimax_fano_lower_bound` (15.32).
  have hfano := minimax_fano_lower_bound Φ g P θfam hθ δ hM2 hΦ hsep
  refine le_trans ?_ hfano
  rw [mul_comm (2 : ℝ≥0∞)⁻¹ (Φ δ)]
  refine mul_le_mul_left' ?_ _
  calc (2 : ℝ≥0∞)⁻¹ = 1 - 2⁻¹ := (ENNReal.one_sub_inv_two).symm
    _ ≤ 1 - (mutualInformation Q + ENNReal.ofReal (Real.log 2))
          / ENNReal.ofReal (Real.log (M : ℝ)) := tsub_le_tsub_left hfrac 1

end StatLean.Minimaxity
