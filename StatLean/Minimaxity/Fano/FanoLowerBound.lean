import StatLean.Minimaxity.EstimationToTesting
import StatLean.Minimaxity.Fano.MutualInformation

/-!
# Fano's method for minimax lower bounds (Wainwright §15.3.2)

Fano's inequality lower bounds the error probability of an M-ary test by its mutual information,
```
inf_ψ ℚ[ψ(Z) ≠ J] ≥ 1 − (I(Z; J) + log 2)/log M           (Eq. (15.31)),
```
and combining it with the estimation-to-testing reduction (Proposition 15.1) yields the Fano
minimax lower bound (Proposition 15.12),
```
M(θ(𝒫); Φ∘ρ) ≥ Φ(δ) (1 − (I(Z; J) + log 2)/log M)          (Eq. (15.32)).
```

The proof of Fano's inequality (Eq. (15.31)) goes through the Shannon-entropy form (Eq. (15.61)) of
the appendix `ForMathlib/Entropy.lean`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

/-- **Entropy form of Fano's inequality** (Wainwright Eq. (15.61)), packaged in the kernel-KL /
Bayes-risk encodings used by this module. Writing `L = log M`, `I = I(Z; J)`,
`q = multiwayTestingError Q` and `c = log 2`, the standard Fano chain
`H(J|Z) ≤ h(q) + q·log(M−1) ≤ log 2 + q·log M` together with `I = H(J) − H(J|Z) = log M − H(J|Z)`
rearranges to
```
log M ≤ I(Z; J) + log 2 + q · log M.
```
This is the single genuinely-hard crux of `fano_inequality`: it bridges `mutualInformation`
(the kernel-KL encoding) and `multiwayTestingError` (the Bayes-risk encoding) to the discrete
Shannon-entropy machinery of `ForMathlib/Entropy.lean` (`discreteMutualInfo`,
`discreteCondEntropy_le_entropy`) via the discrete posterior of `J` given the continuous
observation `Z` (built through `ProbabilityTheory.condDistrib` / disintegration of the joint
`(Z, J)` law). The surrounding `ℝ≥0∞` rearrangement (division and truncated subtraction) is
discharged in `fano_inequality` below. -/
private lemma fano_entropy_continuous {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    (hM : 2 ≤ M) :
    ENNReal.ofReal (Real.log (M : ℝ))
      ≤ mutualInformation Q + ENNReal.ofReal (Real.log 2)
          + multiwayTestingError Q * ENNReal.ofReal (Real.log (M : ℝ)) := by
  -- TODO(mmx): entropy Fano (Eq. (15.61)). Disintegrate the joint `(Z, J)` law to get the
  -- discrete posterior `J | Z`, apply `discreteCondEntropy_le_entropy` to bound
  -- `H(J|Z) ≤ h(q) + q·log(M−1)`, use `discreteEntropy_le_log_card` for `h(q) ≤ log 2`, and
  -- `I = log M − H(J|Z)`. Named debt.
  sorry

/-- **Fano's inequality** (Wainwright Eq. (15.31)): the error probability of the M-ary test is
lower bounded by `1 − (I(Z; J) + log 2)/log M`, where `I(Z; J)` is the mutual information.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.2, Eq. (15.31). -/
theorem fano_inequality {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    -- USER-INPUT: at least two hypotheses, so `log M > 0`; Wainwright §15.3.2.
    (hM : 2 ≤ M) :
    1 - (mutualInformation Q + ENNReal.ofReal (Real.log 2)) / ENNReal.ofReal (Real.log (M : ℝ))
      ≤ multiwayTestingError Q := by
  -- `ℝ≥0∞` rearrangement of the entropy-form bound `L ≤ I + c + q·L` into `1 − (I+c)/L ≤ q`,
  -- using `0 < L < ∞` (since `log M > 0` for `M ≥ 2`).
  have hbound := fano_entropy_continuous Q hM
  have hMr : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (show 1 < M by omega)
  have hLpos : 0 < ENNReal.ofReal (Real.log (M : ℝ)) :=
    ENNReal.ofReal_pos.mpr (Real.log_pos hMr)
  have hLtop : ENNReal.ofReal (Real.log (M : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  set L := ENNReal.ofReal (Real.log (M : ℝ)) with hL
  set I := mutualInformation Q with hI
  set c := ENNReal.ofReal (Real.log 2) with hc
  set q := multiwayTestingError Q with hq
  -- goal: `1 - (I + c) / L ≤ q`
  rw [tsub_le_iff_right]
  -- goal: `1 ≤ q + (I + c) / L`
  calc (1 : ℝ≥0∞)
      = L / L := (ENNReal.div_self hLpos.ne' hLtop).symm
    _ ≤ (I + c + q * L) / L := by gcongr
    _ = (I + c) / L + q * L / L := by rw [ENNReal.add_div]
    _ = (I + c) / L + q := by rw [mul_div_assoc, ENNReal.div_self hLpos.ne' hLtop, mul_one]
    _ = q + (I + c) / L := add_comm _ _

/-- **Fano minimax lower bound** (Wainwright Proposition 15.12, Eq. (15.32)): for an increasing
distortion `Φ` and a `2δ`-separated family `θfam : Fin M → Θ`,
`M(θ(𝒫); Φ∘ρ) ≥ Φ(δ)(1 − (I(Z; J) + log 2)/log M)`, where `I(Z; J)` is the mutual information of the
induced sub-model.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.2, Proposition 15.12. -/
theorem minimax_fano_lower_bound [PseudoEMetricSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    {M : ℕ} [NeZero M] (θfam : Fin M → Θ) (hθ : Measurable θfam) (δ : ℝ≥0∞)
    -- USER-INPUT: at least two hypotheses; Wainwright §15.3.2, Prop 15.12.
    (hM : 2 ≤ M)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.3.2, Prop 15.12.
    (hΦ : Monotone Φ)
    -- USER-INPUT: `{θfam j}` is a `2δ`-separated set; Wainwright §15.3.2, Prop 15.12.
    (hsep : IsSeparatedFamily g θfam δ) :
    Φ δ * (1 - (mutualInformation (P.comap θfam hθ) + ENNReal.ofReal (Real.log 2))
                / ENNReal.ofReal (Real.log (M : ℝ)))
      ≤ minimaxRiskDist Φ g P :=
  -- `Φ δ · (Fano bound) ≤ Φ δ · (testing error) ≤ minimax risk`: Fano's inequality (15.31) bounds
  -- the bracket by the M-ary testing error, and the estimation-to-testing reduction (Prop 15.1)
  -- turns that into the minimax risk.
  calc Φ δ * (1 - (mutualInformation (P.comap θfam hθ) + ENNReal.ofReal (Real.log 2))
                  / ENNReal.ofReal (Real.log (M : ℝ)))
      ≤ Φ δ * multiwayTestingError (P.comap θfam hθ) :=
        mul_le_mul_left' (fano_inequality (P.comap θfam hθ) hM) _
    _ ≤ minimaxRiskDist Φ g P := minimax_ge_testing_error Φ g P θfam hθ δ hΦ hsep

end StatLean.Minimaxity
