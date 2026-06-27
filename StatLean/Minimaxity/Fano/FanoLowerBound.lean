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

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

/-- Pointwise expansion of `negMulLog` under the uniform-prior rescaling `x ↦ M⁻¹ · x` (with
`x = (dQⱼ/dμ)(z) ≥ 0` the component density against the mixture). The identity
`negMulLog (M⁻¹ x) = M⁻¹ (log M) x − M⁻¹ (x log x)` is the per-`j`, per-`z` algebra that turns the
posterior entropy `∑ⱼ negMulLog (M⁻¹ rⱼ)` into `log M − M⁻¹ ∑ⱼ rⱼ log rⱼ` (after using
`∑ⱼ rⱼ = M`). The `x = 0` boundary is consistent because `negMulLog 0 = 0 = 0·log 0`. -/
private lemma negMulLog_inv_mul {M : ℕ} (hM : (M : ℝ) ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    Real.negMulLog ((M : ℝ)⁻¹ * x)
      = (M : ℝ)⁻¹ * Real.log (M : ℝ) * x - (M : ℝ)⁻¹ * (x * Real.log x) := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0]; simp
  · simp only [Real.negMulLog_def]
    rw [Real.log_mul (inv_ne_zero hM) hx0.ne', Real.log_inv]
    ring

/-- Radon–Nikodym derivative of a finite sum of finite measures splits over the sum, a.e. against a
common dominating measure. (Local copy of the same fact used in `Fano/MutualInformation.lean`;
proved by induction from the two-term `rnDeriv_add'`.) -/
private lemma rnDeriv_finset_sum_ae {α : Type*} [MeasurableSpace α] {ι : Type*} (s : Finset ι)
    (P : ι → Measure α) (ξ : Measure α) [SigmaFinite ξ] [∀ i, IsFiniteMeasure (P i)] :
    (∑ i ∈ s, P i).rnDeriv ξ =ᵐ[ξ] ∑ i ∈ s, (P i).rnDeriv ξ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Measure.rnDeriv_add' (P i) (∑ k ∈ s, P k) ξ, ih] with x h1 h2
      rw [Finset.sum_insert hi, Pi.add_apply, h1, Pi.add_apply, h2]

/-- **Conditional Shannon entropy `H(J | Z)`** of the M-ary testing problem, built concretely from
the component densities `rⱼ(z) = d(Q j)/d(mixture Q)(z)`. With the uniform prior the posterior mass
is `ℙ(J = j | Z = z) = M⁻¹ rⱼ(z)`, so
`H(J | Z) = ∫ z, ∑ⱼ negMulLog (M⁻¹ rⱼ(z)) ∂(mixture Q)`. This is `H(J|Z)` of Wainwright's
appendix (Def. 15.25 specialised to the testing posterior), phrased without the `posterior` kernel
so that the mutual-information identity below is a pure Radon–Nikodym computation. -/
private noncomputable def condEntropy {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) : ℝ :=
  ∫ z, (∑ j, Real.negMulLog ((M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)) ∂(mixture Q)

/-- **Mutual-information identity** `I(Z; J) = H(J) − H(J | Z) = log M − H(J | Z)` (Wainwright
Eq. (15.60d) with the uniform prior, so `H(J) = log M`). The genuinely-mechanical half of the
entropy form of Fano's inequality: it is a Radon–Nikodym computation, needing only that the mutual
information is finite (so every `klDiv (Q j) (mixture Q)` is finite, i.e. each component is
absolutely continuous with integrable log-likelihood ratio against the mixture).

The proof expands `(mutualInformation Q).toReal = M⁻¹ ∑ⱼ (klDiv (Q j) (mixture Q)).toReal`, writes
each `(klDiv (Q j) (mixture Q)).toReal = ∫ rⱼ log rⱼ ∂(mixture Q)` via
`toReal_klDiv_of_measure_eq` and the change of variables `integral_rnDeriv_smul`, and matches it
against `condEntropy` after the pointwise `negMulLog_inv_mul` expansion and the a.e. identity
`∑ⱼ rⱼ = M`. -/
private lemma mutualInformation_toReal_eq {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧)
    [IsMarkovKernel Q] (hI : mutualInformation Q ≠ ⊤) :
    (mutualInformation Q).toReal = Real.log (M : ℝ) - condEntropy Q := by
  classical
  haveI hμprob : IsProbabilityMeasure (mixture Q) := by unfold mixture; infer_instance
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hMne : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hMtop : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
  have hMinv_ne : (M : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hMtop
  -- each component is absolutely continuous w.r.t. the mixture
  have hac : ∀ j, Q j ≪ mixture Q := fun j => by
    rw [mixture_eq_inv_smul_sum]
    exact (Measure.absolutelyContinuous_of_le
      (Finset.single_le_sum (f := fun k => Q k) (fun i _ => Measure.zero_le _)
        (Finset.mem_univ j))).smul_right hMinv_ne
  -- finiteness of the mutual information forces every KL term finite
  have hsum_ne : (∑ j, klDiv (Q j) (mixture Q)) ≠ ⊤ := by
    intro hcon; exact hI (by rw [mutualInformation, hcon, ENNReal.mul_top hMinv_ne])
  have hfin : ∀ j, klDiv (Q j) (mixture Q) ≠ ⊤ := fun j hcon =>
    hsum_ne (top_le_iff.mp (hcon ▸ Finset.single_le_sum
      (f := fun k => klDiv (Q k) (mixture Q)) (fun i _ => zero_le _) (Finset.mem_univ j)))
  have hint : ∀ j, Integrable (llr (Q j) (mixture Q)) (Q j) := fun j =>
    (klDiv_ne_top_iff.mp (hfin j)).2
  -- per-component integrability of `rⱼ log rⱼ` against the mixture
  have hintμ : ∀ j, Integrable (fun z => ((Q j).rnDeriv (mixture Q) z).toReal *
      Real.log ((Q j).rnDeriv (mixture Q) z).toReal) (mixture Q) := fun j =>
    (integrable_rnDeriv_mul_log_iff (hac j)).mpr (hint j)
  -- each KL term, in real form, is `∫ rⱼ log rⱼ` against the mixture
  have hklj : ∀ j, (klDiv (Q j) (mixture Q)).toReal = ∫ z, ((Q j).rnDeriv (mixture Q) z).toReal *
      Real.log ((Q j).rnDeriv (mixture Q) z).toReal ∂(mixture Q) := by
    intro j
    haveI : IsProbabilityMeasure (Q j) := inferInstance
    rw [toReal_klDiv_of_measure_eq (hac j) (by rw [measure_univ, measure_univ]),
      ← integral_rnDeriv_smul (hac j)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [llr_def, smul_eq_mul]
  -- the real form of the mutual information
  have hMItoReal : (mutualInformation Q).toReal
      = (M : ℝ)⁻¹ * ∑ j, (klDiv (Q j) (mixture Q)).toReal := by
    rw [mutualInformation, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun j _ => hfin j)]
  -- the component densities sum to `M`, a.e. against the mixture (ℝ≥0∞ form)
  have hsum_ennreal : (fun z => ∑ k, (Q k).rnDeriv (mixture Q) z)
      =ᵐ[mixture Q] (fun _ => (M : ℝ≥0∞)) := by
    have hS : (M : ℝ≥0∞) • mixture Q = ∑ k, Q k := by
      rw [mixture_eq_inv_smul_sum, smul_smul, ENNReal.mul_inv_cancel hMne hMtop, one_smul]
    have h1 := rnDeriv_finset_sum_ae (Finset.univ : Finset (Fin M)) (fun k => Q k) (mixture Q)
    have h2 : (∑ k, Q k).rnDeriv (mixture Q) =ᵐ[mixture Q] (fun _ => (M : ℝ≥0∞)) := by
      rw [← hS]
      filter_upwards [Measure.rnDeriv_smul_left_of_ne_top (mixture Q) (mixture Q) hMtop,
        Measure.rnDeriv_self (mixture Q)] with x hx hx2
      simp [hx, Pi.smul_apply, hx2]
    filter_upwards [h1, h2] with z e1 e2
    rw [← Finset.sum_apply, ← e1, e2]
  have htop : ∀ᵐ z ∂(mixture Q), ∀ k, (Q k).rnDeriv (mixture Q) z ≠ ∞ := by
    rw [ae_all_iff]; intro k; exact Measure.rnDeriv_ne_top (Q k) (mixture Q)
  -- the real (toReal) form of the sum identity
  have hsumR : (fun z => ∑ j, ((Q j).rnDeriv (mixture Q) z).toReal) =ᵐ[mixture Q]
      fun _ => (M : ℝ) := by
    filter_upwards [hsum_ennreal, htop] with z hz hzt
    rw [← ENNReal.toReal_sum (fun k _ => hzt k), hz, ENNReal.toReal_natCast]
  -- pointwise: the posterior entropy integrand equals `log M − M⁻¹ ∑ⱼ rⱼ log rⱼ`
  have hpt : (fun z => ∑ j, Real.negMulLog ((M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal))
      =ᵐ[mixture Q] fun z => Real.log (M : ℝ) - (M : ℝ)⁻¹ * ∑ j,
        (((Q j).rnDeriv (mixture Q) z).toReal * Real.log ((Q j).rnDeriv (mixture Q) z).toReal) := by
    filter_upwards [hsumR] with z hz
    have key : ∀ j, Real.negMulLog ((M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)
        = (M : ℝ)⁻¹ * Real.log (M : ℝ) * ((Q j).rnDeriv (mixture Q) z).toReal
          - (M : ℝ)⁻¹ * (((Q j).rnDeriv (mixture Q) z).toReal
            * Real.log ((Q j).rnDeriv (mixture Q) z).toReal) :=
      fun j => negMulLog_inv_mul hMr ENNReal.toReal_nonneg
    rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hz,
      show (M : ℝ)⁻¹ * Real.log (M : ℝ) * (M : ℝ) = Real.log (M : ℝ) from by
        rw [mul_comm ((M : ℝ)⁻¹) (Real.log (M : ℝ)), mul_assoc, inv_mul_cancel₀ hMr, mul_one]]
  -- assemble: integrate the pointwise identity and recognise the KL terms
  have hcond : condEntropy Q
      = Real.log (M : ℝ) - (M : ℝ)⁻¹ * ∑ j, (klDiv (Q j) (mixture Q)).toReal := by
    have hg_int : Integrable (fun z => (M : ℝ)⁻¹ * ∑ j,
        (((Q j).rnDeriv (mixture Q) z).toReal * Real.log ((Q j).rnDeriv (mixture Q) z).toReal))
        (mixture Q) :=
      (integrable_finset_sum Finset.univ (fun j _ => hintμ j)).const_mul _
    have hconst : ∫ _z, Real.log (M : ℝ) ∂(mixture Q) = Real.log (M : ℝ) := by
      simp
    rw [condEntropy, integral_congr_ae hpt, integral_sub (integrable_const _) hg_int, hconst,
      integral_const_mul, integral_finset_sum _ (fun j _ => hintμ j),
      Finset.sum_congr rfl (fun j _ => (hklj j).symm)]
  rw [hMItoReal, hcond]; ring

/-- **Conditional-entropy Fano inequality** (Wainwright Eq. (15.61), the genuinely-deep
information-theoretic half): the posterior entropy `H(J | Z)` is controlled by the testing error,
```
H(J | Z) ≤ log 2 + q · log M,        q = multiwayTestingError Q.
```
This is the single named residual of the Fano lower bound. (The other half — the mutual-information
identity `I = log M − H(J | Z)` — is fully proved in `mutualInformation_toReal_eq`, and the
surrounding `ℝ≥0∞` bookkeeping in `fano_entropy_continuous` / the division rearrangement in
`fano_inequality`.) The hypothesis `q ≠ ⊤` is genuine: for `q = ⊤` the bound (with `q.toReal = 0`)
would read `H(J|Z) ≤ log 2`, false for large `M`; it is supplied by the finite branch of
`fano_entropy_continuous` (and in fact always holds, the Bayes risk of the `0–1` loss being `≤ 1`).

TODO(mmx, named debt — strictly smaller than the former whole-crux `fano_real`): prove the sharp
Fano chain `H(J | Z) ≤ h(e) + e·log(M−1) ≤ log 2 + q·log M`, where `e(z) = 1 − maxⱼ ℙ(J=j|Z=z)` is
the pointwise MAP error. The route: (i) a pointwise discrete Fano `∑ⱼ negMulLog pⱼ ≤ binEntropy (1 −
maxⱼ pⱼ) + (1 − maxⱼ pⱼ)·log (M−1)` for a pmf `p` on `Fin M`; (ii) integrate over `mixture Q`,
using concavity of `Real.binEntropy` (Jensen) to pull `∫ binEntropy (e z) ≤ binEntropy (∫ e z)`;
(iii) identify `∫ e z ∂(mixture Q) = multiwayTestingError Q` (the MAP test attains the Bayes risk of
the `0–1` loss); (iv) close with `Real.binEntropy_le_log_two` and `log (M−1) ≤ log M`. -/
private lemma condEntropy_le_fano {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    (hM : 2 ≤ M) (hq : multiwayTestingError Q ≠ ⊤) :
    condEntropy Q ≤ Real.log 2 + (multiwayTestingError Q).toReal * Real.log (M : ℝ) := by
  sorry

/-- **Real-valued entropy form of Fano's inequality** (Wainwright Eq. (15.61)). Writing
`I = (I(Z;J)).toReal`, `q = (multiwayTestingError Q).toReal`, the mutual-information identity
`I = log M − H(J|Z)` (`mutualInformation_toReal_eq`) and the conditional-entropy Fano bound
`H(J|Z) ≤ log 2 + q·log M` (`condEntropy_le_fano`) combine to
```
log M ≤ I + log 2 + q · log M.
```
It is stated over `ℝ`; the `ℝ≥0∞` bookkeeping is discharged in `fano_entropy_continuous`, which
supplies the finiteness hypotheses `mutualInformation Q ≠ ⊤`, `multiwayTestingError Q ≠ ⊤` from its
`⊤`-case split. -/
private lemma fano_real {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    -- LEAN-ONLY: finiteness of the mutual information; supplied by `fano_entropy_continuous`'s
    -- `⊤`-branch split, no scope change (the `I = ⊤` case is handled there separately).
    (hI : mutualInformation Q ≠ ⊤)
    -- LEAN-ONLY: finiteness of the testing error; supplied by `fano_entropy_continuous`, no scope
    -- change (always holds, Bayes risk of the bounded `0–1` loss being `≤ 1`).
    (hq : multiwayTestingError Q ≠ ⊤)
    (hM : 2 ≤ M) :
    Real.log (M : ℝ)
      ≤ (mutualInformation Q).toReal + Real.log 2
          + (multiwayTestingError Q).toReal * Real.log (M : ℝ) := by
  have hid := mutualInformation_toReal_eq Q hI
  have hfano := condEntropy_le_fano Q hM hq
  linarith

/-- **Entropy form of Fano's inequality** (Wainwright Eq. (15.61)), packaged in the kernel-KL /
Bayes-risk encodings used by this module. Writing `L = log M`, `I = I(Z; J)`,
`q = multiwayTestingError Q` and `c = log 2`, the standard Fano chain
`H(J|Z) ≤ h(q) + q·log(M−1) ≤ log 2 + q·log M` together with `I = H(J) − H(J|Z) = log M − H(J|Z)`
rearranges to
```
log M ≤ I(Z; J) + log 2 + q · log M.
```
The genuinely-hard real-analytic content is isolated in `fano_real`; this wrapper discharges only
the `ℝ≥0∞` bookkeeping (the `⊤` cases and the `ENNReal.ofReal` push-through). The surrounding
`ℝ≥0∞` rearrangement into `1 − (I+c)/L ≤ q` (division and truncated subtraction) is discharged in
`fano_inequality` below. -/
private lemma fano_entropy_continuous {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    (hM : 2 ≤ M) :
    ENNReal.ofReal (Real.log (M : ℝ))
      ≤ mutualInformation Q + ENNReal.ofReal (Real.log 2)
          + multiwayTestingError Q * ENNReal.ofReal (Real.log (M : ℝ)) := by
  -- `ℝ≥0∞` wrapper around the real-valued Fano bound `fano_real`: handle the `⊤` cases and then
  -- push everything through `ENNReal.ofReal`.
  have hlogM_pos : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogM_nonneg : (0 : ℝ) ≤ Real.log (M : ℝ) := hlogM_pos.le
  have hlog2_nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- If the mutual information is infinite the RHS is `⊤`.
  by_cases hItop : mutualInformation Q = ⊤
  · rw [hItop]; simp
  -- If the testing error is infinite, then `q · log M = ⊤` (since `log M > 0`) and the RHS is `⊤`.
  by_cases hqtop : multiwayTestingError Q = ⊤
  · have hne : ENNReal.ofReal (Real.log (M : ℝ)) ≠ 0 := (ENNReal.ofReal_pos.mpr hlogM_pos).ne'
    rw [hqtop, ENNReal.top_mul hne]; simp
  -- Both quantities finite: rewrite the RHS as a single `ENNReal.ofReal` and apply `fano_real`.
  have hReal := fano_real Q hItop hqtop hM
  have hsum_eq : mutualInformation Q + ENNReal.ofReal (Real.log 2)
        + multiwayTestingError Q * ENNReal.ofReal (Real.log (M : ℝ))
      = ENNReal.ofReal ((mutualInformation Q).toReal + Real.log 2
          + (multiwayTestingError Q).toReal * Real.log (M : ℝ)) := by
    rw [ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg hlog2_nonneg)
          (mul_nonneg ENNReal.toReal_nonneg hlogM_nonneg),
        ENNReal.ofReal_add ENNReal.toReal_nonneg hlog2_nonneg,
        ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hItop, ENNReal.ofReal_toReal hqtop]
  rw [hsum_eq]
  exact ENNReal.ofReal_le_ofReal hReal

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
theorem minimax_fano_lower_bound [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
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
