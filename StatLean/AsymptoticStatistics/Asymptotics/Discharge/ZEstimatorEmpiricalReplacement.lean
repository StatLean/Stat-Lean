import StatLean.AsymptoticStatistics.EmpiricalProcess.RandomFunctions
import StatLean.AsymptoticStatistics.ForMathlib.InProbability
import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw

/-!
# Random-index empirical-score replacement

This file isolates the public empirical-process layer used when an estimated score is
evaluated at the same product sample that selected it.  It contains no estimator,
parametric model, score equation, Taylor condition, Bartlett identity, bias condition,
or asymptotic-linearity conclusion.

The scalar result is the product-law form of vdV Lemma 19.24 used privately by the
Z-estimator discharge.  The finite-dimensional result assumes the scalar Donsker and
expected-`L²` inputs coordinatewise and concludes the native Euclidean residual by
finite-coordinate assembly; in particular, it introduces no vector-Donsker predicate.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimator

open AsymptoticStatistics.EmpiricalProcess

-- The iid carrier agrees with the `Type`-valued carrier of `RandomFunctions`.
variable {Omega : Type} [MeasurableSpace Omega]

/-- Minimal scalar hypotheses for replacing a random estimated score by its fixed
reference score inside the centered empirical process under the product laws `P^n`.

This bundle records only the concrete inputs used by the public product-law transport
of vdV Lemma 19.24.  In particular, membership of `score0` in `F` is unnecessary: the
faithful random-function theorem extracts deterministic anchors in `F` from the `L²`
consistency premise. -/
structure RandomIndexScoreReplacementHyp
    (P : Measure Omega) [IsProbabilityMeasure P]
    (scoreHat : forall n, (Fin n -> Omega) -> (Omega -> Real))
    (score0 : Omega -> Real) (F : Set (Omega -> Real)) : Prop where
  /-- Constitutive (vdV Lemma 19.24): measurable representative of the
  fixed reference score. -/
  score0_meas : Measurable score0
  /-- Constitutive (vdV Lemma 19.24): fixed reference score in `L²(P)`. -/
  score0_memLp : MemLp score0 2 P
  /-- Constitutive (vdV Lemma 19.24): scalar `P`-Donsker class. -/
  is_donsker : IsPDonsker F P
  /-- Constitutive (Lean product-law adapter): joint measurability of the
  sample-indexed score, used to transport expected `L²` consistency from `P^n` to the
  infinite iid product representation. -/
  scoreHat_meas : forall n,
    Measurable (fun p : (Fin n -> Omega) × Omega => scoreHat n p.1 p.2)
  /-- Constitutive (vdV Lemma 19.24): every realized estimated scalar score
  belongs to the Donsker class. -/
  scoreHat_mem : forall n (X : Fin n -> Omega), scoreHat n X ∈ F
  /-- Constitutive (vdV Lemma 19.24, expected-`L²` form): expected squared
  `L²(P)` distance of the estimated score from the fixed score tends to zero under the
  product sample law `P^n`. -/
  score_l2_consistency :
    Tendsto (fun n =>
      ∫ X, (∫ x, (scoreHat n X x - score0 x) ^ 2 ∂P)
        ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 0)
  /-- Constitutive (Lean Markov adapter): integrability needed to convert
  expected `L²` consistency into the explicit outer-probability tail of Lemma 19.24. -/
  score_l2_int : forall n, Integrable
    (fun X : Fin n -> Omega => ∫ x, (scoreHat n X x - score0 x) ^ 2 ∂P)
    (Measure.pi (fun _ : Fin n => P))

set_option maxHeartbeats 2000000 in
-- The infinite-product transport and empirical-process event normalization are heartbeat-heavy.
/-- The centered empirical-process residual obtained by replacing a random estimated
scalar score by its fixed reference score is `o_P(1)` under the product sample laws.

Proof idea: transport `P^n` to the truncation of the infinite iid product, derive the
explicit `distL2` tail from `score_l2_consistency` and `score_l2_int` by Markov, apply
`donsker_random_function_consistency_core`, and transport its empirical-process event
back to `P^n`. -/
theorem randomIndex_empiricalScoreReplacement_oP
    {P : Measure Omega} [IsProbabilityMeasure P]
    {scoreHat : forall n, (Fin n -> Omega) -> (Omega -> Real)}
    {score0 : Omega -> Real} {F : Set (Omega -> Real)}
    -- the minimal scalar random-index replacement bundle above.
    (h : RandomIndexScoreReplacementHyp P scoreHat score0 F) :
    TendstoInProbZero (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (Real.sqrt n)⁻¹ *
            (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
          - Real.sqrt n * (∫ x, (scoreHat n X x - score0 x) ∂P)) := by
  intro ε hε
  let μ : Measure (ℕ → Omega) := Measure.infinitePi (fun _ : ℕ => P)
  let trunc (n : ℕ) (ξ : ℕ → Omega) : Fin n → Omega := fun i => ξ i.val
  have htrunc : ∀ n, Measurable (trunc n) := fun n =>
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hXmeas : ∀ i : ℕ, Measurable (fun ξ : ℕ → Omega => ξ i) := fun _ =>
    measurable_pi_apply _
  have hXindep : ProbabilityTheory.iIndepFun
      (fun (i : ℕ) (ξ : ℕ → Omega) => ξ i) μ := by
    simpa [μ] using ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : ℕ => P) (X := fun _ : ℕ => id) (mX := fun _ => measurable_id)
  have hXlaw : μ.map (fun ξ : ℕ → Omega => ξ 0) = P := by
    change (Measure.infinitePi (fun _ : ℕ => P)).map (Function.eval 0) = P
    rw [Measure.infinitePi_map_eval]
  have hXidem : ∀ i : ℕ, ProbabilityTheory.IdentDistrib
      (fun ξ : ℕ → Omega => ξ i) (fun ξ : ℕ → Omega => ξ 0) μ μ := by
    intro i
    refine ⟨(hXmeas i).aemeasurable, (hXmeas 0).aemeasurable, ?_⟩
    change μ.map (Function.eval i) = μ.map (Function.eval 0)
    simp [μ, Measure.infinitePi_map_eval]
  let fhat (n : ℕ) (ξ : ℕ → Omega) := scoreHat n (trunc n ξ)
  have hfhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)) := by
    intro n
    exact (h.scoreHat_meas n).comp <| Measurable.prodMk
      ((htrunc n).comp measurable_fst) measurable_snd
  have hinner : ∀ n, StronglyMeasurable (fun X : Fin n → Omega =>
      ∫ x, (scoreHat n X x - score0 x) ^ 2 ∂P) := by
    intro n
    exact ((h.scoreHat_meas n).sub (h.score0_meas.comp measurable_snd)).pow_const 2
      |>.stronglyMeasurable.integral_prod_right'
  have hl2 : Tendsto (fun n =>
      ∫ ξ, (∫ x, (fhat n ξ x - score0 x) ^ 2 ∂P) ∂μ) atTop (nhds 0) := by
    apply h.score_l2_consistency.congr'
    filter_upwards [] with n
    rw [AsymptoticStatistics.pi_const_eq_infinitePi_map P n,
      integral_map (htrunc n).aemeasurable (hinner n).aestronglyMeasurable]
  have hl2int : ∀ n, Integrable
      (fun ξ => ∫ x, (fhat n ξ x - score0 x) ^ 2 ∂P) μ := by
    intro n
    simp only [μ]
    exact (integrable_map_measure (hinner n).aestronglyMeasurable
      (htrunc n).aemeasurable).mp (by
        rw [← AsymptoticStatistics.pi_const_eq_infinitePi_map P n]
        exact h.score_l2_int n)
  have htail : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      μ.outerMeasureStar {ξ | δ < distL2 P (fhat n ξ) score0}) atTop (nhds 0) := by
    intro δ hδ
    have hm : Tendsto (fun n => μ {ξ | δ ≤ distL2 P (fhat n ξ) score0})
        atTop (nhds 0) := markov_distL2_tail (P := P)
      (Ξ := ℕ → Omega) μ fhat (fun _ _ => score0) hfhat_meas
      (fun _ => h.score0_meas.comp measurable_snd) hl2int (by simpa using hl2) hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hm
      (Eventually.of_forall fun _ => zero_le _) (Eventually.of_forall fun n => ?_)
    exact (outerMeasureStar_mono μ fun (ξ : ℕ → Omega) hx =>
      show δ ≤ distL2 P (fhat n ξ) score0 from hx.le).trans
      (AsymptoticStatistics.outerMeasureStar_le_measure μ _)
  have hcore := donsker_random_function_consistency_core (F := F) (P := P)
    h.is_donsker score0 h.score0_memLp (Ξ := ℕ → Omega) (μ := μ)
    (X := fun i ξ => ξ i) hXmeas hXindep hXidem hXlaw (f_hat := fhat)
    (fun n ξ => h.scoreHat_mem n (trunc n ξ)) htail (ε / 2) (half_pos hε)
  have hstat : ∀ (n : ℕ) (ξ : ℕ → Omega),
      (Real.sqrt n)⁻¹ *
          (∑ i : Fin n, (scoreHat n (trunc n ξ) (ξ i) - score0 (ξ i)))
        - Real.sqrt n * (∫ x, (scoreHat n (trunc n ξ) x - score0 x) ∂P)
        = empiricalProcess P n (trunc n ξ) (fhat n ξ)
          - empiricalProcess P n (trunc n ξ) score0 := by
    intro n ξ
    have hfint : Integrable (fhat n ξ) P :=
      (h.is_donsker.marginalCLT.memLp _ (h.scoreHat_mem n _)).integrable (by norm_num)
    rw [integral_sub hfint (h.score0_memLp.integrable (by norm_num)),
      Finset.sum_sub_distrib]
    unfold empiricalProcess empiricalAvg
    simp only [fhat, trunc]
    by_cases hn : n = 0
    · subst n; simp
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
      have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      have hinv : (Real.sqrt (n : ℝ))⁻¹ = Real.sqrt n * (n : ℝ)⁻¹ := by
        field_simp
        exact (Real.sq_sqrt hnpos.le).symm
      rw [hinv]
      ring
  have hZmeas : ∀ n, Measurable (fun X : Fin n → Omega =>
      (Real.sqrt n)⁻¹ * (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
        - Real.sqrt n * (∫ x, (scoreHat n X x - score0 x) ∂P)) := by
    intro n
    apply Measurable.sub (measurable_const.mul <| Finset.measurable_sum _ fun i _ =>
      ((h.scoreHat_meas n).comp (Measurable.prodMk measurable_id
        (measurable_pi_apply i))).sub (h.score0_meas.comp (measurable_pi_apply i)))
    exact measurable_const.mul <|
      ((h.scoreHat_meas n).sub (h.score0_meas.comp measurable_snd)).stronglyMeasurable
        |>.integral_prod_right'.measurable
  have hcoreR := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcore
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcoreR
    (Eventually.of_forall fun _ => measureReal_nonneg) (Eventually.of_forall fun n => ?_)
  rw [AsymptoticStatistics.pi_real_eq_infinitePi_real_of_truncate P n
    (measurableSet_le measurable_const (hZmeas n).norm)]
  refine measureReal_mono (μ := μ) (h₂ := measure_ne_top μ _) ?_
  intro ξ hξ
  change ε / 2 < |empiricalProcess P n (trunc n ξ) (fhat n ξ)
    - empiricalProcess P n (trunc n ξ) score0|
  rw [← hstat n ξ]
  change ε ≤ ‖(Real.sqrt n)⁻¹ *
      (∑ i : Fin n, (scoreHat n (trunc n ξ) (ξ i) - score0 (ξ i)))
    - Real.sqrt n * (∫ x, (scoreHat n (trunc n ξ) x - score0 x) ∂P)‖ at hξ
  rw [Real.norm_eq_abs] at hξ
  exact (half_lt_self hε).trans_le hξ

/-- Coordinatewise scalar hypotheses for native finite-dimensional empirical-score
replacement.  Each coordinate may use its own scalar Donsker class; no Donsker
assumption is made on the vector-valued score class. -/
structure RandomIndexScoreReplacementHyp_vec
    (P : Measure Omega) [IsProbabilityMeasure P] (d : Nat)
    (scoreHat : forall n,
      (Fin n -> Omega) -> (Omega -> EuclideanSpace Real (Fin d)))
    (score0 : Omega -> EuclideanSpace Real (Fin d))
    (F : Fin d -> Set (Omega -> Real)) : Prop where
  /-- Constitutive (finite-dimensional coordinate lift): minimal scalar
  replacement hypotheses for every coordinate, possibly with coordinate-dependent
  Donsker classes. -/
  coord_hyp : forall j : Fin d,
    RandomIndexScoreReplacementHyp P
      (fun n X x => scoreHat n X x j) (fun x => score0 x j) (F j)

/-- Native finite-dimensional empirical-score replacement from the scalar theorem in
each coordinate.  The conclusion is the Euclidean centered residual under `P^n`; its
proof uses only finiteness of `Fin d`, not a vector-Donsker assumption.

Proof idea: apply `randomIndex_empiricalScoreReplacement_oP` to every coordinate and
combine the finitely many scalar `o_P(1)` bounds using the Euclidean norm formula and a
finite union bound. -/
theorem randomIndex_empiricalScoreReplacement_oP_vec
    {P : Measure Omega} [IsProbabilityMeasure P] {d : Nat}
    {scoreHat : forall n,
      (Fin n -> Omega) -> (Omega -> EuclideanSpace Real (Fin d))}
    {score0 : Omega -> EuclideanSpace Real (Fin d)}
    {F : Fin d -> Set (Omega -> Real)}
    -- coordinatewise scalar random-index replacement hypotheses.
    (h : RandomIndexScoreReplacementHyp_vec P d scoreHat score0 F) :
    TendstoInProbZero (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (Real.sqrt n)⁻¹ •
            (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
          - Real.sqrt n • (∫ x, (scoreHat n X x - score0 x) ∂P)) := by
  classical
  let Z (n : ℕ) (X : Fin n → Omega) :=
    (Real.sqrt n)⁻¹ • (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
      - Real.sqrt n • (∫ x, (scoreHat n X x - score0 x) ∂P)
  change TendstoInProbZero (fun n : ℕ => Measure.pi (fun _ : Fin n => P)) Z
  have hint (n : ℕ) (X : Fin n → Omega) (j : Fin d) :
      (∫ x, (scoreHat n X x - score0 x) ∂P) j
        = ∫ x, (scoreHat n X x j - score0 x j) ∂P := by
    apply MeasureTheory.eval_integral_piLp
    intro k
    exact ((h.coord_hyp k).is_donsker.marginalCLT.memLp _
      ((h.coord_hyp k).scoreHat_mem n X)).integrable (by norm_num) |>.sub
        ((h.coord_hyp k).score0_memLp.integrable (by norm_num))
  have hcoord : ∀ j : Fin d, TendstoInProbZero
      (fun n : ℕ => Measure.pi (fun _ : Fin n => P)) (fun n X => Z n X j) := by
    intro j
    have hj := randomIndex_empiricalScoreReplacement_oP (h.coord_hyp j)
    convert hj using 1
    funext n X
    simp only [Z, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [show (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i))).ofLp j
        = ∑ i : Fin n, (scoreHat n X (X i) j - score0 (X i) j) by
          simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.sub_apply], hint n X j]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · intro ε hε
    have hz : ∀ n (X : Fin n → Omega), Z n X = 0 := fun _ _ => Subsingleton.elim _ _
    simp only [hz, norm_zero, not_le.mpr hε, Set.setOf_false, measureReal_empty]
    exact tendsto_const_nhds
  · intro ε hε
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hlevel : 0 < ε / d := div_pos hε hdR
    have hsum : Tendsto (fun n => ∑ j : Fin d,
        (Measure.pi (fun _ : Fin n => P)).real {X | ε / d ≤ ‖Z n X j‖})
        atTop (nhds 0) := by
      simpa using tendsto_finset_sum (Finset.univ : Finset (Fin d))
        (fun j _ => hcoord j (ε / d) hlevel)
    refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hsum
    refine (measureReal_mono (fun X hX => ?_)).trans (measureReal_iUnion_fintype_le _)
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hall
    push Not at hall
    have hnorm : ‖Z n X‖ < ε := by
      calc
        ‖Z n X‖ = ‖∑ j : Fin d, PiLp.single (β := fun _ : Fin d => ℝ) 2 j (Z n X j)‖ := by
          congr 1; ext j; simp
        _ ≤ ∑ j : Fin d, ‖PiLp.single (β := fun _ : Fin d => ℝ) 2 j (Z n X j)‖ :=
          norm_sum_le _ _
        _ = ∑ j : Fin d, ‖Z n X j‖ := by simp
        _ < ∑ _j : Fin d, ε / d := Finset.sum_lt_sum_of_nonempty
          (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd)) (fun j _ => hall j)
        _ = ε := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
    exact (not_lt_of_ge hX) hnorm

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
