import StatLean.ConcentrationInequalities.Chaining.DiscreteDudley

/-!
# Dudley's integral inequality (Theorem 8.1.3 / Eqs. (8.13)–(8.16))

Integral-form Dudley from the discrete core via the comparison
$\Sigma \le 2 I$: for a process with sub-gaussian increments on a finite
index set $T$ with $\operatorname{diam} T \le D$,
$$ \mathbb{E}\Bigl[\sup_{t \in T} X_t\Bigr] \;\le\;
     12\sqrt{3}\; K \int_0^{D} \sqrt{\log \mathcal{N}(T,d,\varepsilon)}\,
     d\varepsilon \quad (\text{mean-zero}), $$
$$ \mathbb{E}\Bigl[\sup_{t \in T} |X_t - X_{t_0}|\Bigr]
     \le 40\, K \int_0^{D}\!\sqrt{\log \mathcal{N}}, \qquad
   \mathbb{E}\Bigl[\sup_{s,t \in T} |X_t - X_s|\Bigr]
     \le 80\, K \int_0^{D}\!\sqrt{\log \mathcal{N}}, $$
plus the $\int_0^\infty$ display of Theorem 8.1.3 and the ONE countable lift
mandated by the sup policy. Assembly file.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Theorem 8.1.3, Eqs. (8.13), (8.14), and
Eq. (8.16) / Remark 8.1.7; the countable form realizes the p. 227 footnote
("the general case follows by approximation").

**Proof formalization notes.** Frozen constants: `12√3 = 2 × 6√3` (mean-zero,
via `dudleySum_le_two_mul_dudleyIntegral`), `40 = 2 × 20` (abs form),
`80 = 2 × 40` (pair form, triangle through a fixed `t₀`), countable lift
`80 = 40 × 2` (the `coveringNumber_subset_le` `ε/2` loss after the `u = ε/2`
change of variables). The diameter-capped Eq. (8.16) is the PRIMARY
statement; the `∫_0^∞` shape of Theorem 8.1.3 is a display corollary via
`dudleyIntegral_Ioi_eq` (the `diam = 0` corner handled separately). The
mean-zero forms carry the LEAN-ONLY hypothesis
`hint : ∀ t ∈ T, Integrable (X t) μ` ruling out Bochner-junk means. The
countable lift is stated wholly in `ℝ≥0∞` (`∫⁻` of
`⨆ ENNReal.ofReal |X_t − X_{t₀}|` against `dudleyLIntegral`) so neither side
can be junk; it goes by monotone convergence (`lintegral_iSup`) over a finite
exhaustion `S_n ↑ T`, with the subset step costing exactly the factor `2`
above. Uncountable-sup statements are left to consumers per the sup policy
(ℚ-grid + right-continuity for Glivenko–Cantelli; `L^∞`-dense subfamilies for
Lipschitz classes). Named-sorry fallback of this work item:
`dudley_inequality_countable` (all finite-`T` integral forms proved; the
MCT/change-of-variables lift is the isolated hard part).

**Bibliographic comments.** R. M. Dudley, "The sizes of compact subsets of
Hilbert space and continuity of Gaussian processes," *J. Funct. Anal.* 1
(1967), 290–330. The entropy-integral formulation for sub-gaussian processes
is the standard textbook synthesis (HDP §8.1; Talagrand 2014, §2.3;
Ledoux–Talagrand, *Probability in Banach Spaces*, Springer 1991, Ch. 11).
See the HDP Chapter 8 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **Dudley's inequality, mean-zero capped form** (HDP §8.1, Theorem 8.1.3
+ Eq. (8.16)): `E sup X ≤ 12√3 · K · ∫_0^D √(log 𝒩)`. Book constant frozen
to `12√3 = 2 × 6√3`. -/
theorem dudley_inequality {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the cap dominates the diameter (Eq (8.16)); HDP §8.1
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap; the D = 0 corner degenerates to a point
    (hD0 : 0 < D) :
    ∫ ω, ⨆ t ∈ T, X t ω ∂μ
      ≤ 12 * Real.sqrt 3 * K * dudleyIntegral T D := by
  calc ∫ ω, ⨆ t ∈ T, X t ω ∂μ
      ≤ 6 * Real.sqrt 3 * K * dudleySum T :=
        discrete_dudley hfin hne hmeas hint hmean hinc
    _ ≤ 6 * Real.sqrt 3 * K * (2 * dudleyIntegral T D) := by
        refine mul_le_mul_of_nonneg_left
          (dudleySum_le_two_mul_dudleyIntegral hfin hne hD hD0) ?_
        positivity
    _ = 12 * Real.sqrt 3 * K * dudleyIntegral T D := by ring

/-- **Dudley's inequality, absolute form** (HDP §8.1, Eq. (8.13), capped):
`E sup |X_t − X_{t₀}| ≤ 40 · K · ∫_0^D √(log 𝒩)`, NO mean-zero — THE
consumer-facing form. Book constant frozen to `40 = 2 × 20`. -/
theorem dudley_inequality_abs {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 40 * K * dudleyIntegral T D := by
  calc ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 20 * K * dudleySum T :=
        discrete_dudley_abs hfin hne hmeas hinc ht₀
    _ ≤ 20 * K * (2 * dudleyIntegral T D) := by
        refine mul_le_mul_of_nonneg_left
          (dudleySum_le_two_mul_dudleyIntegral hfin hne hD hD0) ?_
        positivity
    _ = 40 * K * dudleyIntegral T D := by ring

/-- **Dudley's inequality, pair form** (HDP §8.1, Eq. (8.14), capped):
`E sup_{s,t} |X_t − X_s| ≤ 80 · K · ∫_0^D √(log 𝒩)` via the triangle
inequality through a fixed `t₀`. Book constant frozen to `80 = 2 × 40`. -/
theorem dudley_inequality_abs_pair {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫ ω, ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω| ∂μ
      ≤ 80 * K * dudleyIntegral T D := by
  classical
  have hbd : Bornology.IsBounded T := hfin.isBounded
  set F := hfin.toFinset with hFdef
  have hFne : F.Nonempty := by rw [hFdef, Set.Finite.toFinset_nonempty]; exact hne
  have hmemT : ∀ t, t ∈ F ↔ t ∈ T := fun t => hfin.mem_toFinset
  set t₀ := hne.some with ht₀def
  have ht₀ : t₀ ∈ T := hne.some_mem
  -- Set ↔ Finset conversion for suprema.
  have setToF : ∀ g : E → ℝ, (⨆ x ∈ T, g x) = ⨆ x ∈ F, g x :=
    fun g => iSup_congr fun x => by rw [hfin.mem_toFinset]
  -- The anchored single supremum and its integrability (Eq. (8.13) form).
  set A : Ω → ℝ := fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω| with hAdef
  have hIntA : MeasureTheory.Integrable A μ :=
    integrable_biSup_sub hfin hne hmeas hinc ht₀
  -- The double supremum as a supremum over the product Finset.
  have hPne : (F ×ˢ F).Nonempty := hFne.product hFne
  -- Integrability of the pair supremum via `integrable_biSup_abs` over `P`.
  have hIntP : MeasureTheory.Integrable
      (fun ω => ⨆ p ∈ (F ×ˢ F), |X p.1 ω - X p.2 ω|) μ := by
    refine integrable_biSup_abs hPne (L := K * Real.toNNReal (Metric.diam T))
      (fun p hp => ?_) (fun p hp => ?_)
    · obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      exact (hmeas p.1 ((hmemT p.1).mp hp1)).sub (hmeas p.2 ((hmemT p.2).mp hp2))
    · obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have h1 : p.1 ∈ T := (hmemT p.1).mp hp1
      have h2 : p.2 ∈ T := (hmemT p.2).mp hp2
      refine (hinc p.2 h2 p.1 h1).trans ?_
      have hde : edist p.2 p.1 ≤ (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hbd h2 h1)
      calc (K : ℝ≥0∞) * edist p.2 p.1
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by gcongr
        _ = ((K * Real.toNNReal (Metric.diam T) : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
  -- Identify the double supremum with the product supremum, pointwise.
  have hpair_eq : (fun ω => ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|)
      = fun ω => ⨆ p ∈ (F ×ˢ F), |X p.1 ω - X p.2 ω| := by
    funext ω
    have e1 : (⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|)
        = F.sup' hFne (fun t => F.sup' hFne (fun s => |X t ω - X s ω|)) := by
      rw [setToF (fun t => ⨆ s ∈ T, |X t ω - X s ω|), biSup_finset_eq_sup' hFne]
      refine Finset.sup'_congr rfl (fun t _ => ?_)
      rw [setToF (fun s => |X t ω - X s ω|), biSup_finset_eq_sup' hFne]
    rw [e1, biSup_finset_eq_sup' hPne,
      Finset.sup'_product_left hPne (fun p => |X p.1 ω - X p.2 ω|)]
  -- Pointwise: the double sup is at most twice the anchored sup.
  have hpt : ∀ ω, (⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|) ≤ 2 * A ω := by
    intro ω
    have hanch : ∀ t ∈ T, |X t ω - X t₀ ω| ≤ A ω := by
      intro t ht
      rw [hAdef, setToF (fun u => |X u ω - X t₀ ω|), biSup_finset_eq_sup' hFne]
      exact Finset.le_sup' (fun u => |X u ω - X t₀ ω|) ((hmemT t).mpr ht)
    rw [setToF (fun t => ⨆ s ∈ T, |X t ω - X s ω|), biSup_finset_eq_sup' hFne]
    refine Finset.sup'_le hFne _ (fun t ht => ?_)
    rw [setToF (fun s => |X t ω - X s ω|), biSup_finset_eq_sup' hFne]
    refine Finset.sup'_le hFne _ (fun s hs => ?_)
    have htri : |X t ω - X s ω| ≤ |X t ω - X t₀ ω| + |X s ω - X t₀ ω| := by
      have h := abs_sub_le (X t ω) (X t₀ ω) (X s ω)
      rwa [abs_sub_comm (X t₀ ω) (X s ω)] at h
    have h1 := hanch t ((hmemT t).mp ht)
    have h2 := hanch s ((hmemT s).mp hs)
    linarith
  -- Assemble the integral bound.
  calc ∫ ω, ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω| ∂μ
      ≤ ∫ ω, 2 * A ω ∂μ := by
        refine integral_mono_ae ?_ (hIntA.const_mul 2) (ae_of_all _ hpt)
        rw [hpair_eq]; exact hIntP
    _ = 2 * ∫ ω, A ω ∂μ := integral_const_mul 2 A
    _ ≤ 2 * (40 * K * dudleyIntegral T D) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact dudley_inequality_abs hfin hne hmeas hinc ht₀ hD hD0
    _ = 80 * K * dudleyIntegral T D := by ring

/-- **Dudley's inequality, `∫_0^∞` display** (HDP §8.1, Theorem 8.1.3
verbatim shape): via `dudleyIntegral_Ioi_eq`; the `diam = 0` corner is
handled separately in the proof. -/
theorem dudley_inequality_Ioi {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ) :
    ∫ ω, ⨆ t ∈ T, X t ω ∂μ
      ≤ 12 * Real.sqrt 3 * K * ∫ ε in Set.Ioi (0 : ℝ), sqrtLogCov T ε := by
  have hDpos : (0 : ℝ) < Metric.diam T + 1 := by
    have := Metric.diam_nonneg (s := T); linarith
  have hDle : Metric.diam T ≤ Metric.diam T + 1 := by linarith
  rw [dudleyIntegral_Ioi_eq hfin hne hDle hDpos]
  exact dudley_inequality hfin hne hmeas hint hmean hinc hDle hDpos

/-- **Dudley's inequality, countable lift** (HDP §8.1, Eq. (8.13), countable
form; p. 227 footnote "general case by approximation"): stated wholly in
`ℝ≥0∞` so neither side can be junk; monotone convergence over a finite
exhaustion + the `coveringNumber_subset_le` `ε/2` loss (frozen constant
`80 = 40 × 2`). -/
theorem dudley_inequality_countable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy (uncountable sups are left
    -- to consumers)
    (hcnt : T.Countable)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: T totally bounded, as finite covering numbers; HDP p.227
    -- footnote
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: uniform diameter bound (T bounded); HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : ∀ s ∈ T, ∀ t ∈ T, dist s t ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal (80 * K) * dudleyLIntegral T D := by sorry

end StatLean.ConcentrationInequalities
