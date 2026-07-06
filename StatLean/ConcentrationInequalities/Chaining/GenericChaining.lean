import StatLean.ConcentrationInequalities.Chaining.GammaTwo
import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
import StatLean.ConcentrationInequalities.Chaining.TailToExpectation
import StatLean.ConcentrationInequalities.Chaining.DyadicNets
import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Generic chaining (Talagrand's γ₂ bound)

For a mean-zero process $(X_t)_{t \in T}$ with sub-Gaussian increments
(Eq. 8.1) on a metric space $(T, d)$,
$$ \mathbb{E} \sup_{t \in T} X_t \;\le\; C K \,\gamma_2(T, d), $$
where $\gamma_2$ is the Talagrand functional over admissible sequences
(Definition 8.5.1, `Chaining/GammaTwo.lean`).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.5.2, Theorem 8.5.2 (proof Steps 1–3,
Eqs. (8.48)–(8.50)); Remark 8.5.3 for the mean-zero-free $|X_t - X_{t_0}|$
form.

**Proof formalization notes.** Finite-`T` core per the batch sup policy
(book WLOG, p. 247 Step 1). The high-probability form
(`generic_chaining_tail`) carries per-level thresholds
$2^{k/2}(\sqrt{2\log 2} + 1) + u$ over the admissible-sequence levels and a
union bound over $|T_k|\cdot|T_{k-1}| \le 2^{2^{k+1}}$ chain pairs; the
expectation forms integrate it via
`Chaining/TailToExpectation.lean`. **Frozen constants** (formula + numeral):
tail threshold factor `(12 + 4u)` (from $\sum_k 2^{k/2}\,2^{-k/2}$-style
geometric bookkeeping at the designed thresholds); expectation constant
`20` (book's absolute `C`; formula $6 + 2\sqrt{\pi} \le 10$). Per batch
reconciliation R4, the mean-zero assemblies carry the LEAN-ONLY hypothesis
`hint : ∀ t ∈ T, Integrable (X t) μ` ruling out Bochner-junk means (the
per-pair increment means are then genuine). Work-item single named-sorry
fallback: `generic_chaining_tail` (the per-level event bookkeeping); the
integration and `iInf` steps to Theorem 8.5.2 must close against it.

**Bibliographic comments.** Generic chaining and the majorizing-measure
theory are due to X. Fernique (1975) and M. Talagrand ("Regularity of
Gaussian processes," *Acta Math.* 159 (1987), 99–149; *Upper and Lower
Bounds for Stochastic Processes*, Springer 2014). The admissible-sequence
formulation follows Talagrand via HDP §8.5; the matching lower bound
(majorizing measure theorem, HDP Theorem 8.5.5) is out of Batch-10 scope.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- A.e.-measurability of a finite (hence countable) `biSup` of
a.e.-measurable functions. -/
private lemma aemeasurable_biSup_of_finite {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {E : Type*} {T : Set E} (hfin : T.Finite) {g : E → Ω → ℝ}
    (hg : ∀ t ∈ T, AEMeasurable (g t) μ) :
    AEMeasurable (fun ω => ⨆ t ∈ T, g t ω) μ :=
  AEMeasurable.biSup T hfin.countable hg

/-- A single value is dominated by the finite `biSup` (via `Finset.sup'`). -/
private lemma le_biSup_of_finite {E : Type*} {T : Set E} (hfin : T.Finite)
    (g : E → ℝ) {t : E} (ht : t ∈ T) : g t ≤ ⨆ s ∈ T, g s := by
  have hFne : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]; exact ⟨t, ht⟩
  have setToF : (⨆ s ∈ hfin.toFinset, g s) = ⨆ s ∈ T, g s :=
    iSup_congr fun s => by rw [hfin.mem_toFinset]
  rw [← setToF, biSup_finset_eq_sup' hFne]
  exact Finset.le_sup' g (hfin.mem_toFinset.mpr ht)

/-- A uniform bound on the values dominates the finite `biSup` (via
`Finset.sup'`). -/
private lemma biSup_le_of_finite {E : Type*} {T : Set E} (hfin : T.Finite)
    (hne : T.Nonempty) (g : E → ℝ) {c : ℝ} (h : ∀ s ∈ T, g s ≤ c) :
    ⨆ s ∈ T, g s ≤ c := by
  have hFne : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]; exact hne
  have setToF : (⨆ s ∈ hfin.toFinset, g s) = ⨆ s ∈ T, g s :=
    iSup_congr fun s => by rw [hfin.mem_toFinset]
  rw [← setToF, biSup_finset_eq_sup' hFne]
  exact Finset.sup'_le hFne g (fun s hs => h s (hfin.mem_toFinset.mp hs))

/-- Exponential geometric tail `∑_{k<n} exp(-(k+1)) ≤ 1`, via `exp(-1) ≤ 1/2`. -/
private lemma sum_exp_neg_succ_le_one (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.exp (-((k : ℝ) + 1)) ≤ 1 := by
  have he1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hsum : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := by
    have hrw : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1)
        = (1 / 2) * ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [pow_succ]; ring
    rw [hrw]; linarith [sum_geometric_two_le n]
  have hterm : ∀ k ∈ Finset.range n, Real.exp (-((k : ℝ) + 1)) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    intro k _
    have hei : Real.exp (-((k : ℝ) + 1)) = Real.exp (-1) ^ (k + 1) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hei]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) he1 (k + 1)
  exact le_trans (Finset.sum_le_sum hterm) hsum

/-- **Generic chaining, high-probability form** (HDP §8.5.2, Theorem 8.5.2
proof Steps 2–3, Eqs. (8.48)–(8.50)): for any admissible sequence `A`, the
sup of increments exceeds `(12 + 4u)·K·γ(A)` with probability at most
`2 exp(−u²)`. This work item's single named-sorry fallback. -/
theorem generic_chaining_tail {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure; bridge-B1 tail machinery requires it
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (book WLOG p.247 Step 1; sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index so the sup is genuine
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the process; regularity
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point of the increment sup; Remark 8.5.3 device
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    -- LEAN-ONLY: finite functional (⊤ makes the event's threshold junk 0)
    (hA : gammaFunctional A ≠ ⊤)
    {u : ℝ}
    -- USER-INPUT: deviation parameter u ≥ 0; HDP Eq (8.50)
    (hu : 0 ≤ u) :
    μ {ω | (12 + 4 * u) * K * (gammaFunctional A).toReal <
        ⨆ t ∈ T, |X t ω - X t₀ ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  classical
  set G : ℝ := (gammaFunctional A).toReal with hGdef
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  -- Finite carrier as a `Finset`, with `⨆ over F = ⨆ over T`.
  set F := hfin.toFinset with hFdef
  have hFne : F.Nonempty := by rw [hFdef, Set.Finite.toFinset_nonempty]; exact hne
  have hmemT : ∀ t, t ∈ F → t ∈ T := fun t ht => hfin.mem_toFinset.mp ht
  have setToF : ∀ f : E → ℝ, (⨆ t ∈ F, f t) = ⨆ t ∈ T, f t :=
    fun f => iSup_congr fun t => by rw [hfin.mem_toFinset]
  -- Canonical anchor `a₀` = the seq-0 singleton point.
  obtain ⟨a₀, ha₀seq⟩ := Finset.card_eq_one.mp A.card_zero
  have ha₀mem : a₀ ∈ A.seq 0 := by rw [ha₀seq]; exact Finset.mem_singleton_self a₀
  have ha₀T : a₀ ∈ T := A.subset_carrier 0 (Finset.mem_coe.mpr ha₀mem)
  have hπ0 : ∀ t : E, netProj (A.seq 0) t = a₀ := by
    intro t; rw [ha₀seq]
    have hmem := netProj_mem (Finset.singleton_nonempty a₀) t
    rwa [Finset.mem_singleton] at hmem
  -- √2 bricks.
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2sq, hs2nn]
  have hw2 : ∀ k : ℕ, (Real.sqrt 2 ^ k) ^ 2 = 2 ^ k := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  by_cases hK0 : K = 0
  · -- K = 0: all increments vanish a.e., so the anchored sup is a.e. 0.
    have hz : ∀ᵐ ω ∂μ, ∀ t ∈ T, X t ω - X t₀ ω = 0 := by
      rw [ae_ball_iff hfin.countable]
      intro t ht
      have hnorm : subGaussianNorm (fun ω => X t ω - X t₀ ω) μ = 0 := by
        have h := hinc t₀ ht₀ t ht
        rw [hK0] at h
        simp only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at h
        exact h
      exact ae_eq_zero_of_subGaussianNorm_eq_zero ((hmeas t ht).sub (hmeas t₀ ht₀)) hnorm
    have hallz : ∀ᵐ ω ∂μ, (⨆ t ∈ T, |X t ω - X t₀ ω|) ≤ 0 := by
      filter_upwards [hz] with ω hω
      exact biSup_le_of_finite hfin hne _ (fun s hs => by rw [hω s hs, abs_zero])
    have hthr0 : (12 + 4 * u) * (K : ℝ) * G = 0 := by rw [hK0]; simp
    rw [hthr0]
    have hnull : μ {ω | (0 : ℝ) < ⨆ t ∈ T, |X t ω - X t₀ ω|} = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp hallz)
      simp only [Set.mem_setOf_eq, not_le]; exact hω
    rw [hnull]; exact zero_le _
  · -- Main case: K > 0.
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : (0 : ℝ≥0) < K := lt_of_le_of_ne (zero_le K) (Ne.symm hK0)
      exact_mod_cast this
    set thr : ℝ := (12 + 4 * u) * (K : ℝ) * G with hthr
    -- Number of chaining levels: past `n` every point has a net point at distance 0.
    obtain ⟨n, hn⟩ := A.exists_eventually_dist_zero hfin hA
    -- Projections onto the admissible levels.
    have hprojmem : ∀ k : ℕ, ∀ t : E, netProj (A.seq k) t ∈ A.seq k :=
      fun k t => netProj_mem (A.nonempty k) t
    have hprojT : ∀ k : ℕ, ∀ t : E, netProj (A.seq k) t ∈ T :=
      fun k t => A.subset_carrier k (Finset.mem_coe.mpr (hprojmem k t))
    have hprojdist : ∀ k : ℕ, ∀ t : E,
        dist t (netProj (A.seq k) t) ≤ Metric.infDist t ↑(A.seq k) := by
      intro k t
      have hcpt : IsCompact (↑(A.seq k) : Set E) := (A.seq k).finite_toSet.isCompact
      have hnek : (↑(A.seq k) : Set E).Nonempty := Finset.coe_nonempty.mpr (A.nonempty k)
      obtain ⟨b, hb_mem, hb_eq⟩ := hcpt.exists_infDist_eq_dist hnek t
      exact dist_netProj_le ⟨b, Finset.mem_coe.mp hb_mem, le_of_eq hb_eq.symm⟩
    -- Chain end: `X (π_n t) = X t` a.e.
    have hfine0 : ∀ t ∈ T, dist t (netProj (A.seq n) t) = 0 := by
      intro t ht
      obtain ⟨a, ha_mem, ha0⟩ := hn n le_rfl t ht
      have hinf0 : Metric.infDist t ↑(A.seq n) = 0 :=
        le_antisymm
          (le_trans (Metric.infDist_le_dist_of_mem (Finset.mem_coe.mpr ha_mem)) ha0.le)
          Metric.infDist_nonneg
      exact le_antisymm (le_trans (hprojdist n t) hinf0.le) dist_nonneg
    have hclean : ∀ᵐ ω ∂μ, ∀ t ∈ T, X (netProj (A.seq n) t) ω = X t ω := by
      rw [hfin.eventually_all]
      intro t ht
      have hsub := hinc.sub_ae_eq_zero (hmeas t ht) (hmeas (netProj (A.seq n) t) (hprojT n t))
        ht (hprojT n t) (hfine0 t ht)
      filter_upwards [hsub] with ω hω
      have : X (netProj (A.seq n) t) ω - X t ω = 0 := hω
      linarith
    -- Per-level threshold sequence and pair sets.
    set L₆ : ℝ := Real.sqrt (6 * Real.log 2) with hL6
    have hL6nn : 0 ≤ L₆ := Real.sqrt_nonneg _
    set s : ℕ → ℝ := fun k => Real.sqrt 2 ^ k * L₆ + Real.sqrt ((k : ℝ) + 1) + u with hsdef
    have hs_nn : ∀ k, 0 ≤ s k := fun k =>
      add_nonneg (add_nonneg (mul_nonneg (pow_nonneg hs2nn k) hL6nn) (Real.sqrt_nonneg _)) hu
    set PS : ℕ → Finset (E × E) := fun k => A.seq (k + 1) ×ˢ A.seq k with hPSdef
    -- The γ-functional dominates every finite partial series.
    have hPle : ∀ t ∈ T, ∀ m : ℕ,
        ∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k) ≤ G := by
      intro t ht m
      rw [hGdef]
      have h1 : ∑ k ∈ Finset.range m,
            ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
          ≤ gammaFunctional A := by
        refine le_trans (ENNReal.sum_le_tsum (Finset.range m)) ?_
        exact le_iSup₂ (f := fun t (_ : t ∈ T) =>
          ∑' k, ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) t ht
      have h2 := ENNReal.toReal_mono hA h1
      rw [ENNReal.toReal_sum (fun k _ => ENNReal.ofReal_ne_top)] at h2
      rw [Finset.sum_congr rfl (fun k _ => ENNReal.toReal_ofReal
        (mul_nonneg (pow_nonneg hs2nn k) Metric.infDist_nonneg))] at h2
      exact h2
    -- Per-pair sub-gaussian tail: `μ {K d(a,b) s_k < |X_a − X_b|} ≤ 2 exp(−s_k²)`.
    have hpair : ∀ k, ∀ p ∈ PS k,
        μ {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(s k) ^ 2)) := by
      intro k p hp
      rw [hPSdef, Finset.mem_product] at hp
      have hp1T : p.1 ∈ T := A.subset_carrier (k + 1) (Finset.mem_coe.mpr hp.1)
      have hp2T : p.2 ∈ T := A.subset_carrier k (Finset.mem_coe.mpr hp.2)
      rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist p.1 p.2) with hd0 | hdpos
      · -- degenerate `dist = 0`: increment vanishes a.e.
        have haez : (fun ω => X p.1 ω - X p.2 ω) =ᵐ[μ] 0 :=
          hinc.sub_ae_eq_zero (hmeas p.2 hp2T) (hmeas p.1 hp1T) hp2T hp1T
            (by rw [dist_comm]; exact hd0.symm)
        have haene : ∀ᵐ ω ∂μ, X p.1 ω - X p.2 ω = 0 := by
          filter_upwards [haez] with ω hω; exact hω
        have hnull : μ {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|} = 0 := by
          refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp haene)
          simp only [Set.mem_setOf_eq] at hω ⊢
          intro h0
          rw [h0, abs_zero] at hω
          have : (0 : ℝ) ≤ (K : ℝ) * dist p.1 p.2 * s k :=
            mul_nonneg (mul_nonneg hKpos.le dist_nonneg) (hs_nn k)
          linarith
        rw [hnull]; exact zero_le _
      · -- non-degenerate: B1 tail with an exact exponent.
        have hdpos' : 0 < dist p.2 p.1 := by rw [dist_comm]; exact hdpos
        have hKd : 0 < (K : ℝ) * dist p.2 p.1 := mul_pos hKpos hdpos'
        have hτ0 : 0 ≤ (K : ℝ) * dist p.1 p.2 * s k :=
          mul_nonneg (mul_nonneg hKpos.le dist_nonneg) (hs_nn k)
        have htail := hinc.measure_abs_sub_ge_le (hmeas p.2 hp2T) (hmeas p.1 hp1T)
          hp2T hp1T hKd hτ0
        have hsub01 : {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|}
            ⊆ {ω | (K : ℝ) * dist p.1 p.2 * s k ≤ |X p.1 ω - X p.2 ω|} := by
          intro ω h; simp only [Set.mem_setOf_eq] at h ⊢; exact le_of_lt h
        refine le_trans (measure_mono hsub01) (le_trans htail ?_)
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        refine le_of_eq (congrArg Real.exp ?_)
        rw [dist_comm p.1 p.2]
        have hAnz : ((K : ℝ) * dist p.2 p.1) ≠ 0 := hKd.ne'
        field_simp
        try ring
    -- Per-level union bound.
    have hlevel : ∀ k, μ (⋃ p ∈ PS k,
          {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|})
        ≤ ENNReal.ofReal (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
      intro k
      have hreal : ((PS k).card : ℝ) * (2 * Real.exp (-(s k) ^ 2))
          ≤ 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by
        set Q : ℝ := 2 ^ (3 * 2 ^ k) with hQ
        have hQpos : 0 < Q := by rw [hQ]; positivity
        have hQ1 : (1 : ℝ) ≤ Q := by rw [hQ]; exact one_le_pow₀ (by norm_num)
        have hMle : ((PS k).card : ℝ) ≤ Q := by
          rw [hPSdef, hQ, Finset.card_product]
          have hc1 : ((A.seq (k + 1)).card : ℝ) ≤ 2 ^ 2 ^ (k + 1) := by
            exact_mod_cast A.card_le (k + 1)
          have hc2 : ((A.seq k).card : ℝ) ≤ 2 ^ 2 ^ k := by exact_mod_cast A.card_le k
          calc (((A.seq (k + 1)).card * (A.seq k).card : ℕ) : ℝ)
              = ((A.seq (k + 1)).card : ℝ) * ((A.seq k).card : ℝ) := by push_cast; ring
            _ ≤ (2 ^ 2 ^ (k + 1) : ℝ) * (2 ^ 2 ^ k : ℝ) :=
                mul_le_mul hc1 hc2 (by positivity) (by positivity)
            _ = (2 : ℝ) ^ (3 * 2 ^ k) := by
                rw [← pow_add]; congr 1; rw [pow_succ]; ring
        have hssq : 6 * 2 ^ k * Real.log 2 + ((k : ℝ) + 1) + u ^ 2 ≤ (s k) ^ 2 := by
          have ha : (0 : ℝ) ≤ Real.sqrt 2 ^ k * L₆ := mul_nonneg (pow_nonneg hs2nn k) hL6nn
          have hb : (0 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
          have hL6sq : L₆ ^ 2 = 6 * Real.log 2 := by rw [hL6, Real.sq_sqrt (by positivity)]
          have hsq1 : (Real.sqrt 2 ^ k * L₆) ^ 2 = 6 * 2 ^ k * Real.log 2 := by
            rw [mul_pow, hw2, hL6sq]; ring
          have hsq2 : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
          simp only [hsdef]
          nlinarith [ha, hb, hu, hsq1, hsq2, mul_nonneg ha hb, mul_nonneg ha hu, mul_nonneg hb hu]
        have hQlog : Real.log (Q ^ 2) = 6 * 2 ^ k * Real.log 2 := by
          rw [hQ, ← pow_mul, Real.log_pow]; push_cast; ring
        have hexpQ : Real.exp (-(6 * 2 ^ k * Real.log 2)) = (Q ^ 2)⁻¹ := by
          rw [← hQlog, Real.exp_neg, Real.exp_log (by positivity)]
        have hchain : Real.exp (-(s k) ^ 2)
            ≤ (Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by
          calc Real.exp (-(s k) ^ 2)
              ≤ Real.exp (-(6 * 2 ^ k * Real.log 2 + ((k : ℝ) + 1) + u ^ 2)) :=
                Real.exp_le_exp.mpr (by linarith [hssq])
            _ = Real.exp (-(6 * 2 ^ k * Real.log 2)) * Real.exp (-((k : ℝ) + 1))
                  * Real.exp (-u ^ 2) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
            _ = (Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by rw [hexpQ]
        calc ((PS k).card : ℝ) * (2 * Real.exp (-(s k) ^ 2))
            ≤ Q * (2 * ((Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2))) := by
              apply mul_le_mul hMle _ (by positivity) hQpos.le
              exact mul_le_mul_of_nonneg_left hchain (by norm_num)
          _ ≤ 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by
              rw [show Q * (2 * ((Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)))
                    = (Q * (Q ^ 2)⁻¹) * (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) from
                    by ring]
              apply mul_le_of_le_one_left (by positivity)
              rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hQpos.ne', one_mul]
              exact (inv_le_one₀ hQpos).mpr hQ1
      calc μ (⋃ p ∈ PS k, {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|})
          ≤ ∑ p ∈ PS k, μ {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|} :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ _p ∈ PS k, ENNReal.ofReal (2 * Real.exp (-(s k) ^ 2)) :=
            Finset.sum_le_sum (fun p hp => hpair k p hp)
        _ = (PS k).card • ENNReal.ofReal (2 * Real.exp (-(s k) ^ 2)) := by rw [Finset.sum_const]
        _ ≤ ENNReal.ofReal (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
            rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast ((PS k).card),
              ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal hreal
    -- Deterministic threshold sum: `∑ (ρ_{k+1}+ρ_k) s_k ≤ (6+2u) G`.
    have hsumG : ∀ t ∈ T, ∑ k ∈ Finset.range n,
        (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
          ≤ (6 + 2 * u) * G := by
      intro t ht
      have hinfnn : ∀ k : ℕ, (0 : ℝ) ≤ Metric.infDist t ↑(A.seq k) := fun k => Metric.infDist_nonneg
      have hS0 : ∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k) ≤ G :=
        hPle t ht n
      have hS1 : Real.sqrt 2
          * ∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)) ≤ G := by
        have heq : Real.sqrt 2
              * ∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
            = ∑ k ∈ Finset.range n, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ]; ring)
        rw [heq]
        calc ∑ k ∈ Finset.range n, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1))
            ≤ ∑ k ∈ Finset.range (n + 1), Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k) := by
              rw [Finset.sum_range_succ' (fun k => Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)) n]
              have h0 : (0 : ℝ) ≤ Real.sqrt 2 ^ 0 * Metric.infDist t ↑(A.seq 0) :=
                mul_nonneg (by positivity) (hinfnn 0)
              linarith
          _ ≤ G := hPle t ht (n + 1)
      have hR0 : ∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq k) ≤ G := by
        refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) hS0
        have h1 : (1 : ℝ) ≤ Real.sqrt 2 ^ k := one_le_pow₀ hs2ge1
        nlinarith [hinfnn k, h1]
      have hR1 : ∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq (k + 1)) ≤ G := by
        have hstep : ∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq (k + 1))
            ≤ ∑ k ∈ Finset.range n, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1)) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have h1 : (1 : ℝ) ≤ Real.sqrt 2 ^ (k + 1) := one_le_pow₀ hs2ge1
          nlinarith [hinfnn (k + 1), h1]
        have heq : ∑ k ∈ Finset.range n, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1))
            = Real.sqrt 2
              * ∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ]; ring)
        rw [heq] at hstep; linarith [hstep, hS1]
      -- key numeric slack.
      have key0 : (L₆ + 1) * (Real.sqrt 2 + 1) ≤ 6 * Real.sqrt 2 := by
        have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
        have hL6sq : L₆ ^ 2 = 6 * Real.log 2 := by rw [hL6, Real.sq_sqrt (by positivity)]
        have hL6bd : L₆ ≤ 2.04 := by nlinarith [hL6sq, hL6nn, hlog]
        have hs2lb : 1.414 ≤ Real.sqrt 2 := by nlinarith [hs2sq, hs2nn]
        have hs2ub : Real.sqrt 2 ≤ 1.4143 := by nlinarith [hs2sq, hs2nn]
        nlinarith [hL6bd, hL6nn, hs2lb, hs2ub, mul_nonneg hL6nn hs2nn]
      -- per-term bound `(ρ_{k+1}+ρ_k) s_k ≤ (L₆+1)(√2^k ρ_{k+1} + √2^k ρ_k) + u(ρ_{k+1}+ρ_k)`.
      have hterm_le : ∀ k ∈ Finset.range n,
          (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
            ≤ (L₆ + 1) * (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
                + Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
              + u * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) := by
        intro k _
        have hsqrtk : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt 2 ^ k := by
          have hk2 : (k : ℝ) + 1 ≤ 2 ^ k := by
            exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self)
          have hle2 : Real.sqrt ((k : ℝ) + 1) ^ 2 ≤ (Real.sqrt 2 ^ k) ^ 2 := by
            rw [Real.sq_sqrt (by positivity), hw2]; exact hk2
          exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (pow_nonneg hs2nn k) two_ne_zero).mp hle2
        have hsk : s k ≤ Real.sqrt 2 ^ k * (L₆ + 1) + u := by
          simp only [hsdef]; nlinarith [hsqrtk, pow_nonneg hs2nn k, hL6nn]
        have hnn : (0 : ℝ) ≤ Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k) :=
          add_nonneg (hinfnn (k + 1)) (hinfnn k)
        calc (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
            ≤ (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k))
                * (Real.sqrt 2 ^ k * (L₆ + 1) + u) := mul_le_mul_of_nonneg_left hsk hnn
          _ = (L₆ + 1) * (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
                + Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
              + u * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) := by ring
      calc ∑ k ∈ Finset.range n,
            (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
          ≤ ∑ k ∈ Finset.range n,
              ((L₆ + 1) * (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
                  + Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
                + u * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k))) :=
            Finset.sum_le_sum hterm_le
        _ = (L₆ + 1) * ((∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                + (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)))
              + u * ((∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq (k + 1)))
                + (∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq k))) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ ≤ (6 + 2 * u) * G := by
            have hL1nn : (0 : ℝ) ≤ L₆ + 1 := by linarith [hL6nn]
            have hs2pos : (0 : ℝ) < Real.sqrt 2 := by linarith [hs2ge1]
            have hLpart : (L₆ + 1)
                * ((∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                  + (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)))
                ≤ 6 * G := by
              have hb : Real.sqrt 2
                    * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                  + Real.sqrt 2
                    * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
                  ≤ G + Real.sqrt 2 * G := by
                have := mul_le_mul_of_nonneg_left hS0 hs2pos.le
                linarith [hS1, this]
              have hkey : Real.sqrt 2 * ((L₆ + 1)
                    * ((∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                      + (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))))
                  ≤ Real.sqrt 2 * (6 * G) := by
                have hstep : Real.sqrt 2 * ((L₆ + 1)
                      * ((∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                        + (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))))
                    = (L₆ + 1) * (Real.sqrt 2
                        * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                      + Real.sqrt 2
                        * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) := by
                  ring
                rw [hstep]
                calc (L₆ + 1) * (Real.sqrt 2
                        * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                      + Real.sqrt 2
                        * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)))
                    ≤ (L₆ + 1) * (G + Real.sqrt 2 * G) := mul_le_mul_of_nonneg_left hb hL1nn
                  _ = (L₆ + 1) * (Real.sqrt 2 + 1) * G := by ring
                  _ ≤ 6 * Real.sqrt 2 * G := by nlinarith [key0, hG0]
                  _ = Real.sqrt 2 * (6 * G) := by ring
              exact le_of_mul_le_mul_left hkey hs2pos
            have hupart : u * ((∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq (k + 1)))
                  + (∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq k))) ≤ 2 * u * G := by
              nlinarith [mul_nonneg hu (sub_nonneg.mpr hR1), mul_nonneg hu (sub_nonneg.mpr hR0)]
            nlinarith [hLpart, hupart]
    -- On the good event the anchored sup is ≤ (6+2u) K G.
    have hgood : ∀ ω, (∀ t ∈ T, X (netProj (A.seq n) t) ω = X t ω) →
        (∀ k ∈ Finset.range n, ∀ p ∈ PS k,
          ¬ ((K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|)) →
        (⨆ t ∈ T, |X t ω - X a₀ ω|) ≤ (6 + 2 * u) * (K : ℝ) * G := by
      intro ω hω hnb
      rw [← setToF (fun t => |X t ω - X a₀ ω|), biSup_finset_eq_sup' hFne]
      refine Finset.sup'_le hFne _ (fun t htF => ?_)
      have htT := hmemT t htF
      have htel : X t ω - X a₀ ω = ∑ k ∈ Finset.range n,
          (X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω) := by
        have h0 : X (netProj (A.seq 0) t) ω = X a₀ ω := by rw [hπ0 t]
        have hnn : X (netProj (A.seq n) t) ω = X t ω := hω t htT
        rw [← hnn, ← h0]
        exact chain_telescope (fun i => X (netProj (A.seq i) t) ω)
      have hpb : ∀ k ∈ Finset.range n,
          |X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω|
            ≤ (K : ℝ) * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k := by
        intro k hk
        have hpair_mem : (netProj (A.seq (k + 1)) t, netProj (A.seq k) t) ∈ PS k := by
          rw [hPSdef, Finset.mem_product]; exact ⟨hprojmem (k + 1) t, hprojmem k t⟩
        have hnot := hnb k hk _ hpair_mem
        push_neg at hnot
        have hdle : dist (netProj (A.seq (k + 1)) t) (netProj (A.seq k) t)
            ≤ Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k) := by
          calc dist (netProj (A.seq (k + 1)) t) (netProj (A.seq k) t)
              ≤ dist (netProj (A.seq (k + 1)) t) t + dist t (netProj (A.seq k) t) :=
                dist_triangle _ _ _
            _ = dist t (netProj (A.seq (k + 1)) t) + dist t (netProj (A.seq k) t) := by
                rw [dist_comm (netProj (A.seq (k + 1)) t) t]
            _ ≤ Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k) :=
                add_le_add (hprojdist (k + 1) t) (hprojdist k t)
        calc |X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω|
            ≤ (K : ℝ) * dist (netProj (A.seq (k + 1)) t) (netProj (A.seq k) t) * s k := hnot
          _ ≤ (K : ℝ) * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k := by
              apply mul_le_mul_of_nonneg_right _ (hs_nn k)
              exact mul_le_mul_of_nonneg_left hdle hKpos.le
      calc |X t ω - X a₀ ω|
          = |∑ k ∈ Finset.range n,
              (X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω)| := by rw [htel]
        _ ≤ ∑ k ∈ Finset.range n,
              |X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n,
              (K : ℝ) * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k :=
            Finset.sum_le_sum hpb
        _ = (K : ℝ) * ∑ k ∈ Finset.range n,
              (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
        _ ≤ (K : ℝ) * ((6 + 2 * u) * G) :=
            mul_le_mul_of_nonneg_left (hsumG t htT) hKpos.le
        _ = (6 + 2 * u) * (K : ℝ) * G := by ring
    -- Arbitrary anchor is at most twice the canonical one.
    have hreduce : ∀ ω, (⨆ t ∈ T, |X t ω - X t₀ ω|) ≤ 2 * ⨆ t ∈ T, |X t ω - X a₀ ω| := by
      intro ω
      have hHnn : (0 : ℝ) ≤ ⨆ t ∈ T, |X t ω - X a₀ ω| := by
        rw [← setToF (fun t => |X t ω - X a₀ ω|), biSup_finset_eq_sup' hFne]
        exact le_trans (abs_nonneg _)
          (Finset.le_sup' (fun t => |X t ω - X a₀ ω|) (hfin.mem_toFinset.mpr ha₀T))
      refine biSup_le_of_finite hfin hne _ (fun t htT => ?_)
      have hta : |X t ω - X a₀ ω| ≤ ⨆ t' ∈ T, |X t' ω - X a₀ ω| :=
        le_biSup_of_finite hfin (fun t' => |X t' ω - X a₀ ω|) htT
      have ht0a : |X t₀ ω - X a₀ ω| ≤ ⨆ t' ∈ T, |X t' ω - X a₀ ω| :=
        le_biSup_of_finite hfin (fun t' => |X t' ω - X a₀ ω|) ht₀
      have htri := abs_sub_le (X t ω) (X a₀ ω) (X t₀ ω)
      have hcomm : |X a₀ ω - X t₀ ω| = |X t₀ ω - X a₀ ω| := abs_sub_comm _ _
      rw [hcomm] at htri
      linarith [hta, ht0a, htri]
    -- The bad set collects all per-level pair-events.
    set BAD : Set Ω := ⋃ k ∈ Finset.range n, ⋃ p ∈ PS k,
      {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|} with hBAD
    have hBADmeas : μ BAD ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
      rw [hBAD]
      calc μ (⋃ k ∈ Finset.range n, ⋃ p ∈ PS k,
              {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|})
          ≤ ∑ k ∈ Finset.range n, μ (⋃ p ∈ PS k,
              {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|}) :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ k ∈ Finset.range n,
              ENNReal.ofReal (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) :=
            Finset.sum_le_sum (fun k _ => hlevel k)
        _ = ENNReal.ofReal
              (∑ k ∈ Finset.range n, 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
        _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [show (∑ k ∈ Finset.range n, 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2))
                  = (2 * Real.exp (-u ^ 2)) * ∑ k ∈ Finset.range n, Real.exp (-((k : ℝ) + 1)) from
                by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)]
            have hle := mul_le_mul_of_nonneg_left (sum_exp_neg_succ_le_one n)
              (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-u ^ 2))
            linarith [hle]
    -- The target event is contained in `BAD` plus the null clean-complement.
    have hincl : {ω | thr < ⨆ t ∈ T, |X t ω - X t₀ ω|}
        ⊆ BAD ∪ {ω | ¬ (∀ t ∈ T, X (netProj (A.seq n) t) ω = X t ω)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      by_contra hcon
      rw [Set.mem_union, not_or] at hcon
      obtain ⟨hnBAD, hnclean⟩ := hcon
      simp only [Set.mem_setOf_eq, not_not] at hnclean
      have hnb : ∀ k ∈ Finset.range n, ∀ p ∈ PS k,
          ¬ ((K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|) := by
        intro k hk p hp hlt
        exact hnBAD (by rw [hBAD]; exact Set.mem_biUnion hk (Set.mem_biUnion hp hlt))
      have hb := hgood ω hnclean hnb
      have hle : (⨆ t ∈ T, |X t ω - X t₀ ω|) ≤ thr := by
        rw [hthr]
        calc ⨆ t ∈ T, |X t ω - X t₀ ω| ≤ 2 * ⨆ t ∈ T, |X t ω - X a₀ ω| := hreduce ω
          _ ≤ 2 * ((6 + 2 * u) * (K : ℝ) * G) := by linarith [hb]
          _ = (12 + 4 * u) * (K : ℝ) * G := by ring
      linarith [hω, hle]
    calc μ {ω | thr < ⨆ t ∈ T, |X t ω - X t₀ ω|}
        ≤ μ (BAD ∪ {ω | ¬ (∀ t ∈ T, X (netProj (A.seq n) t) ω = X t ω)}) := measure_mono hincl
      _ ≤ μ BAD + μ {ω | ¬ (∀ t ∈ T, X (netProj (A.seq n) t) ω = X t ω)} := measure_union_le _ _
      _ = μ BAD := by rw [ae_iff.mp hclean, add_zero]
      _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := hBADmeas

/-- Generic chaining, expectation form at a fixed admissible sequence (HDP
§8.5.2 + Remark 8.5.3 — no mean-zero for the `|X_t − X_{t₀}|` form).
Frozen constant `20` (formula `6 + 2√π ≤ 10`), integrating
`generic_chaining_tail` via `TailToExpectation`. -/
theorem generic_chaining_of_admissible {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T) :
    ENNReal.ofReal (∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ) ≤
      20 * K * gammaFunctional A := by
  -- Measurability and nonnegativity of the increment sup.
  have hZm : AEMeasurable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ :=
    aemeasurable_biSup_of_finite hfin (g := fun t ω => |X t ω - X t₀ ω|)
      (fun t ht => ((hmeas t ht).sub (hmeas t₀ ht₀)).abs)
  have hZ0 : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω| := by
    filter_upwards with ω
    exact Real.iSup_nonneg (fun t => Real.iSup_nonneg (fun _ => abs_nonneg _))
  by_cases hK0 : K = 0
  · -- K = 0: all increments vanish a.e., so the sup is a.e. 0.
    subst hK0
    have hz : ∀ᵐ ω ∂μ, ∀ t ∈ T, X t ω - X t₀ ω = 0 := by
      rw [ae_ball_iff hfin.countable]
      intro t ht
      have hnorm : subGaussianNorm (fun ω => X t ω - X t₀ ω) μ = 0 := by
        have h := hinc t₀ ht₀ t ht
        simp only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at h
        exact h
      exact ae_eq_zero_of_subGaussianNorm_eq_zero ((hmeas t ht).sub (hmeas t₀ ht₀)) hnorm
    have hZae : (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) =ᵐ[μ] 0 := by
      filter_upwards [hz] with ω hω
      have hup : (⨆ t ∈ T, |X t ω - X t₀ ω|) ≤ 0 :=
        biSup_le_of_finite hfin hne _ (fun s hs => by rw [hω s hs]; simp)
      have hlo : (0 : ℝ) ≤ ⨆ t ∈ T, |X t ω - X t₀ ω| :=
        Real.iSup_nonneg (fun t => Real.iSup_nonneg (fun _ => abs_nonneg _))
      simp only [Pi.zero_apply]
      linarith
    rw [integral_congr_ae hZae]
    simp
  · by_cases hγ : gammaFunctional A = ⊤
    · rw [hγ, ENNReal.mul_top (mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr hK0))]
      exact le_top
    · -- Main case: integrate the tail bound via `TailToExpectation`.
      have ha0 : (0 : ℝ) ≤ 12 * (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg (mul_nonneg (by norm_num) K.coe_nonneg) ENNReal.toReal_nonneg
      have hb0 : (0 : ℝ) ≤ 4 * (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg (mul_nonneg (by norm_num) K.coe_nonneg) ENNReal.toReal_nonneg
      have htail : ∀ u : ℝ, 0 ≤ u →
          μ {ω | 12 * (K : ℝ) * (gammaFunctional A).toReal
                + 4 * (K : ℝ) * (gammaFunctional A).toReal * u
              < ⨆ t ∈ T, |X t ω - X t₀ ω|}
            ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
        intro u hu
        have hval := generic_chaining_tail hfin hne hmeas hinc ht₀ A hγ hu
        have hthr : 12 * (K : ℝ) * (gammaFunctional A).toReal
              + 4 * (K : ℝ) * (gammaFunctional A).toReal * u
            = (12 + 4 * u) * (K : ℝ) * (gammaFunctional A).toReal := by ring
        have hset : {ω | 12 * (K : ℝ) * (gammaFunctional A).toReal
                + 4 * (K : ℝ) * (gammaFunctional A).toReal * u
              < ⨆ t ∈ T, |X t ω - X t₀ ω|}
            = {ω | (12 + 4 * u) * (K : ℝ) * (gammaFunctional A).toReal
              < ⨆ t ∈ T, |X t ω - X t₀ ω|} := by
          ext ω; simp only [Set.mem_setOf_eq, hthr]
        rw [hset]; exact hval
      have hInt : ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
          ≤ 12 * (K : ℝ) * (gammaFunctional A).toReal
            + Real.sqrt Real.pi * (4 * (K : ℝ) * (gammaFunctional A).toReal) :=
        integral_le_of_tail_le hZm hZ0 ha0 hb0 htail
      have hc : (0 : ℝ) ≤ (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg K.coe_nonneg ENNReal.toReal_nonneg
      have hsqrt : Real.sqrt Real.pi ≤ 2 := by
        nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_lt_d2]
      have hmid : 12 * (K : ℝ) * (gammaFunctional A).toReal
          + Real.sqrt Real.pi * (4 * (K : ℝ) * (gammaFunctional A).toReal)
          ≤ 20 * (K : ℝ) * (gammaFunctional A).toReal := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) hc, hc, hsqrt]
      have hfinal : ENNReal.ofReal (20 * (K : ℝ) * (gammaFunctional A).toReal)
          = 20 * ↑K * gammaFunctional A := by
        rw [show (20 : ℝ) * (K : ℝ) * (gammaFunctional A).toReal
              = 20 * ((K : ℝ) * (gammaFunctional A).toReal) from by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20),
            ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_toReal hγ, ENNReal.ofReal_ofNat]
        ring
      calc ENNReal.ofReal (∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ)
          ≤ ENNReal.ofReal (12 * (K : ℝ) * (gammaFunctional A).toReal
              + Real.sqrt Real.pi * (4 * (K : ℝ) * (gammaFunctional A).toReal)) :=
            ENNReal.ofReal_le_ofReal hInt
        _ ≤ ENNReal.ofReal (20 * (K : ℝ) * (gammaFunctional A).toReal) :=
            ENNReal.ofReal_le_ofReal hmid
        _ = 20 * ↑K * gammaFunctional A := hfinal

/-- **Theorem 8.5.2 (generic chaining bound)** (HDP §8.5.2; book's absolute
constant frozen `C = 10`): mean-zero process with sub-Gaussian increments
has `E sup X ≤ 10·K·γ₂(T,d)`, in `ofReal` form. -/
theorem generic_chaining {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (book WLOG; sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: integrability of the process, ruling out Bochner-junk
    -- means (batch reconciliation R4; the book's E X_t = 0 presupposes it)
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero process; HDP Thm 8.5.2
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ) :
    ENNReal.ofReal (∫ ω, ⨆ t ∈ T, X t ω ∂μ) ≤ 20 * K * gammaTwo T := by
  -- Anchor at a point of `T` (Remark 8.5.3 device).
  set t₀ := hne.some with ht₀def
  have ht₀ : t₀ ∈ T := hne.some_mem
  -- Measurability of the two increment sups.
  have hWm : AEMeasurable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ :=
    aemeasurable_biSup_of_finite hfin (g := fun t ω => |X t ω - X t₀ ω|)
      (fun t ht => ((hmeas t ht).sub (hmeas t₀ ht₀)).abs)
  have hSXm : AEMeasurable (fun ω => ⨆ t ∈ T, X t ω) μ :=
    aemeasurable_biSup_of_finite hfin (g := fun t ω => X t ω) (fun t ht => hmeas t ht)
  -- Integrability of the increment sup via domination by a finite sum.
  have hSumInt : Integrable (fun ω => ∑ t ∈ hfin.toFinset, |X t ω - X t₀ ω|) μ :=
    integrable_finset_sum _
      (fun t ht => ((hint t (hfin.mem_toFinset.mp ht)).sub (hint t₀ ht₀)).abs)
  have hWint : Integrable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ := by
    refine Integrable.mono' hSumInt hWm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.iSup_nonneg (fun t => Real.iSup_nonneg (fun _ => abs_nonneg _)))]
    exact biSup_le_of_finite hfin ⟨t₀, ht₀⟩ _
      (fun s hs => Finset.single_le_sum (f := fun t => |X t ω - X t₀ ω|)
        (fun i _ => abs_nonneg _) (hfin.mem_toFinset.mpr hs))
  -- Integrability of the process sup, sandwiched by `X t₀` and `X t₀ + sup |·|`.
  have hSXint : Integrable (fun ω => ⨆ t ∈ T, X t ω) μ := by
    refine Integrable.mono' ((hint t₀ ht₀).norm.add hWint) hSXm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    have hlo : X t₀ ω ≤ ⨆ t ∈ T, X t ω := le_biSup_of_finite hfin (fun t => X t ω) ht₀
    have hhi : ⨆ t ∈ T, X t ω ≤ X t₀ ω + ⨆ t ∈ T, |X t ω - X t₀ ω| := by
      refine biSup_le_of_finite hfin ⟨t₀, ht₀⟩ _ (fun s hs => ?_)
      have h1 : |X s ω - X t₀ ω| ≤ ⨆ t ∈ T, |X t ω - X t₀ ω| :=
        le_biSup_of_finite hfin (fun r => |X r ω - X t₀ ω|) hs
      have h2 := le_abs_self (X s ω - X t₀ ω)
      linarith
    have hW0 : (0 : ℝ) ≤ ⨆ t ∈ T, |X t ω - X t₀ ω| :=
      Real.iSup_nonneg (fun t => Real.iSup_nonneg (fun _ => abs_nonneg _))
    simp only [Real.norm_eq_abs, Pi.add_apply, abs_le]
    refine ⟨?_, ?_⟩
    · nlinarith [hlo, neg_abs_le (X t₀ ω), hW0]
    · nlinarith [hhi, le_abs_self (X t₀ ω), hW0]
  -- E sup X ≤ E sup |X − X t₀| (mean-zero anchor cancels).
  have hred : ∫ ω, ⨆ t ∈ T, X t ω ∂μ ≤ ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ := by
    have hbound : ∫ ω, ⨆ t ∈ T, X t ω ∂μ
        ≤ ∫ ω, (X t₀ ω + ⨆ t ∈ T, |X t ω - X t₀ ω|) ∂μ := by
      refine integral_mono hSXint ((hint t₀ ht₀).add hWint) (fun ω => ?_)
      refine biSup_le_of_finite hfin ⟨t₀, ht₀⟩ _ (fun s hs => ?_)
      have h1 : |X s ω - X t₀ ω| ≤ ⨆ t ∈ T, |X t ω - X t₀ ω| :=
        le_biSup_of_finite hfin (fun r => |X r ω - X t₀ ω|) hs
      have h2 := le_abs_self (X s ω - X t₀ ω)
      linarith
    rwa [integral_add (hint t₀ ht₀) hWint, hmean t₀ ht₀, zero_add] at hbound
  refine le_trans (ENNReal.ofReal_le_ofReal hred) ?_
  haveI : Nonempty (AdmissibleSequence T) := nonempty_admissibleSequence hne
  have ha_top : (20 : ℝ≥0∞) * ↑K ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  have hpush : (20 : ℝ≥0∞) * ↑K * gammaTwo T
      = ⨅ A : AdmissibleSequence T, 20 * ↑K * gammaFunctional A := by
    rw [show gammaTwo T = ⨅ A : AdmissibleSequence T, gammaFunctional A from rfl]
    exact ENNReal.mul_iInf (fun h => absurd h ha_top)
  rw [hpush]
  exact le_iInf (fun A => generic_chaining_of_admissible hfin hne hmeas hinc ht₀ A)

/-- Theorem 8.5.2, real display (LEAN-ONLY: via `gammaTwo_lt_top_of_finite`
the `ℝ≥0∞` bound descends to `ℝ`). -/
theorem generic_chaining_real {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: integrability (R4, as above)
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero process; HDP Thm 8.5.2
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ) :
    ∫ ω, ⨆ t ∈ T, X t ω ∂μ ≤ 20 * K * (gammaTwo T).toReal := by
  have h3 := generic_chaining hfin hne hmeas hint hmean hinc
  have htop : (20 : ℝ≥0∞) * ↑K * gammaTwo T ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
      (gammaTwo_lt_top_of_finite hfin hne).ne
  rw [ENNReal.ofReal_le_iff_le_toReal htop, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.coe_toReal] at h3
  exact h3

end StatLean.ConcentrationInequalities
