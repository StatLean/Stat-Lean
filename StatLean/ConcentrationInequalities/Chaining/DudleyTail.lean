import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
import StatLean.ConcentrationInequalities.Chaining.PsiTwoMaximal
import StatLean.ConcentrationInequalities.Chaining.DyadicNets
import StatLean.ConcentrationInequalities.Chaining.EntropySum
import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# High-probability Dudley inequality (Eq. (8.15) / Exercise 8.1)

The tail form of Dudley's inequality for a finite index set: with
probability at least $1 - 2e^{-u^2}$,
$$ \sup_{s,t \in T} |X_t - X_s| \;\le\; C K \Bigl[
     \int_0^{D} \sqrt{\log \mathcal{N}(T,d,\varepsilon)}\, d\varepsilon
     + u \cdot \operatorname{diam} T \Bigr], $$
via per-level tail thresholds $\sqrt{2\log N_k} + \sqrt{k - \kappa'} + u$
instead of per-level expectations. No mean-zero hypothesis. We state a sharp
three-term core and the book-shaped display corollary.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Remark 8.1.6 / Eq. (8.15) (stated there as
Exercise 8.1 — we prove it).

**Proof formalization notes.** The three-term core achieves the book's exact
failure probability `2exp(−u²)`: per-level threshold
`3K·2^{−k}·(√(2 log N_k) + √(k−κ') + u)` over `closePairs`, the
`(a+b+c)² ≥ a²+b²+c²` inflation, and the geometric union bound give failure
probability `≤ 2/(e−1)·e^{−u²} ≤ 1.17·e^{−u²} ≤ 2e^{−u²}` — the book's
`2exp(−u²)` is MET exactly, no deviation. Frozen core constants: event bound
`K·(9·dudleySum + 17·diam + 12·u·diam)` (chosen with ≥ 15% slack in the
per-level threshold algebra). The display form absorbs the bare `diam` term
via `diam·√log2 ≤ 8·dudleyIntegral` (`Chaining/EntropySum.lean`) into the
frozen display constant `200`. This file shares the Step-2/Step-3 event
pattern with `Chaining/GenericChaining.lean` — accepted small duplication in
exchange for pairwise-disjoint parallel proof sessions; the shared
tail-integrates-to-expectation step is factored in
`Chaining/TailToExpectation.lean`. Named-sorry fallback of this work item:
`dudley_tail` (the display form with diameter absorption), with
`dudley_tail_three_term` proved.

**Bibliographic comments.** The high-probability form of Dudley's bound is
folklore refinement of Dudley (1967) by the concentration-of-chaining
argument; the exposition followed here is HDP §8.1 (Exercise 8.1) and
Talagrand, *Upper and Lower Bounds for Stochastic Processes*, 2014, §2.2
(where it appears as the tail version of the generic chaining bound
specialized to entropy numbers). See the HDP Chapter 8 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option maxRecDepth 4000

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- Geometric tail: `∑_{i<n} 2^{-(i+1)} ≤ 1`. -/
private lemma sum_half_succ_le_one (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1) ≤ 1 := by
  have hrw : ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1)
      = (1 / 2) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
  rw [hrw]; linarith [sum_geometric_two_le n]

/-- Closed form for the weighted geometric sum `∑_{i<n} (i+1)2^{-(i+1)}`. -/
private lemma sum_succ_half_succ (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (1 / 2) ^ (i + 1)
      = 2 - ((n : ℝ) + 2) * (1 / 2) ^ n := by
  induction n with
  | zero => norm_num
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Weighted geometric bound `∑_{i<n} (i+1)2^{-(i+1)} ≤ 2`. -/
private lemma sum_succ_half_succ_le_two (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * (1 / 2) ^ (i + 1) ≤ 2 := by
  rw [sum_succ_half_succ]
  have : (0 : ℝ) ≤ ((n : ℝ) + 2) * (1 / 2) ^ n := by positivity
  linarith

/-- Cauchy–Schwarz: `∑_{i<n} 2^{-(i+1)}√(i+1) ≤ √2`. Sharp bound driving the
frozen diameter constant `17` (needs `12√2 ≈ 16.97 < 17`). -/
private lemma sum_half_succ_sqrt_le_sqrt_two (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1) * Real.sqrt ((i : ℝ) + 1)
      ≤ Real.sqrt 2 := by
  set s := Finset.range n
  set f : ℕ → ℝ := fun i => Real.sqrt ((1 / 2 : ℝ) ^ (i + 1)) with hf
  set g : ℕ → ℝ := fun i => Real.sqrt ((i : ℝ) + 1) * Real.sqrt ((1 / 2 : ℝ) ^ (i + 1))
    with hg
  have hfg : ∀ i, f i * g i = (1 / 2 : ℝ) ^ (i + 1) * Real.sqrt ((i : ℝ) + 1) := by
    intro i
    have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (i + 1) := by positivity
    simp only [hf, hg]
    rw [show Real.sqrt ((1 / 2 : ℝ) ^ (i + 1))
          * (Real.sqrt ((i : ℝ) + 1) * Real.sqrt ((1 / 2 : ℝ) ^ (i + 1)))
        = (Real.sqrt ((1 / 2 : ℝ) ^ (i + 1)) * Real.sqrt ((1 / 2 : ℝ) ^ (i + 1)))
          * Real.sqrt ((i : ℝ) + 1) by ring, Real.mul_self_sqrt hpos]
  have hf2 : ∀ i, f i ^ 2 = (1 / 2 : ℝ) ^ (i + 1) := fun i => by
    simp only [hf]; rw [Real.sq_sqrt (by positivity)]
  have hg2 : ∀ i, g i ^ 2 = ((i : ℝ) + 1) * (1 / 2 : ℝ) ^ (i + 1) := fun i => by
    simp only [hg]; rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s f g
  rw [Finset.sum_congr rfl (fun i _ => hfg i), Finset.sum_congr rfl (fun i _ => hf2 i),
    Finset.sum_congr rfl (fun i _ => hg2 i)] at hCS
  have hsumnn : (0 : ℝ) ≤ ∑ i ∈ s, (1 / 2 : ℝ) ^ (i + 1) * Real.sqrt ((i : ℝ) + 1) :=
    Finset.sum_nonneg fun i _ => by positivity
  refine (Real.le_sqrt hsumnn (by norm_num)).mpr (le_trans hCS ?_)
  calc (∑ i ∈ s, (1 / 2 : ℝ) ^ (i + 1)) * ∑ i ∈ s, ((i : ℝ) + 1) * (1 / 2) ^ (i + 1)
      ≤ 1 * 2 :=
        mul_le_mul (sum_half_succ_le_one n) (sum_succ_half_succ_le_two n)
          (Finset.sum_nonneg fun i _ => by positivity) (by norm_num)
    _ = 2 := by norm_num

/-- Exponential geometric tail `∑_{i<n} exp(-(i+1)) ≤ 1`, via `exp(-1) ≤ 1/2`. -/
private lemma sum_exp_neg_succ_le_one (n : ℕ) :
    ∑ i ∈ Finset.range n, Real.exp (-((i : ℝ) + 1)) ≤ 1 := by
  have he1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hterm : ∀ i ∈ Finset.range n, Real.exp (-((i : ℝ) + 1)) ≤ (1 / 2 : ℝ) ^ (i + 1) := by
    intro i _
    have hei : Real.exp (-((i : ℝ) + 1)) = Real.exp (-1) ^ (i + 1) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hei]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) he1 (i + 1)
  exact le_trans (Finset.sum_le_sum hterm) (sum_half_succ_le_one n)

/-- **High-probability Dudley, sharp three-term core** (HDP §8.1, Remark
8.1.6 / Exercise 8.1): with failure probability at most `2exp(−u²)`,
`sup_{s,t} |X_t − X_s| ≤ K(9·dudleySum + 17·diam + 12·u·diam)`. Frozen core
constants `9 / 17 / 12`; the book's `2exp(−u²)` is met exactly. -/
theorem dudley_tail_three_term {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: T finite (the book's standing assumption for (8.15))
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | K * (9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T)
        < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  classical
  have hbd : Bornology.IsBounded T := hfin.isBounded
  set thr : ℝ := (K : ℝ) * (9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T)
    with hthr
  -- Finite carrier as a Finset, with `⨆ over F = ⨆ over T`.
  set F := hfin.toFinset with hFdef
  have hFne : F.Nonempty := by rw [hFdef, Set.Finite.toFinset_nonempty]; exact hne
  have hmemT : ∀ t, t ∈ F → t ∈ T := fun t ht => hfin.mem_toFinset.mp ht
  have setToF : ∀ f : E → ℝ, (⨆ t ∈ F, f t) = ⨆ t ∈ T, f t :=
    fun f => iSup_congr fun t => by rw [hfin.mem_toFinset]
  -- Degenerate branch: if every increment vanishes a.e., the event is null.
  have trivial_case : (∀ s ∈ T, ∀ t ∈ T, (fun ω => X t ω - X s ω) =ᵐ[μ] 0) →
      μ {ω | thr < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
        ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
    intro htriv
    have hall : ∀ᵐ ω ∂μ, ∀ t ∈ T, ∀ s ∈ T, |X t ω - X s ω| = 0 := by
      rw [hfin.eventually_all]
      intro t ht
      rw [hfin.eventually_all]
      intro s hs
      filter_upwards [htriv s hs t ht] with ω hω
      have : X t ω - X s ω = 0 := hω
      rw [this, abs_zero]
    have hnull : {ω | thr < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
        ⊆ {ω | ¬ (∀ t ∈ T, ∀ s ∈ T, |X t ω - X s ω| = 0)} := by
      intro ω hω hcontra
      simp only [Set.mem_setOf_eq] at hω
      have hthr0 : (0 : ℝ) ≤ thr := by
        rw [hthr]
        exact mul_nonneg (NNReal.coe_nonneg K)
          (by nlinarith [dudleySum_nonneg T, Metric.diam_nonneg (s := T),
            mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hu) (Metric.diam_nonneg (s := T))])
      have hG0 : (⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|) ≤ 0 :=
        Real.iSup_le (fun t => Real.iSup_le (fun ht =>
          Real.iSup_le (fun s => Real.iSup_le (fun hs => (hcontra t ht s hs).le) le_rfl) le_rfl)
          le_rfl) le_rfl
      linarith
    calc μ {ω | thr < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
        ≤ μ {ω | ¬ (∀ t ∈ T, ∀ s ∈ T, |X t ω - X s ω| = 0)} := measure_mono hnull
      _ = 0 := ae_iff.mp hall
      _ ≤ _ := zero_le _
  rcases eq_or_lt_of_le (Metric.diam_nonneg (s := T)) with hDeq | hDpos
  · -- diam T = 0
    apply trivial_case
    intro s hs t ht
    have hle : dist s t ≤ Metric.diam T := Metric.dist_le_diam_of_mem hbd hs ht
    exact hinc.sub_ae_eq_zero (hmeas s hs) (hmeas t ht) hs ht
      (le_antisymm (hle.trans_eq hDeq.symm) dist_nonneg)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ K from K.coe_nonneg) with hKeq | hKpos
  · -- K = 0
    apply trivial_case
    intro s hs t ht
    have hK0 : K = 0 := by rw [← NNReal.coe_eq_zero]; exact hKeq.symm
    have hnorm : subGaussianNorm (fun ω => X t ω - X s ω) μ = 0 := by
      refine le_antisymm ?_ (zero_le _)
      have h := hinc s hs t ht
      rw [hK0] at h; simpa using h
    exact ae_eq_zero_of_subGaussianNorm_eq_zero ((hmeas t ht).sub (hmeas s hs)) hnorm
  -- MAIN CASE: diam T > 0 and K > 0.
  obtain ⟨κ, hκ1, hκ2⟩ := exists_coarse_scale hDpos
  set ε : ℕ → ℝ := fun j => (2 : ℝ) ^ (-(κ + (j : ℤ))) with hεdef
  have hεval : ∀ j : ℕ, ε j = (2 : ℝ) ^ (-(κ + (j : ℤ))) := fun j => by rw [hεdef]
  have hεpos : ∀ j : ℕ, 0 < ε j := fun j => by rw [hεval]; exact zpow_pos (by norm_num) _
  have hεrec : ∀ j : ℕ, ε j = 2 * ε (j + 1) := by
    intro j
    rw [hεval, hεval,
      show (-(κ + ((j + 1 : ℕ) : ℤ))) = (-(κ + (j : ℤ))) - 1 by push_cast; ring,
      zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zpow_one]; ring
  have hεle : ∀ j : ℕ, ε (j + 1) ≤ ε j := fun j => by rw [hεrec j]; linarith [hεpos (j + 1)]
  have hεfac : ∀ j : ℕ, ε j = (2 : ℝ) ^ (-κ) * (1 / 2) ^ j := by
    intro j
    have hpow : (1 / 2 : ℝ) ^ j = (2 : ℝ) ^ (-(j : ℤ)) := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [hεval, hpow, show (-(κ + (j : ℤ))) = -κ + -(j : ℤ) by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  have hεbnd : ∀ j : ℕ, ε (j + 1) ≤ 2 * Metric.diam T * (1 / 2) ^ (j + 1) := by
    intro j
    rw [hεfac (j + 1)]
    exact mul_le_mul_of_nonneg_right hκ2.le (by positivity)
  -- Dyadic nets.
  have hnet : ∀ j : ℕ, ∃ N : Finset E, ↑N ⊆ T ∧ N.Nonempty ∧
      (∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε j) ∧ (N.card : ℕ∞) = coveringNumber T (ε j) :=
    fun j => exists_finset_net hfin hne (hεpos j)
  choose N hN using hnet
  have hprojT : ∀ i : ℕ, ∀ t : E, netProj (N i) t ∈ T :=
    fun i t => (hN i).1 (Finset.mem_coe.mpr (netProj_mem (hN i).2.1 t))
  have hproj : ∀ i : ℕ, ∀ t ∈ T, dist t (netProj (N i) t) ≤ ε i :=
    fun i t ht => dist_netProj_le ((hN i).2.2.1 t ht)
  have hcov1 : coveringNumber T (ε 0) = 1 := by
    apply coveringNumber_eq_one_of_diam_le hne hbd (le_of_lt (hεpos 0))
    rw [hεval]; push_cast; simpa using hκ1
  have hcard0 : (N 0).card = 1 := by
    have h := (hN 0).2.2.2; rw [hcov1] at h; exact_mod_cast h
  obtain ⟨c, hc0⟩ := Finset.card_eq_one.mp hcard0
  have hcT : c ∈ T := (hN 0).1 (Finset.mem_coe.mpr (hc0 ▸ Finset.mem_singleton_self c))
  have hπ0 : ∀ t : E, netProj (N 0) t = c := by
    intro t
    rw [hc0]
    have hmem := netProj_mem (Finset.singleton_nonempty c) t
    rwa [Finset.mem_singleton] at hmem
  obtain ⟨n, hn_pos, hfineScale⟩ := exists_fine_scale hfin κ
  have hfine0 : ∀ t ∈ T, dist t (netProj (N n) t) = 0 := by
    intro t ht
    apply hfineScale t ht (netProj (N n) t) (hprojT n t)
    rw [← hεval n]; exact hproj n t ht
  have hclean : ∀ᵐ ω ∂μ, ∀ t ∈ T, X (netProj (N n) t) ω = X t ω := by
    rw [hfin.eventually_all]
    intro t ht
    have hsub := hinc.sub_ae_eq_zero (hmeas t ht) (hmeas (netProj (N n) t) (hprojT n t))
      ht (hprojT n t) (hfine0 t ht)
    filter_upwards [hsub] with ω hω
    have : X (netProj (N n) t) ω - X t ω = 0 := hω
    linarith
  -- Per-level close pairs, radii, thresholds.
  set r : ℕ → ℝ := fun j => ε (j + 1) + ε j with hrdef
  have hrpos : ∀ j, 0 < r j := fun j => by
    show 0 < ε (j + 1) + ε j; linarith [hεpos (j + 1), hεpos j]
  have hr3 : ∀ j, r j = 3 * ε (j + 1) := fun j => by
    show ε (j + 1) + ε j = 3 * ε (j + 1); rw [hεrec j]; ring
  set CP : ℕ → Finset (E × E) := fun j => closePairs (N (j + 1)) (N j) (r j) with hCPdef
  have hCPne : ∀ j : ℕ, (CP j).Nonempty := fun j =>
    ⟨(netProj (N (j + 1)) hne.some, netProj (N j) hne.some),
      proj_pair_mem_closePairs (hproj (j + 1) hne.some hne.some_mem)
        (hproj j hne.some hne.some_mem) (hN (j + 1)).2.1 (hN j).2.1⟩
  have hCPmem : ∀ j : ℕ, ∀ p ∈ CP j, p.1 ∈ T ∧ p.2 ∈ T := by
    intro j p hp
    rw [hCPdef] at hp
    simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨(hN (j + 1)).1 (Finset.mem_coe.mpr hp.1.1), (hN j).1 (Finset.mem_coe.mpr hp.1.2)⟩
  have hNjle : ∀ j, (N j).card ≤ (N (j + 1)).card := by
    intro j
    have h1 := (hN j).2.2.2
    have h2 := (hN (j + 1)).2.2.2
    have hanti : coveringNumber T (ε j) ≤ coveringNumber T (ε (j + 1)) :=
      coveringNumber_anti (hεle j)
    rw [← h1, ← h2] at hanti
    exact_mod_cast hanti
  have hcardCPnat : ∀ j, (CP j).card ≤ (N (j + 1)).card ^ 2 := by
    intro j
    calc (CP j).card ≤ (N (j + 1)).card * (N j).card := card_closePairs_le _ _ _
      _ ≤ (N (j + 1)).card * (N (j + 1)).card := Nat.mul_le_mul le_rfl (hNjle j)
      _ = (N (j + 1)).card ^ 2 := by rw [sq]
  have hslc : ∀ j, sqrtLogCov T (ε (j + 1)) = Real.sqrt (Real.log ((N (j + 1)).card : ℝ)) := by
    intro j
    have hcov : (coveringNumber T (ε (j + 1))).toNat = (N (j + 1)).card := by
      have h := (hN (j + 1)).2.2.2; rw [← h]; simp
    unfold sqrtLogCov; rw [hcov]
  have hdud : ∀ j : ℕ, dudleySummand T (κ + 1 + (j : ℤ))
      = ε (j + 1) * sqrtLogCov T (ε (j + 1)) := by
    intro j
    have hkk : (-(κ + 1 + (j : ℤ))) = (-(κ + ((j + 1 : ℕ) : ℤ))) := by push_cast; ring
    simp only [dudleySummand]
    rw [hkk, hεval (j + 1)]
  set τ : ℕ → ℝ := fun j => (K : ℝ) * r j *
    (Real.sqrt (2 * Real.log ((N (j + 1)).card : ℝ)) + Real.sqrt ((j : ℝ) + 1) + u) with hτdef
  -- Per-pair sub-gaussian tail bound (with the level radius `r j` in the exponent).
  have hpair : ∀ j, ∀ p ∈ CP j, μ {ω | τ j < |X p.1 ω - X p.2 ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(τ j) ^ 2 / ((K : ℝ) * r j) ^ 2)) := by
    intro j p hp
    have hp1 : p.1 ∈ T := (hCPmem j p hp).1
    have hp2 : p.2 ∈ T := (hCPmem j p hp).2
    have hdle : dist p.1 p.2 ≤ r j := by
      rw [hCPdef] at hp
      simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
      exact hp.2
    have hτ0 : 0 ≤ τ j := by
      simp only [hτdef]
      exact mul_nonneg (mul_nonneg (NNReal.coe_nonneg K) (hrpos j).le)
        (add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hu)
    have hτpos : 0 < τ j := by
      simp only [hτdef]
      apply mul_pos (mul_pos hKpos (hrpos j))
      have : 0 < Real.sqrt ((j : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have h0 : 0 ≤ Real.sqrt (2 * Real.log ((N (j + 1)).card : ℝ)) := Real.sqrt_nonneg _
      linarith
    rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist p.1 p.2) with hd0 | hdpos
    · -- dist = 0: the increment vanishes a.e., so the event is null.
      have haez : (fun ω => X p.1 ω - X p.2 ω) =ᵐ[μ] 0 :=
        hinc.sub_ae_eq_zero (hmeas p.2 hp2) (hmeas p.1 hp1) hp2 hp1
          (by rw [dist_comm]; exact hd0.symm)
      have hae2 : ∀ᵐ ω ∂μ, X p.1 ω - X p.2 ω = 0 := by
        filter_upwards [haez] with ω hω; exact hω
      have hsub : {ω | τ j < |X p.1 ω - X p.2 ω|} ⊆ {ω | X p.1 ω - X p.2 ω ≠ 0} := by
        intro ω hω hcontra
        simp only [Set.mem_setOf_eq] at hω
        rw [hcontra, abs_zero] at hω
        exact absurd hω (not_lt.mpr hτpos.le)
      rw [measure_mono_null hsub (ae_iff.mp hae2)]
      exact zero_le _
    · -- dist > 0: apply the B1 pair-tail bound and inflate the radius.
      have hdpos' : 0 < dist p.2 p.1 := by rw [dist_comm]; exact hdpos
      have hK' : 0 < (K : ℝ) * dist p.2 p.1 := mul_pos hKpos hdpos'
      have htail := hinc.measure_abs_sub_ge_le (hmeas p.2 hp2) (hmeas p.1 hp1) hp2 hp1 hK' hτ0
      have hsub01 : {ω | τ j < |X p.1 ω - X p.2 ω|} ⊆ {ω | τ j ≤ |X p.1 ω - X p.2 ω|} :=
        Set.setOf_subset_setOf.mpr (fun ω h => le_of_lt h)
      refine le_trans (measure_mono hsub01) (le_trans htail ?_)
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Real.exp_le_exp.mpr
      have hle : (K : ℝ) * dist p.2 p.1 ≤ (K : ℝ) * r j := by
        rw [dist_comm]; exact mul_le_mul_of_nonneg_left hdle hKpos.le
      have hd2 : ((K : ℝ) * dist p.2 p.1) ^ 2 ≤ ((K : ℝ) * r j) ^ 2 := by
        nlinarith [hle, hK'.le]
      have hpos1 : (0 : ℝ) < ((K : ℝ) * dist p.2 p.1) ^ 2 := pow_pos hK' 2
      have hpos2 : (0 : ℝ) < ((K : ℝ) * r j) ^ 2 := pow_pos (mul_pos hKpos (hrpos j)) 2
      rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ hpos2 hpos1]
      exact mul_le_mul_of_nonneg_left hd2 (sq_nonneg (τ j))
  -- Key per-level real bound: `Nc² · 2exp(−τ²/(Kr)²) ≤ 2 exp(−(j+1)) exp(−u²)`.
  have hreal : ∀ j, ((N (j + 1)).card : ℝ) ^ 2 * (2 * Real.exp (-(τ j) ^ 2 / ((K : ℝ) * r j) ^ 2))
      ≤ 2 * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2) := by
    intro j
    have hMpos : (0 : ℝ) < ((N (j + 1)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (hN (j + 1)).2.1
    have hMne : ((N (j + 1)).card : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hMpos.ne'
    have hKr : 0 < (K : ℝ) * r j := mul_pos hKpos (hrpos j)
    have hKrne : (K : ℝ) * r j ≠ 0 := hKr.ne'
    set S : ℝ := Real.sqrt (2 * Real.log ((N (j + 1)).card : ℝ)) + Real.sqrt ((j : ℝ) + 1) + u
      with hSdef
    have hτeq : τ j = (K : ℝ) * r j * S := by simp only [hτdef, hSdef]
    have hquot : (τ j) ^ 2 / ((K : ℝ) * r j) ^ 2 = S ^ 2 := by
      rw [hτeq, mul_pow, mul_comm (((K : ℝ) * r j) ^ 2) (S ^ 2), mul_div_assoc,
        div_self (pow_ne_zero 2 hKrne), mul_one]
    rw [show -(τ j) ^ 2 / ((K : ℝ) * r j) ^ 2 = -S ^ 2 from by rw [neg_div, hquot]]
    have hlogM : (0 : ℝ) ≤ Real.log ((N (j + 1)).card : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Finset.card_pos.mpr (hN (j + 1)).2.1)
    have hSsq : 2 * Real.log ((N (j + 1)).card : ℝ) + ((j : ℝ) + 1) + u ^ 2 ≤ S ^ 2 := by
      have ha : (0 : ℝ) ≤ Real.sqrt (2 * Real.log ((N (j + 1)).card : ℝ)) := Real.sqrt_nonneg _
      have hb : (0 : ℝ) ≤ Real.sqrt ((j : ℝ) + 1) := Real.sqrt_nonneg _
      have hsa : Real.sqrt (2 * Real.log ((N (j + 1)).card : ℝ)) ^ 2
          = 2 * Real.log ((N (j + 1)).card : ℝ) := Real.sq_sqrt (by positivity)
      have hsb : Real.sqrt ((j : ℝ) + 1) ^ 2 = (j : ℝ) + 1 := Real.sq_sqrt (by positivity)
      rw [hSdef]
      nlinarith [ha, hb, hu, hsa, hsb, mul_nonneg ha hb, mul_nonneg ha hu, mul_nonneg hb hu]
    have hexpM : Real.exp (-(2 * Real.log ((N (j + 1)).card : ℝ))) = (((N (j + 1)).card : ℝ) ^ 2)⁻¹ := by
      rw [Real.exp_neg,
        show 2 * Real.log ((N (j + 1)).card : ℝ) = Real.log (((N (j + 1)).card : ℝ) ^ 2) by
          rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (pow_pos hMpos 2)]
    have hexp : Real.exp (-S ^ 2) ≤ Real.exp (-(2 * Real.log ((N (j + 1)).card : ℝ)))
        * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hSsq])
    calc ((N (j + 1)).card : ℝ) ^ 2 * (2 * Real.exp (-S ^ 2))
        ≤ ((N (j + 1)).card : ℝ) ^ 2 * (2 * (Real.exp (-(2 * Real.log ((N (j + 1)).card : ℝ)))
            * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hMpos.le 2)
          exact mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = ((N (j + 1)).card : ℝ) ^ 2 * (2 * ((((N (j + 1)).card : ℝ) ^ 2)⁻¹
            * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2))) := by rw [hexpM]
      _ = 2 * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2) := by
          rw [show ((N (j + 1)).card : ℝ) ^ 2 * (2 * ((((N (j + 1)).card : ℝ) ^ 2)⁻¹
                * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2)))
              = (((N (j + 1)).card : ℝ) ^ 2 * (((N (j + 1)).card : ℝ) ^ 2)⁻¹)
                * (2 * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2)) by ring,
            mul_inv_cancel₀ hMne, one_mul]
  -- Per-level union bound over close pairs.
  have hlevel : ∀ j, μ {ω | τ j < ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
    intro j
    have hsub : {ω | τ j < ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω|}
        ⊆ ⋃ p ∈ CP j, {ω | τ j < |X p.1 ω - X p.2 ω|} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      rw [biSup_finset_eq_sup' (hCPne j) (fun p => |X p.1 ω - X p.2 ω|)
        (fun _ _ => abs_nonneg _), Finset.lt_sup'_iff] at hω
      obtain ⟨p, hp, hlt⟩ := hω
      exact Set.mem_biUnion hp hlt
    calc μ {ω | τ j < ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω|}
        ≤ μ (⋃ p ∈ CP j, {ω | τ j < |X p.1 ω - X p.2 ω|}) := measure_mono hsub
      _ ≤ ∑ p ∈ CP j, μ {ω | τ j < |X p.1 ω - X p.2 ω|} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _p ∈ CP j, ENNReal.ofReal (2 * Real.exp (-(τ j) ^ 2 / ((K : ℝ) * r j) ^ 2)) :=
          Finset.sum_le_sum (fun p hp => hpair j p hp)
      _ = (CP j).card • ENNReal.ofReal (2 * Real.exp (-(τ j) ^ 2 / ((K : ℝ) * r j) ^ 2)) := by
          rw [Finset.sum_const]
      _ ≤ ENNReal.ofReal (2 * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
          rw [nsmul_eq_mul]
          calc ((CP j).card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(τ j) ^ 2 / ((K : ℝ) * r j) ^ 2))
              ≤ (((N (j + 1)).card ^ 2 : ℕ) : ℝ≥0∞)
                  * ENNReal.ofReal (2 * Real.exp (-(τ j) ^ 2 / ((K : ℝ) * r j) ^ 2)) := by
                gcongr
                exact Nat.cast_le.mpr (hcardCPnat j)
            _ = ENNReal.ofReal (((N (j + 1)).card : ℝ) ^ 2
                  * (2 * Real.exp (-(τ j) ^ 2 / ((K : ℝ) * r j) ^ 2))) := by
                rw [← ENNReal.ofReal_natCast ((N (j + 1)).card ^ 2),
                  ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
                congr 1; push_cast; ring
            _ ≤ ENNReal.ofReal (2 * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2)) :=
                ENNReal.ofReal_le_ofReal (hreal j)
  -- Two-sided sup ≤ twice the anchored one-sided sup.
  have hHnn : ∀ ω, 0 ≤ ⨆ t ∈ T, |X t ω - X c ω| := by
    intro ω
    rw [← setToF (fun t => |X t ω - X c ω|)]
    exact le_trans (abs_nonneg _)
      (le_biSup_finset (fun t => |X t ω - X c ω|) (hfin.mem_toFinset.mpr hcT))
  have hG2H : ∀ ω, (⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|) ≤ 2 * ⨆ t ∈ T, |X t ω - X c ω| := by
    intro ω
    have h2H : (0 : ℝ) ≤ 2 * ⨆ t ∈ T, |X t ω - X c ω| := by linarith [hHnn ω]
    refine Real.iSup_le (fun t => Real.iSup_le (fun ht =>
      Real.iSup_le (fun s => Real.iSup_le (fun hs => ?_) h2H) h2H) h2H) h2H
    have htc : |X t ω - X c ω| ≤ ⨆ t' ∈ T, |X t' ω - X c ω| := by
      rw [← setToF (fun t => |X t ω - X c ω|)]
      exact le_biSup_finset (fun t => |X t ω - X c ω|) (hfin.mem_toFinset.mpr ht)
    have hsc : |X s ω - X c ω| ≤ ⨆ t' ∈ T, |X t' ω - X c ω| := by
      rw [← setToF (fun t => |X t ω - X c ω|)]
      exact le_biSup_finset (fun t => |X t ω - X c ω|) (hfin.mem_toFinset.mpr hs)
    have habs := abs_sub_le (X t ω) (X c ω) (X s ω)
    have hcs : |X c ω - X s ω| = |X s ω - X c ω| := abs_sub_comm _ _
    linarith
  -- Anchored telescoping bound (a.e.).
  have htele : ∀ᵐ ω ∂μ, (⨆ t ∈ T, |X t ω - X c ω|)
      ≤ ∑ j ∈ Finset.range n, ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω| := by
    filter_upwards [hclean] with ω hω
    rw [← setToF (fun t => |X t ω - X c ω|),
      biSup_finset_eq_sup' hFne _ (fun _ _ => abs_nonneg _)]
    refine Finset.sup'_le hFne _ (fun t ht => ?_)
    have htT := hmemT t ht
    have htel : X t ω - X c ω = ∑ i ∈ Finset.range n,
        (X (netProj (N (i + 1)) t) ω - X (netProj (N i) t) ω) := by
      have h0 : X (netProj (N 0) t) ω = X c ω := by rw [hπ0 t]
      have hnn : X (netProj (N n) t) ω = X t ω := hω t htT
      rw [← hnn, ← h0]
      exact chain_telescope (fun i => X (netProj (N i) t) ω)
    calc |X t ω - X c ω|
        = |∑ i ∈ Finset.range n,
            (X (netProj (N (i + 1)) t) ω - X (netProj (N i) t) ω)| := by rw [htel]
      _ ≤ ∑ i ∈ Finset.range n,
            |X (netProj (N (i + 1)) t) ω - X (netProj (N i) t) ω| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range n, ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω| := by
          apply Finset.sum_le_sum
          intro i _
          exact le_biSup_finset (fun p => |X p.1 ω - X p.2 ω|)
            (proj_pair_mem_closePairs (hproj (i + 1) t htT) (hproj i t htT)
              (hN (i + 1)).2.1 (hN i).2.1)
  -- Threshold sum: `2 ∑ τ_j ≤ thr`.
  have hwin : ∑ j ∈ Finset.range n, dudleySummand T (κ + 1 + (j : ℤ)) ≤ dudleySum T := by
    have hemb : Function.Injective (fun j : ℕ => κ + 1 + (j : ℤ)) := by
      intro a b hab; simp only at hab; omega
    rw [show (∑ j ∈ Finset.range n, dudleySummand T (κ + 1 + (j : ℤ)))
          = ∑ k ∈ (Finset.range n).map ⟨fun j : ℕ => κ + 1 + (j : ℤ), hemb⟩, dudleySummand T k
        from by rw [Finset.sum_map]; rfl]
    exact sum_window_le_dudleySum hfin hne _
  have hpartA_term : ∀ j : ℕ, ε (j + 1) * Real.sqrt (2 * Real.log ((N (j + 1)).card : ℝ))
      = Real.sqrt 2 * dudleySummand T (κ + 1 + (j : ℤ)) := by
    intro j
    rw [hdud j, hslc j, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hSAp : ∑ j ∈ Finset.range n, ε (j + 1) * Real.sqrt (2 * Real.log ((N (j + 1)).card : ℝ))
      = Real.sqrt 2 * ∑ j ∈ Finset.range n, dudleySummand T (κ + 1 + (j : ℤ)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => hpartA_term j)
  have hSB : ∑ j ∈ Finset.range n, ε (j + 1) * Real.sqrt ((j : ℝ) + 1)
      ≤ 2 * Metric.diam T * Real.sqrt 2 := by
    calc ∑ j ∈ Finset.range n, ε (j + 1) * Real.sqrt ((j : ℝ) + 1)
        ≤ ∑ j ∈ Finset.range n, (2 * Metric.diam T * (1 / 2) ^ (j + 1)) * Real.sqrt ((j : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hεbnd j) (Real.sqrt_nonneg _)
      _ = 2 * Metric.diam T * ∑ j ∈ Finset.range n, (1 / 2) ^ (j + 1) * Real.sqrt ((j : ℝ) + 1) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ 2 * Metric.diam T * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left (sum_half_succ_sqrt_le_sqrt_two n)
            (mul_nonneg (by norm_num) hDpos.le)
  have hSC : ∑ j ∈ Finset.range n, ε (j + 1) ≤ 2 * Metric.diam T := by
    calc ∑ j ∈ Finset.range n, ε (j + 1)
        ≤ ∑ j ∈ Finset.range n, 2 * Metric.diam T * (1 / 2) ^ (j + 1) :=
          Finset.sum_le_sum (fun j _ => hεbnd j)
      _ = 2 * Metric.diam T * ∑ j ∈ Finset.range n, (1 / 2) ^ (j + 1) := by rw [Finset.mul_sum]
      _ ≤ 2 * Metric.diam T * 1 :=
          mul_le_mul_of_nonneg_left (sum_half_succ_le_one n) (mul_nonneg (by norm_num) hDpos.le)
      _ = 2 * Metric.diam T := by ring
  have hsplit : ∑ j ∈ Finset.range n, τ j
      = 3 * (K : ℝ) * (∑ j ∈ Finset.range n, ε (j + 1)
            * Real.sqrt (2 * Real.log ((N (j + 1)).card : ℝ)))
        + 3 * (K : ℝ) * (∑ j ∈ Finset.range n, ε (j + 1) * Real.sqrt ((j : ℝ) + 1))
        + 3 * (K : ℝ) * u * (∑ j ∈ Finset.range n, ε (j + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp only [hτdef, hr3 j]; ring)
  have h6 : 6 * Real.sqrt 2 ≤ 9 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h12 : 12 * Real.sqrt 2 ≤ 17 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hbA : 6 * (K : ℝ) * Real.sqrt 2 * (∑ j ∈ Finset.range n, dudleySummand T (κ + 1 + (j : ℤ)))
      ≤ 9 * (K : ℝ) * dudleySum T := by
    have h1 : 6 * (K : ℝ) * Real.sqrt 2
          * (∑ j ∈ Finset.range n, dudleySummand T (κ + 1 + (j : ℤ)))
        ≤ 6 * (K : ℝ) * Real.sqrt 2 * dudleySum T :=
      mul_le_mul_of_nonneg_left hwin (by positivity)
    have hnn : (0 : ℝ) ≤ (9 - 6 * Real.sqrt 2) * ((K : ℝ) * dudleySum T) :=
      mul_nonneg (by linarith [h6]) (mul_nonneg (NNReal.coe_nonneg K) (dudleySum_nonneg T))
    nlinarith [h1, hnn]
  have hbB : 6 * (K : ℝ) * (∑ j ∈ Finset.range n, ε (j + 1) * Real.sqrt ((j : ℝ) + 1))
      ≤ 17 * (K : ℝ) * Metric.diam T := by
    have h1 : 6 * (K : ℝ) * (∑ j ∈ Finset.range n, ε (j + 1) * Real.sqrt ((j : ℝ) + 1))
        ≤ 6 * (K : ℝ) * (2 * Metric.diam T * Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left hSB (by positivity)
    have hnn : (0 : ℝ) ≤ (17 - 12 * Real.sqrt 2) * ((K : ℝ) * Metric.diam T) :=
      mul_nonneg (by linarith [h12]) (mul_nonneg (NNReal.coe_nonneg K) hDpos.le)
    nlinarith [h1, hnn]
  have hbC : 6 * (K : ℝ) * u * (∑ j ∈ Finset.range n, ε (j + 1))
      ≤ 12 * (K : ℝ) * u * Metric.diam T := by
    have h1 : 6 * (K : ℝ) * u * (∑ j ∈ Finset.range n, ε (j + 1))
        ≤ 6 * (K : ℝ) * u * (2 * Metric.diam T) :=
      mul_le_mul_of_nonneg_left hSC
        (mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg K)) hu)
    nlinarith [h1]
  have hthrsum : 2 * ∑ j ∈ Finset.range n, τ j ≤ thr := by
    rw [hsplit, hSAp, hthr]
    have hexp : (K : ℝ) * (9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T)
        = 9 * (K : ℝ) * dudleySum T + 17 * (K : ℝ) * Metric.diam T
          + 12 * (K : ℝ) * u * Metric.diam T := by ring
    rw [hexp]
    nlinarith [hbA, hbB, hbC]
  -- Assemble: the bad event is contained in the null clean-complement plus the level unions.
  set bad : Set Ω := {ω | ¬ ((⨆ t ∈ T, |X t ω - X c ω|)
    ≤ ∑ j ∈ Finset.range n, ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω|)} with hbaddef
  have hbadnull : μ bad = 0 := ae_iff.mp htele
  have hincl : {ω | thr < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ⊆ bad ∪ ⋃ j ∈ Finset.range n, {ω | τ j < ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω|} := by
    intro ω hω
    by_cases hb : ω ∈ bad
    · exact Set.mem_union_left _ hb
    · right
      simp only [hbaddef, Set.mem_setOf_eq, not_not] at hb
      simp only [Set.mem_setOf_eq] at hω
      have hsumlt : ∑ j ∈ Finset.range n, τ j
          < ∑ j ∈ Finset.range n, ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω| := by
        have hchain : thr < 2 * ∑ j ∈ Finset.range n, ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω| := by
          calc thr < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω| := hω
            _ ≤ 2 * ⨆ t ∈ T, |X t ω - X c ω| := hG2H ω
            _ ≤ 2 * ∑ j ∈ Finset.range n, ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω| := by linarith [hb]
        linarith [hthrsum]
      have hex : ∃ j ∈ Finset.range n, τ j < ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω| := by
        by_contra hcon
        push_neg at hcon
        exact absurd (Finset.sum_le_sum (fun j hj => hcon j hj)) (not_le.mpr hsumlt)
      obtain ⟨j, hj, hlt⟩ := hex
      exact Set.mem_biUnion hj hlt
  calc μ {ω | thr < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ≤ μ (bad ∪ ⋃ j ∈ Finset.range n, {ω | τ j < ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω|}) :=
        measure_mono hincl
    _ ≤ μ bad + μ (⋃ j ∈ Finset.range n, {ω | τ j < ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω|}) :=
        measure_union_le _ _
    _ = μ (⋃ j ∈ Finset.range n, {ω | τ j < ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω|}) := by
        rw [hbadnull, zero_add]
    _ ≤ ∑ j ∈ Finset.range n, μ {ω | τ j < ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω|} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range n, ENNReal.ofReal (2 * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2)) :=
        Finset.sum_le_sum (fun j _ => hlevel j)
    _ = ENNReal.ofReal (∑ j ∈ Finset.range n, 2 * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [show (∑ j ∈ Finset.range n, 2 * Real.exp (-((j : ℝ) + 1)) * Real.exp (-u ^ 2))
              = (2 * Real.exp (-u ^ 2)) * ∑ j ∈ Finset.range n, Real.exp (-((j : ℝ) + 1))
            from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)]
        have hle := mul_le_mul_of_nonneg_left (sum_exp_neg_succ_le_one n)
          (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-u ^ 2))
        linarith [hle]

/-- **High-probability Dudley, book display** (HDP §8.1, Eq. (8.15)): with
probability at least `1 − 2exp(−u²)`,
`sup_{s,t} |X_t − X_s| ≤ 200·K·(∫_0^D √(log 𝒩) + u·diam T)`. Book's unnamed
`C` frozen to `200` (the bare diameter term of the three-term core absorbed
via `diam·√log2 ≤ 8·dudleyIntegral`). -/
theorem dudley_tail {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: T finite (the book's standing assumption for (8.15))
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
    (hD0 : 0 < D)
    -- USER-INPUT: deviation parameter u ≥ 0; HDP §8.1, Eq (8.15)
    {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | 200 * K * (dudleyIntegral T D + u * Metric.diam T)
        < ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  -- Reduce to the three-term core by absorbing the bare diameter into the integral.
  refine le_trans (measure_mono ?_) (dudley_tail_three_term hfin hne hmeas hinc hu)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  refine lt_of_le_of_lt ?_ hω
  have hInt0 : 0 ≤ dudleyIntegral T D := dudleyIntegral_nonneg T D
  have hDs : dudleySum T ≤ 2 * dudleyIntegral T D :=
    dudleySum_le_two_mul_dudleyIntegral hfin hne hD hD0
  have hdiam : Metric.diam T * Real.sqrt (Real.log 2) ≤ 8 * dudleyIntegral T D :=
    diam_mul_sqrt_log_two_le_eight_mul_dudleyIntegral hfin hne hD hD0
  have hdnn : 0 ≤ Metric.diam T := Metric.diam_nonneg
  -- √(log 2) ≥ 68/91 (a valid lower bound: `(68/91)² ≈ 0.558 < log 2 ≈ 0.693`).
  have hL : (68 : ℝ) / 91 ≤ Real.sqrt (Real.log 2) := by
    rw [show (68 : ℝ) / 91 = Real.sqrt ((68 / 91) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.log_two_gt_d9])
  have key : 9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T
      ≤ 200 * (dudleyIntegral T D + u * Metric.diam T) := by
    have hprod : 0 ≤ Metric.diam T * (Real.sqrt (Real.log 2) - 68 / 91) :=
      mul_nonneg hdnn (by linarith [hL])
    have hudiam : 0 ≤ u * Metric.diam T := mul_nonneg hu hdnn
    nlinarith [hDs, hdiam, hInt0, hprod, hudiam]
  calc (K : ℝ) * (9 * dudleySum T + 17 * Metric.diam T + 12 * u * Metric.diam T)
      ≤ (K : ℝ) * (200 * (dudleyIntegral T D + u * Metric.diam T)) :=
        mul_le_mul_of_nonneg_left key K.coe_nonneg
    _ = 200 * (K : ℝ) * (dudleyIntegral T D + u * Metric.diam T) := by ring

end StatLean.ConcentrationInequalities
