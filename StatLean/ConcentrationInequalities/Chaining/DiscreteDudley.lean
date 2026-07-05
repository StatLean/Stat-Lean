import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal
import StatLean.ConcentrationInequalities.Chaining.PsiTwoMaximal
import StatLean.ConcentrationInequalities.Chaining.DyadicNets
import StatLean.ConcentrationInequalities.Chaining.EntropySum

/-!
# Discrete Dudley inequality (Theorem 8.1.4)

The chaining workhorse: for a process with sub-gaussian increments
(parameter $K$) on a finite index set $T$,
$$ \mathbb{E}\Bigl[\sup_{t \in T} X_t\Bigr]
     \;\le\; 6\sqrt{3}\; K \sum_{k \in \mathbb{Z}} 2^{-k}
       \sqrt{\log \mathcal{N}(T, d, 2^{-k})} $$
under mean-zero coordinates, and the no-mean-zero absolute deviation form
$$ \mathbb{E}\Bigl[\sup_{t \in T} |X_t - X_{t_0}|\Bigr]
     \;\le\; 20\, K \sum_{k \in \mathbb{Z}} 2^{-k}
       \sqrt{\log \mathcal{N}(T, d, 2^{-k})}. $$
Assembly file.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Theorem 8.1.4 and Eq. (8.2); the absolute
form is the discrete Remark 8.1.5 (the book stresses no mean-zero is needed
for the `|X_t − X_{t₀}|` forms).

**Proof formalization notes.** Book constant `C` frozen to `6√3` for the
mean-zero form: per level, the increment MGF bridge (B2 normalization
`C = 3`) gives each close-pair increment variance proxy `3·(3K·2^{−k})²`,
the pair count over `closePairs` is `≤ N_k²`, and
`expectation_max_finset_le` yields per-level cost
`√(3·(3K·2^{−k})²)·√(2·log N_k²) = 6√3·K·2^{−k}·√(log N_k)`; summing gives
`6√3·K·dudleySum`. (The per-link radius is `ε_k + ε_{k−1} = 3·2^{−k}`,
sharper than the book's rounding to `4·2^{−k}`.) The abs form re-anchors the
chain at the finest scale `κ'` with covering number `1` (so every window
level has `N_k ≥ 2`, killing spurious `√log 2` terms) and reconnects `t₀` by
ONE first-moment bound `E|X_{t₀'} − X_{t₀}| ≤ √π·K·diam T`
(`integral_abs_le_of_subGaussianNorm_le`), absorbed via
`diam·√log2 ≤ 4·dudleySum`; total frozen to `20` (`6√3 ≈ 10.4` chaining +
`4√π/√log 2 ≈ 8.52` re-anchoring, with slack). The mean-zero form carries
the LEAN-ONLY hypothesis `hint : ∀ t ∈ T, Integrable (X t) μ` ruling out
Bochner-junk means (a non-integrable `X t` satisfies `∫ X t = 0` vacuously);
increment means are then derived. The pseudometric chain end is identified
a.e. via `ae_eq_zero_of_subGaussianNorm_eq_zero` over the finitely many
points. Named-sorry fallback of this work item: `discrete_dudley_abs`
(the mean-zero headline `discrete_dudley` lands first).

**Bibliographic comments.** Dudley's bound is from R. M. Dudley, "The sizes
of compact subsets of Hilbert space and continuity of Gaussian processes,"
*J. Funct. Anal.* 1 (1967), 290–330 (for Gaussian processes; the
sub-gaussian extension is folklore). The dyadic discrete form as the primary
statement follows HDP §8.1. See the HDP Chapter 8 Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- Monotonicity of the sub-Gaussian variance proxy: a smaller proxy is still a
valid proxy (larger proxy Gaussian dominates). Used to feed the per-level
close-pair increments (proxy `3(K·nndist)²`) into `expectation_max_finset_le`
with a uniform per-level proxy `3(K·3ε)²`. -/
private lemma isSubGaussian_mono {Y : Ω → ℝ} {σ2 σ2' : ℝ≥0}
    (h : IsSubGaussian Y σ2 μ) (hle : σ2 ≤ σ2') : IsSubGaussian Y σ2' μ := by
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  have hσ : (σ2 : ℝ) ≤ (σ2' : ℝ) := by exact_mod_cast hle
  gcongr

/-- **Discrete Dudley inequality, mean-zero form** (HDP §8.1, Theorem 8.1.4,
Eq. (8.2)): `E sup_{t ∈ T} X_t ≤ 6√3 · K · dudleySum T`. Book's unnamed
absolute constant `C` frozen to `6√3` (see file notes for the derivation). -/
theorem discrete_dudley {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG, HDP p.224 / p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ) :
    ∫ ω, ⨆ t ∈ T, X t ω ∂μ ≤ 6 * Real.sqrt 3 * K * dudleySum T := by
  classical
  have hbd : Bornology.IsBounded T := hfin.isBounded
  set F := hfin.toFinset with hFdef
  have hFne : F.Nonempty := by rw [hFdef, Set.Finite.toFinset_nonempty]; exact hne
  have hmemT : ∀ t, t ∈ F → t ∈ T := fun t ht => hfin.mem_toFinset.mp ht
  have setToF : ∀ f : E → ℝ, (⨆ t ∈ F, f t) = ⨆ t ∈ T, f t :=
    fun f => iSup_congr fun t => by rw [hfin.mem_toFinset]
  have ht' : hne.some ∈ T := hne.some_mem
  rcases eq_or_lt_of_le (Metric.diam_nonneg (s := T)) with hD0 | hDpos
  · -- Degenerate case: `diam T = 0`, all coordinates coincide a.e.
    set c := hne.some with hcdef
    have hcT : c ∈ T := hne.some_mem
    have hzero : ∀ t ∈ T, dist c t = 0 := by
      intro t ht
      have hle := Metric.dist_le_diam_of_mem hbd hcT ht
      rw [← hD0] at hle
      exact le_antisymm hle dist_nonneg
    have hae : ∀ t ∈ T, (fun ω => X t ω - X c ω) =ᵐ[μ] 0 := by
      intro t ht
      exact hinc.sub_ae_eq_zero (hmeas c hcT) (hmeas t ht) hcT ht (hzero t ht)
    have haeeq : (fun ω => ⨆ t ∈ T, X t ω) =ᵐ[μ] fun ω => X c ω := by
      have hall : ∀ᵐ ω ∂μ, ∀ t ∈ T, X t ω = X c ω := by
        rw [hfin.eventually_all]
        intro t ht
        filter_upwards [hae t ht] with ω hω
        have : X t ω - X c ω = 0 := hω
        linarith
      filter_upwards [hall] with ω hω
      rw [← setToF (fun t => X t ω), biSup_finset_eq_sup' hFne]
      apply le_antisymm
      · exact Finset.sup'_le hFne _ (fun t ht => le_of_eq (hω t (hmemT t ht)))
      · exact Finset.le_sup' (fun t => X t ω) (hfin.mem_toFinset.mpr hcT)
    rw [integral_congr_ae haeeq, hmean c hcT]
    exact mul_nonneg (by positivity) (dudleySum_nonneg T)
  · -- Main case: `diam T > 0`, dyadic chaining.
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
    have hεle : ∀ j : ℕ, ε (j + 1) ≤ ε j := fun j => by
      rw [hεrec j]; linarith [hεpos (j + 1)]
    -- Dyadic nets at every scale.
    have hnet : ∀ j : ℕ, ∃ N : Finset E, ↑N ⊆ T ∧ N.Nonempty ∧
        (∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε j) ∧ (N.card : ℕ∞) = coveringNumber T (ε j) :=
      fun j => exists_finset_net hfin hne (hεpos j)
    choose N hN using hnet
    have hprojT : ∀ i : ℕ, ∀ t : E, netProj (N i) t ∈ T :=
      fun i t => (hN i).1 (Finset.mem_coe.mpr (netProj_mem (hN i).2.1 t))
    have hproj : ∀ i : ℕ, ∀ t ∈ T, dist t (netProj (N i) t) ≤ ε i :=
      fun i t ht => dist_netProj_le ((hN i).2.2.1 t ht)
    -- Coarse net is a singleton; its point `c` anchors the chain.
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
    -- Fine scale where the finest net identifies with `T` a.e.
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
    -- Per-level suprema and close-pair suprema.
    set S : ℕ → Ω → ℝ := fun j ω =>
      ⨆ t ∈ F, (X (netProj (N (j + 1)) t) ω - X (netProj (N j) t) ω) with hSdef
    set CP : ℕ → Finset (E × E) := fun j =>
      closePairs (N (j + 1)) (N j) (ε (j + 1) + ε j) with hCPdef
    set CPS : ℕ → Ω → ℝ := fun j ω =>
      ⨆ p ∈ CP j, (X p.1 ω - X p.2 ω) with hCPSdef
    have hCPne : ∀ j : ℕ, (CP j).Nonempty := fun j =>
      ⟨(netProj (N (j + 1)) hne.some, netProj (N j) hne.some),
        proj_pair_mem_closePairs (hproj (j + 1) hne.some ht') (hproj j hne.some ht')
          (hN (j + 1)).2.1 (hN j).2.1⟩
    have hCPmem : ∀ j : ℕ, ∀ p ∈ CP j, p.1 ∈ T ∧ p.2 ∈ T := by
      intro j p hp
      rw [hCPdef] at hp
      simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
      exact ⟨(hN (j + 1)).1 (Finset.mem_coe.mpr hp.1.1), (hN j).1 (Finset.mem_coe.mpr hp.1.2)⟩
    -- Integrability of all suprema.
    have hIntS : ∀ j : ℕ, MeasureTheory.Integrable (S j) μ := fun j =>
      integrable_biSup_finset hFne fun t ht =>
        (hint _ (hprojT (j + 1) t)).sub (hint _ (hprojT j t))
    have hIntCPS : ∀ j : ℕ, MeasureTheory.Integrable (CPS j) μ := fun j =>
      integrable_biSup_finset (hCPne j) fun p hp =>
        (hint _ (hCPmem j p hp).1).sub (hint _ (hCPmem j p hp).2)
    have hIntSupX : MeasureTheory.Integrable (fun ω => ⨆ t ∈ F, X t ω) μ :=
      integrable_biSup_finset hFne fun t ht => hint t (hmemT t ht)
    have hIntSupA : MeasureTheory.Integrable (fun ω => ⨆ t ∈ F, (X t ω - X c ω)) μ :=
      integrable_biSup_finset hFne fun t ht => (hint t (hmemT t ht)).sub (hint c hcT)
    -- Per-level term is dominated by its supremum.
    have term_le_S : ∀ j : ℕ, ∀ t ∈ T, ∀ ω,
        (X (netProj (N (j + 1)) t) ω - X (netProj (N j) t) ω) ≤ S j ω := by
      intro j t ht ω
      rw [hSdef]; simp only
      rw [biSup_finset_eq_sup' hFne]
      exact Finset.le_sup'
        (fun s => X (netProj (N (j + 1)) s) ω - X (netProj (N j) s) ω)
        (hfin.mem_toFinset.mpr ht)
    -- STEP A: reduce to the `X_t - X_c` sup via mean-zero anchoring at `c`.
    have hstepA : (∫ ω, ⨆ t ∈ F, X t ω ∂μ) ≤ ∫ ω, ⨆ t ∈ F, (X t ω - X c ω) ∂μ := by
      have hpt : ∀ ω, (⨆ t ∈ F, X t ω) ≤ X c ω + ⨆ t ∈ F, (X t ω - X c ω) := by
        intro ω
        rw [biSup_finset_eq_sup' hFne]
        refine Finset.sup'_le hFne _ (fun t ht => ?_)
        have hle : (X t ω - X c ω) ≤ ⨆ s ∈ F, (X s ω - X c ω) := by
          rw [biSup_finset_eq_sup' hFne]
          exact Finset.le_sup' (fun s => X s ω - X c ω) ht
        linarith
      calc (∫ ω, ⨆ t ∈ F, X t ω ∂μ)
          ≤ ∫ ω, (X c ω + ⨆ t ∈ F, (X t ω - X c ω)) ∂μ :=
            integral_mono_ae hIntSupX ((hint c hcT).add hIntSupA) (ae_of_all _ hpt)
        _ = (∫ ω, X c ω ∂μ) + ∫ ω, ⨆ t ∈ F, (X t ω - X c ω) ∂μ :=
            integral_add (hint c hcT) hIntSupA
        _ = ∫ ω, ⨆ t ∈ F, (X t ω - X c ω) ∂μ := by rw [hmean c hcT, zero_add]
    -- STEP B1: split the anchored sup along the chain.
    have hB1 : (∫ ω, ⨆ t ∈ F, (X t ω - X c ω) ∂μ)
        ≤ ∑ j ∈ Finset.range n, ∫ ω, S j ω ∂μ := by
      rw [← integral_finset_sum (Finset.range n) (fun j _ => hIntS j)]
      refine integral_mono_ae hIntSupA
        (integrable_finset_sum _ (fun j _ => hIntS j)) ?_
      filter_upwards [hclean] with ω hω
      rw [biSup_finset_eq_sup' hFne]
      refine Finset.sup'_le hFne _ (fun t ht => ?_)
      have htT := hmemT t ht
      have htel : X t ω - X c ω
          = ∑ i ∈ Finset.range n,
              (X (netProj (N (i + 1)) t) ω - X (netProj (N i) t) ω) := by
        have h0 : X (netProj (N 0) t) ω = X c ω := by rw [hπ0 t]
        have hnn : X (netProj (N n) t) ω = X t ω := hω t htT
        rw [← hnn, ← h0]
        exact chain_telescope (fun i => X (netProj (N i) t) ω)
      rw [htel]
      exact Finset.sum_le_sum (fun i _ => term_le_S i t htT ω)
    -- STEP B2: bound each level by `6√3 K` times the dyadic summand.
    have hB2 : ∀ j ∈ Finset.range n,
        (∫ ω, S j ω ∂μ) ≤ 6 * Real.sqrt 3 * K * dudleySummand T (κ + 1 + (j : ℤ)) := by
      intro j _
      set r : ℝ := ε (j + 1) + ε j with hrdef
      have hrpos : 0 < r := by rw [hrdef]; linarith [hεpos (j + 1), hεpos j]
      have hr3 : r = 3 * ε (j + 1) := by rw [hrdef, hεrec j]; ring
      set σ2 : ℝ≥0 := 3 * (K * Real.toNNReal r) ^ 2 with hσ2def
      -- centering & sub-Gaussianity of every close-pair increment
      have hcenter : ∀ p ∈ CP j, ∫ ω, (X p.1 ω - X p.2 ω) ∂μ = 0 := by
        intro p hp
        rw [integral_sub (hint _ (hCPmem j p hp).1) (hint _ (hCPmem j p hp).2),
          hmean _ (hCPmem j p hp).1, hmean _ (hCPmem j p hp).2, sub_zero]
      have hSG : ∀ p ∈ CP j, IsSubGaussian (fun ω => X p.1 ω - X p.2 ω) σ2 μ := by
        intro p hp
        have hdle : dist p.1 p.2 ≤ r := by
          rw [hCPdef] at hp
          simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
          exact hp.2
        refine isSubGaussian_mono
          (hinc.isSubGaussian_sub (hmeas _ (hCPmem j p hp).2) (hmeas _ (hCPmem j p hp).1)
            (hCPmem j p hp).2 (hCPmem j p hp).1 (hcenter p hp)) ?_
        rw [hσ2def]
        have hnn : nndist p.2 p.1 ≤ Real.toNNReal r := by
          rw [nndist_dist, dist_comm]; exact Real.toNNReal_le_toNNReal hdle
        gcongr
      -- close-pair cardinality control
      set Mnat : ℕ := (N (j + 1)).card with hMnatdef
      set M : ℝ := (Mnat : ℝ) with hMdef
      have hNjle : (N j).card ≤ (N (j + 1)).card := by
        have h1 := (hN j).2.2.2
        have h2 := (hN (j + 1)).2.2.2
        have hanti : coveringNumber T (ε j) ≤ coveringNumber T (ε (j + 1)) :=
          coveringNumber_anti (hεle j)
        rw [← h1, ← h2] at hanti
        exact_mod_cast hanti
      have hcardCPnat : (CP j).card ≤ Mnat ^ 2 := by
        calc (CP j).card ≤ (N (j + 1)).card * (N j).card := card_closePairs_le _ _ _
          _ ≤ (N (j + 1)).card * (N (j + 1)).card := by gcongr
          _ = Mnat ^ 2 := by rw [hMnatdef, sq]
      have hcard1nat : 0 < (CP j).card := Finset.card_pos.mpr (hCPne j)
      have hM1nat : 0 < Mnat := Finset.card_pos.mpr (hN (j + 1)).2.1
      have hcardCP : ((CP j).card : ℝ) ≤ M ^ 2 := by rw [hMdef]; exact_mod_cast hcardCPnat
      -- identify the covering number toNat with the net cardinality
      have hcov : (coveringNumber T (ε (j + 1))).toNat = (N (j + 1)).card := by
        have h := (hN (j + 1)).2.2.2; rw [← h]; simp
      have hslc : sqrtLogCov T (ε (j + 1)) = Real.sqrt (Real.log M) := by
        unfold sqrtLogCov; rw [hcov, hMdef, hMnatdef]
      -- √(σ2) = √3 · (K·r)
      have hsqrtσ : Real.sqrt (σ2 : ℝ) = Real.sqrt 3 * ((K : ℝ) * r) := by
        have hcoe : ((σ2 : ℝ≥0) : ℝ) = 3 * ((K : ℝ) * r) ^ 2 := by
          rw [hσ2def]; push_cast [Real.coe_toNNReal r hrpos.le]; ring
        rw [hcoe, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
          Real.sqrt_sq (mul_nonneg (NNReal.coe_nonneg K) hrpos.le)]
      -- √(2 log |CP|) ≤ 2 · sqrtLogCov
      have hstep : Real.sqrt (2 * Real.log ((CP j).card : ℝ))
          ≤ 2 * sqrtLogCov T (ε (j + 1)) := by
        have hR : 2 * sqrtLogCov T (ε (j + 1)) = Real.sqrt (4 * Real.log M) := by
          rw [hslc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
            show Real.sqrt 4 = 2 from by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        rw [hR]
        apply Real.sqrt_le_sqrt
        have hlogcard : Real.log ((CP j).card : ℝ) ≤ 2 * Real.log M := by
          have hpos : (0 : ℝ) < ((CP j).card : ℝ) := by exact_mod_cast hcard1nat
          have h := Real.log_le_log hpos hcardCP
          rw [Real.log_pow] at h; push_cast at h; linarith
        linarith
      -- dyadic summand identity
      have hdud : dudleySummand T (κ + 1 + (j : ℤ))
          = ε (j + 1) * sqrtLogCov T (ε (j + 1)) := by
        have hkk : (-(κ + 1 + (j : ℤ))) = (-(κ + ((j + 1 : ℕ) : ℤ))) := by push_cast; ring
        simp only [dudleySummand]
        rw [hkk, hεval (j + 1)]
      -- assemble the level bound
      calc (∫ ω, S j ω ∂μ)
          ≤ ∫ ω, CPS j ω ∂μ := by
            refine integral_mono_ae (hIntS j) (hIntCPS j) (ae_of_all _ (fun ω => ?_))
            rw [hSdef, hCPSdef]; simp only
            rw [biSup_finset_eq_sup' hFne, biSup_finset_eq_sup' (hCPne j)]
            refine Finset.sup'_le hFne _ (fun t ht => ?_)
            have htT := hmemT t ht
            exact Finset.le_sup' (fun p => X p.1 ω - X p.2 ω)
              (proj_pair_mem_closePairs (hproj (j + 1) t htT) (hproj j t htT)
                (hN (j + 1)).2.1 (hN j).2.1)
        _ ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log (CP j).card) := by
            rw [hCPSdef]; exact expectation_max_finset_le (hCPne j) hcenter hSG
        _ ≤ 6 * Real.sqrt 3 * K * dudleySummand T (κ + 1 + (j : ℤ)) := by
            rw [hsqrtσ, hdud]
            calc Real.sqrt 3 * ((K : ℝ) * r) * Real.sqrt (2 * Real.log (CP j).card)
                ≤ Real.sqrt 3 * ((K : ℝ) * r) * (2 * sqrtLogCov T (ε (j + 1))) := by
                  apply mul_le_mul_of_nonneg_left hstep
                  exact mul_nonneg (Real.sqrt_nonneg 3)
                    (mul_nonneg (NNReal.coe_nonneg K) hrpos.le)
              _ = 6 * Real.sqrt 3 * K * (ε (j + 1) * sqrtLogCov T (ε (j + 1))) := by
                  rw [hr3]; ring
    -- WINDOW SUM: the level costs sum below the full dyadic entropy sum.
    have hwin : ∑ j ∈ Finset.range n, dudleySummand T (κ + 1 + (j : ℤ)) ≤ dudleySum T := by
      have hemb : Function.Injective (fun j : ℕ => κ + 1 + (j : ℤ)) := by
        intro a b hab; simp only at hab; omega
      rw [show (∑ j ∈ Finset.range n, dudleySummand T (κ + 1 + (j : ℤ)))
            = ∑ k ∈ (Finset.range n).map ⟨fun j : ℕ => κ + 1 + (j : ℤ), hemb⟩, dudleySummand T k
          from by rw [Finset.sum_map]; rfl]
      exact sum_window_le_dudleySum hfin hne _
    -- COMBINE.
    rw [show (fun ω => ⨆ t ∈ T, X t ω) = (fun ω => ⨆ t ∈ F, X t ω)
        from funext fun ω => (setToF _).symm]
    calc (∫ ω, ⨆ t ∈ F, X t ω ∂μ)
        ≤ ∫ ω, ⨆ t ∈ F, (X t ω - X c ω) ∂μ := hstepA
      _ ≤ ∑ j ∈ Finset.range n, ∫ ω, S j ω ∂μ := hB1
      _ ≤ ∑ j ∈ Finset.range n, 6 * Real.sqrt 3 * K * dudleySummand T (κ + 1 + (j : ℤ)) :=
          Finset.sum_le_sum hB2
      _ ≤ 6 * Real.sqrt 3 * K * dudleySum T := by
          have heq : ∑ j ∈ Finset.range n,
                6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + 1 + (j : ℤ))
              = 6 * Real.sqrt 3 * K * ∑ j ∈ Finset.range n, dudleySummand T (κ + 1 + (j : ℤ)) := by
            rw [Finset.mul_sum]
          rw [heq]
          exact mul_le_mul_of_nonneg_left hwin (by positivity)

/-- **Discrete Dudley inequality, absolute form** (HDP §8.1, Remark 8.1.5,
discrete): `E sup_{t ∈ T} |X_t − X_{t₀}| ≤ 20 · K · dudleySum T`, with NO
mean-zero hypothesis (as the book stresses for Eq. (8.13)). Book constant
frozen to `20` (`6√3` chaining + `4√π/√log 2` re-anchoring, slack). -/
theorem discrete_dudley_abs {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG, HDP p.224 / p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Remark 8.1.5
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ ≤ 20 * K * dudleySum T := by sorry

/-- Integrability of the anchored supremum, exported for `Chaining/Dudley.lean`
and the countable lift (derived from the increment tails, never
hypothesized). -/
lemma integrable_biSup_sub {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (finite sup domination)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    MeasureTheory.Integrable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ := by
  classical
  have hbd : Bornology.IsBounded T := hfin.isBounded
  have hFne : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]; exact hne
  set L : ℝ≥0 := K * Real.toNNReal (Metric.diam T) with hL
  have key : MeasureTheory.Integrable
      (fun ω => ⨆ t ∈ hfin.toFinset, |X t ω - X t₀ ω|) μ := by
    refine integrable_biSup_abs hFne (L := L) (fun t ht => ?_) (fun t ht => ?_)
    · exact (hmeas t (hfin.mem_toFinset.mp ht)).sub (hmeas t₀ ht₀)
    · have htT : t ∈ T := hfin.mem_toFinset.mp ht
      refine (hinc t₀ ht₀ t htT).trans ?_
      have hde : edist t₀ t ≤ (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hbd ht₀ htT)
      calc (K : ℝ≥0∞) * edist t₀ t
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by gcongr
        _ = (L : ℝ≥0∞) := by rw [hL]; push_cast; ring
  have hcongr : (fun ω => ⨆ t ∈ hfin.toFinset, |X t ω - X t₀ ω|)
      = fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω| := by
    funext ω
    exact iSup_congr fun t => by rw [hfin.mem_toFinset]
  rwa [hcongr] at key

end StatLean.ConcentrationInequalities
