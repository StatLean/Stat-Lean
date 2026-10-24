/-
Copyright (c) 2026 Benjamin O. Harrison, Gustavo Canavire Bacarreza, David Jacho-Chavez and
Fernando Rios-Avila.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Jacho-Chávez
-/
import StatLean.AsymptoticStatistics.DependencyGraphCLT.Moments
import StatLean.AsymptoticStatistics.DependencyGraphCLT.Lemma4

/-!
# Janson's central limit theorems: Theorems 1 and 2

This file proves the two limit theorems of Janson (1988).

* **Theorem 1.** Let $X_n$ be real random variables with finite moments of all orders. If
  $\kappa_1(X_n) \to \mu$ (1.1), $\kappa_2(X_n) \to \sigma^2$ (1.2) and $\kappa_j(X_n) \to 0$
  for every $j \ge m$, for some integer $m$ (1.3), then $X_n \to N(\mu, \sigma^2)$ in
  distribution (1.4), and every moment of $X_n$ converges to the corresponding moment of
  $N(\mu, \sigma^2)$. The degenerate case $\sigma^2 = 0$ is included.
* **Theorem 2.** For each $n$ let $S_n = \sum_{i=1}^{N_n} X_{n,i}$, where $|X_{n,i}| \le A_n$
  almost surely and the family $(X_{n,i})_i$ admits a dependency graph of maximal degree $M_n$,
  and let $\sigma_n^2 = \operatorname{Var} S_n > 0$. If for some integer $m \ge 3$
  $$ \Bigl(\frac{N_n}{M_n}\Bigr)^{1/m} \frac{M_n A_n}{\sigma_n} \longrightarrow 0
     \qquad (1.5), $$
  then $(S_n - \mathbf{E} S_n)/\sigma_n \to N(0, 1)$ in distribution.

Laws on $\mathbb{R}$ are bundled as `ProbabilityMeasure ℝ`, convergence in distribution is
convergence in the weak topology on `ProbabilityMeasure ℝ`, and `Janson.gaussPM μ v` is the
Gaussian law with mean `μ` and variance `v` (truncated at `0`).

**Reference.** S. Janson, "Normal convergence by higher semiinvariants with applications to
sums of dependent random variables and random graphs", *Ann. Probab.* **16** (1988), 305–312,
Theorems 1 and 2.

**Proof formalization notes: two departures from Janson's proof of Theorem 1.** Theorem 1 is
reduced to showing $\kappa_j(X_n) \to 0$ for every $3 \le j < m$ (`Janson.cumulant_tendsto_zero`),
after which the semiinvariant form of the method of moments (Lemma 1,
`Janson.tendsto_gaussPM_of_tendsto_cumulant`) applies. Arguing by contradiction, along a
subsequence $|\kappa_{j_0}(X_n)| \ge \eta > 0$ for some $3 \le j_0 < m$; put
$\varepsilon_n = \max_{3 \le j < m} |\kappa_j(X_n)|^{1/j}$ (3.1), so that
$\varepsilon_n \ge \delta := \eta^{1/j_0} > 0$.

1. *No auxiliary Gaussian.* Janson's proof adds an auxiliary Gaussian variable to the rescaled
   variables. Here the rescaling alone suffices: with $a_n = \delta / \varepsilon_n \in (0, 1]$
   and $Z_n = a_n X_n$ (the law `Q.map (a_n * ·)`), homogeneity (2.3) and (3.1) give
   $|\kappa_j(Z_n)| \le \delta^j$ for $3 \le j < m$ (3.5), with equality for at least one such
   $j$ (3.6), while $a_n \le 1$ bounds every other cumulant of $Z_n$ by the corresponding
   cumulant of $X_n$, which converges and is therefore bounded.
2. *Prokhorov on the scaled laws instead of coordinatewise extraction.* Instead of extracting
   a subsequence along which the cumulants of $Z_n$ converge order by order and then invoking
   Lemma 1, the bounded cumulants are turned into bounded moments
   (`Janson.exists_moment_bound_of_cumulant_bound`); the laws of $Z_n$ are then tight, and
   Prokhorov's theorem yields a single weakly convergent subsequence along which every moment,
   hence every cumulant, converges (`Janson.exists_limit_of_moment_bound`,
   `Janson.tendsto_cumulant_of_tendsto_integral_pow`). The limit law has $\kappa_j = 0$ for
   $j \ge m$, hence for $j \ge 3$ by Marcinkiewicz's theorem in semiinvariant form (§1),
   contradicting $|\kappa_j(Z_n)| = \delta^j$ for some $3 \le j < m$ along the subsequence.

Theorem 2 combines Theorem 1 with Lemma 4 applied to the standardized sum
(`Janson.abs_cumulant_standardized_le`). Since `DepGraph.nbhd` is the closed neighbourhood, the
rate enters through $M_n + 1$; `Janson.tendsto_rate_of_janson15` derives that form of the rate
from (1.5), using the side conditions $1 \le M_n \le N_n$.

The hypotheses of both versions of Theorem 2 are required for every $n$, not only eventually;
a sequence satisfying them only for large $n$ is handled by shifting the index. Theorem 1
likewise assumes all moments finite for every $n$, slightly more than the Note on p. 306 of
the paper.

## Correspondence with Janson (1988)

| Janson (1988) | Lean |
|---|---|
| semiinvariant $\kappa_j$ (2.1), see note | `Cumulant.cumulant` |
| mixed semiinvariant (4.1), see note | `Cumulant.mixedCumulant` |
| additivity (2.2) | `Cumulant.cumulant_add_of_indepFun` |
| homogeneity (2.3) | `Cumulant.cumulant_const_smul`, `Janson.cumulant_map_const_mul` |
| the polynomial $p_j$ | `Janson.momentOf` |
| Lemma 1, existence | `Janson.exists_measure_cumulant_eq` |
| Lemma 1, convergence | `Janson.tendsto_of_tendsto_moments` |
| Lemma 1, Gaussian case | `Janson.tendsto_gaussPM_of_tendsto_cumulant` |
| Marcinkiewicz, semiinvariant form (§1) | `Cumulant.cumulant_eq_zero_of_three_le` |
| the limit law is Gaussian | `Cumulant.eq_gaussianReal_of_cumulant_eq_zero` |
| Lemma 2, $\kappa_j$ eventually zero | `Cumulant.charFun_eq_exp_charPoly` |
| Lemma 3 | `Cumulant.mixedCumulant_eq_zero_of_indepFun` |
| Lemma 3 on a dependency graph | `Janson.mixedCumulant_eq_zero_of_not_connFam` |
| (4.2) | `Cumulant.cumulant_sum_eq` |
| (4.4), bounded variables; $C_j$ | `Cumulant.abs_mixedCumulant_le`, `Cumulant.mobiusBound` |
| Lemma 4 and its constant $C'_j$ | `Janson.abs_cumulant_sum_le`, `Janson.jansonConst` |
| Lemma 4, standardized | `Janson.abs_cumulant_standardized_le` |
| counting step of Lemma 4 | `Janson.card_conn_le` |
| dependency graph, degree $M$ | `DepGraph`, with `#((D.nbhd i).erase i) ≤ M` |
| (3.1), (3.5), (3.6) | steps of `Janson.cumulant_tendsto_zero` |
| Theorem 1, (1.1)–(1.4) | `Janson.tendsto_gaussPM` |
| Theorem 1, moments | `Janson.tendsto_integral_pow_gaussPM` |
| Theorem 2, rate of Lemma 4 | `Janson.tendsto_gaussPM_of_depGraph` |
| Theorem 2 under (1.5) | `Janson.tendsto_gaussPM_of_depGraph_janson15` |
| $N(\mu, \sigma^2)$ | `Janson.gaussPM μ σ²` |
| law of $(S_n - \mathbf{E} S_n)/\sigma_n$ | `Janson.stdSumPM (μ n) (X n) (σ n) (-𝔼[S_n] / σ n)` |

*Note.* `Cumulant.cumulant` and `Cumulant.mixedCumulant` are defined by the set-partition
(Leonov–Shiryaev) formula, which needs only finite moments; their agreement with the
derivative definitions (2.1) and (4.1) is not formalized.

## Main results

* `Janson.tendsto_gaussPM`, `Janson.tendsto_integral_pow_gaussPM`: Theorem 1.
* `Janson.tendsto_gaussPM_of_depGraph`: Theorem 2 with the rate in the form of Janson's Lemma 4.
* `Janson.tendsto_gaussPM_of_depGraph_janson15`: Theorem 2 under Janson's condition (1.5).
-/

open Finset MeasureTheory ProbabilityTheory Filter Topology

namespace StatLean.AsymptoticStatistics.Janson

/-! ### Section 1. The law of a scaled variable -/

section Scale

/-- Janson `(2.3)` on laws: `kappa_j (a X) = a ^ j kappa_j (X)`, where `Q.map (a * ·)` is the
law of `a * X` when `X` has law `Q`. -/
lemma cumulant_map_const_mul (a : ℝ) (Q : ProbabilityMeasure ℝ) (j : ℕ) :
    Cumulant.cumulant id j (Q.map (fun x => a * x) : Measure ℝ)
      = a ^ j * Cumulant.cumulant id j (Q : Measure ℝ) := by
  have h1 := Cumulant.cumulant_map (Q : Measure ℝ) (measurable_id'.const_mul a).aemeasurable
    id measurable_id j
  have h2 := Cumulant.cumulant_const_smul (id : ℝ → ℝ) a j (Q : Measure ℝ)
  rw [ProbabilityMeasure.toMeasure_map, h1]
  simpa using h2

/-- A law with finite moments of every order keeps them under scaling. -/
lemma integrable_pow_map_const_mul {a : ℝ} {Q : ProbabilityMeasure ℝ}
    (h : ∀ p, Integrable (fun x : ℝ => x ^ p) (Q : Measure ℝ)) (p : ℕ) :
    Integrable (fun x : ℝ => x ^ p) (Q.map (fun x => a * x) : Measure ℝ) := by
  rw [ProbabilityMeasure.toMeasure_map,
    integrable_map_measure (measurable_id'.pow_const p).aestronglyMeasurable
      (measurable_id'.const_mul a).aemeasurable]
  have he : ((fun x : ℝ => x ^ p) ∘ fun x : ℝ => a * x) = fun x : ℝ => a ^ p * x ^ p := by
    funext x
    simp [Function.comp, mul_pow]
  rw [he]
  exact (h p).const_mul _

end Scale

/-! ### Section 2. `Theorem 1`

Under `(1.1)`–`(1.3)` the cumulants vanish in the limit at every order `>= 3`
(`Janson.cumulant_tendsto_zero`); Theorem 1 then follows from
`Janson.tendsto_gaussPM_of_tendsto_cumulant`.
-/

section Theorem1

lemma exists_abs_bound_of_tendsto {f : ℕ → ℝ} {L : ℝ} (h : Tendsto f atTop (𝓝 L)) :
    ∃ C : ℝ, ∀ n, |f n| ≤ C := by
  obtain ⟨C, hC⟩ := h.abs.bddAbove_range
  exact ⟨C, fun n => hC ⟨n, rfl⟩⟩

/-- Under `(1.1)`–`(1.3)`, `kappa_j (X_n) -> 0` for every `j >= 3`. -/
theorem cumulant_tendsto_zero {P : ℕ → ProbabilityMeasure ℝ}
    (hint : ∀ n p, Integrable (fun x : ℝ => x ^ p) (P n : Measure ℝ))
    {m : ℕ} {mu s2 : ℝ}
    (h1 : Tendsto (fun n => Cumulant.cumulant id 1 (P n : Measure ℝ)) atTop (𝓝 mu))
    (h2 : Tendsto (fun n => Cumulant.cumulant id 2 (P n : Measure ℝ)) atTop (𝓝 s2))
    (h3 : ∀ j, m ≤ j → Tendsto (fun n => Cumulant.cumulant id j (P n : Measure ℝ)) atTop (𝓝 0))
    {j₀ : ℕ} (hj3 : 3 ≤ j₀) :
    Tendsto (fun n => Cumulant.cumulant id j₀ (P n : Measure ℝ)) atTop (𝓝 0) := by
  classical
  rcases le_or_gt m j₀ with hmj | hjm
  · exact h3 j₀ hmj
  by_contra hcon
  -- Step 1: a subsequence along which `|kappa_{j_0}|` stays above `eta > 0`
  rw [Metric.tendsto_atTop] at hcon
  push Not at hcon
  obtain ⟨η, hη, hNex⟩ := hcon
  have hfreq : ∃ᶠ n in atTop, η ≤ |Cumulant.cumulant id j₀ (P n : Measure ℝ)| := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hd⟩ := hNex N
    exact ⟨n, hn, by rwa [Real.dist_eq, sub_zero] at hd⟩
  obtain ⟨ψ, hψmono, hψ⟩ := extraction_of_frequently_atTop hfreq
  have hψtop : Tendsto ψ atTop atTop := hψmono.tendsto_atTop
  -- Step 2: Janson's `(3.1)` on that subsequence
  have hj₀mem : j₀ ∈ Finset.Ico 3 m := Finset.mem_Ico.mpr ⟨hj3, hjm⟩
  have hne : (Finset.Ico 3 m).Nonempty := ⟨j₀, hj₀mem⟩
  set R : ℕ → ProbabilityMeasure ℝ := fun k => P (ψ k) with hRdef
  set eps : ℕ → ℝ := fun k => (Finset.Ico 3 m).sup' hne
    (fun j => |Cumulant.cumulant id j (R k : Measure ℝ)| ^ ((j : ℝ)⁻¹)) with hepsdef
  have hepsle : ∀ k, ∀ j ∈ Finset.Ico 3 m,
      |Cumulant.cumulant id j (R k : Measure ℝ)| ^ ((j : ℝ)⁻¹) ≤ eps k := by
    intro k j hj
    simp only [hepsdef]
    exact Finset.le_sup'
      (fun j => |Cumulant.cumulant id j (R k : Measure ℝ)| ^ ((j : ℝ)⁻¹)) hj
  have hepsex : ∀ k, ∃ j ∈ Finset.Ico 3 m,
      eps k = |Cumulant.cumulant id j (R k : Measure ℝ)| ^ ((j : ℝ)⁻¹) := by
    intro k
    obtain ⟨j, hj, hje⟩ := Finset.exists_mem_eq_sup' hne
      (fun j => |Cumulant.cumulant id j (R k : Measure ℝ)| ^ ((j : ℝ)⁻¹))
    exact ⟨j, hj, by simp only [hepsdef]; exact hje⟩
  set δ : ℝ := η ^ ((j₀ : ℝ)⁻¹) with hδdef
  have hδ : 0 < δ := Real.rpow_pos_of_pos hη _
  have hδeps : ∀ k, δ ≤ eps k := by
    intro k
    refine le_trans ?_ (hepsle k j₀ hj₀mem)
    exact Real.rpow_le_rpow hη.le (hψ k) (by positivity)
  have hepspos : ∀ k, 0 < eps k := fun k => lt_of_lt_of_le hδ (hδeps k)
  set a : ℕ → ℝ := fun k => δ / eps k with hadef
  have ha0 : ∀ k, 0 < a k := fun k => div_pos hδ (hepspos k)
  have ha1 : ∀ k, a k ≤ 1 := fun k => (div_le_one (hepspos k)).mpr (hδeps k)
  have haeps : ∀ k, a k * eps k = δ := fun k => div_mul_cancel₀ δ (ne_of_gt (hepspos k))
  -- Step 3: the scaled laws and Janson's `(3.5)`
  set W : ℕ → ProbabilityMeasure ℝ := fun k => (R k).map (fun x => a k * x) with hWdef
  have hWcum : ∀ k j, Cumulant.cumulant id j (W k : Measure ℝ)
      = a k ^ j * Cumulant.cumulant id j (R k : Measure ℝ) := by
    intro k j
    simp only [hWdef]
    exact cumulant_map_const_mul _ _ _
  have hWint : ∀ k p, Integrable (fun x : ℝ => x ^ p) (W k : Measure ℝ) := by
    intro k p
    simp only [hWdef]
    exact integrable_pow_map_const_mul (fun q => hint (ψ k) q) p
  have hpow : ∀ k, ∀ j ∈ Finset.Ico 3 m,
      |Cumulant.cumulant id j (R k : Measure ℝ)| ≤ eps k ^ j := by
    intro k j hj
    have hj0 : j ≠ 0 := by rw [Finset.mem_Ico] at hj; omega
    calc |Cumulant.cumulant id j (R k : Measure ℝ)|
        = (|Cumulant.cumulant id j (R k : Measure ℝ)| ^ ((j : ℝ)⁻¹)) ^ j :=
          (Real.rpow_inv_natCast_pow (abs_nonneg _) hj0).symm
      _ ≤ eps k ^ j :=
          pow_le_pow_left₀ (Real.rpow_nonneg (abs_nonneg _) _) (hepsle k j hj) j
  -- `|kappa_j (Z_n)| <= delta ^ j` for `3 <= j < m`
  have hkey : ∀ k, ∀ j ∈ Finset.Ico 3 m,
      |Cumulant.cumulant id j (W k : Measure ℝ)| ≤ δ ^ j := by
    intro k j hj
    rw [hWcum, abs_mul, abs_pow, abs_of_pos (ha0 k)]
    calc a k ^ j * |Cumulant.cumulant id j (R k : Measure ℝ)|
        ≤ a k ^ j * eps k ^ j :=
          mul_le_mul_of_nonneg_left (hpow k j hj) (pow_nonneg (ha0 k).le j)
      _ = (a k * eps k) ^ j := (mul_pow _ _ _).symm
      _ = δ ^ j := by rw [haeps]
  -- every other order is bounded because the original sequence converges there
  have hbd : ∀ j, 1 ≤ j → ∃ C : ℝ, ∀ k, |Cumulant.cumulant id j (W k : Measure ℝ)| ≤ C := by
    intro j hj1
    by_cases hjw : 3 ≤ j ∧ j < m
    · exact ⟨δ ^ j, fun k => hkey k j (Finset.mem_Ico.mpr hjw)⟩
    · obtain ⟨L, hL⟩ : ∃ L : ℝ,
          Tendsto (fun n => Cumulant.cumulant id j (P n : Measure ℝ)) atTop (𝓝 L) := by
        rcases Nat.lt_or_ge j 3 with hj3' | hj3'
        · interval_cases j
          · exact ⟨mu, h1⟩
          · exact ⟨s2, h2⟩
        · exact ⟨0, h3 j (by omega)⟩
      obtain ⟨C, hC⟩ := exists_abs_bound_of_tendsto hL
      refine ⟨C, fun k => ?_⟩
      rw [hWcum, abs_mul, abs_pow, abs_of_pos (ha0 k)]
      calc a k ^ j * |Cumulant.cumulant id j (R k : Measure ℝ)|
          ≤ 1 * |Cumulant.cumulant id j (R k : Measure ℝ)| :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (ha0 k).le (ha1 k)) (abs_nonneg _)
        _ = |Cumulant.cumulant id j (P (ψ k) : Measure ℝ)| := by rw [one_mul, hRdef]
        _ ≤ C := hC _
  -- Step 4: bounded cumulants give bounded moments; Prokhorov gives a limit law
  have hWmom : ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ∫ x, |x| ^ p ∂(W k : Measure ℝ) ≤ C := by
    intro p
    obtain ⟨C, hC⟩ := exists_moment_bound_of_cumulant_bound hbd (2 * p)
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
    refine ⟨1 + C, by linarith, fun k => ?_⟩
    calc ∫ x, |x| ^ p ∂(W k : Measure ℝ)
        ≤ ∫ x, (1 + x ^ (2 * p)) ∂(W k : Measure ℝ) := by
          refine integral_mono (integrable_abs_pow (hWint k p))
            ((integrable_const 1).add (hWint k (2 * p))) fun x => abs_pow_le_one_add x
      _ = 1 + ∫ x, x ^ (2 * p) ∂(W k : Measure ℝ) := by
          rw [integral_add (integrable_const 1) (hWint k (2 * p)), integral_const]
          simp
      _ ≤ 1 + C := by linarith [(le_abs_self _).trans (hC k)]
  obtain ⟨Q, φ, hφ, -, hQi, hQm⟩ := exists_limit_of_moment_bound W hWint hWmom
  have hQcum := tendsto_cumulant_of_tendsto_integral_pow hQm
  -- Step 5: the limit law's cumulants vanish from `m` on, hence from `3` on
  have hWzero : ∀ j, m ≤ j →
      Tendsto (fun k => Cumulant.cumulant id j (W k : Measure ℝ)) atTop (𝓝 0) := by
    intro j hj
    have hg : Tendsto (fun k => |Cumulant.cumulant id j (P (ψ k) : Measure ℝ)|) atTop (𝓝 0) := by
      have h := ((h3 j hj).comp hψtop).abs
      rwa [abs_zero] at h
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hg
    rw [Real.norm_eq_abs, hWcum, abs_mul, abs_pow, abs_of_pos (ha0 k)]
    calc a k ^ j * |Cumulant.cumulant id j (R k : Measure ℝ)|
        ≤ 1 * |Cumulant.cumulant id j (R k : Measure ℝ)| :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (ha0 k).le (ha1 k)) (abs_nonneg _)
      _ = |Cumulant.cumulant id j (P (ψ k) : Measure ℝ)| := by rw [one_mul, hRdef]
  have hQzero : ∀ j, m ≤ j → Cumulant.cumulant id j (Q : Measure ℝ) = 0 := fun j hj =>
    tendsto_nhds_unique (hQcum j) ((hWzero j hj).comp hφ.tendsto_atTop)
  have hQ3 : ∀ j, 3 ≤ j → Cumulant.cumulant id j (Q : Measure ℝ) = 0 := fun j hj =>
    Cumulant.cumulant_eq_zero_of_three_le hQi (m₀ := m) (by omega) hQzero hj
  -- Step 6: Janson's `(3.6)`, the supremum is attained
  have hattain : ∀ k, ∃ j ∈ Finset.Ico 3 m,
      |Cumulant.cumulant id j (W k : Measure ℝ)| = δ ^ j := by
    intro k
    obtain ⟨j, hj, hje⟩ := hepsex k
    have hj0 : j ≠ 0 := by rw [Finset.mem_Ico] at hj; omega
    refine ⟨j, hj, ?_⟩
    have habs : |Cumulant.cumulant id j (R k : Measure ℝ)| = eps k ^ j := by
      rw [hje]
      exact (Real.rpow_inv_natCast_pow (abs_nonneg _) hj0).symm
    rw [hWcum, abs_mul, abs_pow, abs_of_pos (ha0 k), habs, ← mul_pow, haeps]
  choose jj hjjmem hjjeq using hattain
  have hpig : ∃ j₁ ∈ Finset.Ico 3 m, ∃ᶠ l in atTop, jj (φ l) = j₁ := by
    by_contra hcon2
    push Not at hcon2
    have hev : ∀ᶠ l in atTop, ∀ j ∈ Finset.Ico 3 m, jj (φ l) ≠ j := by
      rw [Filter.eventually_all_finset]
      exact fun j hj => hcon2 j hj
    obtain ⟨l, hl⟩ := hev.exists
    exact hl (jj (φ l)) (hjjmem (φ l)) rfl
  obtain ⟨j₁, hj₁mem, hj₁freq⟩ := hpig
  have hzero1 : Tendsto (fun l => Cumulant.cumulant id j₁ (W (φ l) : Measure ℝ)) atTop (𝓝 0) := by
    have h := hQcum j₁
    rwa [hQ3 j₁ (Finset.mem_Ico.mp hj₁mem).1] at h
  have hsmall : ∀ᶠ l in atTop, |Cumulant.cumulant id j₁ (W (φ l) : Measure ℝ)| < δ ^ j₁ := by
    have h := hzero1.abs
    rw [abs_zero] at h
    exact h.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ j₁))
  obtain ⟨l, hlq, hlt⟩ := (hj₁freq.and_eventually hsmall).exists
  rw [← hlq] at hlt
  exact absurd (hjjeq (φ l)) (ne_of_lt hlt)

/-- **Janson's Theorem 1** (1988), conclusion (1.4). Let `P n` be laws on `ℝ` with finite moments
of every order. Suppose that the first cumulant `κ₁(P n)` converges to `mu`, the second cumulant
`κ₂(P n)` converges to `s2`, and, for some natural number `m`, the cumulant `κⱼ(P n)` converges to
`0` for every order `j ≥ m`. Then `P n` converges weakly to the Gaussian law `gaussPM mu s2` with
mean `mu` and variance `s2`. The limiting variance `s2` is automatically nonnegative, and
`s2 = 0` (a Dirac limit) is allowed. -/
theorem tendsto_gaussPM {P : ℕ → ProbabilityMeasure ℝ}
    (hint : ∀ n p, Integrable (fun x : ℝ => x ^ p) (P n : Measure ℝ))
    {m : ℕ} {mu s2 : ℝ}
    (h1 : Tendsto (fun n => Cumulant.cumulant id 1 (P n : Measure ℝ)) atTop (𝓝 mu))
    (h2 : Tendsto (fun n => Cumulant.cumulant id 2 (P n : Measure ℝ)) atTop (𝓝 s2))
    (h3 : ∀ j, m ≤ j → Tendsto (fun n => Cumulant.cumulant id j (P n : Measure ℝ)) atTop (𝓝 0)) :
    Tendsto P atTop (𝓝 (gaussPM mu s2)) :=
  tendsto_gaussPM_of_tendsto_cumulant hint h1 h2
    (fun _ hj => cumulant_tendsto_zero hint h1 h2 h3 hj)

/-- **Janson's Theorem 1** (1988), convergence of moments. Under the hypotheses of
`Janson.tendsto_gaussPM` (laws `P n` on `ℝ` with finite moments of every order, `κ₁(P n) → mu`,
`κ₂(P n) → s2`, and `κⱼ(P n) → 0` for every `j ≥ m`), for every natural number `p` the `p`-th
moment `∫ x ^ p ∂(P n)` converges to the `p`-th moment of the Gaussian law `gaussPM mu s2`. -/
theorem tendsto_integral_pow_gaussPM {P : ℕ → ProbabilityMeasure ℝ}
    (hint : ∀ n p, Integrable (fun x : ℝ => x ^ p) (P n : Measure ℝ))
    {m : ℕ} {mu s2 : ℝ}
    (h1 : Tendsto (fun n => Cumulant.cumulant id 1 (P n : Measure ℝ)) atTop (𝓝 mu))
    (h2 : Tendsto (fun n => Cumulant.cumulant id 2 (P n : Measure ℝ)) atTop (𝓝 s2))
    (h3 : ∀ j, m ≤ j → Tendsto (fun n => Cumulant.cumulant id j (P n : Measure ℝ)) atTop (𝓝 0))
    (p : ℕ) :
    Tendsto (fun n => ∫ x, x ^ p ∂(P n : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ p ∂(gaussPM mu s2 : Measure ℝ))) := by
  classical
  -- the limiting variance is nonnegative, because every `kappa_2` is
  have hs2 : 0 ≤ s2 := by
    refine ge_of_tendsto h2 (Eventually.of_forall fun n => ?_)
    exact Cumulant.cumulant_two_nonneg (hint n 2)
  set c : ℕ → ℝ := fun j => if j = 1 then mu else if j = 2 then s2 else 0 with hcdef
  have hc : ∀ j, 1 ≤ j →
      Tendsto (fun n => Cumulant.cumulant id j (P n : Measure ℝ)) atTop (𝓝 (c j)) := by
    intro j hj
    rcases Nat.lt_or_ge j 3 with h | h
    · interval_cases j
      · simpa [hcdef] using h1
      · simpa [hcdef] using h2
    · have hz : c j = 0 := by
        simp only [hcdef]
        split_ifs <;> first | rfl | omega
      rw [hz]
      exact cumulant_tendsto_zero hint h1 h2 h3 h
  have hgc : ∀ j, 1 ≤ j → Cumulant.cumulant id j (gaussPM mu s2 : Measure ℝ) = c j := by
    intro j hj
    rw [gaussPM_toMeasure, Cumulant.cumulant_gaussianReal _ _ j hj]
    simp only [Cumulant.gaussCumulants, hcdef, Real.coe_toNNReal _ hs2]
  have hgauss : ∫ x, x ^ p ∂(gaussPM mu s2 : Measure ℝ) = momentOf c p := by
    have hconst := tendsto_integral_pow_of_tendsto_cumulant
      (P := fun _ : ℕ => gaussPM mu s2) (c := c)
      (fun j hj => by rw [hgc j hj]; exact tendsto_const_nhds) p
    exact tendsto_nhds_unique tendsto_const_nhds hconst
  rw [hgauss]
  exact tendsto_integral_pow_of_tendsto_cumulant hc p

end Theorem1

/-! ### Section 3. The rate arithmetic of `Theorem 2`

Since `N_n >= M_n`, `(1.5)` implies `N_n M_n ^ (j-1) A_n ^ j -> 0` for every `j >= m`.
-/

section Rate

/-- The rate condition of Theorem 2 from `(1.5)`. Stated for an arbitrary positive sequence in
the degree slot, so that it applies with `M_n + 1`, the closed-neighbourhood count of
`DepGraph.nbhd`. -/
theorem tendsto_rate_of_janson15 {N Md u : ℕ → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hMd : ∀ n, 0 < Md n) (hNM : ∀ n, Md n ≤ N n) (hu : ∀ n, 0 ≤ u n)
    (h15 : Tendsto (fun n => (N n / Md n) ^ ((m : ℝ)⁻¹) * (Md n * u n)) atTop (𝓝 0))
    {j : ℕ} (hj : m ≤ j) :
    Tendsto (fun n => N n * Md n ^ (j - 1) * u n ^ j) atTop (𝓝 0) := by
  have hj1 : 1 ≤ j := le_trans hm hj
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hj0 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hj1
  have hbase : ∀ n, 1 ≤ N n / Md n := fun n => (one_le_div (hMd n)).mpr (hNM n)
  have hexp : ((j : ℝ))⁻¹ ≤ ((m : ℝ))⁻¹ := by
    rw [inv_le_inv₀ hj0 hm0]
    exact_mod_cast hj
  have hv : Tendsto (fun n => (N n / Md n) ^ ((j : ℝ)⁻¹) * (Md n * u n)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_) h15
    · have h1 : (0 : ℝ) ≤ (N n / Md n) ^ ((j : ℝ)⁻¹) :=
        Real.rpow_nonneg (le_trans zero_le_one (hbase n)) _
      have h2 : (0 : ℝ) ≤ Md n * u n := mul_nonneg (hMd n).le (hu n)
      positivity
    · refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (hMd n).le (hu n))
      exact Real.rpow_le_rpow_of_exponent_le (hbase n) hexp
  have hvj := hv.pow j
  rw [zero_pow (by omega : j ≠ 0)] at hvj
  have heq : ∀ n, ((N n / Md n) ^ ((j : ℝ)⁻¹) * (Md n * u n)) ^ j
      = N n * Md n ^ (j - 1) * u n ^ j := by
    intro n
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [mul_pow, Nat.add_sub_cancel]
    rw [Real.rpow_inv_natCast_pow (le_trans zero_le_one (hbase n)) (by omega), pow_succ]
    have hMn : Md n ≠ 0 := ne_of_gt (hMd n)
    field_simp
  simpa only [heq] using hvj

end Rate

/-! ### Section 4. `Theorem 2` -/

section Theorem2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
theorem measurable_stdSum (D : DepGraph X μ) (σ c : ℝ) :
    Measurable (fun ω => (∑ i, X i ω) / σ + c) :=
  ((Finset.measurable_sum _ fun i _ => D.meas i).div_const σ).add_const c

variable (μ X) in
/-- The law of Janson's standardized sum `S / σ + c` under `μ`, where `S = ∑ i, X i`. -/
noncomputable def stdSumPM (σ c : ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map ⟨μ, inferInstance⟩ (fun ω => (∑ i, X i ω) / σ + c)

variable (μ X) in
lemma stdSumPM_toMeasure (σ c : ℝ) :
    (stdSumPM μ X σ c : Measure ℝ) = μ.map (fun ω => (∑ i, X i ω) / σ + c) := rfl

lemma cumulant_stdSumPM (D : DepGraph X μ) (σ c : ℝ) (j : ℕ) :
    Cumulant.cumulant id j (stdSumPM μ X σ c : Measure ℝ)
      = Cumulant.cumulant (fun ω => (∑ i, X i ω) / σ + c) j μ := by
  rw [stdSumPM_toMeasure,
    Cumulant.cumulant_map μ (measurable_stdSum D σ c).aemeasurable id measurable_id j]
  simp only [id_eq]

omit [IsProbabilityMeasure μ] in
lemma abs_stdSum_le {A : ℝ} (hbd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ A)
    {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    ∀ᵐ ω ∂μ, |(∑ i, X i ω) / σ + c| ≤ (Fintype.card ι : ℝ) * A / σ + |c| := by
  filter_upwards [ae_all_iff.mpr hbd] with ω hω
  have hS : |∑ i, X i ω| ≤ (Fintype.card ι : ℝ) * A := by
    calc |∑ i, X i ω| ≤ ∑ i, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, A := Finset.sum_le_sum fun i _ => hω i
      _ = (Fintype.card ι : ℝ) * A := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc |(∑ i, X i ω) / σ + c| ≤ |(∑ i, X i ω) / σ| + |c| :=
      abs_add_le ((∑ i, X i ω) / σ) c
    _ ≤ (Fintype.card ι : ℝ) * A / σ + |c| := by
        have hq : |(∑ i, X i ω) / σ| ≤ (Fintype.card ι : ℝ) * A / σ := by
          rw [abs_div, abs_of_pos hσ]
          gcongr
        linarith

lemma integrable_pow_stdSumPM (D : DepGraph X μ) {A : ℝ} (hbd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ A)
    {σ : ℝ} (hσ : 0 < σ) (c : ℝ) (p : ℕ) :
    Integrable (fun x : ℝ => x ^ p) (stdSumPM μ X σ c : Measure ℝ) := by
  rw [stdSumPM_toMeasure,
    integrable_map_measure (measurable_id'.pow_const p).aestronglyMeasurable
      (measurable_stdSum D σ c).aemeasurable]
  simp only [Function.comp_def]
  refine Integrable.of_bound ((measurable_stdSum D σ c).pow_const p).aestronglyMeasurable
    (((Fintype.card ι : ℝ) * A / σ + |c|) ^ p) ?_
  filter_upwards [abs_stdSum_le hbd hσ c] with ω hω
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hω p

/-- With `c = - E S / sigma`, `kappa_1` of the standardized sum is `0`. -/
lemma cumulant_one_stdSumPM (D : DepGraph X μ) {A : ℝ} (hbd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ A)
    {σ : ℝ} {c : ℝ} (hc : c = -(∫ ω, (∑ i, X i ω) ∂μ) / σ) :
    Cumulant.cumulant id 1 (stdSumPM μ X σ c : Measure ℝ) = 0 := by
  have hSint : Integrable (fun ω => ∑ i, X i ω) μ := by
    refine Integrable.of_bound
      (Finset.measurable_sum _ fun i _ => D.meas i).aestronglyMeasurable
      ((Fintype.card ι : ℝ) * A) ?_
    filter_upwards [ae_all_iff.mpr hbd] with ω hω
    rw [Real.norm_eq_abs]
    calc |∑ i, X i ω| ≤ ∑ i, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, A := Finset.sum_le_sum fun i _ => hω i
      _ = (Fintype.card ι : ℝ) * A := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [cumulant_stdSumPM D, Cumulant.cumulant_one,
    integral_add (hSint.div_const σ) (integrable_const c), integral_div, integral_const, hc]
  simp
  ring

/-- With `sigma ^ 2 = var S`, `kappa_2` of the standardized sum is `1`. -/
lemma cumulant_two_stdSumPM (D : DepGraph X μ) {A : ℝ} (hbd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ A)
    {σ : ℝ} (hσ : 0 < σ) (c : ℝ)
    (hσsq : σ ^ 2 = Cumulant.cumulant (fun ω => ∑ i, X i ω) 2 μ) :
    Cumulant.cumulant id 2 (stdSumPM μ X σ c : Measure ℝ) = 1 := by
  have hSm : Measurable (fun ω => ∑ i, X i ω) := Finset.measurable_sum _ fun i _ => D.meas i
  rw [cumulant_stdSumPM D,
    Cumulant.cumulant_add_const _ (hSm.div_const σ) c (by norm_num) μ
      (fun r _ => integrable_sum_div_pow D hbd σ r),
    show (fun ω => (∑ i, X i ω) / σ) = fun ω => σ⁻¹ * (∑ i, X i ω) from
      funext fun ω => div_eq_inv_mul _ _,
    Cumulant.cumulant_const_smul (fun ω => ∑ i, X i ω) σ⁻¹ 2 μ, ← hσsq]
  field_simp

/-- **Janson's Theorem 2** (1988), with the rate in the form of Lemma 4. For each `n`, let
`X n i` (`i` ranging over a finite index set of size `N_n`) be real random variables on a
probability space `(Ω n, μ n)` with dependency graph `D n`, in which every vertex has at most
`M n` neighbours other than itself, and with `|X n i| ≤ A n` almost surely. Let `S_n = ∑ i, X n i`
and let `σ n > 0` satisfy `(σ n) ^ 2 = κ₂(S_n)`, the variance of `S_n`. If, for some `m ≥ 3`,
`N_n (M n + 1) ^ (j - 1) (A n / σ n) ^ j → 0` for every `j ≥ m`, then the law of the
standardized sum `(S_n - 𝔼 S_n) / σ n` converges weakly to the standard Gaussian law
`gaussPM 0 1`. -/
theorem tendsto_gaussPM_of_depGraph
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {X : ∀ n, ι n → Ω n → ℝ} (D : ∀ n, DepGraph (X n) (μ n))
    {M : ℕ → ℕ} (hdeg : ∀ n, ∀ i : ι n, #(((D n).nbhd i).erase i) ≤ M n)
    {A : ℕ → ℝ} (hA : ∀ n, 0 ≤ A n) (hbd : ∀ n, ∀ i, ∀ᵐ ω ∂(μ n), |X n i ω| ≤ A n)
    {σ : ℕ → ℝ} (hσ : ∀ n, 0 < σ n)
    (hσsq : ∀ n, σ n ^ 2 = Cumulant.cumulant (fun ω => ∑ i, X n i ω) 2 (μ n))
    {m : ℕ} (hm : 3 ≤ m)
    (hrate : ∀ j, m ≤ j → Tendsto (fun n => (Fintype.card (ι n) : ℝ)
      * ((M n : ℝ) + 1) ^ (j - 1) * (A n / σ n) ^ j) atTop (𝓝 0)) :
    Tendsto (fun n => stdSumPM (μ n) (X n) (σ n) (-(∫ ω, (∑ i, X n i ω) ∂(μ n)) / σ n)) atTop
      (𝓝 (gaussPM 0 1)) := by
  have hint : ∀ n p, Integrable (fun x : ℝ => x ^ p)
      ((stdSumPM (μ n) (X n) (σ n) (-(∫ ω, (∑ i, X n i ω) ∂(μ n)) / σ n) : ProbabilityMeasure ℝ) :
        Measure ℝ) :=
    fun n p => integrable_pow_stdSumPM (D n) (hbd n) (hσ n) _ p
  have h1 : Tendsto (fun n => Cumulant.cumulant id 1
      ((stdSumPM (μ n) (X n) (σ n) (-(∫ ω, (∑ i, X n i ω) ∂(μ n)) / σ n) : ProbabilityMeasure ℝ) :
        Measure ℝ)) atTop (𝓝 0) := by
    have he : ∀ n, Cumulant.cumulant id 1
        ((stdSumPM (μ n) (X n) (σ n) (-(∫ ω, (∑ i, X n i ω) ∂(μ n)) / σ n) : ProbabilityMeasure ℝ) :
          Measure ℝ) = 0 :=
      fun n => cumulant_one_stdSumPM (D n) (hbd n) rfl
    simp only [he]
    exact tendsto_const_nhds
  have h2 : Tendsto (fun n => Cumulant.cumulant id 2
      ((stdSumPM (μ n) (X n) (σ n) (-(∫ ω, (∑ i, X n i ω) ∂(μ n)) / σ n) : ProbabilityMeasure ℝ) :
        Measure ℝ)) atTop (𝓝 1) := by
    have he : ∀ n, Cumulant.cumulant id 2
        ((stdSumPM (μ n) (X n) (σ n) (-(∫ ω, (∑ i, X n i ω) ∂(μ n)) / σ n) : ProbabilityMeasure ℝ) :
          Measure ℝ) = 1 :=
      fun n => cumulant_two_stdSumPM (D n) (hbd n) (hσ n) _ (hσsq n)
    simp only [he]
    exact tendsto_const_nhds
  have h3 : ∀ j, m ≤ j → Tendsto (fun n => Cumulant.cumulant id j
      ((stdSumPM (μ n) (X n) (σ n) (-(∫ ω, (∑ i, X n i ω) ∂(μ n)) / σ n) : ProbabilityMeasure ℝ) :
        Measure ℝ)) atTop (𝓝 0) := by
    intro j hj
    have hg : Tendsto (fun n => jansonConst j * ((Fintype.card (ι n) : ℝ)
        * ((M n : ℝ) + 1) ^ (j - 1) * (A n / σ n) ^ j)) atTop (𝓝 0) := by
      simpa using (hrate j hj).const_mul (jansonConst j)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
    rw [Real.norm_eq_abs, cumulant_stdSumPM (D n)]
    exact abs_cumulant_standardized_le (D n) (hdeg n) (hA n) (hbd n) (hσ n) _ (by omega)
  have hfinal := tendsto_gaussPM hint h1 h2 h3
  simpa using hfinal

/-- **Janson's Theorem 2** (1988), under condition (1.5). For each `n`, let `X n i` (`i`
ranging over a finite index set of size `N_n`) be real random variables on a probability space
`(Ω n, μ n)` with dependency graph `D n`, in which every vertex has at most `M n` neighbours other
than itself, where `1 ≤ M n ≤ N_n`, and with `|X n i| ≤ A n` almost surely. Let `S_n = ∑ i, X n i`
and let `σ n > 0` satisfy `(σ n) ^ 2 = κ₂(S_n)`, the variance of `S_n`. If, for some integer
`m ≥ 3`, `(N_n / M n) ^ (1 / m) * M n * A n / σ n → 0`, then the law of the standardized sum
`(S_n - 𝔼 S_n) / σ n` converges weakly to the standard Gaussian law `gaussPM 0 1`. -/
theorem tendsto_gaussPM_of_depGraph_janson15
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)]
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
    {X : ∀ n, ι n → Ω n → ℝ} (D : ∀ n, DepGraph (X n) (μ n))
    {M : ℕ → ℕ} (hdeg : ∀ n, ∀ i : ι n, #(((D n).nbhd i).erase i) ≤ M n)
    (hM1 : ∀ n, 1 ≤ M n) (hMN : ∀ n, M n ≤ Fintype.card (ι n))
    {A : ℕ → ℝ} (hA : ∀ n, 0 ≤ A n) (hbd : ∀ n, ∀ i, ∀ᵐ ω ∂(μ n), |X n i ω| ≤ A n)
    {σ : ℕ → ℝ} (hσ : ∀ n, 0 < σ n)
    (hσsq : ∀ n, σ n ^ 2 = Cumulant.cumulant (fun ω => ∑ i, X n i ω) 2 (μ n))
    {m : ℕ} (hm : 3 ≤ m)
    (h15 : Tendsto (fun n => ((Fintype.card (ι n) : ℝ) / (M n : ℝ)) ^ ((m : ℝ)⁻¹)
      * ((M n : ℝ) * (A n / σ n))) atTop (𝓝 0)) :
    Tendsto (fun n => stdSumPM (μ n) (X n) (σ n) (-(∫ ω, (∑ i, X n i ω) ∂(μ n)) / σ n)) atTop
      (𝓝 (gaussPM 0 1)) := by
  have hu : ∀ n, 0 ≤ A n / σ n := fun n => div_nonneg (hA n) (hσ n).le
  have hM1r : ∀ n, (1 : ℝ) ≤ (M n : ℝ) := fun n => by exact_mod_cast hM1 n
  have hNr : ∀ n, ((M n : ℝ) + 1) ≤ (Fintype.card (ι n) : ℝ) + 1 := by
    intro n
    have : (M n : ℝ) ≤ (Fintype.card (ι n) : ℝ) := by exact_mod_cast hMN n
    linarith
  -- `(1.5)` transported from `M_n` to the closed-neighbourhood count `M_n + 1`, on `N_n + 1`
  have h15' : Tendsto (fun n => (((Fintype.card (ι n) : ℝ) + 1) / ((M n : ℝ) + 1)) ^ ((m : ℝ)⁻¹)
      * (((M n : ℝ) + 1) * (A n / σ n))) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => ?_) (fun n => ?_) (by simpa using h15.const_mul (2 : ℝ))
    · have h1 : (0 : ℝ) ≤ (((Fintype.card (ι n) : ℝ) + 1) / ((M n : ℝ) + 1)) ^ ((m : ℝ)⁻¹) :=
        Real.rpow_nonneg (by positivity) _
      have h2 : (0 : ℝ) ≤ ((M n : ℝ) + 1) * (A n / σ n) :=
        mul_nonneg (by positivity) (hu n)
      positivity
    · have hbase : ((Fintype.card (ι n) : ℝ) + 1) / ((M n : ℝ) + 1)
          ≤ (Fintype.card (ι n) : ℝ) / (M n : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) (by linarith [hM1r n])]
        nlinarith [hNr n, hM1r n]
      have hrpow : (((Fintype.card (ι n) : ℝ) + 1) / ((M n : ℝ) + 1)) ^ ((m : ℝ)⁻¹)
          ≤ ((Fintype.card (ι n) : ℝ) / (M n : ℝ)) ^ ((m : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hbase (by positivity)
      have hfac : ((M n : ℝ) + 1) * (A n / σ n) ≤ 2 * ((M n : ℝ) * (A n / σ n)) := by
        nlinarith [hM1r n, hu n]
      calc (((Fintype.card (ι n) : ℝ) + 1) / ((M n : ℝ) + 1)) ^ ((m : ℝ)⁻¹)
            * (((M n : ℝ) + 1) * (A n / σ n))
          ≤ ((Fintype.card (ι n) : ℝ) / (M n : ℝ)) ^ ((m : ℝ)⁻¹)
            * (((M n : ℝ) + 1) * (A n / σ n)) :=
            mul_le_mul_of_nonneg_right hrpow (mul_nonneg (by positivity) (hu n))
        _ ≤ ((Fintype.card (ι n) : ℝ) / (M n : ℝ)) ^ ((m : ℝ)⁻¹)
            * (2 * ((M n : ℝ) * (A n / σ n))) :=
            mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg (by positivity) _)
        _ = 2 * (((Fintype.card (ι n) : ℝ) / (M n : ℝ)) ^ ((m : ℝ)⁻¹)
            * ((M n : ℝ) * (A n / σ n))) := by ring
  refine tendsto_gaussPM_of_depGraph D hdeg hA hbd hσ hσsq hm ?_
  intro j hj
  have hbig := tendsto_rate_of_janson15 (N := fun n => (Fintype.card (ι n) : ℝ) + 1)
    (Md := fun n => ((M n : ℝ) + 1)) (u := fun n => A n / σ n) (m := m) (by omega)
    (fun n => by positivity) hNr hu h15' hj
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hbig
  · have : (0 : ℝ) ≤ (A n / σ n) ^ j := pow_nonneg (hu n) j
    positivity
  · have hrest : (0 : ℝ) ≤ ((M n : ℝ) + 1) ^ (j - 1) * (A n / σ n) ^ j :=
      mul_nonneg (by positivity) (pow_nonneg (hu n) j)
    have h2 : (Fintype.card (ι n) : ℝ) ≤ (Fintype.card (ι n) : ℝ) + 1 := by linarith
    calc (Fintype.card (ι n) : ℝ) * ((M n : ℝ) + 1) ^ (j - 1) * (A n / σ n) ^ j
        = (Fintype.card (ι n) : ℝ) * (((M n : ℝ) + 1) ^ (j - 1) * (A n / σ n) ^ j) := by ring
      _ ≤ ((Fintype.card (ι n) : ℝ) + 1) * (((M n : ℝ) + 1) ^ (j - 1) * (A n / σ n) ^ j) :=
          mul_le_mul_of_nonneg_right h2 hrest
      _ = ((Fintype.card (ι n) : ℝ) + 1) * ((M n : ℝ) + 1) ^ (j - 1) * (A n / σ n) ^ j := by ring

end Theorem2

end StatLean.AsymptoticStatistics.Janson
