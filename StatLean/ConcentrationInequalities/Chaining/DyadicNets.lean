import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
import Mathlib.Data.Int.Log
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Dyadic nets and chain scaffolding

Purely metric chaining scaffolding (no probability): realizer Finset nets at
each dyadic scale $\varepsilon_k = 2^{-k}$ ($k \in \mathbb{Z}$), coarse-scale
selection via `Int.clog` (so that $2^{-\kappa} \in [\operatorname{diam} T,
2\operatorname{diam} T)$ and the $\kappa$-level net is a singleton), a
pseudometric-safe fine scale below the minimum positive distance of a finite
$T$, closest-point projections $\pi_k(t)$, the distance-filtered close-pair
Finsets over which per-level maxima are taken, the chain telescoping
$X_t - X_{\pi_\kappa(t)} = \sum_k (X_{\pi_{k+1}(t)} - X_{\pi_k(t)})$, and
sup-of-sum ≤ sum-of-sups. Shared by `DiscreteDudley`, `DudleyTail`, and
`GenericChaining`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Eqs. (8.4)–(8.10) (the chaining setup in
the proof of Theorem 8.1.4).

**Proof formalization notes.** Nets are realizer Finsets extracted from
`Metric.exists_set_encard_eq_coveringNumber` (the `≠ ⊤` discharge is
`coveringNumber ≤ encard < ⊤` for finite `T`). Scales are ℤ-dyadic with
`κ := −Int.clog 2 D` (via `Int.self_le_zpow_clog` /
`Int.zpow_pred_clog_lt_self`); levels are re-indexed by ℕ offsets so the
telescoping is literally `Finset.sum_range_sub`. In a PSEUDOmetric the finest
projection satisfies `dist t (π t) = 0` only — the a.e. identification
`X_{π t} = X_t` is done downstream via
`ae_eq_zero_of_subGaussianNorm_eq_zero`. Per-level maxima run over
`closePairs N M r` — the distance-FILTERED product Finset — so far-apart
pairs never enter the maximal inequality; `card ≤ |N|·|M|`. `netProj N x` is
total with junk value `x` for `N = ∅` (documented; all consumers supply
`N.Nonempty`). Pre-agreed >300-line split plan (design risk register): if
this file exceeds ~300 lines during proof closure, split into
`Chaining/DyadicScales.lean` (scale selection: `exists_coarse_scale`,
`exists_fine_scale`, covering-number facts) and
`Chaining/NetProjections.lean` (`netProj`, `closePairs`, telescoping,
sup-exchange) — the `def`s stay byte-identical, only lemma homes move.
Named-sorry fallback of this work item: `exists_finset_net` (the
encard-to-Finset plumbing).

**Bibliographic comments.** The dyadic-scale chaining construction goes back
to A. N. Kolmogorov (continuity criterion, unpublished lectures, 1930s) and
was developed for Gaussian processes by R. M. Dudley, "The sizes of compact
subsets of Hilbert space and continuity of Gaussian processes," *J. Funct.
Anal.* 1 (1967), 290–330; the ε-net vocabulary is Kolmogorov–Tikhomirov
(1959). See the HDP Chapter 8 Notes.
-/

open Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {E : Type*} [PseudoMetricSpace E]

/-- Realizer net (HDP §8.1, Eq. (8.5)): a finite set `T` admits, at every
radius `ε > 0`, an internal Finset net whose cardinality realizes the
covering number (from `Metric.exists_set_encard_eq_coveringNumber`; the
`≠ ⊤` discharge is `coveringNumber ≤ encard < ⊤`). -/
lemma exists_finset_net {T : Set E}
    -- LEAN-ONLY: T finite (book WLOG, HDP p.227 footnote); realizer plumbing
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness so the net is nonempty
    (hne : T.Nonempty)
    -- LEAN-ONLY: positive radius; ε ≤ 0 is never used by chaining
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset E, ↑N ⊆ T ∧ N.Nonempty ∧ (∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε) ∧
      (N.card : ℕ∞) = coveringNumber T ε := by sorry

/-- Above the diameter one center suffices (HDP §8.1, Eq. (8.6), the coarse
net): real-radius wrapper of `Metric.coveringNumber_eq_one_of_ediam_le`. -/
lemma coveringNumber_eq_one_of_diam_le {T : Set E}
    -- LEAN-ONLY: nonemptiness (empty T has covering number 0, not 1)
    (hne : T.Nonempty)
    -- LEAN-ONLY: boundedness so `Metric.diam` is meaningful (not junk 0)
    (hbd : Bornology.IsBounded T)
    -- LEAN-ONLY: nonnegative radius (negative radii clamp to 0)
    {ε : ℝ} (hε : 0 ≤ ε)
    -- LEAN-ONLY: radius above the diameter; HDP §8.1, Eq (8.6)
    (h : Metric.diam T ≤ ε) :
    coveringNumber T ε = 1 := by sorry

/-- Two far-apart points force at least two centers — the quantitative
`𝒩 ≥ 2` below `diam/2` device feeding the diameter lower bounds on the
entropy sum (HDP §8.1, Remark 8.1.6 absorption). -/
lemma one_lt_coveringNumber_of_two_mul_lt_dist {T : Set E} {ε : ℝ} {a b : E}
    -- LEAN-ONLY: the two witnesses live in T
    (ha : a ∈ T) (hb : b ∈ T)
    -- LEAN-ONLY: separation 2ε < d(a,b); pure metric pigeonhole
    (h : 2 * ε < dist a b) :
    1 < coveringNumber T ε := by sorry

/-- Coarse dyadic scale (HDP §8.1, Eqs. (8.4)/(8.6)): `κ := −Int.clog 2 D`
satisfies `D ≤ 2^{−κ} < 2D` (via `Int.self_le_zpow_clog` and
`Int.zpow_pred_clog_lt_self`). -/
lemma exists_coarse_scale {D : ℝ}
    -- LEAN-ONLY: positive diameter bound; the D = 0 corner is degenerate
    (hD : 0 < D) :
    ∃ κ : ℤ, D ≤ (2 : ℝ) ^ (-κ) ∧ (2 : ℝ) ^ (-κ) < 2 * D := by sorry

/-- Fine dyadic scale (HDP §8.1, Eq. (8.6), the fine net), pseudometric-safe:
below the minimum POSITIVE distance of the finite `T`, dyadically-close
points are at pseudo-distance exactly `0`. -/
lemma exists_fine_scale {T : Set E}
    -- LEAN-ONLY: T finite so the minimum positive distance exists
    (hfin : T.Finite) (κ : ℤ) :
    ∃ n : ℕ, 0 < n ∧ ∀ s ∈ T, ∀ t ∈ T,
      dist s t ≤ (2 : ℝ) ^ (-(κ + n : ℤ)) → dist s t = 0 := by sorry

/-- **Closest-point projection** `π_N(x)` onto a Finset net (HDP §8.1, the
projections `π_k(t)` of Eq. (8.7)): a point of `N` minimizing the distance to
`x`. Edge behavior: junk value `x` itself when `N = ∅` (every consumer
supplies `N.Nonempty`). -/
noncomputable def netProj (N : Finset E) (x : E) : E :=
  if h : N.Nonempty then (N.exists_min_image (fun a => dist x a) h).choose else x

/-- The projection lands in the net (HDP §8.1, Eq. (8.7)). -/
lemma netProj_mem {N : Finset E}
    -- LEAN-ONLY: nonemptiness excludes the junk branch of `netProj`
    (hN : N.Nonempty) (x : E) :
    netProj N x ∈ N := by sorry

/-- The projection beats any witness: if some net point is `ε`-close to `x`,
so is `netProj N x` (HDP §8.1, Eq. (8.7)). -/
lemma dist_netProj_le {N : Finset E} {x : E} {ε : ℝ}
    -- LEAN-ONLY: a witness net point within ε (from the net property)
    (hx : ∃ a ∈ N, dist x a ≤ ε) :
    dist x (netProj N x) ≤ ε := by sorry

open Classical in
/-- **Close pairs** (HDP §8.1, proof of Theorem 8.1.4, Step 2): the
distance-filtered product Finset `{(a,b) ∈ N × M : d(a,b) ≤ r}` indexing one
chaining level, so far-apart pairs (whose increments are not ψ₂-small) never
enter the maximal inequality. Edge behavior: empty when `r < 0` in a genuine
metric space with `N`, `M` disjoint far apart — consumers re-establish
nonemptiness via `proj_pair_mem_closePairs`. -/
noncomputable def closePairs (N M : Finset E) (r : ℝ) : Finset (E × E) :=
  (N ×ˢ M).filter fun p => dist p.1 p.2 ≤ r

/-- Cardinality of a chaining level (HDP §8.1, Step 2:
`|T_k|·|T_{k−1}| ≤ |T_k|²`). -/
lemma card_closePairs_le (N M : Finset E) (r : ℝ) :
    (closePairs N M r).card ≤ N.card * M.card := by sorry

/-- Consecutive projections form a close pair (HDP §8.1, Step 2: the triangle
inequality `d(π_k t, π_{k−1} t) ≤ ε_k + ε_{k−1}`). -/
lemma proj_pair_mem_closePairs {N M : Finset E} {x : E} {ε δ : ℝ}
    -- LEAN-ONLY: projection quality at the two consecutive scales
    (hN : dist x (netProj N x) ≤ ε) (hM : dist x (netProj M x) ≤ δ)
    -- LEAN-ONLY: nonemptiness excludes the junk branches of `netProj`
    (hNne : N.Nonempty) (hMne : M.Nonempty) :
    (netProj N x, netProj M x) ∈ closePairs N M (ε + δ) := by sorry

/-- Chain telescoping (HDP §8.1, Eqs. (8.8)/(8.9)): literally
`Finset.sum_range_sub`. -/
lemma chain_telescope {n : ℕ} (g : ℕ → ℝ) :
    g n - g 0 = ∑ i ∈ Finset.range n, (g (i + 1) - g i) := by sorry

/-- Sup-of-sum ≤ sum-of-sups over a finite index set (HDP §8.1, Eq. (8.10)). -/
lemma biSup_sum_le_sum_biSup {T : Set E}
    -- LEAN-ONLY: T finite so all real biSups are honest finite maxima
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty) {n : ℕ} (g : ℕ → E → ℝ) :
    (⨆ t ∈ T, ∑ i ∈ Finset.range n, g i t)
      ≤ ∑ i ∈ Finset.range n, ⨆ t ∈ T, g i t := by sorry

end StatLean.ConcentrationInequalities
