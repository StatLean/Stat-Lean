import StatLean.ConcentrationInequalities.Chaining.EntropyIntegrand
import StatLean.ConcentrationInequalities.Chaining.DyadicNets
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Dyadic entropy sum and Dudley integral carriers

The dyadic entropy sum of HDP Eq. (8.2),
$$ \Sigma(T) \;=\; \sum_{k \in \mathbb{Z}} 2^{-k}
     \sqrt{\log \mathcal{N}(T, d, 2^{-k})}, $$
and the diameter-capped Dudley entropy integral of Eq. (8.16),
$$ I(T, D) \;=\; \int_0^{D} \sqrt{\log \mathcal{N}(T, d, \varepsilon)}\,
     d\varepsilon , $$
with: summability for finite nonempty $T$ (derived, never hypothesized),
window-sum control, the one-directional comparison $\Sigma \le 2 I$ (book
p. 226), the diameter lower bounds used for term absorption
(Remark 8.1.6), and the $\mathbb{R}_{\ge 0}^\infty$ twin `dudleyLIntegral`
used solely by the countable lift.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1: Eq. (8.2) (Theorem 8.1.4's sum),
Eq. (8.16) / Remark 8.1.7 (the diameter-capped integral), p. 226 (the sum-vs-
integral comparison in the proof of Theorem 8.1.3), Remark 8.1.6.

**Proof formalization notes.** `dudleySum` is a REAL ℤ-indexed `tsum` (junk
`0` only when non-summable, ruled out for finite nonempty `T` by
`summable_dudleySummand`: terms vanish left of the coarse scale since
`𝒩 = 1` at `ε ≥ diam`, and are geometrically dominated by `2^{−k}√(log |T|)`
on the right). Proofs use finite WINDOW sums `∑ k ∈ Icc (κ+1) (κ+n)` and the
bridge `sum_window_le_dudleySum`. Only the direction `∑ ≤ 2∫` is formalized
(book p. 226: `2^{−k} = 2∫_{2^{−k−1}}^{2^{−k}} dε` + antitonicity): per
dyadic block `2^{−k−1}·f(2^{−k}) ≤ ∫_{Ioc(2^{−k−1}, 2^{−k})} f`, the blocks
are pairwise disjoint and tile inside `Ioc 0 D` — NOT via the unit-step
`AntitoneOn.sum_le_integral` family (wrong grid shape). The reverse
`∫ ≤ 2∑` (HDP Exercise 8.3) is out of scope. The cap `D` is an explicit
parameter with hypothesis `diam T ≤ D`, making Eq. (8.16) the PRIMARY
statement and Eq. (8.13)'s `∫_0^∞` a display corollary
(`dudleyIntegral_Ioi_eq`). The diameter absorption lemmas
(`diam·√log2 ≤ 4·dudleySum`, `≤ 8·dudleyIntegral`) are the only places the
book's constant-free "`𝒩 ≥ 2` below `diam/2`" step becomes a quantitative
Lean cost. Pre-agreed >300-line split plan (design risk register): if this
file exceeds ~300 lines during proof closure, split into
`Chaining/EntropySum.lean` (the ℤ-sum carrier: `dudleySummand`, `dudleySum`,
summability, window bridges, `diam ≤ 4·dudleySum`) and a new
`Chaining/DudleyIntegral.lean` (the integral carriers `dudleyIntegral` /
`dudleyLIntegral`, the `∑ ≤ 2∫` comparison, `dudleyIntegral_Ioi_eq`, and the
`diam ≤ 8·dudleyIntegral` absorption) — all `def` bodies stay byte-identical,
only lemma homes move. Named-sorry fallback of this work item:
`sum_window_le_two_mul_dudleyIntegral` (the block-tiling comparison), with
both carriers and all other lemmas proved.

**Bibliographic comments.** The entropy integral is due to R. M. Dudley,
"The sizes of compact subsets of Hilbert space and continuity of Gaussian
processes," *J. Funct. Anal.* 1 (1967), 290–330; the dyadic-sum form and the
sum/integral equivalence are standard (HDP §8.1; Talagrand, *Upper and Lower
Bounds for Stochastic Processes*, 2014, §2.3). See the HDP Chapter 8 Notes.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {E : Type*} [PseudoMetricSpace E]

/-- **Dyadic entropy summand** (HDP §8.1, Eq. (8.2)):
`2^{−k} √(log 𝒩(T, d, 2^{−k}))` at the dyadic scale `k ∈ ℤ`. Edge behavior
inherited from `sqrtLogCov` (junk `0` at `𝒩 = ⊤`). -/
noncomputable def dudleySummand (T : Set E) (k : ℤ) : ℝ :=
  (2 : ℝ) ^ (-k) * sqrtLogCov T ((2 : ℝ) ^ (-k))

/-- **Dyadic entropy sum** (HDP §8.1, Eq. (8.2) RHS): the ℤ-indexed `tsum`
of `dudleySummand`. Edge behavior: junk `0` when non-summable — ruled out
for finite nonempty `T` by `summable_dudleySummand`, so the junk zone is
never load-bearing in the chaining theorems. -/
noncomputable def dudleySum (T : Set E) : ℝ :=
  ∑' k : ℤ, dudleySummand T k

lemma dudleySummand_nonneg (T : Set E) (k : ℤ) :
    -- LEAN-ONLY: product of nonnegatives; no book content
    0 ≤ dudleySummand T k := by sorry

/-- Summability of the dyadic entropy sum for finite nonempty `T` (HDP §8.1,
proof Step 1): finitely many nonzero terms on the left (`𝒩 = 1` for
`2^{−k} ≥ diam T`) and a geometric tail on the right (`𝒩 ≤ |T|`). Derived,
never hypothesized. -/
lemma summable_dudleySummand {T : Set E}
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) :
    Summable (dudleySummand T) := by sorry

lemma dudleySum_nonneg (T : Set E) :
    -- LEAN-ONLY: tsum of nonnegatives (junk 0 also nonneg); no book content
    0 ≤ dudleySum T := by sorry

/-- Finite windows are dominated by the full sum (HDP §8.1, the
Eq. (8.12) ⇒ Eq. (8.2) step): nonneg partial sums vs `tsum`. -/
lemma sum_window_le_dudleySum {T : Set E}
    -- LEAN-ONLY: T finite so the tsum is honest (summable)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) (s : Finset ℤ) :
    ∑ k ∈ s, dudleySummand T k ≤ dudleySum T := by sorry

/-- **Dudley entropy integral, diameter-capped** (HDP §8.1, Eq. (8.16)):
`∫_0^D √(log 𝒩(T,d,ε)) dε` as a Bochner set integral over `Ioc 0 D` w.r.t.
`volume`. The cap `D` is explicit: `D = diam T` gives Eq. (8.16), and the
zero-extension beyond the diameter gives the `∫_0^∞` display of Theorem
8.1.3 (`dudleyIntegral_Ioi_eq`). Edge behavior: `0` for `D ≤ 0` (empty
interval) and under the `sqrtLogCov` junk zone (guarded by consumers). -/
noncomputable def dudleyIntegral (T : Set E) (D : ℝ) : ℝ :=
  ∫ ε in Set.Ioc (0 : ℝ) D, sqrtLogCov T ε

lemma dudleyIntegral_nonneg (T : Set E) (D : ℝ) :
    -- LEAN-ONLY: integral of a nonneg integrand; no book content
    0 ≤ dudleyIntegral T D := by sorry

/-- Monotonicity in the cap (LEAN-ONLY: nonneg integrand on a larger set). -/
lemma dudleyIntegral_mono_cap {T : Set E}
    -- LEAN-ONLY: T finite gives integrability on both intervals
    (hfin : T.Finite) {D D' : ℝ}
    -- LEAN-ONLY: cap comparison
    (h : D ≤ D') :
    dudleyIntegral T D ≤ dudleyIntegral T D' := by sorry

/-- The `∫_0^∞` display equals the capped integral (HDP §8.1, Remark 8.1.7):
the integrand vanishes on `[diam T, ∞)`; bridges Eq. (8.13)'s `∫_0^∞` to the
capped carrier. -/
lemma dudleyIntegral_Ioi_eq {T : Set E}
    -- LEAN-ONLY: T finite (integrability + the √(log|T|) bound)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {D : ℝ}
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap (the diam = 0 corner is handled by consumers)
    (hD0 : 0 < D) :
    ∫ ε in Set.Ioi (0 : ℝ), sqrtLogCov T ε = dudleyIntegral T D := by sorry

/-- **Window-sum vs integral comparison** (HDP §8.1, p. 226, proof of
Theorem 8.1.3): per dyadic block,
`2^{−k−1}·sqrtLogCov T (2^{−k}) ≤ ∫_{Ioc(2^{−k−1}, 2^{−k})} sqrtLogCov`
(constant-on-block lower bound + `sqrtLogCov_anti`); the blocks are pairwise
disjoint and tile inside `Ioc 0 D`, so any finite window sum is at most
`2 · dudleyIntegral T D`. This is the file's named-sorry fallback. -/
theorem sum_window_le_two_mul_dudleyIntegral {T : Set E}
    -- LEAN-ONLY: T finite (integrability, antitonicity below ⊤)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {s : Finset ℤ} {D : ℝ}
    -- LEAN-ONLY: the window scales fit under the cap, so the blocks tile
    -- inside Ioc 0 D
    (hs : ∀ k ∈ s, (2 : ℝ) ^ (-k) ≤ D) :
    ∑ k ∈ s, dudleySummand T k ≤ 2 * dudleyIntegral T D := by sorry

/-- **Sum ≤ 2·integral** (HDP §8.1, p. 226): tsum version of the window
comparison via `Summable.tsum_le_of_sum_le` (window terms above the diameter
scale vanish). -/
theorem dudleySum_le_two_mul_dudleyIntegral {T : Set E}
    -- LEAN-ONLY: T finite (summability + integrability)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {D : ℝ}
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    dudleySum T ≤ 2 * dudleyIntegral T D := by sorry

/-- Diameter lower bound on the sum (HDP §8.1, Remark 8.1.6 absorption
device): at the last scale `κ'` with `𝒩 = 1`, the `(κ'+1)`-term is
`≥ 2^{−κ'−1}·√log 2 ≥ (diam/4)·√log 2` (uses
`one_lt_coveringNumber_of_two_mul_lt_dist`). The frozen numeral `4` is the
quantitative cost of the book's constant-free "`𝒩 ≥ 2` below `diam/2`". -/
lemma diam_mul_sqrt_log_two_le_four_mul_dudleySum {T : Set E}
    -- LEAN-ONLY: T finite (summability; honest diam)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) :
    Metric.diam T * Real.sqrt (Real.log 2) ≤ 4 * dudleySum T := by sorry

/-- Diameter lower bound on the integral (HDP §8.1, Remark 8.1.6): previous
lemma + `∑ ≤ 2∫`; frozen numeral `8 = 4 × 2`. -/
lemma diam_mul_sqrt_log_two_le_eight_mul_dudleyIntegral {T : Set E}
    -- LEAN-ONLY: T finite
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty) {D : ℝ}
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    Metric.diam T * Real.sqrt (Real.log 2) ≤ 8 * dudleyIntegral T D := by sorry

/-- ℝ≥0∞ twin of the Dudley integral (HDP §8.1, p. 227 footnote), used
SOLELY by the countable lift `dudley_inequality_countable` so that neither
side of the lifted inequality can be junk. -/
noncomputable def dudleyLIntegral (T : Set E) (D : ℝ) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc (0 : ℝ) D, ENNReal.ofReal (sqrtLogCov T ε)

/-- The twin agrees with the Bochner carrier under integrability. -/
lemma dudleyLIntegral_eq_ofReal {T : Set E} {D : ℝ}
    -- LEAN-ONLY: integrability so `ofReal ∘ ∫ = ∫⁻ ∘ ofReal`; no book content
    (hint : MeasureTheory.IntegrableOn (sqrtLogCov T) (Set.Ioc 0 D)
      MeasureTheory.volume) :
    dudleyLIntegral T D = ENNReal.ofReal (dudleyIntegral T D) := by sorry

end StatLean.ConcentrationInequalities
