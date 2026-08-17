import StatLean.RobustStatistics.Core.BreakdownPoint
import StatLean.RobustStatistics.LocationScale.MAD
import StatLean.RobustStatistics.LocationScale.Mean

/-!
# Finite-sample breakdown of dispersion estimators — the SD implodes never but explodes
# at once; the MAD resists half

For a dispersion estimator the parameter space is `Θ = (0, ∞)`, so the finite-sample
breakdown notion (`MMY §3.2.5`, Definition (3.25)) must guard *both* boundary pieces:
a corrupted sample breaks the estimator if it can be driven to `∞` (**explosion**) *or*
to `0` (**implosion**). This file gives the dispersion analogue of Round-1's
`Resists`/`breakdownCount` lattice and the two classical verdicts (`MMY §3.2.2`,
Problem 3.3, finite-sample form):

* the sample standard deviation breaks under a **single** replacement (`ε* = 0`);
* the sample MAD (odd `n = 2k+1`, distinct data) resists `k − 1` replacements and
  implodes under `k` — duplicating `k` values at one data point collapses a majority of
  the absolute deviations to `0` — so its breakdown count is exactly `k − 1` and its
  breakdown point tends to `1/2`.

* `DispersionResists`, `DispersionBreaksUnder`, `dispersionBreakdownCount` — the
  implosion-aware lattice (mirroring `Core/BreakdownPoint`).
* `sampleSD` and `sampleSD_breaksUnder_one` / `sampleSD_dispersionBreakdownCount`.
* `sampleMAD_implodes_under` / `sampleMAD_dispersionResists` /
  `sampleMAD_dispersionBreakdownCount`.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera,
*Robust Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.)
§2.6 (the SD and the dispersion conditions (2.58)), §3.2.2 ("the BPs of the SD, the MAD
and the IQR are 0, 1/2 and 1/4", Problem 3.3), §3.2.5 (the replacement FBP (3.24)–
(3.25) and its boundary-aware reading for `Θ = (0, ∞)`); the FBP notion is from
Donoho–Huber (1983).
-/

open MeasureTheory

namespace StatLean.RobustStatistics

variable {n : ℕ}

/-- **Dispersion resistance** (`MMY §3.2.5`, Definition (3.25) read at `Θ = (0, ∞)`):
`m` replacements cannot drive `S` to the boundary — there are `0 < lo ≤ hi` with
`S y ∈ [lo, hi]` for every `y` within Hamming distance `m` of `x`. Note `Resists` of
`Core/BreakdownPoint` guards only `∞`; a dispersion estimator must also stay away from
`0` (implosion). -/
def DispersionResists (S : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (m : ℕ) : Prop :=
  ∃ lo hi : ℝ, 0 < lo ∧
    ∀ y : Fin n → ℝ, hammingDist x y ≤ m → S y ∈ Set.Icc lo hi

/-- `m` replacements break the dispersion estimator: explosion or implosion. -/
def DispersionBreaksUnder (S : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (m : ℕ) : Prop :=
  ¬DispersionResists S x m

/-- Resistance is antitone in the contamination budget. -/
theorem DispersionResists.anti {S : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {m m' : ℕ}
    (hmm' : m ≤ m') (h : DispersionResists S x m') : DispersionResists S x m := by
  sorry

/-- Zero replacements are resisted exactly when the uncorrupted value is off the
boundary (`0 < S x`) — unlike the location lattice, this is *not* free (a constant
sample already has `MAD = 0`). -/
theorem dispersionResists_zero {S : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : 0 < S x) : DispersionResists S x 0 := by
  sorry

/-- **The dispersion breakdown count** `m* = max{m ≤ n : DispersionResists S x m}`
(`MMY (3.25)`, boundary-aware form); junk value `0` when even `m = 0` is not resisted. -/
noncomputable def dispersionBreakdownCount (S : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℕ :=
  sSup {m | m ≤ n ∧ DispersionResists S x m}

/-- The two-sided characterization of the dispersion breakdown count (mirror of
Round-1's `breakdownCount_eq_of_resists_of_breaksUnder`). -/
theorem dispersionBreakdownCount_eq_of_resists_of_breaksUnder
    {S : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} {m : ℕ} (hm : m ≤ n)
    (hres : DispersionResists S x m) (hbrk : DispersionBreaksUnder S x (m + 1)) :
    dispersionBreakdownCount S x = m := by
  sorry

/-- **The sample standard deviation** `SD(x) = √((1/n) ∑ (xᵢ − x̄)²)` (`MMY §2.6`,
with the `1/n` normalization in place of the book's `1/(n−1)` — the breakdown
statements are unaffected by the constant factor). -/
noncomputable def sampleSD (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (sampleMean fun i => (x i - sampleMean x) ^ 2)

/-- The SD satisfies the dispersion conditions (`MMY (2.58)`): shift invariance and
absolute-scale equivariance. -/
theorem sampleSD_isDispersionEstimator (hn : n ≠ 0) :
    IsDispersionEstimator (sampleSD (n := n)) := by
  sorry

/-- **One replacement explodes the SD** (`MMY §3.2.2`, "the BPs of the SD … are 0",
finite-sample form): a single arbitrarily-large replacement drives the SD beyond any
bound (`n ≥ 2`, so the corrupted mean cannot chase the outlier). -/
theorem sampleSD_breaksUnder_one (hn : 2 ≤ n) (x : Fin n → ℝ) :
    DispersionBreaksUnder sampleSD x 1 := by
  sorry

/-- The SD's dispersion breakdown count is `0` (for data with `SD > 0`). -/
theorem sampleSD_dispersionBreakdownCount (hn : 2 ≤ n) {x : Fin n → ℝ}
    (hx : 0 < sampleSD x) : dispersionBreakdownCount sampleSD x = 0 := by
  sorry

/-- **`k` replacements implode the MAD** (`MMY §3.2.2` + Problem 3.3, finite-sample
form, `n = 2k+1`): replacing `k` coordinates by the value of a remaining data point
creates `k + 1` copies of one value; the corrupted median is that value, a majority of
the absolute deviations vanish, and the MAD is `0`. -/
theorem sampleMAD_implodes_under {k : ℕ} (hn : n = 2 * k + 1) (hk : 1 ≤ k)
    {x : Fin n → ℝ} (hinj : Function.Injective x) :
    DispersionBreaksUnder sampleMAD x k := by
  sorry

/-- **The MAD resists `k − 1` replacements** (`MMY §3.2.2` + Problem 3.3, finite-sample
form, `n = 2k+1`, distinct data): with at most `k − 1` replacements, at most `k` of the
`n` values can coincide within half the minimal gap of the original data, so the
corrupted median-of-absolute-deviations stays above `(min gap)/2 > 0`; boundedness above
follows from the Round-1 order-statistic perturbation bricks. -/
theorem sampleMAD_dispersionResists {k : ℕ} (hn : n = 2 * k + 1) (hk : 1 ≤ k)
    {x : Fin n → ℝ} (hinj : Function.Injective x) :
    DispersionResists sampleMAD x (k - 1) := by
  sorry

/-- **The dispersion breakdown count of the MAD is exactly `k − 1`** (`MMY §3.2.2` +
Problem 3.3, finite-sample form): `(k−1)/(2k+1) → 1/2`, the asymptotic MAD breakdown
point. Note the contrast with the median's location breakdown count `k`
(`LocationScale/MedianBreakdown.lean`): the MAD pays one replacement earlier because
implosion — impossible for a location estimator — binds first. -/
theorem sampleMAD_dispersionBreakdownCount {k : ℕ} (hn : n = 2 * k + 1) (hk : 1 ≤ k)
    {x : Fin n → ℝ} (hinj : Function.Injective x) :
    dispersionBreakdownCount sampleMAD x = k - 1 := by
  sorry

end StatLean.RobustStatistics
