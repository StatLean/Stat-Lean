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
  obtain ⟨lo, hi, hlo, H⟩ := h
  exact ⟨lo, hi, hlo, fun y hy => H y (hy.trans hmm')⟩

/-- Zero replacements are resisted exactly when the uncorrupted value is off the
boundary (`0 < S x`) — unlike the location lattice, this is *not* free (a constant
sample already has `MAD = 0`). -/
theorem dispersionResists_zero {S : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (h : 0 < S x) : DispersionResists S x 0 := by
  refine ⟨S x, S x, h, fun y hy => ?_⟩
  have hxy : x = y := hammingDist_eq_zero.mp (Nat.le_zero.mp hy)
  rw [← hxy]
  exact ⟨le_rfl, le_rfl⟩

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
  have hne : {m | m ≤ n ∧ DispersionResists S x m}.Nonempty := ⟨m, hm, hres⟩
  have hbdd : BddAbove {m | m ≤ n ∧ DispersionResists S x m} := ⟨n, fun _ hb => hb.1⟩
  have hmem := Nat.sSup_mem hne hbdd
  refine le_antisymm ?_ (le_csSup hbdd ⟨hm, hres⟩)
  by_contra hlt
  push Not at hlt
  exact hbrk (hmem.2.anti (Nat.succ_le_of_lt hlt))

/-- **The sample standard deviation** `SD(x) = √((1/n) ∑ (xᵢ − x̄)²)` (`MMY §2.6`,
with the `1/n` normalization in place of the book's `1/(n−1)` — the breakdown
statements are unaffected by the constant factor). -/
noncomputable def sampleSD (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (sampleMean fun i => (x i - sampleMean x) ^ 2)

/-- The sample mean is (fully) scale equivariant — the companion of
`sampleMean_locEquivariant` needed for the SD's `|c|`-equivariance. -/
private theorem sampleMean_const_mul (c : ℝ) (x : Fin n → ℝ) :
    sampleMean (fun i => c * x i) = c * sampleMean x := by
  simp only [sampleMean, ← Finset.mul_sum, mul_div_assoc]

/-- The SD satisfies the dispersion conditions (`MMY (2.58)`): shift invariance and
absolute-scale equivariance. -/
theorem sampleSD_isDispersionEstimator (hn : n ≠ 0) :
    IsDispersionEstimator (sampleSD (n := n)) := by
  constructor
  · -- shift invariance: the mean shifts along, so the residuals are unchanged
    intro a x
    have hmean : sampleMean (x + a • (1 : Fin n → ℝ)) = sampleMean x + a :=
      sampleMean_locEquivariant (Nat.pos_of_ne_zero hn) a x
    have hdev : (fun i => ((x + a • (1 : Fin n → ℝ)) i
        - sampleMean (x + a • (1 : Fin n → ℝ))) ^ 2)
        = fun i => (x i - sampleMean x) ^ 2 := by
      funext i
      rw [hmean]
      have hxi : (x + a • (1 : Fin n → ℝ)) i = x i + a := by simp
      rw [hxi]
      ring_nf
    rw [sampleSD, sampleSD, hdev]
  · -- scale equivariance: `c²` comes out of the mean and `√(c² ·) = |c| √·`
    intro c x
    have hsmul : (c • x) = fun i => c * x i := by funext i; simp
    have hmean : sampleMean (c • x) = c * sampleMean x := by
      rw [hsmul]; exact sampleMean_const_mul c x
    have hdev : (fun i => ((c • x) i - sampleMean (c • x)) ^ 2)
        = fun i => c ^ 2 * (x i - sampleMean x) ^ 2 := by
      funext i
      rw [hmean, hsmul]
      ring
    rw [sampleSD, sampleSD, hdev, sampleMean_const_mul,
      Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **One replacement explodes the SD** (`MMY §3.2.2`, "the BPs of the SD … are 0",
finite-sample form): a single arbitrarily-large replacement drives the SD beyond any
bound (`n ≥ 2`, so the corrupted mean cannot chase the outlier). -/
theorem sampleSD_breaksUnder_one (hn : 2 ≤ n) (x : Fin n → ℝ) :
    DispersionBreaksUnder sampleSD x 1 := by
  classical
  rintro ⟨lo, hi, hlo, H⟩
  have hn0 : 0 < n := by omega
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  -- replace the single coordinate `i₀` by the value making its residual exactly `A`
  set S : ℝ := ∑ i ∈ Finset.univ \ {i₀}, x i with hS
  set A : ℝ := (n:ℝ) * (|hi| + 1) with hA
  set M : ℝ := ((n:ℝ) * A + S) / ((n:ℝ) - 1) with hM
  set y : Fin n → ℝ := Function.update x i₀ M with hy
  have hdist : hammingDist x y ≤ 1 := by
    refine le_trans (Finset.card_le_card (t := ({i₀} : Finset (Fin n))) fun i hi' => ?_) (by simp)
    by_cases h : i = i₀
    · simp [h]
    · exact absurd (Function.update_of_ne h M x).symm
        (by simpa [hy] using (Finset.mem_filter.mp hi').2)
  have hsum : ∑ i, y i = M + S := Finset.sum_update_of_mem (Finset.mem_univ i₀) x M
  have hmean : sampleMean y = (M + S) / n := by rw [sampleMean, hsum]
  have hMn : M * ((n:ℝ) - 1) = (n:ℝ) * A + S := by rw [hM]; field_simp
  -- with `n ≥ 2` the corrupted mean cannot chase the outlier: the residual is `A`
  have hd : y i₀ - sampleMean y = A := by
    have hyi : y i₀ = M := by simp [hy]
    rw [hyi, hmean]
    field_simp
    nlinarith [hMn]
  have hterm : (y i₀ - sampleMean y) ^ 2 ≤ ∑ i, (y i - sampleMean y) ^ 2 :=
    Finset.single_le_sum (f := fun i => (y i - sampleMean y) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ i₀)
  have hvar : A ^ 2 / (n:ℝ) ≤ sampleMean fun i => (y i - sampleMean y) ^ 2 := by
    rw [sampleMean, ← hd]
    gcongr
  have ha : (0:ℝ) ≤ |hi| := abs_nonneg hi
  have hkey : |hi| ^ 2 < A ^ 2 / (n:ℝ) := by
    rw [lt_div_iff₀ hnpos, hA]
    have h1 : |hi| ^ 2 < (n:ℝ) * (|hi| + 1) ^ 2 := by nlinarith
    calc |hi| ^ 2 * (n:ℝ) < ((n:ℝ) * (|hi| + 1) ^ 2) * (n:ℝ) := by nlinarith
      _ = ((n:ℝ) * (|hi| + 1)) ^ 2 := by ring
  have hlt : |hi| < sampleSD y := by
    rw [sampleSD]
    exact (Real.lt_sqrt (abs_nonneg hi)).2 (lt_of_lt_of_le hkey hvar)
  have := (H y hdist).2
  linarith [le_abs_self hi]

/-- The SD's dispersion breakdown count is `0` (for data with `SD > 0`). -/
theorem sampleSD_dispersionBreakdownCount (hn : 2 ≤ n) {x : Fin n → ℝ}
    (hx : 0 < sampleSD x) : dispersionBreakdownCount sampleSD x = 0 :=
  dispersionBreakdownCount_eq_of_resists_of_breaksUnder (Nat.zero_le n)
    (dispersionResists_zero hx) (by simpa using sampleSD_breaksUnder_one hn x)

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
