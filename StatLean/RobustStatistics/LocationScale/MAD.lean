import StatLean.RobustStatistics.LocationScale.Median
import StatLean.RobustStatistics.Core.Equivariance

/-!
# The median absolute deviation (MAD)

The MAD is the robust dispersion estimator obtained by centering at the median and taking
the median of the absolute deviations (`MMY §2.6`, eq. (2.60)):

$$\operatorname{MAD}(x) = \operatorname{Med}_i\,|x_i - \operatorname{Med}(x)|.$$

Its basic properties — nonnegativity, location invariance, absolute scale equivariance,
vanishing on constant samples — make it the canonical high-breakdown companion dispersion
for M-estimation with previously computed scale (`MMY §2.7.1`).

**Scope (odd `n` for scale equivariance).** With the low-median convention the identity
`Med(cx) = c·Med(x)` for negative `c` needs the middle index to be reversal-invariant,
which holds exactly for odd `n`; the scale-equivariance and dispersion statements are
therefore given for odd `n`. Location invariance holds for every `n`.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.6 (eq.
(2.58), (2.60), (2.63)), §2.7.1.
-/

namespace StatLean.RobustStatistics

variable {n : ℕ}

/-- The **sample MAD** (`MMY §2.6`, eq. (2.60)): the median of the absolute deviations
from the median. Junk value `0` when `n = 0`. -/
noncomputable def sampleMAD (x : Fin n → ℝ) : ℝ :=
  sampleMedian fun i => |x i - sampleMedian x|

/-- The MAD is nonnegative. -/
theorem sampleMAD_nonneg (x : Fin n → ℝ) : 0 ≤ sampleMAD x := by
  sorry

/-- **The MAD is location invariant** (`MMY` eq. (2.58), first condition). -/
theorem sampleMAD_add_const (x : Fin n → ℝ) (a : ℝ) :
    sampleMAD (x + a • (1 : Fin n → ℝ)) = sampleMAD x := by
  sorry

/-- **The MAD is absolutely scale equivariant for odd `n`** (`MMY` eq. (2.58), second
condition): `MAD(cx) = |c|·MAD(x)`. -/
theorem sampleMAD_const_mul {k : ℕ} (hn : n = 2 * k + 1) (c : ℝ) (x : Fin n → ℝ) :
    sampleMAD (fun i => c * x i) = |c| * sampleMAD x := by
  sorry

/-- **The MAD is a dispersion estimator for odd `n`** (`MMY` eq. (2.58)). -/
theorem sampleMAD_isDispersionEstimator {k : ℕ} (hn : n = 2 * k + 1) :
    IsDispersionEstimator (sampleMAD (n := n)) := by
  sorry

/-- The MAD of a constant sample vanishes (`MMY §2.7.1`, the degenerate case handled
there by the convention `μ̂ = Med(x)`). -/
theorem sampleMAD_const (a : ℝ) : sampleMAD (fun _ : Fin n => a) = 0 := by
  sorry

end StatLean.RobustStatistics
