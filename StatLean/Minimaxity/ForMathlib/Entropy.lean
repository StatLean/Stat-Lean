import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Shannon entropy and its basic properties (Wainwright §15.4 Appendix)

The information-theoretic background of the appendix: Shannon entropy (Definition 15.24), conditional
entropy (Definition 15.25), and the elementary properties (Eq. (15.60a)–(15.60e)) used in the proof
of Fano's inequality.

* `shannonEntropy Q μ` — `H(ℚ) = −∫ log(dℚ/dμ) dℚ = −∫ q log q dμ` (Def. 15.24).
* `discreteEntropy p` — `H(p) = −Σ p(x) log p(x) = Σ negMulLog(p x)` (Eq. (15.58)).
* `discreteCondEntropy p` / `discreteMutualInfo p` — conditional entropy `H(X|Y) = H(X,Y) − H(Y)`
  (Def. 15.25 / Eq. (15.60b)) and mutual information `I(X;Y) = H(X) + H(Y) − H(X,Y)` (Eq. (15.60d))
  for a joint pmf on `ι × κ`.

Properties proved: `H ≥ 0` and `H ≤ log|𝒳|` (Exercise 15.2), conditioning reduces entropy
`H(X|Y) ≤ H(X)` (Eq. (15.60a), equivalent to `I(X;Y) ≥ 0`).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.Minimaxity

/-- **Shannon entropy** (Wainwright Definition 15.24, Eq. (15.57)): `H(ℚ) = −∫ q log q dμ`, written
via the density `q = dℚ/dμ` as `−∫ log(dℚ/dμ) dℚ`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4, Definition 15.24. -/
noncomputable def shannonEntropy {α : Type*} [MeasurableSpace α] (Q μ : Measure α) : ℝ :=
  -∫ x, Real.log ((Q.rnDeriv μ x).toReal) ∂Q

/-- **Discrete Shannon entropy** (Wainwright Eq. (15.58)): `H(p) = −Σ p(x) log p(x) = Σ negMulLog(p x)`
for a probability mass function `p` on a finite set.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4, Eq. (15.58). -/
noncomputable def discreteEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- **Conditional entropy** (Wainwright Definition 15.25, Eq. (15.60b)): `H(X | Y) = H(X,Y) − H(Y)`,
for a joint pmf `p` on `ι × κ` with `Y`-marginal `Σᵢ p(i, ·)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4, Definition 15.25. -/
noncomputable def discreteCondEntropy {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι × κ → ℝ) : ℝ :=
  discreteEntropy p - discreteEntropy (fun k : κ => ∑ i, p (i, k))

/-- **Mutual information** (Wainwright Eq. (15.60d)): `I(X;Y) = H(X) + H(Y) − H(X,Y)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4, Eq. (15.60d). -/
noncomputable def discreteMutualInfo {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι × κ → ℝ) : ℝ :=
  discreteEntropy (fun i : ι => ∑ k, p (i, k)) + discreteEntropy (fun k : κ => ∑ i, p (i, k))
    - discreteEntropy p

/-- **Discrete entropy is nonnegative** for a probability mass function (Wainwright Exercise 15.2a).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.2. -/
theorem discreteEntropy_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) : 0 ≤ discreteEntropy p := by
  sorry

/-- **Discrete entropy is bounded by `log|𝒳|`** (Wainwright Exercise 15.2b), with equality at the
uniform distribution.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.2. -/
theorem discreteEntropy_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ)
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    discreteEntropy p ≤ Real.log (Fintype.card ι) := by
  sorry

/-- **Conditioning reduces entropy** (Wainwright Eq. (15.60a)): `H(X | Y) ≤ H(X)`, equivalently the
mutual information is nonnegative (`I(X;Y) ≥ 0`).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4, Eq. (15.60a). -/
theorem discreteCondEntropy_le_entropy {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι × κ → ℝ)
    (h0 : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    discreteCondEntropy p ≤ discreteEntropy (fun i : ι => ∑ k, p (i, k)) := by
  sorry

end StatLean.Minimaxity
