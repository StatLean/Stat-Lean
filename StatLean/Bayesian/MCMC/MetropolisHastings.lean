import StatLean.Bayesian.MCMC.Defs

/-!
# Metropolis–Hastings correctness: reversibility and stationarity

Correctness of the Metropolis–Hastings kernel on a countable state space (Robert Theorem 6.3.1):

* the kernel is **Markov** (2F.2): acceptance mass plus rejection mass is one;
* **detailed balance** (2F.3): `π{x}·K(x, {y}) = π{y}·K(y, {x})` — in kernel form,
  `Kernel.IsReversible (mhKernel π q) π`;
* **stationarity** (2F.1/2F.4): reversibility implies invariance, `π·K = π`, loaded from the
  pinned `Kernel.IsReversible.invariant`.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §6.3.2, Theorem 6.3.1 and the detailed-balance identity
eq. (6.3.1), p. 304.

**Proof formalization notes.** The pointwise engine is the symmetry lemma `mhAccept_mul_symm`
(`π{x}·q(x,{y})·α(x,y) = π{y}·q(y,{x})·α(y,x)`), an `ℝ≥0∞` computation via the helper
`c · min 1 (d/c) = min c d` (case-split `c ∈ {0, ∞}`; masses are finite for finite `π` and Markov
`q`). Reversibility integrates it over `A × B` with `lintegral_countable'`-style indicator sums
(`ENNReal.tsum_comm` for the swap); the rejection part is diagonal-supported and symmetric by
construction. Stationarity is the pinned `IsReversible.invariant` — the textbook-named wrapper
`invariant_of_isReversible` (2F.1) records Robert's phrasing; we load, not reprove.

**Bibliographic comments.** Metropolis et al. (1953) introduced the symmetric-proposal algorithm
for statistical mechanics; Hastings (1970) the general ratio used here. That detailed balance
(reversibility) suffices for stationarity is the classical reversible-chain argument (A. N.
Kolmogorov's reversibility criterion, 1936); the MCMC-correctness reading is Robert Theorem 6.3.1,
with the convergence theory (irreducibility, Harris recurrence, ergodic theorems) deferred to
Meyn–Tweedie-style analysis outside this batch's scope.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {S : Type*} [mS : MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- `ℝ≥0∞` helper: `c · min 1 (d/c) = min c d` for finite `c` (both sides `0` at `c = 0`). -/
theorem mul_min_one_div {c d : ℝ≥0∞}
    -- LEAN-ONLY: finiteness of the reference mass (holds for finite `π`, Markov `q`)
    (hc : c ≠ ∞) :
    c * min 1 (d / c) = min c d := sorry

/-- **The MH kernel is Markov** (2F.2): acceptance mass plus rejection mass is one. -/
theorem isMarkovKernel_mhKernel (π : Measure S) (q : Kernel S S) [IsMarkovKernel q] :
    IsMarkovKernel (mhKernel π q) := sorry

/-- Pointwise detailed balance of the acceptance flow:
`π{x}·q(x,{y})·α(x,y) = π{y}·q(y,{x})·α(y,x)`. -/
theorem mhAccept_mul_symm (π : Measure S) [IsFiniteMeasure π] (q : Kernel S S)
    [IsMarkovKernel q] (x y : S) :
    π {x} * (q x {y} * mhAccept π q x y) = π {y} * (q y {x} * mhAccept π q y x) := sorry

/-- **Metropolis–Hastings detailed balance** (2F.3; Robert Theorem 6.3.1 / eq. (6.3.1)): the MH
kernel is reversible with respect to its target. -/
theorem isReversible_mhKernel (π : Measure S) [IsFiniteMeasure π] (q : Kernel S S)
    [IsMarkovKernel q] :
    Kernel.IsReversible (mhKernel π q) π := sorry

/-- **Detailed balance implies stationarity** (2F.1; Robert Theorem 6.3.1) — textbook-named
wrapper of the pinned `Kernel.IsReversible.invariant`. -/
theorem invariant_of_isReversible {κ : Kernel S S} [IsMarkovKernel κ] {π : Measure S}
    -- USER-INPUT: detailed balance of the chain; Robert eq. (6.3.1)
    (h : Kernel.IsReversible κ π) :
    Kernel.Invariant κ π :=
  h.invariant

/-- **Metropolis–Hastings stationarity** (2F.4; Robert Theorem 6.3.1): the target is invariant
for the MH kernel. -/
theorem invariant_mhKernel (π : Measure S) [IsFiniteMeasure π] (q : Kernel S S)
    [IsMarkovKernel q] :
    Kernel.Invariant (mhKernel π q) π := sorry

end StatLean.Bayesian
