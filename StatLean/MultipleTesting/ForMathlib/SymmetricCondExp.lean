import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Symmetric conditional expectation of an exchangeable Bool vector — `ForMathlib`

The **exchangeable / sampling-without-replacement** identity behind the knock-off supermartingale
step (Lu-BDA §19): for i.i.d. fair `Bool` variables `σ : Fin k → Ω → Bool`, the conditional
expectation of the indicator of *one* coordinate `i₀`, given the **count** σ-algebra
`σ(#{i : σ i = true})`, equals `count / k`.

Mathlib has **no** exchangeability / de Finetti / Pólya / hypergeometric conditional-expectation
support, so this is built from scratch. It is the single Mathlib-absent ingredient the knock-off
FDR proof (`count_condExp`, `Knockoff/Step.lean`) consumes — and is independently upstreamable.

Two equivalent proof routes (either is fine):
* **swap-symmetry + summation.** The pushforward law of `σ` is uniform on `Bool^k`; a coordinate
  transposition `(i₀ j)` is a measure-preserving equivalence preserving `σ(count)`, so all the
  conditional indicators `μ[𝟙(σ i = true) | σ(count)]` agree a.e.; their sum is
  `μ[count | σ(count)] = count` (`condExp_finset_sum` + `condExp_of_stronglyMeasurable`), hence each
  equals `count / k`.
* **direct, via `ae_eq_condExp_of_forall_setIntegral_eq`** + the `Nat.choose` absorption
  `a * k.choose a = k * (k-1).choose (a-1)`: per count value `a`,
  `P(σ i₀ = true ∧ count = a) = (k-1).choose (a-1) / 2^k = (a/k) * k.choose a / 2^k
  = (a/k) * P(count = a)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Hamming weight (number of `true` entries) of the `Bool` sample `fun i => σ i ω`. -/
noncomputable def signCount {k : ℕ} (σ : Fin k → Ω → Bool) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun i => σ i ω = true)).card

/-- `signCount σ` is measurable when each coordinate `σ i` is measurable. -/
lemma measurable_signCount {k : ℕ} (σ : Fin k → Ω → Bool)
    (hσ : ∀ i, Measurable (σ i)) : Measurable (signCount σ) := by
  sorry

/-- **Exchangeable coordinate conditional expectation** (sampling-without-replacement / Pólya).
For i.i.d. fair `Bool` variables `σ : Fin k → Ω → Bool`, the conditional expectation of the
indicator of coordinate `i₀` given the count σ-algebra `σ(signCount σ)` equals `signCount σ / k`.

The brick the knock-off supermartingale step (`count_condExp`, Lu-BDA §19) consumes. -/
theorem condExp_coord_eq_count_div {k : ℕ} (hk : 0 < k)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Fin k → Ω → Bool)
    (hσ : ∀ i, Measurable (σ i)) (hindep : iIndepFun σ μ)
    (hfair : ∀ i, μ {ω | σ i ω = true} = 1 / 2) (i₀ : Fin k) :
    μ[(fun ω => if σ i₀ ω then (1 : ℝ) else 0) |
        MeasurableSpace.comap (signCount σ) inferInstance]
      =ᵐ[μ] fun ω => (signCount σ ω : ℝ) / (k : ℝ) := by
  sorry

end StatLean.MultipleTesting
