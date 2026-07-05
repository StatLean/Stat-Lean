import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic

/-!
# The Rademacher law and the canonical sign vector

A *Rademacher (symmetric Bernoulli) random variable* $\varepsilon$ takes the
values $\pm 1$ with probability $\tfrac12$ each:
$$ \mathbb{P}(\varepsilon = 1) = \mathbb{P}(\varepsilon = -1) = \tfrac12. $$
This file defines its law `radLaw` $= \tfrac12\delta_{1} + \tfrac12\delta_{-1}$
on $\mathbb{R}$ and the canonical vector of $N$ independent Rademacher signs
`signVec N` $= \mathrm{radLaw}^{\otimes N}$ on $\mathrm{Fin}\,N \to \mathbb{R}$,
together with their integral / a.e. / pushforward API. Throughout the
symmetrization chapter, auxiliary sign randomness lives on this explicit
product space (as the second coordinate of `μ.prod (signVec N)`), never on the
abstract sample space.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.3 (symmetric Bernoulli signs
$\varepsilon_1,\dots,\varepsilon_N$, p. 179); the symmetric Bernoulli
distribution itself is §2.2.

**Proof formalization notes.** `radLaw` is a weighted sum of two Dirac
measures on `ℝ` (not `PMF.bernoulli` on `Bool`): integrals against it compute
*unconditionally* for every `f : ℝ → ℝ` (every `f` is a.e. equal to a two-value
simple function, hence integrable), via `integral_dirac` +
`integral_add_measure`. The property "takes values ±1" is the a.e. statement
`radLaw_ae_pm` / `signVec_ae_pm`. The `2^N` finite-average representation of
`signVec` is deliberately not provided: contraction uses coordinate-convexity
induction and the symmetrization flip uses measure-preserving maps, so only
the pushforward API below is ever consumed. Named-sorry fallback of this work
item: `signVec_map_mul_pm` (the vertex change of variables of Theorem 6.6.1),
via `Measure.pi_map_pi` + `radLaw_map_mul_pm`; all scalar `radLaw` lemmas are
provable directly from `integral_dirac` / `Measure.map_dirac`.

**Bibliographic comments.** Rademacher functions originate with H. Rademacher,
"Einige Sätze über Reihen von allgemeinen Orthogonalfunktionen," *Math. Ann.*
87 (1922), 112–138; their systematic use as random signs in Banach-space
probability is classical (Kahane, *Some Random Series of Functions*, 1968).
The present role as the carrier of symmetrization follows HDP §6.3 and its
end-of-chapter Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The Rademacher law** (HDP §6.3, symmetric Bernoulli §2.2): the uniform
distribution on `{-1, 1}` as the two-Dirac measure `½·δ₁ + ½·δ₋₁` on `ℝ`.
Edge behavior: none — a genuine probability measure; integrals against it
compute unconditionally (`radLaw_integral`). -/
noncomputable def radLaw : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac (1 : ℝ) + (2⁻¹ : ℝ≥0∞) • Measure.dirac (-1 : ℝ)

instance : IsProbabilityMeasure radLaw := ⟨by sorry⟩

/-- Integration against `radLaw` is the two-point average (HDP §6.3). Holds
for *every* `f` — no integrability hypothesis, since every `f` is a.e. equal
to a two-value simple function under `radLaw`. -/
theorem radLaw_integral (f : ℝ → ℝ) : ∫ x, f x ∂radLaw = (f 1 + f (-1)) / 2 := by
  sorry

/-- A Rademacher variable takes only the values `±1` (HDP §6.3), as an a.e.
statement of the law. -/
theorem radLaw_ae_pm : ∀ᵐ x ∂radLaw, x = 1 ∨ x = -1 := by
  sorry

/-- Rademacher signs are mean zero (HDP §6.3). -/
theorem radLaw_integral_id : ∫ x, x ∂radLaw = 0 := by
  sorry

/-- `E|ε| = 1` for a Rademacher sign (HDP §6.3). -/
theorem radLaw_integral_abs : ∫ x, |x| ∂radLaw = 1 := by
  sorry

/-- The Rademacher law is symmetric: `(-ε) =ᵈ ε` (HDP §6.3). -/
theorem radLaw_map_neg : radLaw.map (fun x => -x) = radLaw := by
  sorry

/-- Multiplying a Rademacher sign by a fixed sign `c ∈ {±1}` preserves the law
(HDP §6.3). -/
theorem radLaw_map_mul_pm {c : ℝ}
    -- USER-INPUT: c is a fixed deterministic sign; HDP §6.3
    (hc : c = 1 ∨ c = -1) :
    radLaw.map (fun x => c * x) = radLaw := by
  sorry

/-- **The canonical sign vector** (HDP §6.3): the joint law of `N` independent
Rademacher signs `ε₁, …, ε_N`, realized as the `N`-fold product measure
`radLaw^⊗N` on `Fin N → ℝ`. Edge behavior: `N = 0` gives the Dirac mass at the
empty function (still a probability measure). -/
noncomputable def signVec (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ => radLaw

instance (N : ℕ) : IsProbabilityMeasure (signVec N) := ⟨by sorry⟩

/-- Almost every realization of the sign vector is `±1`-valued in each
coordinate. -/
-- LEAN-ONLY: a.e. ±1-valued; transfers `radLaw_ae_pm` through `Measure.pi`.
theorem signVec_ae_pm (N : ℕ) : ∀ᵐ s ∂signVec N, ∀ i, s i = 1 ∨ s i = -1 := by
  sorry

/-- Each coordinate of the sign vector is a Rademacher variable. -/
-- LEAN-ONLY: coordinate marginal of the product measure; no book content.
theorem measurePreserving_eval_signVec (N : ℕ) (i : Fin N) :
    MeasurePreserving (fun s => s i) (signVec N) radLaw := by
  sorry

/-- Flipping the coordinates of the sign vector by any fixed sign pattern
`c ∈ {±1}^N` preserves the law: `(cᵢεᵢ)ᵢ =ᵈ (εᵢ)ᵢ` (HDP §6.6, Theorem 6.6.1
vertex step). Named-sorry debt candidate of this work item; via
`Measure.pi_map_pi` + `radLaw_map_mul_pm`. -/
theorem signVec_map_mul_pm {N : ℕ} {c : Fin N → ℝ}
    -- USER-INPUT: c is a fixed deterministic sign pattern; HDP §6.6 Thm 6.6.1
    (hc : ∀ i, c i = 1 ∨ c i = -1) :
    (signVec N).map (fun s i => c i * s i) = signVec N := by
  sorry

/-- The coordinates of the canonical sign vector are independent
(HDP §6.3: `ε₁, …, ε_N` independent). -/
-- LEAN-ONLY: coordinates of `Measure.pi` are independent; via `iIndepFun_pi`.
theorem iIndepFun_eval_signVec (N : ℕ) :
    ProbabilityTheory.iIndepFun (fun (i : Fin N) (s : Fin N → ℝ) => s i)
      (signVec N) := by
  sorry

end StatLean.ConcentrationInequalities
