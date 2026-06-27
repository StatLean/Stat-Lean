import StatLean.Minimaxity.Defs
import StatLean.Minimaxity.ForMathlib.HellingerDivergence

/-!
# Le Cam's method for functionals (Wainwright §15.2.1)

For estimating a real functional `θ : ℱ → ℝ` of a density, Le Cam's two-point bound reduces to a
geometric object: the **modulus of continuity** of the functional with respect to the Hellinger
distance (Eq. (15.17)),
```
ω(ε; θ, ℱ) = sup { |θ(f) − θ(g)| : H²(f ‖ g) ≤ ε² }.
```
Corollary 15.6 then gives, for the `n`-sample model,
```
inf_θ̂ sup_f 𝔼[Φ(θ̂ − θ(f))] ≥ ¼ Φ( ½ ω(1/(2√n); θ, ℱ) )       (Eq. (15.18)).
```

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {ι 𝓧 : Type*} [mι : MeasurableSpace ι] [m𝓧 : MeasurableSpace 𝓧]

/-- **Hellinger modulus of continuity** (Wainwright Eq. (15.17)):
`ω(ε; θ, ℱ) = sup { |θ(i) − θ(j)| : H²(P i ‖ P j) ≤ ε² }`, the largest fluctuation of the functional
`θfunc` over a Hellinger ball of radius `ε`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Eq. (15.17). -/
noncomputable def hellingerModulus (θfunc : ι → ℝ) (P : ι → Measure 𝓧) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (i : ι) (j : ι) (_ : sqHellinger (P i) (P j) ≤ ε ^ 2), ENNReal.ofReal |θfunc i - θfunc j|

/-- **Le Cam's bound for functionals** (Wainwright Corollary 15.6, Eq. (15.18)): for the `n`-sample
i.i.d. model `Pn i = (P i)^{⊗n}` and an increasing distortion `Φ`,
`inf_θ̂ sup_i 𝔼[Φ(|θ̂ − θ(i)|)] ≥ ¼ Φ(½ ω(1/(2√n); θ, ℱ))`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Corollary 15.6. -/
theorem minimax_functional_modulus
    (θfunc : ι → ℝ) (P : ι → Measure 𝓧) (n : ℕ) (Pn : Kernel ι (Fin n → 𝓧)) [IsMarkovKernel Pn]
    (Φ : ℝ≥0∞ → ℝ≥0∞)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.2.1, Cor 15.6.
    (hΦ : Monotone Φ)
    -- USER-INPUT: `Pn` is the `n`-fold i.i.d. product of the family `P`; Wainwright §15.2.1.
    (hPn : ∀ i, Pn i = Measure.pi fun _ : Fin n => P i) :
    4⁻¹ * Φ (2⁻¹ * hellingerModulus θfunc P (ENNReal.ofReal (1 / (2 * Real.sqrt n))))
      ≤ minimaxRiskDist Φ θfunc Pn := by
  sorry

end StatLean.Minimaxity
