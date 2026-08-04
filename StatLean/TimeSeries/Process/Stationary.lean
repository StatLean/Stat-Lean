import StatLean.TimeSeries.Process.Defs
import Mathlib.Probability.IdentDistrib

/-!
# Strict stationarity — basic theory (FY §2.1.1)

Consequences of `IsStrictlyStationary`: identical one-dimensional marginals, closure
under time shift, the equivalence with the book's consecutive-window formulation
(FY Definition 2.2 as printed), and the implication *strict + L² ⇒ weak* (the unnumbered
relation of FY §2.1.1, p. 30).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.1,
Definitions 2.1–2.2 and the following remark (pp. 29–30). (`FY §2.1.1`.)

**Proof formalization notes.** `strict + L² ⇒ weak` transports the mean and the lag-`k`
covariance along the equality of the pair laws `(X_{t+k}, X_t) ≐ (X_k, X_0)` (an `n = 2`
instance of the definition); the covariance is a functional of the pair law once both
coordinates are square-integrable, which is where the `L²` hypothesis (stated at time
`0`, propagated by identical distribution) enters. The converse fails (FY p. 30) — no
claim is stated. In `isStrictlyStationary_iff_window`, the general-tuple form follows
from consecutive windows by projecting a sufficiently long window along a measurable
coordinate-selection map.

**Bibliographic comments.** The strict/weak dichotomy and the observation that second
moments see only the weak structure are classical (Khinchin 1934; Wold 1938;
Doob, *Stochastic Processes*, 1953, ch. X).
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℤ → Ω → ℝ}

/-- Strictly stationary processes have identically distributed marginals. -/
theorem IsStrictlyStationary.identDistrib (h : IsStrictlyStationary X μ)
    -- LEAN-ONLY: coordinate random variables are measurable; implicit in FY
    (hmeas : ∀ t, Measurable (X t)) (s t : ℤ) :
    IdentDistrib (X s) (X t) μ μ := by
  -- The `n = 1` instance of the definition, pushed forward along evaluation at `0`.
  have key := h 1 (fun _ => s) (t - s)
  have hst : s + (t - s) = t := by ring
  simp only [hst] at key
  have he : Measurable fun f : Fin 1 → ℝ => f 0 := measurable_pi_apply 0
  have hFt : Measurable fun ω (_ : Fin 1) => X t ω := measurable_pi_lambda _ fun _ => hmeas t
  have hFs : Measurable fun ω (_ : Fin 1) => X s ω := measurable_pi_lambda _ fun _ => hmeas s
  have hmap : μ.map (X t) = μ.map (X s) := by
    have := congrArg (fun ν : Measure (Fin 1 → ℝ) => ν.map fun f : Fin 1 → ℝ => f 0) key
    simpa [Measure.map_map he hFt, Measure.map_map he hFs, Function.comp_def] using this
  exact ⟨(hmeas s).aemeasurable, (hmeas t).aemeasurable, hmap.symm⟩

/-- Strict stationarity is preserved by time shifts. -/
theorem IsStrictlyStationary.shift (h : IsStrictlyStationary X μ) (k : ℤ) :
    IsStrictlyStationary (shift X k) μ := by
  intro n t k'
  have key := h n (fun i => t i + k) k'
  -- `shift X k t = X (t + k)` is definitional, so the goal is the `h`-instance at the
  -- shifted tuple `t + k` up to reassociating the two displacements.
  change (μ.map fun ω (i : Fin n) => X (t i + k' + k) ω)
      = μ.map fun ω (i : Fin n) => X (t i + k) ω
  have e : (fun ω (i : Fin n) => X (t i + k' + k) ω)
      = fun ω (i : Fin n) => X (t i + k + k') ω := by
    funext ω i
    congr 1
    ring
  rw [e]
  exact key

/-- Two pairs of random variables with the same joint law on `Fin 2 → ℝ` have the same
product integral (the product is a fixed measurable functional of the pair). This is the
step that turns an `n = 2` instance of strict stationarity into an equality of
covariances. -/
private lemma integral_mul_of_map_pair_eq {Y Z : Fin 2 → Ω → ℝ}
    (hY : ∀ i, Measurable (Y i)) (hZ : ∀ i, Measurable (Z i))
    (hmap : (μ.map fun ω i => Y i ω) = μ.map fun ω i => Z i ω) :
    ∫ ω, Y 0 ω * Y 1 ω ∂μ = ∫ ω, Z 0 ω * Z 1 ω ∂μ := by
  have hg : Measurable fun p : Fin 2 → ℝ => p 0 * p 1 :=
    (measurable_pi_apply 0).mul (measurable_pi_apply 1)
  have hFY : Measurable fun ω (i : Fin 2) => Y i ω := measurable_pi_lambda _ hY
  have hFZ : Measurable fun ω (i : Fin 2) => Z i ω := measurable_pi_lambda _ hZ
  have eY := integral_map (μ := μ) (φ := fun ω (i : Fin 2) => Y i ω)
    (f := fun p : Fin 2 → ℝ => p 0 * p 1) hFY.aemeasurable hg.aestronglyMeasurable
  have eZ := integral_map (μ := μ) (φ := fun ω (i : Fin 2) => Z i ω)
    (f := fun p : Fin 2 → ℝ => p 0 * p 1) hFZ.aemeasurable hg.aestronglyMeasurable
  rw [hmap] at eY
  exact eY.symm.trans eZ

/-- **Strict + L² ⇒ weak** (FY §2.1.1, p. 30): a strictly stationary process with a
square-integrable marginal is (weakly) stationary. -/
theorem IsStrictlyStationary.isStationary [IsProbabilityMeasure μ]
    (h : IsStrictlyStationary X μ)
    -- LEAN-ONLY: coordinate random variables are measurable; implicit in FY
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: finite second moment (at one time; propagates); FY §2.1.1 p. 30
    (hL2 : MemLp (X 0) 2 μ) :
    IsStationary X μ := by
  have hid : ∀ s t : ℤ, IdentDistrib (X s) (X t) μ μ := h.identDistrib hmeas
  have hmem : ∀ t : ℤ, MemLp (X t) 2 μ := fun t => (hid 0 t).memLp_snd hL2
  refine ⟨hmem, fun s t => (hid s t).integral_eq, fun t k => ?_⟩
  -- The pair `(X_{t+k}, X_t)` is the tuple `(k, 0)` shifted by `t`, so it has the same
  -- joint law as `(X_k, X_0)`; the covariance is a functional of that joint law.
  have hprod : ∫ ω, X (t + k) ω * X t ω ∂μ = ∫ ω, X k ω * X 0 ω ∂μ := by
    have hpair := integral_mul_of_map_pair_eq (μ := μ)
      (Y := fun i => X (![k, 0] i + t)) (Z := fun i => X (![k, 0] i))
      (fun _ => hmeas _) (fun _ => hmeas _) (h 2 ![k, 0] t)
    simpa [add_comm k t] using hpair
  rw [covariance_eq_sub (hmem (t + k)) (hmem t), covariance_eq_sub (hmem k) (hmem 0)]
  simp only [Pi.mul_apply]
  rw [hprod, (hid (t + k) k).integral_eq, (hid t 0).integral_eq]

/-- The general-tuple formulation of strict stationarity coincides with FY Definition
2.2's consecutive-window form `(X_1, …, X_n) ≐ (X_{1+k}, …, X_{n+k})`. -/
theorem isStrictlyStationary_iff_window
    -- LEAN-ONLY: coordinate random variables are measurable; implicit in FY
    (hmeas : ∀ t, Measurable (X t)) :
    IsStrictlyStationary X μ ↔
      ∀ (n : ℕ) (k : ℤ),
        (μ.map fun ω (i : Fin n) => X ((i : ℕ) + 1 + k) ω)
          = μ.map fun ω (i : Fin n) => X ((i : ℕ) + 1) ω := by
  sorry

end StatLean.TimeSeries
