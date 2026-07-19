import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Pólya's theorem: pointwise convergence of distribution functions is uniform — ForMathlib brick

If nondecreasing functions `Fₙ : ℝ → ℝ` with limits `0` at `−∞` and `1` at `+∞` converge
pointwise to a **continuous** function `F` with the same tail limits, then the convergence is
**uniform** on `ℝ`:
$$ \sup_{x \in \mathbb{R}} |F_n(x) - F(x)| \longrightarrow 0 . $$

This is the bridge from "convergence in distribution" to "the approximation is uniform in the
argument", which every calibration argument (critical values, p-values, bootstrap thresholds)
needs before it may pass from a pointwise limit law to a statement about the level attained.

Mathlib-only; the conclusion is stated with Mathlib's `TendstoUniformly`.

**Reference.** Classical distribution-function theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* Standard proof: fix `ε > 0` and choose a finite grid `x₀ < ⋯ < x_k` with `F x₀ < ε`,
  `F x_k > 1 − ε` and `F xᵢ₊₁ − F xᵢ < ε` (continuity of `F` plus the tail limits make this
  possible — this is the only place continuity is used). On the grid, pointwise convergence
  gives a uniform-in-`i` bound for large `n`; between grid points, monotonicity of `Fₙ` and of
  `F` interpolates it; on the two tails the tail limits of `F` and of each `Fₙ` close the
  argument.
* Monotonicity of the limit `F` is *not* a hypothesis: it is forced by monotonicity of the
  `Fₙ` together with pointwise convergence, and is derived in the proof body.
* The tail limits of the approximants (`hFn_atBot`, `hFn_atTop`) are genuinely needed and not
  cosmetic: `Fₙ = F − n·1_{(−∞,−n)}` is nondecreasing and converges pointwise to a continuous
  distribution function while `sup |Fₙ − F| = n → ∞`. The helper
  `mem_Icc_of_monotone_of_tendsto` is what those hypotheses are used through.

**Bibliographic comments.** The theorem is due to G. Pólya ("Über den zentralen Grenzwertsatz
der Wahrscheinlichkeitsrechnung und das Momentenproblem," *Math. Z.* **8** (1920), 171–181),
where it is used to upgrade the central limit theorem to a uniform approximation statement.
-/

open Filter
open scoped Topology

namespace StatLean.HypothesisTesting

/-- A nondecreasing function with limits `0` at `−∞` and `1` at `+∞` takes values in `[0,1]`.

Helper for Pólya's theorem: this is what pins the approximants in the two tails. -/
theorem mem_Icc_of_monotone_of_tendsto {f : ℝ → ℝ}
    -- USER-INPUT: `f` is a distribution function — nondecreasing; classical
    (hmono : Monotone f)
    -- USER-INPUT: `f` is a distribution function — vanishing at `−∞`; classical
    (h0 : Tendsto f atBot (𝓝 0))
    -- USER-INPUT: `f` is a distribution function — total mass `1` at `+∞`; classical
    (h1 : Tendsto f atTop (𝓝 1))
    (x : ℝ) :
    f x ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- **Pólya's theorem**: pointwise convergence of distribution functions to a *continuous*
distribution function is uniform. -/
theorem tendstoUniformly_of_monotone_of_continuous {Fn : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    -- USER-INPUT: each approximant is a distribution function — nondecreasing; classical
    (hmono : ∀ n, Monotone (Fn n))
    -- USER-INPUT: each approximant vanishes at `−∞`; classical
    (hFn_atBot : ∀ n, Tendsto (Fn n) atBot (𝓝 0))
    -- USER-INPUT: each approximant has total mass `1` at `+∞`; classical
    (hFn_atTop : ∀ n, Tendsto (Fn n) atTop (𝓝 1))
    -- USER-INPUT: the limit is continuous — the hypothesis of the theorem; Pólya (1920)
    (hFcont : Continuous F)
    -- USER-INPUT: the limit vanishes at `−∞`; classical
    (hF_atBot : Tendsto F atBot (𝓝 0))
    -- USER-INPUT: the limit has total mass `1` at `+∞`; classical
    (hF_atTop : Tendsto F atTop (𝓝 1))
    -- USER-INPUT: pointwise convergence of the distribution functions; classical
    (hconv : ∀ x : ℝ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x))) :
    TendstoUniformly Fn F atTop := by
  sorry

end StatLean.HypothesisTesting
