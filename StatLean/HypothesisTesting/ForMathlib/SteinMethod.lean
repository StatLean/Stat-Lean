import StatLean.HypothesisTesting.ForMathlib.EsseenSmoothing
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF

/-!
# Stein's method for exchangeable pairs on a finite space

Stein's method replaces the characteristic function by a differential characterisation of the
standard normal law: a real random variable `Z` is `N(0,1)` if and only if
`𝔼[f'(Z) − Z f(Z)] = 0` for every bounded smooth `f`. Given a test function `h`, the **Stein
equation**
$$ f'(w) - w\,f(w) \;=\; h(w) - \mathbb E\,h(Z) $$
has the explicit solution
$$ f_h(w) \;=\; e^{w^2/2}\int_{-\infty}^{w} \bigl(h(x) - \mathbb E\,h(Z)\bigr)\,e^{-x^2/2}\,dx ,$$
so that bounding `|𝔼 h(W) − 𝔼 h(Z)|` for *some* random variable `W` becomes the problem of
bounding `𝔼[f_h'(W) − W f_h(W)]`, which needs no independence at all — only a way of
integrating `W f(W)` by parts. The **exchangeable-pair** device supplies that: if `(W, W')` is
an exchangeable pair with the linearity condition `𝔼[W' − W \mid W] = -\lambda W`, then for
every antisymmetric `F` one has `𝔼 F(W, W') = 0`, and choosing
`F(w, w') = (w' - w)\,(f(w') + f(w))` gives the exact identity
$$ 2\lambda\,\mathbb E\,[W f(W)] \;=\; \mathbb E\bigl[(W' - W)(f(W') - f(W))\bigr] . $$
A first-order Taylor expansion of `f(W') - f(W)` then produces the classical three-term bound.

## Main results

* `steinSolution` — the explicit solution of the Stein equation for the standard normal law,
  and `hasDerivAt_steinSolution` / `steinSolution_sub_mul` — the fact that it *is* a solution.
* `abs_steinSolution_le`, `abs_deriv_steinSolution_le`, `lipschitzWith_deriv_steinSolution` —
  the classical bounds on the solution and its derivative for a Lipschitz test function `h`.
* `sum_eq_of_exchangeable` — the antisymmetry identity for an exchangeable pair.
* `sum_stein_pair` — the exact integration-by-parts identity
  `2λ|K| ∑_ω W(ω) f(W(ω)) = ∑_ω ∑_k (W'(ω,k) − W(ω))(f(W'(ω,k)) − f(W(ω)))`.
* `abs_avg_sub_gaussianExpect_le` — **the abstract exchangeable-pair theorem**: the three-term
  bound on `|𝔼 h(W) − 𝔼 h(Z)|` in terms of the conditional-variance defect and the third
  absolute moment of the increment.
* `tendsto_of_ramp_squeeze` — the de-smoothing step: a quantity squeezed between the values of
  a *continuous* limit c.d.f. at `t ± ε`, up to `o(1)`, converges to that c.d.f. at `t`.

## Design notes

* *Everything is a finite sum.* The exchangeable pair is carried by a **finite** index type
  `Ω` (the configuration) together with a **finite** auxiliary randomisation `K` (which of the
  possible swaps is performed): `W : Ω → ℝ` and `W' : Ω → K → ℝ`. Conditioning on the
  configuration is then literally averaging over `K`, so no conditional-expectation machinery
  is needed and the "conditional variance" `V ω = |K|⁻¹ ∑ₖ (W' ω k − W ω)²` is a *definition*
  rather than a hypothesis. This is exactly the shape in which the combinatorial CLT arrives
  (`ForMathlib/CombinatorialCLT`): `Ω = Equiv.Perm (Fin N)` and `K` indexes the pairs
  (sampled position, unsampled position).
* *Unnormalised Gaussian kernel.* The solution is written with `e^{-x²/2}` and not with the
  density `φ(x) = (2π)^{-1/2}e^{-x²/2}`; the two differ by the factor `√(2π)` that the
  classical normalisation of `f_h` carries anyway, so the classical constants
  (`‖f_h‖ ≤ ‖h'‖`, `‖f_h'‖ ≤ √(2/π)‖h'‖`, `f_h'` is `2‖h'‖`-Lipschitz) apply verbatim.
* *Provable constants.* Where a constant below differs from the textbook one the deviation is
  documented at the statement. The limit theorems downstream are insensitive to constants.

**Reference.** C. Stein, *Approximate Computation of Expectations*, IMS Lecture Notes 7, 1986,
Chapter III; L.H.Y. Chen, L. Goldstein and Q.-M. Shao, *Normal Approximation by Stein's
Method*, Springer, 2011, Lemma 2.4 (bounds on the solution) and Theorem 4.9 (the
exchangeable-pair bound). See also E.L. Lehmann and J.P. Romano, *Testing Statistical
Hypotheses*, 4th ed., 2022, §12.2 for the application to sampling without replacement.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace StatLean.HypothesisTesting

/-! ### The Stein equation and its solution -/

/-- The expectation of a test function under the standard normal law. -/
noncomputable def stdGaussianExpect (h : ℝ → ℝ) : ℝ := ∫ x, h x ∂(gaussianReal 0 1)

/-- The **solution of the Stein equation** for the standard normal law and the test function
`h`:
$$ f_h(w) = e^{w^2/2}\int_{-\infty}^w \bigl(h(x) - \mathbb E h(Z)\bigr) e^{-x^2/2}\,dx . $$
The unnormalised kernel `e^{-x²/2}` (rather than the density) is deliberate: it absorbs the
`√(2π)` that the classical normalisation of `f_h` carries, so that `f_h' - w f_h = h - 𝔼h(Z)`
on the nose. -/
noncomputable def steinSolution (h : ℝ → ℝ) (w : ℝ) : ℝ :=
  Real.exp (w ^ 2 / 2) * ∫ x in Iic w, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2)

/-- The Gaussian kernel `e^{-x²/2}` is integrable on the line. -/
theorem integrable_exp_neg_sq_half :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2)) := by
  have h := integrable_exp_neg_mul_sq (b := (1 : ℝ) / 2) (by norm_num)
  refine h.congr ?_
  filter_upwards with x
  congr 1
  ring

/-- A bounded measurable function times the Gaussian kernel is integrable. -/
theorem integrable_mul_exp_neg_sq_half {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) :
    Integrable (fun x : ℝ => g x * Real.exp (-x ^ 2 / 2)) := by
  refine (integrable_exp_neg_sq_half.const_mul C).mono'
    (hg.aestronglyMeasurable.mul (by fun_prop)) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le

/-- **The Stein solution is differentiable, with the derivative dictated by the Stein
equation.** Writing `f = e^{w²/2} G` with `G(w) = ∫_{-∞}^w g e^{-x²/2}` and `g = h - 𝔼h(Z)`,
the fundamental theorem of calculus gives `G' (w) = g(w) e^{-w²/2}`, and the product rule
cancels the two exponentials. -/
theorem hasDerivAt_steinSolution {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    HasDerivAt (steinSolution h)
      (w * steinSolution h w + (h w - stdGaussianExpect h)) w := by
  sorry

/-- **The Stein equation.** The derivative of the Stein solution minus `w` times the solution
recovers the centred test function. -/
theorem steinSolution_sub_mul {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    deriv (steinSolution h) w - w * steinSolution h w = h w - stdGaussianExpect h := by
  rw [(hasDerivAt_steinSolution hh hC w).deriv]; ring

/-! ### Bounds on the Stein solution for a Lipschitz test function

For an `L`-Lipschitz `h` the classical bounds are `‖f_h‖ ≤ L`, `‖f_h'‖ ≤ √(2/π)·L ≤ L` and
`f_h'` is `2L`-Lipschitz (Chen–Goldstein–Shao, Lemma 2.4; the first is sharp, as `h = id`
gives `f_h ≡ -1`). They are recorded here in the weakest form the exchangeable-pair theorem
needs, namely with the *provable* constants stated. -/

/-- **Sup-norm bound on the Stein solution.** For an `L`-Lipschitz test function `h`,
`|f_h(w)| ≤ L` for every `w`; the constant is sharp (take `h = id`, for which `f_h ≡ -1`).

STATUS: OPEN. The classical proof integrates the antisymmetric decomposition
`∫_{-∞}^w (h - 𝔼h)φ = ∫_{x<w}∫_{y>w}(h(x) - h(y))φ(x)φ(y)` and evaluates the resulting
one-sided first moments `∫_w^∞ yφ(y)dy = φ(w)`; equivalently, `u(w) = ∫_{-∞}^w (h - 𝔼h)φ`
satisfies `u(±∞) = 0` and `(Lφ ∓ u)' = -φ·(Lw ± (h - 𝔼h))` with a *monotone* second factor,
so `Lφ ∓ u` is unimodal with vanishing limits, hence nonnegative. -/
theorem abs_steinSolution_le {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    |steinSolution h w| ≤ L := by
  sorry

/-- **Sup-norm bound on the derivative of the Stein solution.** For an `L`-Lipschitz test
function, `|f_h'(w)| ≤ 2L`. (The sharp constant is `√(2/π) < 1`; `2` is what the elementary
route below yields and it suffices downstream.)

STATUS: OPEN. -/
theorem abs_deriv_steinSolution_le {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    |deriv (steinSolution h) w| ≤ 2 * L := by
  sorry

/-- **Lipschitz bound on the derivative of the Stein solution**, i.e. the `‖f_h''‖ ≤ 2L` of
the classical statement in the form actually used by the Taylor step.

STATUS: OPEN. -/
theorem lipschitz_deriv_steinSolution {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (x y : ℝ) :
    |deriv (steinSolution h) x - deriv (steinSolution h) y| ≤ 2 * L * |x - y| := by
  sorry

/-! ### A second-order Taylor bound from a Lipschitz derivative -/

/-- **Taylor's theorem with a Lipschitz derivative.** If `f` is differentiable with derivative
`f'` and `f'` is `M`-Lipschitz, then `|f y - f x - (y - x) f' x| ≤ M (y - x)² / 2`. -/
theorem abs_sub_sub_mul_deriv_le {f f' : ℝ → ℝ} (hf : ∀ u, HasDerivAt f (f' u) u) {M : ℝ}
    (hM : 0 ≤ M) (hlip : ∀ u v, |f' u - f' v| ≤ M * |u - v|) (x y : ℝ) :
    |f y - f x - (y - x) * f' x| ≤ M * (y - x) ^ 2 / 2 := by
  sorry

/-! ### Exchangeable pairs on a finite space

The pair is carried by a finite configuration type `Ω` and a finite auxiliary randomisation
`K`: the first coordinate of the pair is `W ω`, the second is `W' ω k`. Averaging over `K`
alone is conditioning on the configuration. -/

section ExchangeablePair

variable {Ω K : Type*} [Fintype Ω] [Fintype K]

/-- The conditional second moment of the increment, given the configuration: the average of
`(W' ω k - W ω)²` over the auxiliary randomisation only. -/
noncomputable def condSqIncrement (W : Ω → ℝ) (W' : Ω → K → ℝ) (ω : Ω) : ℝ :=
  (Fintype.card K : ℝ)⁻¹ * ∑ k, (W' ω k - W ω) ^ 2

/-- **Antisymmetry kills the average.** If the pair `(W, W')` is exchangeable then the total
sum of any *antisymmetric* function of the pair vanishes. -/
theorem sum_eq_zero_of_exchangeable {W : Ω → ℝ} {W' : Ω → K → ℝ}
    (hexch : ∀ F : ℝ → ℝ → ℝ,
      ∑ ω, ∑ k, F (W ω) (W' ω k) = ∑ ω, ∑ k, F (W' ω k) (W ω))
    (F : ℝ → ℝ → ℝ) (hF : ∀ x y, F y x = -F x y) :
    ∑ ω, ∑ k, F (W ω) (W' ω k) = 0 := by
  have h := hexch F
  have h2 : ∑ ω, ∑ k, F (W' ω k) (W ω) = -∑ ω, ∑ k, F (W ω) (W' ω k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => hF (W ω) (W' ω k)
  rw [h2] at h
  linarith

/-- **The exchangeable-pair integration-by-parts identity.** For an exchangeable pair
satisfying the linearity condition `∑ₖ (W' ω k − W ω) = -λ |K| W ω`, and *any* function `f`,
$$ 2\lambda |K| \sum_\omega W(\omega) f(W(\omega))
   \;=\; \sum_\omega \sum_k \bigl(W'(\omega,k) - W(\omega)\bigr)
          \bigl(f(W'(\omega,k)) - f(W(\omega))\bigr). $$
This is the exact substitute for integration by parts against the Gaussian density; no
smoothness of `f` is used. -/
theorem sum_stein_pair {W : Ω → ℝ} {W' : Ω → K → ℝ} {lam : ℝ}
    (hexch : ∀ F : ℝ → ℝ → ℝ,
      ∑ ω, ∑ k, F (W ω) (W' ω k) = ∑ ω, ∑ k, F (W' ω k) (W ω))
    (hlin : ∀ ω, ∑ k, (W' ω k - W ω) = -lam * (Fintype.card K : ℝ) * W ω) (f : ℝ → ℝ) :
    2 * lam * (Fintype.card K : ℝ) * ∑ ω, W ω * f (W ω)
      = ∑ ω, ∑ k, (W' ω k - W ω) * (f (W' ω k) - f (W ω)) := by
  sorry

/-- **The abstract exchangeable-pair bound.** Let `(W, W')` be an exchangeable pair on the
finite space `Ω × K` with `𝔼[W' − W ∣ Ω] = -λ W`, and let `f` solve the Stein equation for the
test function `h`, with `|f'| ≤ B₁` and `f'` `B₂`-Lipschitz. Then
$$ \bigl|\mathbb E h(W) - \mathbb E h(Z)\bigr|
   \;\le\; B_1\,\mathbb E\Bigl|1 - \tfrac1{2\lambda}\,\mathbb E[(W'-W)^2 \mid \Omega]\Bigr|
     \;+\; \frac{B_2}{4\lambda}\,\mathbb E\,|W' - W|^3 . $$
The first term is the *variance-regression defect* and the second is the *third-moment*
term; both are pure finite sums here. -/
theorem abs_avg_sub_le [Nonempty Ω] [Nonempty K] {W : Ω → ℝ} {W' : Ω → K → ℝ} {lam : ℝ}
    (hlam : 0 < lam)
    (hexch : ∀ F : ℝ → ℝ → ℝ,
      ∑ ω, ∑ k, F (W ω) (W' ω k) = ∑ ω, ∑ k, F (W' ω k) (W ω))
    (hlin : ∀ ω, ∑ k, (W' ω k - W ω) = -lam * (Fintype.card K : ℝ) * W ω)
    {h f f' : ℝ → ℝ} {c B₁ B₂ : ℝ} (hB₂ : 0 ≤ B₂)
    (hf : ∀ u, HasDerivAt f (f' u) u)
    (hstein : ∀ u, f' u - u * f u = h u - c)
    (hfb : ∀ u, |f' u| ≤ B₁)
    (hflip : ∀ u v, |f' u - f' v| ≤ B₂ * |u - v|) :
    |(Fintype.card Ω : ℝ)⁻¹ * ∑ ω, h (W ω) - c|
      ≤ B₁ * ((Fintype.card Ω : ℝ)⁻¹ *
            ∑ ω, |1 - (2 * lam)⁻¹ * condSqIncrement W W' ω|)
        + (4 * lam)⁻¹ * B₂ * ((Fintype.card Ω : ℝ)⁻¹ * (Fintype.card K : ℝ)⁻¹ *
            ∑ ω, ∑ k, |W' ω k - W ω| ^ 3) := by
  sorry

end ExchangeablePair

/-! ### De-smoothing: from Lipschitz test functions to the c.d.f.

The output of Stein's method is a bound on `|𝔼 h(W) − 𝔼 h(Z)|` for *Lipschitz* `h`; the
statement wanted downstream is convergence of `P(W ≤ t)` to `Φ(t)`. Since `Φ` is continuous,
sandwiching the indicator of `Iic t` between the ramps of `ForMathlib/EsseenSmoothing` at
scale `ε` and letting `ε → 0` suffices — no rate is lost that matters. -/

/-- The ramp of width `δ` is `δ⁻¹`-Lipschitz. -/
theorem abs_ramp_sub_ramp_le {u δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    |ramp u δ x - ramp u δ y| ≤ δ⁻¹ * |x - y| := by
  sorry

/-- **The squeeze against a continuous limit c.d.f.** If, for every `ε > 0`, the quantity
`G i` eventually lies between `Φ(t - ε) - ε` and `Φ(t + ε) + ε`, and `Φ` is continuous at `t`,
then `G i → Φ t`. This is the only form of de-smoothing the combinatorial CLT needs, the limit
c.d.f. being continuous everywhere. -/
theorem tendsto_of_squeeze_continuousAt {ι : Type*} {l : Filter ι} {G : ι → ℝ} {Φ : ℝ → ℝ}
    {t : ℝ} (hΦ : ContinuousAt Φ t)
    (hb : ∀ ε > (0 : ℝ), ∀ᶠ i in l, Φ (t - ε) - ε ≤ G i ∧ G i ≤ Φ (t + ε) + ε) :
    Tendsto G l (𝓝 (Φ t)) := by
  sorry

end StatLean.HypothesisTesting
