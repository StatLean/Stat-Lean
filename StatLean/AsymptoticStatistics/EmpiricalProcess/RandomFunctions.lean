import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
import Mathlib.Probability.IdentDistrib

/-!
# Random functions in a Donsker class

Let $\mathcal{F}$ be a $P$-Donsker class of measurable functions, and let
$\hat f_n$ be a sequence of random functions taking values in $\mathcal{F}$
such that the $L^2(P)$ distance to a fixed $f_0 \in L^2(P)$ vanishes in
probability, i.e. $\int (\hat f_n - f_0)^2 \, dP \xrightarrow{P} 0$. Then the
empirical process applied to the increment converges to zero in probability,
$\mathbb{G}_n(\hat f_n - f_0) \xrightarrow{P} 0$, and consequently
$\mathbb{G}_n \hat f_n \rightsquigarrow \mathbb{G}_P f_0$. Here
$\mathbb{G}_n f = n^{-1/2} \sum_{i=1}^n (f(X_i) - Pf)$ is the empirical process
indexed by $\mathcal{F}$ and $\mathbb{G}_P$ is the $P$-Brownian-bridge limit.

The headline declaration `donsker_random_function_consistency` proves the
in-probability part: for every $\eta > 0$,
$\mu\{\xi : |\mathbb{G}_n(\hat f_n(\xi)) - \mathbb{G}_n(f_0)| > \eta\} \to 0$.

*Alignment with the Lean statement / added hypotheses.* The Lean formalization
makes explicit several items that vdV leaves implicit. Without loss of
generality we take $f_0 \in \mathcal{F}$ (vdV's first reduction). The
$L^2$-consistency hypothesis is supplied in **expectation form**,
$\int \big(\int (\hat f_n(\xi) - f_0)^2 \, dP\big) \, d\mu(\xi) \to 0$, which is
equivalent to the book's convergence-in-probability statement given the square
envelope of $\mathcal{F}$ and is more compact in Lean than the iterated
"$\xrightarrow{P}$" form. Joint measurability of $\hat f_n$ and of $f_0$, and the
i.i.d. structure of the sample $(X_i)$ (independence, identical distribution,
law $= P$), are stated as explicit adapters needed to apply equicontinuity at
the random pair $(\hat f_n, f_0)$.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series
in Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 19 (Empirical Processes), §19.4 (Random Functions), Lemma 19.24.

**Proof formalization notes.** vdV's proof defines the map
$g : \ell^\infty(\mathcal{F}) \times \mathcal{F} \to \mathbb{R}$,
$g(z, f) = z(f) - z(f_0)$, and applies the continuous-mapping theorem together
with Lemma 18.15 (almost all sample paths of the limiting Gaussian process are
uniformly continuous on $(\mathcal{F}, \|\cdot\|_{P,2})$). The proof here
routes directly through the random-pair-in-probability form of
`IsAsymptoticallyEquicontinuous` (from `Donsker.lean`), with no
$\ell^\infty(\mathcal{F})$-topology infrastructure. That predicate is in
consumer form: for any i.i.d. sample and any pair of measurable random
functions in $\mathcal{F}$ whose squared $L^2(P)$-distance has expectation
tending to $0$, the empirical process applied to the difference tends to $0$ in
$\mu$-probability. We instantiate it at the pair $(\hat f_n, \text{const } f_0)$;
the constant random function $(n, \xi) \mapsto f_0$ has uncurry
$(\xi, x) \mapsto f_0(x) = f_0 \circ \mathrm{snd}$, which is jointly measurable
exactly when $f_0$ is.

**Bibliographic comments.** This is a folklore synthesis with no single seminal
origin: it is a routine consequence of weak convergence of the empirical
process over a Donsker class combined with asymptotic equicontinuity, the
framework systematized in A. W. van der Vaart and J. A. Wellner, *Weak
Convergence and Empirical Processes: With Applications to Statistics*, Springer
Series in Statistics, Springer, 1996. vdV (1998) presents it as Lemma 19.24 in
§19.4 and uses it as the key device for controlling remainder terms in the
asymptotic analysis of $Z$- and $M$-estimators (cf. its application in vdV
(5.22)). No attribution to a specific research paper is warranted.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ENNReal
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 19.24 (Random functions in a Donsker class)**.

Suppose `F` is a `P`-Donsker class of measurable functions and `f_hat n`
is a sequence of jointly measurable random functions taking values in
`F` such that `∫ (f_hat n − f₀)² dP →_P 0` for some `f₀ ∈ F` with
`f₀ ∈ L²(P)`. Then for every `η > 0`,
`μ{ξ | η < |G_n(f_hat n ξ) − G_n(f₀)|} → 0`,
i.e. `G_n(f_hat n) − G_n(f₀) →_P 0`.

vdV §19.4 Lemma 19.24.

Hypotheses:
* `h_donsker` — vdV §19.4 Theorem 19.24: `F` is `P`-Donsker.
* `_hf₀_in_F` — vdV §19.4: WLOG `f₀ ∈ F`.
* `_hf₀` — vdV §19.4: `f₀ ∈ L²(P)`.
* `h_range` — vdV §19.4: random functions take values in `F`.
* `h_l2_consistent` — vdV §19.4: the `→_P 0` of the L²(P)-distance
  hypothesis, expressed in expectation form (which is equivalent given
  the L² envelope of `F` and is more compact in Lean than the iterated
  `→_P` form).
* `hf₀_meas`, `h_fhat_meas` — joint measurability adapters required to
  apply equicontinuity at the random pair `(f_hat n, const f₀)`.
* `hX_*` — iid hypotheses on the sample (empirical-process setup).

**Proof.** The `IsAsymptoticallyEquicontinuous` predicate
(`Donsker.lean`) is in consumer form: it says that for any iid sample
and any pair of measurable random functions in `F` whose L²(P)-distance
squared has expectation tending to 0, the empirical process applied to
the difference tends to 0 in `μ`-probability. We apply this directly to
the pair `(f_hat n, fun _ => f₀)`. -/
theorem donsker_random_function_consistency
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_donsker : IsPDonsker F P)
    (f₀ : Ω → ℝ) (_hf₀ : MemLp f₀ 2 P)
    (_hf₀_in_F : f₀ ∈ F)
    (hf₀_meas : Measurable f₀)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (f_hat : ℕ → Ξ → (Ω → ℝ))
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (f_hat n)))
    (h_range : ∀ n ω, f_hat n ω ∈ F)
    -- Expectation of squared L²-distance. The
    -- `IsAsymptoticallyEquicontinuous` predicate consumes this; we pass it
    -- through unchanged with `ghat = const f₀`.
    (h_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (f_hat n ξ x - f₀ x) ^ 2 ∂P) μ)
    (h_l2_consistent :
      Tendsto (fun n =>
        ∫ ω, (∫ x, (f_hat n ω x - f₀ x) ^ 2 ∂P) ∂μ) atTop (𝓝 0)) :
    ∀ η : ℝ, 0 < η → Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f_hat n ξ) -
                  empiricalProcess P n (fun i : Fin n => X i.val ξ) f₀|}) atTop (𝓝 0) := by
  intro η hη
  -- Apply the equicontinuity predicate to the pair (f_hat, const f₀).
  -- The constant random function `(n, ξ) ↦ f₀` has uncurry `(ξ, x) ↦ f₀ x = f₀ ∘ Prod.snd`,
  -- jointly measurable iff `f₀` is.
  set ghat : ℕ → Ξ → (Ω → ℝ) := fun (_ : ℕ) (_ : Ξ) => f₀
  have hghat_meas : ∀ n : ℕ, Measurable (Function.uncurry (ghat n)) := by
    intro _
    exact hf₀_meas.comp measurable_snd
  have hghat_range : ∀ (n : ℕ) (ξ : Ξ), ghat n ξ ∈ F := fun _ _ => _hf₀_in_F
  exact h_donsker.asymptoticallyEquicontinuous μ X hX_meas hX_iindep hX_idem hX_law
    f_hat ghat h_fhat_meas hghat_meas h_range hghat_range
    h_l2_int h_l2_consistent η hη

end AsymptoticStatistics.EmpiricalProcess
