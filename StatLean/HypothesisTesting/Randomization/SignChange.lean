import StatLean.HypothesisTesting.Randomization.Asymptotics
import StatLean.HypothesisTesting.ForMathlib.LindebergCLT
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The sign-change randomization test is asymptotically normal

For i.i.d. real observations $X_1, \dots, X_n$ the natural randomization group is the
group of **sign changes**: $\varepsilon = (\varepsilon_1, \dots, \varepsilon_n)$ with
$\varepsilon_i \in \{\pm 1\}$ acting by
$(\varepsilon \cdot x)_i = \varepsilon_i x_i$, a group of order $2^n$. If the common law
is symmetric about $0$ the randomization hypothesis holds, and the resulting test is exact
at every sample size. The point of this file is what happens *asymptotically*, in
particular when symmetry fails.

Assume the statistic is **asymptotically linear**,
$$ T_n = n^{-1/2}\sum_{i=1}^n \psi(X_i) + o_P(1), \qquad
   \tau^2 = \operatorname{Var}[\psi(X_1)] < \infty , $$
with $\psi$ an **odd** function. Then:

* if the common law is symmetric about $0$, the randomization distribution satisfies
  $\hat R_n(t) \xrightarrow{P} \Phi(t/\tau)$;
* if it is not, let $\tilde P$ be its **symmetrization**, the law with c.d.f.
  $\tilde F(t) = \tfrac12\bigl[F(t) + 1 - F(-t)\bigr]$, and assume asymptotic linearity
  under $\tilde P$; then, still under the original law,
  $\hat R_n(t) \xrightarrow{P} \Phi(t/\tau(\tilde P))$ and
  $\hat r_n(1-\alpha) \xrightarrow{P} \tau(\tilde P)\, z_{1-\alpha}$.

The second part is the reason the sign-change test is usable without symmetry: the
randomization distribution still stabilizes, at the symmetrized model's scale.

**Reference.** Classical randomization/permutation testing; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* *The sign-change group.* It is `Fin n → ℤˣ`: the units of `ℤ` are exactly `±1`, so this
  is `{±1}ⁿ` on the nose, a finite abelian group of order `2ⁿ` (`card_signChangeGroup`).
  Its action on `Fin n → ℝ` is Mathlib's componentwise action, obtained by composing
  `Pi.mulAction'` (a product of monoids acting componentwise), `Units.instMulAction`
  (`u • a = (u : M) • a`) and the `ℤ`-module structure of `ℝ`; no new instance is declared
  here, and `signChange_smul_apply` pins the resulting formula
  `(ε • x) i = εᵢ · xᵢ` so that downstream proofs never have to unfold that chain.
* *Symmetrization.* `symmetrize P` is the equal mixture of `P` and its reflection, i.e.
  the law of `X` multiplied by an independent random sign. Its c.d.f. agrees with the
  book's $\tilde F(t) = \tfrac12[F(t) + 1 - F(-t)]$ at every continuity point of $F$; at an
  atom of $P$ located at $-t$ the two differ by half that atom's mass, because
  $1 - F(-t)$ is the *open* upper tail while the reflected measure contributes the closed
  one. The mixture form is the standard object and is what the argument uses (the
  randomization distribution depends on the data only through $|X_1|, \dots, |X_n|$, whose
  law is the same under `P` and `symmetrize P`).
* *Mean-zero is not a hypothesis.* Oddness of `ψ` together with symmetry of the law and
  square-integrability already force $E[\psi(X_1)] = 0$; carrying it as an assumption
  would be laundering a derivable fact through the signature. It is therefore omitted, and
  `τ²` is stated as the **second moment** $\int \psi^2$, which equals the variance exactly
  because the mean vanishes.
* *Nondegeneracy.* `0 < τ` is required so that `Φ(t/τ)` is a c.d.f.; the degenerate case
  `τ = 0` has no limiting distribution of this form.
* *Asymptotic linearity* is stated with the triangular-array convergence in probability of
  `Randomization/Asymptotics`, applied to the remainder
  `T n x − n^{-1/2} ∑ᵢ ψ(xᵢ)`; that is exactly the `o_P(1)` of the display.
* The limit is reached through the bivariate central limit theorem applied to the i.i.d.
  pairs `(εᵢψ(Xᵢ), ε'ᵢψ(Xᵢ))`, which have zero covariance since
  `E[εᵢ]E[ε'ᵢ] = 0`; the Lindeberg-type machinery is the sibling brick
  `StatLean.HypothesisTesting.ForMathlib.LindebergCLT`, imported here.

**Bibliographic comments.** Sign-change (randomization) tests for a symmetric location
model go back to R. A. Fisher (*The Design of Experiments*, Oliver & Boyd, Edinburgh,
1935) and E. J. G. Pitman ("Significance tests which may be applied to samples from any
populations," *J. R. Statist. Soc. Suppl.* **4** (1937), 119–130), with the group-theoretic
exactness in E. L. Lehmann and C. Stein ("On the theory of some non-parametric
hypotheses," *Ann. Math. Statist.* **20** (1949), 28–45). The large-sample analysis is due
to W. Hoeffding ("The large-sample power of tests based on permutations of observations,"
*Ann. Math. Statist.* **23** (1952), 169–192); the behaviour without the group invariance
assumption, i.e. the asymmetric case handled here through symmetrization, is
J. P. Romano ("On the behavior of randomization tests without a group invariance
assumption," *J. Amer. Statist. Assoc.* **85** (1990), 686–692), sharpened by E. Chung and
J. P. Romano ("Exact and asymptotically robust permutation tests," *Ann. Statist.* **41**
(2013), 484–507).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)

/-! ### The sign-change group -/

/-- The sign-change action, written out: `(ε • x) i = εᵢ · xᵢ`. The action itself is
Mathlib's componentwise `Pi` action of `Fin n → ℤˣ` on `Fin n → ℝ`; this lemma is the
interface downstream proofs use. -/
lemma signChange_smul_apply {n : ℕ} (ε : Fin n → ℤˣ) (x : Fin n → ℝ) (i : Fin n) :
    (ε • x) i = ((ε i : ℤ) : ℝ) * x i := by
  change ((ε i : ℤ)) • x i = ((ε i : ℤ) : ℝ) * x i
  exact zsmul_eq_mul _ _

/-- The sign-change group has `2ⁿ` elements. -/
lemma card_signChangeGroup (n : ℕ) : Fintype.card (Fin n → ℤˣ) = 2 ^ n := by
  simp [Fintype.card_fun, Fintype.card_units_int]

/-- **Symmetrization** of a law on the line: the equal mixture of `P` and its reflection,
i.e. the law of the data multiplied by an independent random sign. Its c.d.f. is
`t ↦ ½(F(t) + 1 − F(−t))` at every continuity point of `F` (see the file notes for the
atom convention). -/
noncomputable def symmetrize (P : Measure ℝ) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (P + P.map (fun t => -t))

/-! ### Symmetric case -/

/-- **The sign-change randomization distribution is asymptotically Gaussian (symmetric
case).** For i.i.d. data symmetric about `0` and an asymptotically linear statistic with
odd influence function `ψ` and scale `τ`, the doubly randomized statistic converges jointly
to a product of centred Gaussians with variance `τ²` — i.e. the hypothesis of the general
asymptotic randomization theorem holds with `R = N(0, τ²)`. -/
theorem weakConverges_randPairLaw_signChange (P : Measure ℝ) [IsProbabilityMeasure P]
    (ψ : ℝ → ℝ) (T : ∀ n, (Fin n → ℝ) → ℝ) {τ : ℝ}
    -- USER-INPUT: the common law is symmetric about `0`; the randomization hypothesis
    -- for the sign-change group
    (hsymm : P.map (fun t => -t) = P)
    -- USER-INPUT: the influence function is odd; needed for `ψ(εᵢXᵢ) = εᵢψ(Xᵢ)`
    (hodd : ∀ t, ψ (-t) = -ψ t)
    -- USER-INPUT: the influence function is measurable; user-supplied function
    (hψmeas : Measurable ψ)
    -- USER-INPUT: finite second moment of the influence function
    (hψL2 : MemLp ψ 2 P)
    -- LEAN-ONLY: nondegenerate scale, so that `Φ(·/τ)` is a c.d.f.; the degenerate case
    -- `τ = 0` has no limit law of this form and is excluded rather than formalized
    (hτpos : 0 < τ)
    -- USER-INPUT: `τ²` is the variance of the influence function (equal to its second
    -- moment, since oddness and symmetry force the mean to vanish)
    (hτ : ∫ t, (ψ t) ^ 2 ∂P = τ ^ 2)
    -- USER-INPUT: the statistic is asymptotically linear with influence function `ψ`
    (hlin : TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => P)
      (fun n x => T n x - (Real.sqrt n)⁻¹ * ∑ i, ψ (x i)) 0) :
    WeakConverges
      (fun n => randPairLaw (Fin n → ℤˣ) (T n) (Measure.pi fun _ : Fin n => P))
      ((gaussianReal 0 ⟨τ ^ 2, sq_nonneg τ⟩).prod
        (gaussianReal 0 ⟨τ ^ 2, sq_nonneg τ⟩)) := by
  sorry

/-- **Consequence: the randomization distribution converges to `Φ(·/τ)`.** Under the
hypotheses above, `R̂ₙ(t) →P Φ(t/τ)` for every `t`. -/
theorem randDist_signChange_tendstoInProb (P : Measure ℝ) [IsProbabilityMeasure P]
    (ψ : ℝ → ℝ) (T : ∀ n, (Fin n → ℝ) → ℝ) {τ : ℝ}
    -- USER-INPUT: the common law is symmetric about `0`
    (hsymm : P.map (fun t => -t) = P)
    -- USER-INPUT: the influence function is odd
    (hodd : ∀ t, ψ (-t) = -ψ t)
    -- USER-INPUT: the influence function is measurable
    (hψmeas : Measurable ψ)
    -- USER-INPUT: finite second moment of the influence function
    (hψL2 : MemLp ψ 2 P)
    -- LEAN-ONLY: nondegenerate scale (see above)
    (hτpos : 0 < τ)
    -- USER-INPUT: `τ²` is the variance of the influence function
    (hτ : ∫ t, (ψ t) ^ 2 ∂P = τ ^ 2)
    -- USER-INPUT: the statistic is asymptotically linear with influence function `ψ`
    (hlin : TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => P)
      (fun n x => T n x - (Real.sqrt n)⁻¹ * ∑ i, ψ (x i)) 0)
    (t : ℝ) :
    TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => P)
      (fun n x => randDist (Fin n → ℤˣ) (T n) x t)
      (cdf (gaussianReal 0 1) (t / τ)) := by
  sorry

/-! ### Asymmetric case, via the symmetrized model -/

/-- **The randomization distribution stabilizes even without symmetry.** If the common law
is *not* symmetric about `0`, asymptotic linearity is assumed under the symmetrized law
`symmetrize P`, with odd influence function `ψ` and scale `τ`. Then, under the original
law, `R̂ₙ(t) →P Φ(t/τ)` — the randomization distribution converges to the symmetrized
model's Gaussian, not to the true sampling distribution. -/
theorem randDist_signChange_tendstoInProb_symmetrized (P : Measure ℝ)
    [IsProbabilityMeasure P] (ψ : ℝ → ℝ) (T : ∀ n, (Fin n → ℝ) → ℝ) {τ : ℝ}
    -- USER-INPUT: the influence function is odd
    (hodd : ∀ t, ψ (-t) = -ψ t)
    -- USER-INPUT: the influence function is measurable
    (hψmeas : Measurable ψ)
    -- USER-INPUT: finite second moment under the **symmetrized** law
    (hψL2 : MemLp ψ 2 (symmetrize P))
    -- LEAN-ONLY: nondegenerate scale (see above)
    (hτpos : 0 < τ)
    -- USER-INPUT: `τ²` is the variance of `ψ` under the **symmetrized** law
    (hτ : ∫ t, (ψ t) ^ 2 ∂(symmetrize P) = τ ^ 2)
    -- USER-INPUT: the statistic is asymptotically linear **under the symmetrized law**
    (hlin : TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => symmetrize P)
      (fun n x => T n x - (Real.sqrt n)⁻¹ * ∑ i, ψ (x i)) 0)
    (t : ℝ) :
    TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => P)
      (fun n x => randDist (Fin n → ℤˣ) (T n) x t)
      (cdf (gaussianReal 0 1) (t / τ)) := by
  sorry

/-- **The randomization critical value converges to `τ z_{1−α}`.** Companion of the
previous statement: the data-dependent critical value of the sign-change test converges in
probability to the symmetrized model's Gaussian quantile. -/
theorem randQuantile_signChange_tendstoInProb_symmetrized (P : Measure ℝ)
    [IsProbabilityMeasure P] (ψ : ℝ → ℝ) (T : ∀ n, (Fin n → ℝ) → ℝ) {τ α : ℝ}
    -- USER-INPUT: the influence function is odd
    (hodd : ∀ t, ψ (-t) = -ψ t)
    -- USER-INPUT: the influence function is measurable
    (hψmeas : Measurable ψ)
    -- USER-INPUT: finite second moment under the **symmetrized** law
    (hψL2 : MemLp ψ 2 (symmetrize P))
    -- LEAN-ONLY: nondegenerate scale (see above)
    (hτpos : 0 < τ)
    -- USER-INPUT: `τ²` is the variance of `ψ` under the **symmetrized** law
    (hτ : ∫ t, (ψ t) ^ 2 ∂(symmetrize P) = τ ^ 2)
    -- USER-INPUT: nominal level strictly between `0` and `1`; the calibration range
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: the statistic is asymptotically linear **under the symmetrized law**
    (hlin : TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => symmetrize P)
      (fun n x => T n x - (Real.sqrt n)⁻¹ * ∑ i, ψ (x i)) 0) :
    TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => P)
      (fun n x => randQuantile (Fin n → ℤˣ) (T n) (1 - α) x)
      (τ * cdfQuantile (gaussianReal 0 1) (1 - α)) := by
  sorry

end StatLean.HypothesisTesting
