import StatLean.AsymptoticStatistics.Core.EIF
import StatLean.AsymptoticStatistics.Core.QMDPath
import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Operational semiparametric efficiency (asymptotic linearity)

An estimator sequence $T_n$ for a real functional $\psi(P)$ is *asymptotically
linear* at $P$ with influence function $\varphi$ (a mean-zero, square-integrable
function under $P$) and centering $c$ when, as the sample size grows, the
normalized estimation error admits the expansion
$$\sqrt{n}\,\bigl(T_n(X) - c\bigr)
   = \frac{1}{\sqrt n}\sum_{i=1}^n \varphi(X_i) + o_P(1),$$
i.e. the residual converges to $0$ in $P^n$-probability. The estimator is
*semiparametrically efficient* at $P$, relative to a tangent space $T$ for the
functional $\psi$, when this expansion holds with $c = \psi(P)$ and the
influence function $\varphi$ equal to the *efficient influence function* — the
canonical-gradient projection of $\psi$ onto the closed linear span of $T$. The
headline result is the operational form of the efficiency criterion: an
efficient influence function together with the asymptotically-linear expansion
based on it certifies efficiency.

This file states this in four pieces — the predicates `AsymptoticallyLinearAt`,
`AsymptoticallyLinearWithBiasAt`, `SemiparametricallyEfficientAt`, and the named
theorem `estimator_semiparametricallyEfficient_of_asympLinear_eif`. The
bias-residual variant `AsymptoticallyLinearWithBiasAt` (vdV §25.8, Theorem
25.59) retains the deterministic bias term $\sqrt{n}\,P_{\hat\theta_n,\eta}\,
\tilde\ell_{\hat\theta_n,\hat\eta_n}$ rather than absorbing it into $o_P(1)$ via
the no-bias condition (25.52); it collapses to `AsymptoticallyLinearAt` exactly
when the bias is identically zero.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.3, Lemma 25.23, Eq (25.22). The
bias-residual variant uses §25.8, Theorem 25.59 and the no-bias condition Eq
(25.52).

**Proof formalization notes.** The centering `c` is kept abstract (rather than
hard-wired to `ψ P`) in `AsymptoticallyLinearAt` so the definition does not
depend on the `PathwiseDifferentiableAt` machinery; concrete consumers pass
`c := ψ P`. Edge behavior: when `φ = 0` the predicate reduces to
`√n · (T_n - c) →_P 0` (consistency at rate), and `SemiparametricallyEfficientAt`
is `False` when no efficient influence function exists for any derivative,
matching vdV's convention that "no EIF" = "no operationally efficient
estimator". The reduction lemma `asympLinearWithBiasAt_zero_iff_asympLinearAt`
shows the bias-residual predicate at the constantly-zero bias is literally
`AsymptoticallyLinearAt` (proved by `simp` through `sub_zero`); it lets the
Theorem 25.54 bundle be recovered from a Theorem 25.59 bundle when the
bias-residual vanishes. The main theorem
`estimator_semiparametricallyEfficient_of_asympLinear_eif` is the And-intro
under existential witnesses — definitional — and is shipped so concrete model
files can supply the EIF and the asymptotically-linear expansion and then invoke
it. The "operational" qualifier distinguishes this achievability statement from
the lower-bound (convolution-theorem) characterization of efficiency; the two
agree under regularity, but the operational form is what model files prove
first.

**Bibliographic comments.** The systematic theory of efficient influence
functions, asymptotic linearity, and semiparametric efficiency bounds was
developed by P. J. Bickel, C. A. J. Klaassen, Y. Ritov & J. A. Wellner,
*Efficient and Adaptive Estimation for Semiparametric Models*, Johns Hopkins
University Press, Baltimore, 1993 (reprinted Springer, 1998), which is the
canonical monograph for the framework van der Vaart's Chapter 25 summarizes. The
efficiency lower bound underlying the criterion descends from the convolution
theorem of J. Hájek, "A characterization of limiting distributions of regular
estimates", *Z. Wahrscheinlichkeitstheorie verw. Geb.* **14** (1970), 323–330,
and the local asymptotic minimax theory of L. Le Cam; the influence-function
representation of regular asymptotically linear estimators originates with
P. J. Bickel, "On adaptive estimation", *Ann. Statist.* **10** (1982), 647–671.
The specific Lemma 25.23 / Eq (25.22) packaging — an estimator is efficient iff
it is asymptotically linear with influence function equal to the efficient
influence function — is van der Vaart's textbook synthesis of this line of work
rather than a single seminal theorem.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.EfficiencyOperational

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.TangentAbstract

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A raw baseline limit distribution for the root-`n` centered estimator.

Constitutive (vdV §25.3, Lemma 25.23): this records only weak convergence
of the centered estimator law. It does not mention asymptotic linearity,
an influence function, pathwise differentiability, or Gaussianity.

Edge behavior: `c` is an explicit centering, so the definition also applies
when the functional is locally constant or the eventual limit is degenerate. -/
def HasLimitDistributionAt
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℝ) (L : Measure ℝ) : Prop :=
  AsymptoticStatistics.WeakConverges
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)).map
      (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - c)))
    L

/-- A selected QMD path for every tangent direction, including the zero
direction.

Constitutive (vdV §25.3, Lemma 25.23): regularity means that recentering at
the perturbed truth gives the same limit law along all tangent paths.

Concrete finite-model example: for a singleton model, constant functional and
constant estimator, take a tangent specification whose carrier is `{0}` and
`L = dirac 0`; the only selected score is zero and every centered statistic is
identically zero. -/
structure SelectedQMDPaths
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T_set : TangentSpec P) where
  zero_mem : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier
  path : {g : ↥(L2ZeroMean P) // g ∈ T_set.carrier} →
    AsymptoticStatistics.Core.QMDPath.QMDPath P
  score_eq : ∀ g, (path g).score = (g : ↥(L2ZeroMean P))

/-- Raw regularity along the selected QMD family, with a common local weak
limit for every scalar local parameter and no derivative, EIF, AL, or
normality bundled into the predicate. -/
def IsRegularAt
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P}
    (paths : SelectedQMDPaths P T_set)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (ψ : Measure Ω → ℝ) (L : Measure ℝ) : Prop :=
  ∀ (g : {g : ↥(L2ZeroMean P) // g ∈ T_set.carrier}) (a : ℝ),
    AsymptoticStatistics.WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n =>
          (paths.path g).curve (a * (Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n *
              (T_n n X - ψ ((paths.path g).curve (a * (Real.sqrt n)⁻¹)))))
      L

/-- An estimator sequence `T_n : (Fin n → Ω) → ℝ` is *asymptotically
linear* at a probability measure `P` with influence function
`φ ∈ ↥(L2ZeroMean P)` and centering `c : ℝ`, iff for every `ε > 0`,
the `Pⁿ`-probability that the residual
`√n · (T_n X - c) - (1/√n) · Σᵢ φ(Xᵢ)` exceeds `ε` in absolute value
tends to zero as `n → ∞`. (Convergence in `Pⁿ`-probability of the
residual to zero.)

Reference: vdV §25.3, eq:25.22. The centering `c` is typically `ψ(P)`;
we keep it abstract so this definition does not depend on the
`PathwiseDifferentiableAt` machinery (concrete consumers pass `c := ψ P`).

Edge behavior: when `φ = 0`, the predicate reduces to
`√n · (T_n - c) →_P 0`, the consistency-at-rate condition. When `T_n`
is the constant `c`, the predicate fails unless `φ = 0` modulo
`L²(P)`-equivalence. -/
def AsymptoticallyLinearAt
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : ↥(L2ZeroMean P)) (c : ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n : ℕ =>
    (MeasureTheory.Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ |Real.sqrt n * (T_n n X - c)
              - (Real.sqrt n)⁻¹
                * (∑ i, ((φ : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i))|})
    atTop (nhds 0)

/-- *Bias-residual variant of asymptotic linearity (vdV §25.8,
thm:25.59).*

`T_n` is asymptotically linear at `P` with influence function
`φ ∈ ↥(L2ZeroMean P)`, centering `c : ℝ`, and bias-residual sequence
`bias : ∀ n, (Fin n → Ω) → ℝ`, iff for every `ε > 0` the
`Pⁿ`-probability that
`√n · (T_n X − c) − (1/√n) · Σᵢ φ(Xᵢ) − bias n X` exceeds `ε` in
absolute value tends to zero as `n → ∞`.

Reference: vdV §25.8, thm:25.59 (the bias-residual expansion). The
predicate generalises `AsymptoticallyLinearAt` by retaining the bias
term `√n · P_{θ̂_n,η} ℓ̃_{θ̂_n,η̂_n}` rather than absorbing it into
`o_P(1)` via the no-bias condition (25.52).

Edge behavior: when `bias = (fun _ _ => 0)`, the predicate is
literally `AsymptoticallyLinearAt T_n P φ c` (see
`asympLinearWithBiasAt_zero_iff_asympLinearAt`). -/
def AsymptoticallyLinearWithBiasAt
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : ↥(L2ZeroMean P)) (c : ℝ)
    (bias : ∀ n, (Fin n → Ω) → ℝ) : Prop :=
  ∀ ε > 0, Tendsto (fun n : ℕ =>
    (MeasureTheory.Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ |Real.sqrt n * (T_n n X - c)
              - (Real.sqrt n)⁻¹
                * (∑ i, ((φ : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i))
              - bias n X|})
    atTop (nhds 0)

/-- *Reduction: thm:25.54 = thm:25.59 with vanishing bias.* The
bias-residual predicate at the constantly-zero bias sequence is
literally `AsymptoticallyLinearAt`. Used by
`EfficientScoreEqBiasResidualAssumptions.toEfficientScoreEqAssumptions`
to recover the thm:25.54 bundle from a thm:25.59 bundle when the
bias-residual is identically zero (i.e., the no-bias condition
(25.52) holds at rate `o_P(n^{−1/2})`).

Reference: vdV §25.8, the (25.52)-collapse step in the discussion
following thm:25.59. -/
theorem asympLinearWithBiasAt_zero_iff_asympLinearAt
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : ↥(L2ZeroMean P)) (c : ℝ) :
    AsymptoticallyLinearWithBiasAt T_n P φ c (fun _ _ => 0)
      ↔ AsymptoticallyLinearAt T_n P φ c := by
  simp only [AsymptoticallyLinearWithBiasAt, AsymptoticallyLinearAt,
    sub_zero]

/-- An estimator sequence `T_n` is *semiparametrically efficient* at `P`
relative to a tangent space `T` for the functional `ψ : Measure Ω → ℝ`,
iff there exists an efficient influence function `φ ∈ ↥(L2ZeroMean P)` and
a derivative `dψ : T →L[ℝ] ℝ` such that `T_n` is asymptotically linear at
`P` with influence `φ` and centering `ψ P`.

Reference: vdV §25.3, definition following lem:25.23 (operational form).
The "operational" qualifier distinguishes this from the lower-bound
characterisation: the operational form says *T_n achieves the
asymptotic-linear-with-EIF expansion*; the lower-bound form would say
*no regular estimator does asymptotically better in variance*. The two
agree under regularity, but the operational form is what concrete
model files prove first.

Edge behavior: when no EIF exists for any derivative (e.g. `dψ` outside
`closure T`), the predicate is `False`. Matches vdV's convention that
"no EIF" = "no operationally efficient estimator". -/
def SemiparametricallyEfficientAt
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (ψ : Measure Ω → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Submodule ℝ ↥(L2ZeroMean P)) : Prop :=
  ∃ (φ : ↥(L2ZeroMean P)) (dψ : T →L[ℝ] ℝ),
    IsEfficientInfluenceFunction P T dψ φ ∧
    AsymptoticallyLinearAt T_n P φ (ψ P)

/-- *Operational form of vdV lem:25.23.* If `φ` is an efficient influence
function for `dψ : T →L[ℝ] ℝ` at `P` relative to `T`, and `T_n` is
asymptotically linear at `P` with influence `φ` and centering `ψ P`, then
`T_n` is semiparametrically efficient at `P` relative to `T` for `ψ`.

Reference: vdV §25.3, lem:25.23 (operational form). The proof is the
And-intro under existential witnesses — definitional. The named theorem
is shipped for downstream consumers (concrete model files supply the
EIF and the asymp-linear expansion, then invoke this theorem). -/
theorem estimator_semiparametricallyEfficient_of_asympLinear_eif
    {T_n : ∀ n, (Fin n → Ω) → ℝ}
    {ψ : Measure Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : Submodule ℝ ↥(L2ZeroMean P)}
    {dψ : T →L[ℝ] ℝ} {φ : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P T dψ φ)
    (hAL : AsymptoticallyLinearAt T_n P φ (ψ P)) :
    SemiparametricallyEfficientAt T_n ψ P T :=
  ⟨φ, dψ, hEIF, hAL⟩
end AsymptoticStatistics.Core.EfficiencyOperational
