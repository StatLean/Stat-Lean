import StatLean.HypothesisTesting.Randomization.Defs
import StatLean.HypothesisTesting.ForMathlib.QuantileFunction
import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Asymptotics of the randomization distribution

When the randomization hypothesis fails, the randomization test is no longer exact, and
the question becomes whether it is *asymptotically* level $\alpha$. The answer is governed
by a single condition: the statistic recomputed at **two independent random group
elements** must be asymptotically independent with a common limit law.

Write $\hat R_n(t) = M_n^{-1}\sum_{g \in \mathbf{G}_n} \mathbf{1}\{T_n(g X^n) \le t\}$ for
the randomization distribution and
$\hat r_n(1-\alpha) = \inf\{t : \hat R_n(t) \ge 1-\alpha\}$ for its $1-\alpha$ quantile.
Let $G_n, G_n'$ be independent and uniform on $\mathbf{G}_n$, independent of $X^n$. If
$$ \bigl(T_n(G_n X^n),\, T_n(G_n' X^n)\bigr) \;\xrightarrow{d}\; (T, T') $$
with $T, T'$ independent and both distributed according to a c.d.f. $R$, then

* $\hat R_n(t) \xrightarrow{P} R(t)$ at every continuity point $t$ of $R$; and
* $\hat r_n(1-\alpha) \xrightarrow{P} r(1-\alpha) = \inf\{t : R(t) \ge 1-\alpha\}$,
  provided $R$ is continuous and strictly increasing at $r(1-\alpha)$.

The converse also holds: pointwise convergence in probability of $\hat R_n$ to a limiting
c.d.f. forces the joint asymptotic-independence condition. Nothing here assumes the
randomization hypothesis.

**Reference.** Classical randomization/permutation testing; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* *Triangular array.* The sample space, the group, the law and the statistic all change
  with `n`, so the setting is formalized with explicit type families `𝓧 : ℕ → Type*` and
  `G : ℕ → Type*` carrying per-`n` `MeasurableSpace` / `Group` / `Fintype` / `MulAction`
  instances. This is honest (nothing forces a common carrier) at the cost of slightly
  heavier binders.
* *Randomizing over the group without a measure on the group.* Because
  $G_n$ is uniform on the finite group and independent of $X^n$, the joint law of
  $(T_n(G_nX^n), T_n(G_n'X^n))$ is the explicit finite mixture
  $M_n^{-2}\sum_{g}\sum_{g'} P_n \circ (T_n(g\,\cdot), T_n(g'\,\cdot))^{-1}$. That is the
  definition of `randPairLaw`, which avoids equipping the group with a measurable
  structure and a uniform measure; mutual independence of $X^n$, $G_n$, $G_n'$ is what the
  double sum encodes, not an extra assumption.
* *Convergence in probability across changing spaces.* `TendstoInMeasure` needs one fixed
  measure space, which a triangular array does not have; `TendstoInProbTriangular` is the
  per-`n` $\varepsilon$-form of the same notion and is used throughout the randomization
  files.
* *Quantiles.* `randQuantile` and `cdfQuantile` are the lower generalized inverses
  $\inf\{t : F(t) \ge p\}$, taken as `sInf` of the corresponding set; the general
  generalized-inverse API lives in the sibling brick
  `StatLean.HypothesisTesting.ForMathlib.QuantileFunction`, which this file imports.
  `sInf ∅ = 0` and unbounded-below sets give `0` in Mathlib's real `sInf`; on the
  probability c.d.f.s used here the sets are nonempty and bounded below, so the junk
  values are unreachable under the stated hypotheses.
* *"Strictly increasing at $r(1-\alpha)$"* is transcribed as: for every
  $\varepsilon > 0$, $R(r - \varepsilon) < 1-\alpha < R(r + \varepsilon)$. Together with
  continuity at $r$ this is exactly what the quantile-convergence argument consumes.

**Bibliographic comments.** The sufficiency direction goes back to W. Hoeffding ("The
large-sample power of tests based on permutations of observations," *Ann. Math. Statist.*
**23** (1952), 169–192); the necessity direction and the modern two-independent-elements
formulation are due to E. Chung and J. P. Romano ("Exact and asymptotically robust
permutation tests," *Ann. Statist.* **41** (2013), 484–507). The behaviour of
randomization tests when the group invariance assumption fails was analysed by
J. P. Romano ("Bootstrap and randomization tests of some nonparametric hypotheses," *Ann.
Statist.* **17** (1989), 141–159; "On the behavior of randomization tests without a group
invariance assumption," *J. Amer. Statist. Assoc.* **85** (1990), 686–692).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)

/-! ### Constructions -/

section Defs

variable (G : Type*) [Group G] [Fintype G] {𝓧 : Type*} [MeasurableSpace 𝓧]
  [MulAction G 𝓧]

/-- The **joint law of the doubly randomized statistic**
$\bigl(T(G\cdot X),\, T(G'\cdot X)\bigr)$, where `G` and `G'` are independent and uniform
on the finite group and independent of the data `X ∼ P`.

Since the group is finite and the two random elements are uniform and independent of
everything else, this law is the explicit mixture
$$ |\mathbf{G}|^{-2} \sum_{g}\sum_{g'} P \circ \bigl(T(g\,\cdot),\, T(g'\,\cdot)\bigr)^{-1},$$
which is how it is defined here — no measurable structure or uniform measure on the group
is required.

The statistic may take values in any measurable space: the scalar case `E = ℝ` drives the
randomization distribution, while vector-valued statistics are needed for the multivariate
quadratic-form applications. -/
noncomputable def randPairLaw {E : Type*} [MeasurableSpace E] (T : 𝓧 → E)
    (P : Measure 𝓧) : Measure (E × E) :=
  ((Fintype.card G : ℝ≥0∞) ^ 2)⁻¹ •
    ∑ g : G, ∑ g' : G, P.map (fun x => (T (g • x), T (g' • x)))

/-- The **quantile of the randomization distribution**,
$\hat r(p \mid x) = \inf\{t : \hat R(t \mid x) \ge p\}$ — the data-dependent critical value
used by the asymptotic theory. (For a finite group it agrees with the order statistic
`randCritValue` at the matching index; the generalized-inverse form is the one that
passes to the limit.) -/
noncomputable def randQuantile (T : 𝓧 → ℝ) (p : ℝ) (x : 𝓧) : ℝ :=
  sInf {t : ℝ | p ≤ randDist G T x t}

end Defs

/-- The **lower generalized inverse** of a c.d.f., $F^{-1}(p) = \inf\{t : F(t) \ge p\}$.
The general API lives in the `ForMathlib/QuantileFunction` brick; this is the packaging
used by the randomization statements. -/
noncomputable def cdfQuantile (R : Measure ℝ) (p : ℝ) : ℝ := sInf {t : ℝ | p ≤ cdf R t}

/-- **Convergence in probability along a triangular array.** The measure spaces change
with `n`, so `TendstoInMeasure` (one fixed space) does not apply; this is the same notion
written out with an explicit `ε`. -/
def TendstoInProbTriangular {𝓨 : ℕ → Type*} [∀ n, MeasurableSpace (𝓨 n)]
    (P : ∀ n, Measure (𝓨 n)) (f : ∀ n, 𝓨 n → ℝ) (c : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), Tendsto (fun n => (P n).real {x | ε ≤ |f n x - c|}) atTop (𝓝 0)

/-! ### Portmanteau bridge -/

/-- **Portmanteau, `Measure.real` form.** If `μ n` converges weakly to `ν` (all probability
measures) and the boundary of `s` is `ν`-null, then `(μ n).real s → ν.real s`. This is the
`WeakConverges`/`Measure.real` packaging of `tendsto_measure_of_null_frontier`. -/
private lemma tendsto_real_of_weakConverges_of_null_frontier {E : Type*}
    [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    {μ : ℕ → Measure E} {ν : Measure E}
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (h : WeakConverges μ ν) {s : Set E} (hs : ν (frontier s) = 0) :
    Tendsto (fun n => (μ n).real s) atTop (𝓝 (ν.real s)) := by
  let pn : ℕ → ProbabilityMeasure E := fun n => ⟨μ n, inferInstance⟩
  let pμ : ProbabilityMeasure E := ⟨ν, inferInstance⟩
  have hpm : Tendsto pn atTop (𝓝 pμ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f; simpa [pn, pμ] using h f
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hpm
    (E := s) (by simpa [pμ] using hs)
  have := (ENNReal.tendsto_toReal (measure_ne_top ν s)).comp key
  simpa [Measure.real, pn, pμ] using this

/-! ### The asymptotic randomization theorem -/

section Asymptotics

variable {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
  {G : ℕ → Type*} [∀ n, Group (G n)] [∀ n, Fintype (G n)] [∀ n, MulAction (G n) (𝓧 n)]

/-- **The randomization distribution converges in probability to the limit c.d.f.**
Under the joint asymptotic-independence condition — the statistic evaluated at two
independent uniform group elements converges jointly in law to a product `R ⊗ R` — the
randomization distribution converges in probability to `R` at every continuity point:
$$ \hat R_n(t) \;\xrightarrow{P}\; R(t) . $$
The randomization hypothesis is *not* assumed. -/
theorem randDist_tendstoInProb_cdf (P : ∀ n, Measure (𝓧 n))
    [∀ n, IsProbabilityMeasure (P n)] (T : ∀ n, 𝓧 n → ℝ) (R : Measure ℝ)
    -- USER-INPUT: the limit is a probability law; it is the limiting c.d.f. `R`
    [IsProbabilityMeasure R]
    -- USER-INPUT: joint weak convergence to a product law — asymptotic independence of
    -- the statistic at two independent uniform group elements, with common limit `R`
    (hjoint : WeakConverges (fun n => randPairLaw (G n) (T n) (P n)) (R.prod R))
    {t : ℝ}
    -- USER-INPUT: `t` is a continuity point of the limit c.d.f.
    (ht : ContinuousAt (cdf R) t) :
    TendstoInProbTriangular P (fun n x => randDist (G n) (T n) x t) (cdf R t) := by
  sorry

/-- **The randomization critical value converges in probability.** Under the same joint
condition, if the limit c.d.f. is continuous and strictly increasing at its
$(1-\alpha)$-quantile, then
$$ \hat r_n(1-\alpha) \;\xrightarrow{P}\; r(1-\alpha) = \inf\{t : R(t) \ge 1-\alpha\} . $$
-/
theorem randQuantile_tendstoInProb (P : ∀ n, Measure (𝓧 n))
    [∀ n, IsProbabilityMeasure (P n)] (T : ∀ n, 𝓧 n → ℝ) (R : Measure ℝ)
    [IsProbabilityMeasure R]
    -- USER-INPUT: joint weak convergence to a product law (asymptotic independence)
    (hjoint : WeakConverges (fun n => randPairLaw (G n) (T n) (P n)) (R.prod R))
    {α : ℝ}
    -- USER-INPUT: nominal level strictly between `0` and `1`; the calibration range
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: the limit c.d.f. is continuous at its `1 − α` quantile
    (hcont : ContinuousAt (cdf R) (cdfQuantile R (1 - α)))
    -- USER-INPUT: the limit c.d.f. is strictly increasing at its `1 − α` quantile
    (hstrict : ∀ ε > (0 : ℝ), cdf R (cdfQuantile R (1 - α) - ε) < 1 - α ∧
      1 - α < cdf R (cdfQuantile R (1 - α) + ε)) :
    TendstoInProbTriangular P (fun n x => randQuantile (G n) (T n) (1 - α) x)
      (cdfQuantile R (1 - α)) := by
  sorry

/-- **Converse.** If the randomization distribution converges in probability to some
limiting c.d.f. at every continuity point, then the joint asymptotic-independence
condition holds — so the two formulations are equivalent. -/
theorem weakConverges_randPairLaw_of_randDist_tendstoInProb (P : ∀ n, Measure (𝓧 n))
    [∀ n, IsProbabilityMeasure (P n)] (T : ∀ n, 𝓧 n → ℝ) (R : Measure ℝ)
    [IsProbabilityMeasure R]
    -- USER-INPUT: pointwise convergence in probability of the randomization distribution
    -- to a limiting c.d.f., at every continuity point
    (h : ∀ t, ContinuousAt (cdf R) t →
      TendstoInProbTriangular P (fun n x => randDist (G n) (T n) x t) (cdf R t)) :
    WeakConverges (fun n => randPairLaw (G n) (T n) (P n)) (R.prod R) := by
  sorry

end Asymptotics

end StatLean.HypothesisTesting
