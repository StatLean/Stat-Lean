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

/-! ### Moment identities linking `randDist` to `randPairLaw` -/

section Identities

variable (G : Type*) [Group G] [Fintype G] {𝓧 : Type*} [MeasurableSpace 𝓧] [MulAction G 𝓧]

/-- **First-moment identity.** The mean of the randomization distribution at `t` is the mass
that `randPairLaw` puts on `Iic t ×ˢ univ`:
`∫ R̂(·,t) dP = randPairLaw(Iic t ×ˢ univ)`. Measurability of the statistic and of the
action is genuinely required: `Measure.map` of a non-measurable map is the zero measure,
so the two sides would otherwise use different junk conventions. -/
lemma integral_randDist_eq_real_randPairLaw (P : Measure 𝓧) [IsProbabilityMeasure P]
    (T : 𝓧 → ℝ) (t : ℝ) (hT : Measurable T)
    (hsmul : ∀ g : G, Measurable (fun x : 𝓧 => g • x)) :
    ∫ x, randDist G T x t ∂P = (randPairLaw G T P).real (Set.Iic t ×ˢ Set.univ) := by
  classical
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have hcardℝ : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast hcard.ne'
  have hcardtop : (Fintype.card G : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hmset : ∀ g : G, MeasurableSet {x : 𝓧 | T (g • x) ≤ t} := fun g =>
    measurableSet_le (hT.comp (hsmul g)) measurable_const
  have hpair : ∀ g g' : G, Measurable (fun x : 𝓧 => (T (g • x), T (g' • x))) := fun g g' =>
    (hT.comp (hsmul g)).prodMk (hT.comp (hsmul g'))
  -- per-`g` indicator integral
  have hind : ∀ g : G, (fun x => if T (g • x) ≤ t then (1 : ℝ) else 0)
      = Set.indicator {x | T (g • x) ≤ t} 1 := fun g => by
    funext x; simp [Set.indicator_apply]
  have hint : ∀ g : G, ∫ x, (if T (g • x) ≤ t then (1 : ℝ) else 0) ∂P
      = P.real {x : 𝓧 | T (g • x) ≤ t} := by
    intro g
    rw [show (∫ x, (if T (g • x) ≤ t then (1 : ℝ) else 0) ∂P)
        = ∫ x, Set.indicator {x | T (g • x) ≤ t} 1 x ∂P from by rw [hind g],
      integral_indicator_one (hmset g)]
  -- LHS
  have hLHS : ∫ x, randDist G T x t ∂P
      = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, P.real {x : 𝓧 | T (g • x) ≤ t} := by
    simp only [randDist]
    rw [integral_const_mul, integral_finset_sum]
    · simp_rw [hint]
    · intro g _
      rw [hind g]
      exact (integrable_const (1 : ℝ)).indicator (hmset g)
  -- RHS: measure of `randPairLaw` at the product set
  have hmeasS : MeasurableSet (Set.Iic t ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Iic.prod MeasurableSet.univ
  have hpre : ∀ g g' : G,
      (fun x : 𝓧 => (T (g • x), T (g' • x))) ⁻¹' (Set.Iic t ×ˢ Set.univ)
        = {x : 𝓧 | T (g • x) ≤ t} := by
    intro g g'; ext x; simp [Set.mem_prod, Set.mem_Iic]
  have hstep : ∀ g : G,
      (∑ g' : G, P.map fun x => (T (g • x), T (g' • x))) (Set.Iic t ×ˢ Set.univ)
        = (Fintype.card G : ℝ≥0∞) * P {x : 𝓧 | T (g • x) ≤ t} := by
    intro g
    rw [Measure.finset_sum_apply,
      Finset.sum_congr rfl (fun g' _ => by
        rw [Measure.map_apply (hpair g g') hmeasS, hpre g g']),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcc : ((Fintype.card G : ℝ≥0∞) ^ 2)⁻¹ * (Fintype.card G : ℝ≥0∞)
      = (Fintype.card G : ℝ≥0∞)⁻¹ := by
    rw [sq, ENNReal.mul_inv (Or.inl hcardℝ) (Or.inl hcardtop), mul_assoc,
      ENNReal.inv_mul_cancel hcardℝ hcardtop, mul_one]
  have hval : (randPairLaw G T P) (Set.Iic t ×ˢ Set.univ)
      = (Fintype.card G : ℝ≥0∞)⁻¹ * ∑ g : G, P {x : 𝓧 | T (g • x) ≤ t} := by
    rw [randPairLaw, Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply]
    simp_rw [hstep]
    rw [← Finset.mul_sum, ← mul_assoc, hcc]
  have hRHS : (randPairLaw G T P).real (Set.Iic t ×ˢ Set.univ)
      = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, P.real {x : 𝓧 | T (g • x) ≤ t} := by
    rw [Measure.real, hval, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum fun g _ => measure_ne_top P _]
    rfl
  rw [hLHS, hRHS]

/-- **Second-moment identity.** The mean square of the randomization distribution at `t` is
the mass that `randPairLaw` puts on `Iic t ×ˢ Iic t`:
`∫ R̂(·,t)² dP = randPairLaw(Iic t ×ˢ Iic t)`. -/
lemma integral_randDist_sq_eq_real_randPairLaw (P : Measure 𝓧) [IsProbabilityMeasure P]
    (T : 𝓧 → ℝ) (t : ℝ) (hT : Measurable T)
    (hsmul : ∀ g : G, Measurable (fun x : 𝓧 => g • x)) :
    ∫ x, (randDist G T x t) ^ 2 ∂P
      = (randPairLaw G T P).real (Set.Iic t ×ˢ Set.Iic t) := by
  classical
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have hcardℝ : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast hcard.ne'
  have hset : ∀ g g' : G, MeasurableSet {x : 𝓧 | T (g • x) ≤ t ∧ T (g' • x) ≤ t} := fun g g' =>
    (measurableSet_le (hT.comp (hsmul g)) measurable_const).inter
      (measurableSet_le (hT.comp (hsmul g')) measurable_const)
  have hpair : ∀ g g' : G, Measurable (fun x : 𝓧 => (T (g • x), T (g' • x))) := fun g g' =>
    (hT.comp (hsmul g)).prodMk (hT.comp (hsmul g'))
  have hind : ∀ g g' : G,
      (fun x => (if T (g • x) ≤ t then (1 : ℝ) else 0) * (if T (g' • x) ≤ t then (1 : ℝ) else 0))
        = Set.indicator {x | T (g • x) ≤ t ∧ T (g' • x) ≤ t} 1 := by
    intro g g'; funext x
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs <;> simp_all
  have hintg' : ∀ g g' : G, Integrable (fun x =>
      (if T (g • x) ≤ t then (1 : ℝ) else 0) * (if T (g' • x) ≤ t then (1 : ℝ) else 0)) P := by
    intro g g'; rw [hind g g']; exact (integrable_const (1 : ℝ)).indicator (hset g g')
  have hintprod : ∀ g g' : G,
      ∫ x, (if T (g • x) ≤ t then (1 : ℝ) else 0) * (if T (g' • x) ≤ t then (1 : ℝ) else 0) ∂P
        = P.real {x : 𝓧 | T (g • x) ≤ t ∧ T (g' • x) ≤ t} := by
    intro g g'
    rw [show (∫ x, (if T (g • x) ≤ t then (1 : ℝ) else 0)
          * (if T (g' • x) ≤ t then (1 : ℝ) else 0) ∂P)
        = ∫ x, Set.indicator {x | T (g • x) ≤ t ∧ T (g' • x) ≤ t} 1 x ∂P from by rw [hind g g'],
      integral_indicator_one (hset g g')]
  have hpt : ∀ x, (randDist G T x t) ^ 2
      = (Fintype.card G : ℝ)⁻¹ ^ 2 * ∑ g : G, ∑ g' : G,
          (if T (g • x) ≤ t then (1 : ℝ) else 0) * (if T (g' • x) ≤ t then (1 : ℝ) else 0) := by
    intro x; simp only [randDist, mul_pow]; congr 1; rw [pow_two, Finset.sum_mul_sum]
  have hLHS : ∫ x, (randDist G T x t) ^ 2 ∂P
      = (Fintype.card G : ℝ)⁻¹ ^ 2 * ∑ g : G, ∑ g' : G,
          P.real {x : 𝓧 | T (g • x) ≤ t ∧ T (g' • x) ≤ t} := by
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    rw [integral_finset_sum _ (fun g _ => integrable_finset_sum _ fun g' _ => hintg' g g')]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [integral_finset_sum _ (fun g' _ => hintg' g g')]
    exact Finset.sum_congr rfl fun g' _ => hintprod g g'
  have hmeasS : MeasurableSet (Set.Iic t ×ˢ Set.Iic t) :=
    measurableSet_Iic.prod measurableSet_Iic
  have hpre : ∀ g g' : G,
      (fun x : 𝓧 => (T (g • x), T (g' • x))) ⁻¹' (Set.Iic t ×ˢ Set.Iic t)
        = {x : 𝓧 | T (g • x) ≤ t ∧ T (g' • x) ≤ t} := fun g g' => by
    ext x; simp [Set.mem_prod, Set.mem_Iic]
  have hval : (randPairLaw G T P) (Set.Iic t ×ˢ Set.Iic t)
      = ((Fintype.card G : ℝ≥0∞) ^ 2)⁻¹ *
          ∑ g : G, ∑ g' : G, P {x : 𝓧 | T (g • x) ≤ t ∧ T (g' • x) ≤ t} := by
    rw [randPairLaw, Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Measure.finset_sum_apply]
    exact Finset.sum_congr rfl fun g' _ => by rw [Measure.map_apply (hpair g g') hmeasS, hpre g g']
  have hRHS : (randPairLaw G T P).real (Set.Iic t ×ˢ Set.Iic t)
      = (Fintype.card G : ℝ)⁻¹ ^ 2 *
          ∑ g : G, ∑ g' : G, P.real {x : 𝓧 | T (g • x) ≤ t ∧ T (g' • x) ≤ t} := by
    have hsc : (((Fintype.card G : ℝ≥0∞) ^ 2)⁻¹).toReal = (Fintype.card G : ℝ)⁻¹ ^ 2 := by
      rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, inv_pow]
    rw [Measure.real, hval, ENNReal.toReal_mul, hsc]
    congr 1
    rw [ENNReal.toReal_sum fun g _ =>
      (ENNReal.sum_lt_top.2 fun g' _ => measure_lt_top P _).ne]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [ENNReal.toReal_sum fun g' _ => measure_ne_top P _]
    rfl
  rw [hLHS, hRHS]

/-- `randPairLaw` is a probability measure: it is `card⁻²` times a sum of `card²` pushforwards
of the probability measure `P`, each of total mass `1` (the maps are measurable). -/
lemma isProbabilityMeasure_randPairLaw {E : Type*} [MeasurableSpace E] (P : Measure 𝓧)
    [IsProbabilityMeasure P] (T : 𝓧 → E) (hT : Measurable T)
    (hsmul : ∀ g : G, Measurable (fun x : 𝓧 => g • x)) :
    IsProbabilityMeasure (randPairLaw G T P) := by
  classical
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have hcardℝ : (Fintype.card G : ℝ≥0∞) ≠ 0 := by exact_mod_cast hcard.ne'
  have hcardtop : (Fintype.card G : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hpair : ∀ g g' : G, Measurable (fun x : 𝓧 => (T (g • x), T (g' • x))) := fun g g' =>
    (hT.comp (hsmul g)).prodMk (hT.comp (hsmul g'))
  constructor
  rw [randPairLaw, Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply]
  have hstep : ∀ g : G, (∑ g' : G, P.map fun x => (T (g • x), T (g' • x))) Set.univ
      = (Fintype.card G : ℝ≥0∞) := by
    intro g
    rw [Measure.finset_sum_apply,
      Finset.sum_congr rfl (fun g' _ => by
        rw [Measure.map_apply (hpair g g') MeasurableSet.univ, Set.preimage_univ, measure_univ]),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl (fun g _ => hstep g), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← pow_two, ENNReal.inv_mul_cancel (pow_ne_zero 2 hcardℝ) (ENNReal.pow_ne_top hcardtop)]

/-- The randomization distribution is nondecreasing in the threshold `t`. -/
lemma randDist_mono (T : 𝓧 → ℝ) (x : 𝓧) : Monotone (fun t => randDist G T x t) := by
  intro s t hst
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => ?_) (by positivity)
  split_ifs with h1 h2
  · exact le_refl _
  · exact absurd (h1.trans hst) h2
  · norm_num
  · exact le_refl _

/-- The `p`-sublevel set `{t : p ≤ R̂(t ∣ x)}` of the randomization distribution is bounded below
whenever `0 < p`: for `t` below every orbit value `R̂(t ∣ x) = 0 < p`. -/
lemma bddBelow_randDist_sublevel (T : 𝓧 → ℝ) (x : 𝓧) {p : ℝ} (hp : 0 < p) :
    BddBelow {t : ℝ | p ≤ randDist G T x t} := by
  refine ⟨⨅ g : G, T (g • x), fun t ht => ?_⟩
  simp only [Set.mem_setOf_eq] at ht
  have hex : ∃ g : G, T (g • x) ≤ t := by
    by_contra hcon
    push_neg at hcon
    have hz : randDist G T x t = 0 := by
      rw [randDist]
      have : ∀ g : G, (if T (g • x) ≤ t then (1 : ℝ) else 0) = 0 := fun g =>
        if_neg (not_le.mpr (hcon g))
      simp [this]
    rw [hz] at ht; linarith
  obtain ⟨g, hg⟩ := hex
  exact le_trans (ciInf_le (Finite.bddBelow_range _) g) hg

end Identities

/-! ### The asymptotic randomization theorem -/

section Asymptotics

variable {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
  {G : ℕ → Type*} [∀ n, Group (G n)] [∀ n, Fintype (G n)] [∀ n, MulAction (G n) (𝓧 n)]

/-- **Second-moment engine for the forward direction.** With the statistic and the action
measurable (so that the moment identities apply and `randPairLaw` is a probability measure),
the mean and mean-square of the randomization distribution at a continuity point `t` converge
to `cdf R t` and `(cdf R t)²`; the variance therefore vanishes and Chebyshev gives convergence
in probability. This is the content of `randDist_tendstoInProb_cdf`; the public statement then
supplies the measurability the moment identities require. -/
private lemma randDist_tendstoInProb_cdf_aux (P : ∀ n, Measure (𝓧 n))
    [∀ n, IsProbabilityMeasure (P n)] (T : ∀ n, 𝓧 n → ℝ) (R : Measure ℝ)
    [IsProbabilityMeasure R]
    (hT : ∀ n, Measurable (T n))
    (hsmul : ∀ (n : ℕ) (g : G n), Measurable (fun x : 𝓧 n => g • x))
    (hjoint : WeakConverges (fun n => randPairLaw (G n) (T n) (P n)) (R.prod R))
    {t : ℝ} (ht : ContinuousAt (cdf R) t) :
    TendstoInProbTriangular P (fun n x => randDist (G n) (T n) x t) (cdf R t) := by
  classical
  set c := cdf R t with hc
  -- `t` is not an atom of `R` (continuity of the c.d.f.).
  have hatom : R {t} = 0 := by
    have hll : Function.leftLim (⇑(cdf R)) t = cdf R t :=
      leftLim_eq_of_tendsto (nhdsLT_neBot t).ne (ht.tendsto.mono_left nhdsWithin_le_nhds)
    have h1 := (cdf R).measure_singleton t
    rw [measure_cdf] at h1
    rw [h1, hll, sub_self, ENNReal.ofReal_zero]
  -- A `(R ⊗ R)`-null set containing the frontiers of the two rectangles.
  set N : Set (ℝ × ℝ) := ({t} ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ {t}) with hN
  have hNnull : (R.prod R) N = 0 := by
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, hatom, zero_mul]
    · rw [Measure.prod_prod, hatom, mul_zero]
  have hfr1 : (R.prod R) (frontier (Set.Iic t ×ˢ (Set.univ : Set ℝ))) = 0 := by
    refine measure_mono_null ?_ hNnull
    rw [frontier_prod_eq, frontier_Iic, frontier_univ, closure_univ, closure_Iic, hN]
    simp only [Set.prod_empty, Set.empty_union]
    exact Set.subset_union_left
  have hfr2 : (R.prod R) (frontier (Set.Iic t ×ˢ Set.Iic t)) = 0 := by
    refine measure_mono_null ?_ hNnull
    rw [frontier_prod_eq, frontier_Iic, closure_Iic, hN]
    refine Set.union_subset (Set.Subset.trans ?_ Set.subset_union_right)
      (Set.Subset.trans ?_ Set.subset_union_left)
    · exact Set.prod_mono (Set.subset_univ _) (Set.Subset.refl _)
    · exact Set.prod_mono (Set.Subset.refl _) (Set.subset_univ _)
  -- `randPairLaw` is a probability measure on each level.
  haveI hprob : ∀ n, IsProbabilityMeasure (randPairLaw (G n) (T n) (P n)) := fun n =>
    isProbabilityMeasure_randPairLaw (G n) (P n) (T n) (hT n) (hsmul n)
  -- Portmanteau: the two rectangle masses converge.
  have hE1 : Tendsto (fun n => (randPairLaw (G n) (T n) (P n)).real (Set.Iic t ×ˢ Set.univ))
      atTop (𝓝 ((R.prod R).real (Set.Iic t ×ˢ Set.univ))) :=
    tendsto_real_of_weakConverges_of_null_frontier hjoint hfr1
  have hE2 : Tendsto (fun n => (randPairLaw (G n) (T n) (P n)).real (Set.Iic t ×ˢ Set.Iic t))
      atTop (𝓝 ((R.prod R).real (Set.Iic t ×ˢ Set.Iic t))) :=
    tendsto_real_of_weakConverges_of_null_frontier hjoint hfr2
  -- Identify the two limits.
  have hlim1 : (R.prod R).real (Set.Iic t ×ˢ Set.univ) = c := by
    rw [hc, cdf_eq_real, Measure.real, Measure.real, Measure.prod_prod, measure_univ, mul_one]
  have hlim2 : (R.prod R).real (Set.Iic t ×ˢ Set.Iic t) = c ^ 2 := by
    rw [hc, cdf_eq_real, Measure.real, Measure.real, Measure.prod_prod, ENNReal.toReal_mul, sq]
  -- Measurability, boundedness and integrability of the randomization distribution.
  have hmset : ∀ (n : ℕ) (g : G n), MeasurableSet {x : 𝓧 n | T n (g • x) ≤ t} := fun n g =>
    measurableSet_le ((hT n).comp (hsmul n g)) measurable_const
  have hind_eq : ∀ (n : ℕ) (g : G n),
      (fun x : 𝓧 n => if T n (g • x) ≤ t then (1 : ℝ) else 0)
        = Set.indicator {x | T n (g • x) ≤ t} 1 := fun n g => by
    funext x; simp [Set.indicator_apply]
  have hrdmeas : ∀ n, Measurable (fun x : 𝓧 n => randDist (G n) (T n) x t) := by
    intro n
    simp only [randDist]
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ (fun g _ => ?_)
    rw [hind_eq n g]
    exact measurable_const.indicator (hmset n g)
  have hbound_rd : ∀ (n : ℕ) (x : 𝓧 n), ‖randDist (G n) (T n) x t‖ ≤ 1 := by
    intro n x
    rw [Real.norm_eq_abs, abs_le]
    have hnn : 0 ≤ randDist (G n) (T n) x t :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun g _ => by split_ifs <;> norm_num)
    refine ⟨by linarith, ?_⟩
    rw [randDist]
    have hS : ∑ g : G n, (if T n (g • x) ≤ t then (1 : ℝ) else 0) ≤ Fintype.card (G n) := by
      calc ∑ g : G n, (if T n (g • x) ≤ t then (1 : ℝ) else 0)
          ≤ ∑ _g : G n, (1 : ℝ) := Finset.sum_le_sum fun g _ => by split_ifs <;> norm_num
        _ = Fintype.card (G n) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    calc (Fintype.card (G n) : ℝ)⁻¹ * ∑ g : G n, (if T n (g • x) ≤ t then (1 : ℝ) else 0)
        ≤ (Fintype.card (G n) : ℝ)⁻¹ * Fintype.card (G n) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 1 := inv_mul_cancel₀ (by exact_mod_cast Fintype.card_pos.ne')
  have hint_f : ∀ n, Integrable (fun x => randDist (G n) (T n) x t) (P n) := by
    intro n
    simp only [randDist]
    refine Integrable.const_mul ?_ _
    refine integrable_finset_sum _ (fun g _ => ?_)
    rw [hind_eq n g]
    exact (integrable_const (1 : ℝ)).indicator (hmset n g)
  have hint_f2 : ∀ n, Integrable (fun x => (randDist (G n) (T n) x t) ^ 2) (P n) := by
    intro n
    have := (hint_f n).bdd_mul (hrdmeas n).aestronglyMeasurable
      (Filter.Eventually.of_forall (hbound_rd n))
    simpa [pow_two] using this
  have hint_fc2 : ∀ n, Integrable (fun x => (randDist (G n) (T n) x t - c) ^ 2) (P n) := by
    intro n
    have heq : (fun x => (randDist (G n) (T n) x t - c) ^ 2)
        = fun x => (randDist (G n) (T n) x t) ^ 2 - 2 * c * randDist (G n) (T n) x t + c ^ 2 := by
      funext x; ring
    rw [heq]
    exact ((hint_f2 n).sub ((hint_f n).const_mul (2 * c))).add (integrable_const _)
  -- The first two moments converge to `c` and `c²`.
  have hBlim : Tendsto (fun n => ∫ x, randDist (G n) (T n) x t ∂(P n)) atTop (𝓝 c) := by
    have h := hE1
    rw [hlim1] at h
    refine h.congr (fun n => ?_)
    exact (integral_randDist_eq_real_randPairLaw (G n) (P n) (T n) t (hT n) (hsmul n)).symm
  have hAlim : Tendsto (fun n => ∫ x, (randDist (G n) (T n) x t) ^ 2 ∂(P n)) atTop (𝓝 (c ^ 2)) := by
    have h := hE2
    rw [hlim2] at h
    refine h.congr (fun n => ?_)
    exact (integral_randDist_sq_eq_real_randPairLaw (G n) (P n) (T n) t (hT n) (hsmul n)).symm
  -- Hence the second moment about `c` vanishes.
  have hM2 : ∀ n, ∫ x, (randDist (G n) (T n) x t - c) ^ 2 ∂(P n)
      = (∫ x, (randDist (G n) (T n) x t) ^ 2 ∂(P n))
        - 2 * c * (∫ x, randDist (G n) (T n) x t ∂(P n)) + c ^ 2 := by
    intro n
    have i1 : Integrable (fun x => (randDist (G n) (T n) x t) ^ 2) (P n) := hint_f2 n
    have i2 : Integrable (fun x => 2 * c * randDist (G n) (T n) x t) (P n) :=
      (hint_f n).const_mul _
    have i3 : Integrable (fun x => (randDist (G n) (T n) x t) ^ 2
        - 2 * c * randDist (G n) (T n) x t) (P n) := i1.sub i2
    have i4 : Integrable (fun _ : 𝓧 n => c ^ 2) (P n) := integrable_const _
    calc ∫ x, (randDist (G n) (T n) x t - c) ^ 2 ∂(P n)
        = ∫ x, ((randDist (G n) (T n) x t) ^ 2 - 2 * c * randDist (G n) (T n) x t + c ^ 2)
            ∂(P n) := integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = (∫ x, ((randDist (G n) (T n) x t) ^ 2 - 2 * c * randDist (G n) (T n) x t) ∂(P n))
            + ∫ _x, (c ^ 2 : ℝ) ∂(P n) := integral_add i3 i4
      _ = ((∫ x, (randDist (G n) (T n) x t) ^ 2 ∂(P n))
            - ∫ x, 2 * c * randDist (G n) (T n) x t ∂(P n)) + ∫ _x, (c ^ 2 : ℝ) ∂(P n) := by
            rw [integral_sub i1 i2]
      _ = (∫ x, (randDist (G n) (T n) x t) ^ 2 ∂(P n))
            - 2 * c * (∫ x, randDist (G n) (T n) x t ∂(P n)) + c ^ 2 := by
            rw [integral_const_mul, integral_const]; simp
  have hM2lim : Tendsto (fun n => ∫ x, (randDist (G n) (T n) x t - c) ^ 2 ∂(P n)) atTop (𝓝 0) := by
    have e : (0 : ℝ) = c ^ 2 - 2 * c * c + c ^ 2 := by ring
    rw [e]
    refine Tendsto.congr (fun n => (hM2 n).symm) ?_
    exact (hAlim.sub (tendsto_const_nhds.mul hBlim)).add tendsto_const_nhds
  -- Chebyshev, then squeeze.
  intro ε hε
  have hnn : ∀ n, 0 ≤ (P n).real {x | ε ≤ |randDist (G n) (T n) x t - c|} :=
    fun n => measureReal_nonneg
  have hbound : ∀ n, (P n).real {x | ε ≤ |randDist (G n) (T n) x t - c|}
      ≤ (∫ x, (randDist (G n) (T n) x t - c) ^ 2 ∂(P n)) / ε ^ 2 := by
    intro n
    have hset : {x | ε ≤ |randDist (G n) (T n) x t - c|}
        = {x | ε ^ 2 ≤ (randDist (G n) (T n) x t - c) ^ 2} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h; nlinarith [abs_nonneg (randDist (G n) (T n) x t - c),
          sq_abs (randDist (G n) (T n) x t - c)]
      · intro h; nlinarith [abs_nonneg (randDist (G n) (T n) x t - c),
          sq_abs (randDist (G n) (T n) x t - c), hε.le]
    rw [hset, le_div_iff₀ (by positivity : (0 : ℝ) < ε ^ 2), mul_comm]
    exact mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (hint_fc2 n) (ε ^ 2)
  exact squeeze_zero hnn hbound (by simpa using hM2lim.div_const (ε ^ 2))

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
    -- USER-INPUT: the statistic is measurable (data regularity). Not derivable from the
    -- other hypotheses, and genuinely needed: for a non-measurable statistic every
    -- `randPairLaw` degenerates to the zero measure and the moment identities fail.
    (hT : ∀ n, Measurable (T n))
    -- USER-INPUT: the group acts measurably (data regularity); required by the same
    -- moment identities `integral_randDist_..._randPairLaw`
    (hsmul : ∀ (n : ℕ) (g : G n), Measurable (fun x : 𝓧 n => g • x))
    -- USER-INPUT: joint weak convergence to a product law — asymptotic independence of
    -- the statistic at two independent uniform group elements, with common limit `R`
    (hjoint : WeakConverges (fun n => randPairLaw (G n) (T n) (P n)) (R.prod R))
    {t : ℝ}
    -- USER-INPUT: `t` is a continuity point of the limit c.d.f.
    (ht : ContinuousAt (cdf R) t) :
    TendstoInProbTriangular P (fun n x => randDist (G n) (T n) x t) (cdf R t) :=
  randDist_tendstoInProb_cdf_aux P T R hT hsmul hjoint ht

/-- **Quantile-convergence engine.** Given the forward convergence at continuity points
(`randDist_tendstoInProb_cdf_aux`), the `(1-α)`-quantile of the randomization distribution
converges in probability to the limiting quantile. The argument brackets the random quantile
between two nearby continuity points `a < q < b` with `cdf R a < 1-α < cdf R b`, obtained by
density of continuity points of the monotone `cdf R`; at those points the forward convergence
controls the two failure events. Requires the same measurability as the forward engine. -/
private lemma randQuantile_tendstoInProb_aux (P : ∀ n, Measure (𝓧 n))
    [∀ n, IsProbabilityMeasure (P n)] (T : ∀ n, 𝓧 n → ℝ) (R : Measure ℝ)
    [IsProbabilityMeasure R]
    (hT : ∀ n, Measurable (T n))
    (hsmul : ∀ (n : ℕ) (g : G n), Measurable (fun x : 𝓧 n => g • x))
    (hjoint : WeakConverges (fun n => randPairLaw (G n) (T n) (P n)) (R.prod R))
    {α : ℝ} (hα₁ : α < 1)
    (hstrict : ∀ ε > (0 : ℝ), cdf R (cdfQuantile R (1 - α) - ε) < 1 - α ∧
      1 - α < cdf R (cdfQuantile R (1 - α) + ε)) :
    TendstoInProbTriangular P (fun n x => randQuantile (G n) (T n) (1 - α) x)
      (cdfQuantile R (1 - α)) := by
  set p := 1 - α with hp
  set q := cdfQuantile R p with hq
  have hp0 : 0 < p := by rw [hp]; linarith
  have hcountable : Set.Countable {x | ¬ ContinuousAt (cdf R) x} :=
    (monotone_cdf (μ := R)).countable_not_continuousAt
  -- Density of continuity points in any open interval.
  have hCP : ∀ {a b : ℝ}, a < b → ∃ x ∈ Set.Ioo a b, ContinuousAt (cdf R) x := by
    intro a b hab
    by_contra hcon
    push_neg at hcon
    have hsub : Set.Ioo a b ⊆ {x | ¬ ContinuousAt (cdf R) x} := fun x hx => hcon x hx
    have hz : volume (Set.Ioo a b) = 0 := measure_mono_null hsub (hcountable.measure_zero volume)
    rw [Real.volume_Ioo] at hz
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne' hz
  intro ε hε
  obtain ⟨hlo, hhi⟩ := hstrict (ε / 2) (by linarith)
  obtain ⟨a, ha_mem, ha_cont⟩ := hCP (show q - ε < q - ε / 2 by linarith)
  obtain ⟨b, hb_mem, hb_cont⟩ := hCP (show q + ε / 2 < q + ε by linarith)
  have hca : cdf R a < p := lt_of_le_of_lt (monotone_cdf (μ := R) ha_mem.2.le) hlo
  have hcb : p < cdf R b := lt_of_lt_of_le hhi (monotone_cdf (μ := R) hb_mem.1.le)
  have hδa : 0 < p - cdf R a := by linarith
  have hδb : 0 < cdf R b - p := by linarith
  have hAa := randDist_tendstoInProb_cdf_aux P T R hT hsmul hjoint ha_cont (p - cdf R a) hδa
  have hBb := randDist_tendstoInProb_cdf_aux P T R hT hsmul hjoint hb_cont (cdf R b - p) hδb
  -- Inclusion of the "quantile off by ε" event into the two forward-controlled events.
  have hincl : ∀ n, {x | ε ≤ |randQuantile (G n) (T n) p x - q|} ⊆
      {x | p - cdf R a ≤ |randDist (G n) (T n) x a - cdf R a|} ∪
      {x | cdf R b - p ≤ |randDist (G n) (T n) x b - cdf R b|} := by
    intro n x hx
    simp only [Set.mem_setOf_eq] at hx
    by_contra hnot
    rw [Set.mem_union, not_or] at hnot
    obtain ⟨hna, hnb⟩ := hnot
    simp only [Set.mem_setOf_eq, not_le] at hna hnb
    have hrda : randDist (G n) (T n) x a < p := by
      have := (abs_lt.mp hna).2; linarith
    have hrdb : p ≤ randDist (G n) (T n) x b := by
      have := (abs_lt.mp hnb).1; linarith
    have hup : randQuantile (G n) (T n) p x ≤ b :=
      csInf_le (bddBelow_randDist_sublevel (G n) (T n) x hp0) hrdb
    have hlo' : a ≤ randQuantile (G n) (T n) p x := by
      refine le_csInf ⟨b, hrdb⟩ (fun s hs => ?_)
      simp only [Set.mem_setOf_eq] at hs
      by_contra hcon
      push_neg at hcon
      exact absurd (le_trans hs (randDist_mono (G n) (T n) x hcon.le)) (not_le.mpr hrda)
    have hcontra : |randQuantile (G n) (T n) p x - q| < ε := by
      rw [abs_lt]
      exact ⟨by linarith [ha_mem.1], by linarith [hb_mem.2]⟩
    linarith
  refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_)
    (by simpa only [add_zero] using hAa.add hBb)
  calc (P n).real {x | ε ≤ |randQuantile (G n) (T n) p x - q|}
      ≤ (P n).real ({x | p - cdf R a ≤ |randDist (G n) (T n) x a - cdf R a|} ∪
          {x | cdf R b - p ≤ |randDist (G n) (T n) x b - cdf R b|}) := measureReal_mono (hincl n)
    _ ≤ _ := measureReal_union_le _ _

/-- **The randomization critical value converges in probability.** Under the same joint
condition, if the limit c.d.f. is continuous and strictly increasing at its
$(1-\alpha)$-quantile, then
$$ \hat r_n(1-\alpha) \;\xrightarrow{P}\; r(1-\alpha) = \inf\{t : R(t) \ge 1-\alpha\} . $$
-/
theorem randQuantile_tendstoInProb (P : ∀ n, Measure (𝓧 n))
    [∀ n, IsProbabilityMeasure (P n)] (T : ∀ n, 𝓧 n → ℝ) (R : Measure ℝ)
    [IsProbabilityMeasure R]
    -- USER-INPUT: the statistic is measurable (data regularity); see
    -- `randDist_tendstoInProb_cdf` for why this is not derivable from the other hypotheses
    (hT : ∀ n, Measurable (T n))
    -- USER-INPUT: the group acts measurably (data regularity); same reason
    (hsmul : ∀ (n : ℕ) (g : G n), Measurable (fun x : 𝓧 n => g • x))
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
      (cdfQuantile R (1 - α)) :=
  -- The bracketing/quantile-transfer argument uses only `hα₁` and `hstrict`, not `hcont`.
  randQuantile_tendstoInProb_aux P T R hT hsmul hjoint hα₁ hstrict

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
  -- TODO (genuine gap, deferred). The intended route: convergence in probability of the random
  -- CDF at continuity points `s, t`, together with boundedness in `[0,1]`, gives (bounded
  -- convergence) `∫ R̂ₙ(s)·R̂ₙ(t) dP → R(s)R(t)`; the left side equals
  -- `randPairLaw(Iic s ×ˢ Iic t)` by a cross-moment identity generalising
  -- `integral_randDist_sq_eq_real_randPairLaw`. This yields convergence of the joint c.d.f. at
  -- every continuity-point rectangle. Upgrading that to weak convergence needs a
  -- convergence-determining-class argument (the rectangles form a π-system, but Mathlib's
  -- `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem` demands convergence on the *whole*
  -- π-system, whereas we only control continuity-point rectangles — the standard right-continuity
  -- patch is not yet formalised). The proof also needs the same measurability of `T n`/action as
  -- the forward direction, which the frozen signature omits. See the accompanying report.
  sorry

end Asymptotics

end StatLean.HypothesisTesting
