import StatLean.HypothesisTesting.Randomization.Defs
import StatLean.MultipleTesting.PValues.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Exact finite-sample level of the randomization test

Let a finite group $\mathbf{G}$ of transformations act on the sample space, write
$M = |\mathbf{G}|$, and let $T$ be an arbitrary real-valued test statistic. Order the
orbit values $T^{(1)}(x) \le \cdots \le T^{(M)}(x)$ of $T(gx)$ as $g$ ranges over
$\mathbf{G}$, put $k = M - \lfloor M\alpha \rfloor$, and let $M^{+}(x)$ and $M^{0}(x)$
count the orbit values strictly above, resp. equal to, the critical value $T^{(k)}(x)$.
The randomization test rejects when $T(x) > T^{(k)}(x)$, accepts when
$T(x) < T^{(k)}(x)$, and rejects with probability
$a(x) = (M\alpha - M^{+}(x)) / M^{0}(x)$ on the boundary.

This file proves the two facts that make the construction work:

* the **pointwise orbit identity** $\sum_{g \in \mathbf{G}} \phi(gx) = M\alpha$, valid for
  *every* $x$ and *every* statistic $T$ — no distributional assumption whatsoever;
* the **exactness theorem**: if the null law is invariant under $\mathbf{G}$ (the
  randomization hypothesis), then $E_P[\phi(X)] = \alpha$ exactly, at every finite sample
  size.

It also records the companion **super-uniformity** of the randomization $p$-value
$\hat p(x) = M^{-1}\#\{g : T(gx) \ge T(x)\}$, so that the nonrandomized test rejecting
when $\hat p \le \alpha$ has level $\alpha$.

**Reference.** Classical randomization/permutation testing; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* *No integrality caveat.* The orbit identity is exact for every $x$: the boundary weight
  $a(x)$ is *defined* so that $M^{+}(x) + a(x)M^{0}(x) = M\alpha$, so nothing is assumed
  about $M\alpha$ being an integer. What the construction does need — and what the level
  restriction $0 < \alpha < 1$ supplies — is that the critical index
  $k = M - \lfloor M\alpha \rfloor$ lands in $\{1, \dots, M\}$, keeping
  `randCritValue` off the junk branch of `orbitOrderStat`; and $M^{0}(x) \ge 1$ always
  (the critical value is attained by at least one group element), so `randGamma` never
  evaluates $0/0$. Both are consequences of the definitions, not extra hypotheses, but
  they are the reason the identity is stated with `0 < α` and `α < 1` in scope.
* The identity is what forces $0 \le a(x) \le 1$, hence `randTest` really is a critical
  function: $M^{+}(x) \le M - k = \lfloor M\alpha \rfloor \le M\alpha$ gives
  $a(x) \ge 0$, and $M^{+}(x) + M^{0}(x) \ge \lfloor M\alpha \rfloor + 1 > M\alpha$ gives
  $a(x) \le 1$. This is isolated as `randTest_mem_Icc`.
* The exactness proof is the averaging argument: integrate the orbit identity, exchange
  the finite sum with the integral, and use the randomization hypothesis to replace each
  $E_P[\phi(gX)]$ by $E_P[\phi(X)]$; the group-invariance lemmas
  `randCritValue_smul`, `randPlusCount_smul`, `randZeroCount_smul`, `randGamma_smul`
  are what make the orbit data constant along orbits.
* Measurability of the action enters as an explicit hypothesis rather than a
  `MeasurableSMul` instance: the group action is user-supplied data, so its measurability
  is a genuine external input and is kept visible in the signature.
* Super-uniformity is stated in the library's `SuperUniform` form, i.e. for all
  $t \ge 0$. The substantive content is the range $0 \le t \le 1$; for $t > 1$ the bound
  is trivial since the measure is a probability measure.

**Bibliographic comments.** Randomization tests originate with R. A. Fisher (*The Design
of Experiments*, Oliver & Boyd, Edinburgh, 1935) and E. J. G. Pitman ("Significance tests
which may be applied to samples from any populations," *J. R. Statist. Soc. Suppl.* **4**
(1937), 119–130). The group-theoretic formulation and the exact-level property are due to
E. L. Lehmann and C. Stein ("On the theory of some non-parametric hypotheses," *Ann. Math.
Statist.* **20** (1949), 28–45); the modification allowing a random subset of the group is
M. Dwass ("Modified randomization tests for nonparametric hypotheses," *Ann. Math.
Statist.* **28** (1957), 181–187). Large-sample behaviour of permutation tests was opened
up by W. Hoeffding ("The large-sample power of tests based on permutations of
observations," *Ann. Math. Statist.* **23** (1952), 169–192), and the modern robustness
theory by J. P. Romano ("Bootstrap and randomization tests of some nonparametric
hypotheses," *Ann. Statist.* **17** (1989), 141–159; "On the behavior of randomization
tests without a group invariance assumption," *J. Amer. Statist. Assoc.* **85** (1990),
686–692) and E. Chung and J. P. Romano ("Exact and asymptotically robust permutation
tests," *Ann. Statist.* **41** (2013), 484–507).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.MultipleTesting (SuperUniform)

variable {G : Type*} [Group G] [Fintype G] {𝓧 : Type*} [MeasurableSpace 𝓧]
  [MulAction G 𝓧]

open StatLean.MultipleTesting (orderStat)

/-! ### Private helpers: order statistics along orbits -/

/-- Translating `x` by `g` reindexes the orbit tuple by right multiplication: it is the same
tuple up to the permutation `i ↦ equivFin (equivFin⁻¹ i * g)` of `Fin |G|`. -/
private lemma orbitValues_smul (T : 𝓧 → ℝ) (g : G) (x : 𝓧) :
    orbitValues G T (g • x)
      = orbitValues G T x ∘ ((Fintype.equivFin G).symm.trans
          ((Equiv.mulRight g).trans (Fintype.equivFin G))) := by
  funext i
  simp only [orbitValues, Function.comp_apply, Equiv.trans_apply, Equiv.coe_mulRight,
    Equiv.symm_apply_apply, mul_smul]

/-- Every orbit order statistic is constant along orbits. -/
private lemma orbitOrderStat_smul (T : 𝓧 → ℝ) (g : G) (x : 𝓧) (j : ℕ) :
    orbitOrderStat G T (g • x) j = orbitOrderStat G T x j := by
  unfold orbitOrderStat
  by_cases h : j - 1 < Fintype.card G
  · rw [dif_pos h, dif_pos h, orbitValues_smul T g x]
    exact congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f := orbitValues G T x)
      (σ := (Fintype.equivFin G).symm.trans ((Equiv.mulRight g).trans (Fintype.equivFin G)))) _
  · rw [dif_neg h, dif_neg h]

/-- Reindexing a filtered count over `G` by right multiplication leaves the count unchanged. -/
private lemma card_filter_mulRight (q : G → Prop) [DecidablePred q] (g : G) :
    (Finset.univ.filter fun h : G => q (h * g)).card
      = (Finset.univ.filter fun h : G => q h).card := by
  refine Finset.card_bij' (fun h _ => h * g) (fun h _ => h * g⁻¹) ?_ ?_ ?_ ?_
  · intro h hh
    rw [Finset.mem_filter] at hh ⊢
    exact ⟨Finset.mem_univ _, hh.2⟩
  · intro h hh
    rw [Finset.mem_filter] at hh ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [inv_mul_cancel_right]; exact hh.2
  · intro h _; simp
  · intro h _; simp

/-! ### The orbit data is constant along orbits -/

/-- The critical orbit value is **constant along orbits**: `T^{(k)}(gx) = T^{(k)}(x)`.
Translating `x` by `g` permutes the orbit `{T(hx) : h ∈ G}`, hence leaves its order
statistics unchanged. -/
theorem randCritValue_smul (T : 𝓧 → ℝ) (α : ℝ) (g : G) (x : 𝓧) :
    randCritValue G T α (g • x) = randCritValue G T α x := by
  unfold randCritValue
  exact orbitOrderStat_smul T g x (randCritIndex G α)

/-- `M⁺` is constant along orbits. -/
theorem randPlusCount_smul (T : 𝓧 → ℝ) (α : ℝ) (g : G) (x : 𝓧) :
    randPlusCount G T α (g • x) = randPlusCount G T α x := by
  unfold randPlusCount
  rw [randCritValue_smul]
  simp only [← mul_smul]
  exact card_filter_mulRight (fun h => randCritValue G T α x < T (h • x)) g

/-- `M⁰` is constant along orbits. -/
theorem randZeroCount_smul (T : 𝓧 → ℝ) (α : ℝ) (g : G) (x : 𝓧) :
    randZeroCount G T α (g • x) = randZeroCount G T α x := by
  unfold randZeroCount
  rw [randCritValue_smul]
  simp only [← mul_smul]
  exact card_filter_mulRight (fun h => T (h • x) = randCritValue G T α x) g

/-- The boundary-randomization weight `a(·)` is constant along orbits. -/
theorem randGamma_smul (T : 𝓧 → ℝ) (α : ℝ) (g : G) (x : 𝓧) :
    randGamma G T α (g • x) = randGamma G T α x := by
  unfold randGamma
  rw [randPlusCount_smul, randZeroCount_smul]

/-! ### The pointwise orbit identity and exactness -/

/-- **The randomization test is a critical function**: `0 ≤ φ ≤ 1` pointwise. The only
non-obvious case is the boundary, where `0 ≤ a(x) ≤ 1` follows from
`M⁺(x) ≤ ⌊Mα⌋ ≤ Mα` and `Mα < ⌊Mα⌋ + 1 ≤ M⁺(x) + M⁰(x)`. -/
theorem randTest_mem_Icc (T : 𝓧 → ℝ) {α : ℝ}
    -- USER-INPUT: nominal level strictly between `0` and `1`; the calibration range
    (hα₀ : 0 < α) (hα₁ : α < 1) (x : 𝓧) :
    randTest G T α x ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- **Pointwise orbit identity.** Summing the randomization test over the orbit of any
point returns exactly `M·α`:
$$ \sum_{g \in \mathbf{G}} \phi(gx) \;=\; M^{+}(x) + a(x)\,M^{0}(x) \;=\; M\alpha . $$
This holds for *every* `x`, for *every* test statistic `T`, and with no assumption on the
data-generating law — it is a counting identity, and it is the engine behind exactness.
There is deliberately **no integrality condition** on `M·α`: the weight `a(x)` absorbs the
fractional part by construction. -/
theorem sum_randTest_orbit (T : 𝓧 → ℝ) {α : ℝ}
    -- USER-INPUT: nominal level strictly between `0` and `1`; the calibration range
    (hα₀ : 0 < α) (hα₁ : α < 1) (x : 𝓧) :
    ∑ g : G, randTest G T α (g • x) = (Fintype.card G : ℝ) * α := by
  sorry

/-- **Exact level of the randomization test.** Under the randomization hypothesis — the
null law `P` is invariant under every element of the finite group `G` — the randomization
test built from an arbitrary statistic `T` has size exactly `α` at every finite sample
size:
$$ E_P[\phi(X)] = \alpha . $$
Averaging the pointwise orbit identity over `P` gives `Mα = ∑_g E_P[φ(gX)]`, and
invariance turns every summand into `E_P[φ(X)]`. -/
theorem randTest_exact_level (P : Measure 𝓧) [IsProbabilityMeasure P] (T : 𝓧 → ℝ)
    -- USER-INPUT: the test statistic is measurable; user-supplied statistic
    (hT : Measurable T)
    -- USER-INPUT: the group acts measurably; the action is user-supplied data
    (hsmul : ∀ g : G, Measurable (fun x : 𝓧 => g • x))
    -- USER-INPUT: the null law is `G`-invariant; the randomization hypothesis
    (hrand : RandomizationHypothesis G P)
    {α : ℝ}
    -- USER-INPUT: nominal level strictly between `0` and `1`; the calibration range
    (hα₀ : 0 < α) (hα₁ : α < 1) :
    powerAgainst P (randTest G T α) = α := by
  sorry

/-! ### The randomization `p`-value -/

/-- **Super-uniformity of the randomization `p`-value.** Under the randomization
hypothesis,
$$ P\{\hat p(X) \le u\} \;\le\; u \qquad \text{for all } 0 \le u \le 1 , $$
so the nonrandomized test that rejects when `p̂ ≤ α` has level `α`. Stated in the
library's `SuperUniform` form (all `t ≥ 0`); the range `t > 1` is vacuous because `P` is a
probability measure. -/
theorem superUniform_randPValue (P : Measure 𝓧) [IsProbabilityMeasure P] (T : 𝓧 → ℝ)
    -- USER-INPUT: the test statistic is measurable; user-supplied statistic
    (hT : Measurable T)
    -- USER-INPUT: the group acts measurably; the action is user-supplied data
    (hsmul : ∀ g : G, Measurable (fun x : 𝓧 => g • x))
    -- USER-INPUT: the null law is `G`-invariant; the randomization hypothesis
    (hrand : RandomizationHypothesis G P) :
    SuperUniform (randPValue G T) P := by
  sorry

end StatLean.HypothesisTesting
