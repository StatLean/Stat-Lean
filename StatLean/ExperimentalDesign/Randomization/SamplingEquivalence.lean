import StatLean.ExperimentalDesign.Randomization.CompleteRandomization
import StatLean.ExperimentalDesign.SurveySampling.SimpleRandomSampling

/-!
# Each arm of a completely randomised design is a simple random sample

The organising theorem of the finite randomisation machinery: under the completely
randomised design with replications `r`, the arm of any fixed treatment `t` is
distributed exactly as a simple random sample of size `r t` — the pushforward
identity
$$(\operatorname{arm}_t)_* D_r = \operatorname{SRS}(r_t).$$
Consequently every arm-statistic moment is inherited from the sampling theory: the
arm mean of a deterministic population quantity `y` is design-unbiased for the
population mean, with the exact finite-population variance
$$\mathbb E[\bar y_t] = \bar y, \qquad
  \operatorname{Var}(\bar y_t)
    = \Bigl(1 - \frac{r_t}{N}\Bigr)\frac{S_y^2}{r_t}.$$
These statements deliberately do not mention potential outcomes: the causal
randomised-experiment theorems are obtained downstream by instantiating `y` at each
potential-outcome function.

## Main results

* `completeRandomization_map_arm` — the pushforward identity.
* `expect_armMean` — design unbiasedness of the arm mean.
* `var_armMean` — exact arm-mean variance with finite-population correction.

**Reference.** R. Mead, *The Design of Experiments*, CUP, 1988, §9.2 and §9.6: "the
random allocation may be achieved either by allocating units to treatments or by
selecting a unit for a particular treatment" — selecting the units for one treatment
uniformly (as in Example 9.3, four mice of twenty) *is* simple random sampling; the
equal-probability requirement of §9.6 is the marginal of the present identity.
(`Mead §9.2`, `Mead §9.6`, `Mead §9.3`.)

**Proof formalization notes.**
* Route for the pushforward identity: both sides are uniform laws.  The map
  `arm t : 𝒜_r → {S : |S| = r_t}` intertwines the permutation actions
  (`arm t (a ∘ σ⁻¹) = σ '' arm t a`), the source law is permutation invariant
  (`completeRandomization_map_precomp`), the action on `r_t`-subsets is transitive,
  and an invariant PMF under a transitive action on a finite set is uniform on it.
  Alternatively, count fibers directly: allocations with `arm t a = S` biject with
  valid allocations of `r` restricted to `U \ S` over `T \ {t}`, a count independent
  of `S`.
* The moment corollaries are three-line transfers:
  `armMean_eq_sampleMean_arm` + `pmfExpect_map` + the SRS moment theorems.
-/

namespace StatLean.ExperimentalDesign

variable {U T : Type*} [Fintype U] [DecidableEq U] [Fintype T] [DecidableEq T]

/-- **Arms of a completely randomised design are simple random samples**: the
pushforward of the design under `a ↦ arm t a` is SRSWOR of size `r t`
(`Mead §9.2`/`§9.6`). -/
theorem completeRandomization_map_arm (r : T → ℕ)
    (hr : ∑ t, r t = Fintype.card U) (t : T) :
    (completeRandomization r hr).map (arm t)
      = simpleRandomSampling (r t) (replication_le_card r hr t) := by
  sorry

/-- **Design unbiasedness of the arm mean**: for a treatment with positive
replication, the arm mean of a deterministic quantity `y` has design expectation the
population mean (`Mead §9.4`, the finite model; no potential outcomes involved). -/
theorem expect_armMean (r : T → ℕ) (hr : ∑ t, r t = Fintype.card U) (t : T)
    -- USER-INPUT: positive replication of the arm, so its mean is well defined; Mead §6.2
    (ht : r t ≠ 0) (y : U → ℝ) :
    pmfExpect (completeRandomization r hr) (armMean y t) = populationMean y := by
  sorry

/-- **Exact design variance of the arm mean with finite-population correction**:
`Var(ȳ_t) = (1 − r_t/N) S²_y / r_t` (`Mead §9.4`; the completely-randomised analogue
of Mead's blocked variance computation). -/
theorem var_armMean (r : T → ℕ) (hr : ∑ t, r t = Fintype.card U) (t : T)
    -- USER-INPUT: positive replication of the arm, so its mean is well defined; Mead §6.2
    (ht : r t ≠ 0) (y : U → ℝ) :
    pmfVar (completeRandomization r hr) (armMean y t)
      = (1 - (r t : ℝ) / (Fintype.card U : ℝ)) * populationVariance y / (r t : ℝ) := by
  sorry

end StatLean.ExperimentalDesign
