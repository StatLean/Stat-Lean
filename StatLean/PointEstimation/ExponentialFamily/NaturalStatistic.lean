import StatLean.PointEstimation.ExponentialFamily.Defs
import Mathlib.Probability.Notation

/-!
# The natural statistic of an exponential family is itself exponentially distributed

If `X` follows an exponential family with natural statistic `T`, then `T(X)` follows an
exponential family on the statistic's own scale, with the *identity* as natural statistic, the
push-forward of the reference measure as reference measure, and the *same* log-partition
function:
$$ \frac{dP^T_\eta}{d(\nu \circ T^{-1})}(t)
   \;=\; \exp\bigl(\langle \eta, t\rangle - A(\eta)\bigr). $$
This is why all inference about `η` may be carried out on the statistic's scale, and it is
the reduction under which completeness of `T` is proved.

* `ExpFamily.statFamily` — the exponential family carried by the natural statistic;
* `ExpFamily.map_stat_P` — the law of `T` under `P_η` is the corresponding member;
* `ExpFamily.natSet_statFamily` — the two families share their natural parameter set;
* `ExpFamily.logPartition_statFamily` — and their log-partition function.

**Reference.** Classical exponential-family theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* `map_stat_P` is stated for **every** `η`, not only for natural parameters: off the natural
  parameter set both sides are the zero measure, since `natSet_statFamily` shows the two
  families become undefined simultaneously. Keeping the statement unconditional means
  consumers never carry a membership side condition through a push-forward.
* The proof is the observation that the tilting density `x ↦ exp⟨η, T x⟩` factors through `T`,
  so tilting commutes with the push-forward along `T`: on a measurable set `S`,
  `∫_{T⁻¹S} exp⟨η, T x⟩ dν = ∫_S exp⟨η, t⟩ d(ν ∘ T⁻¹)` by `setLIntegral_map`, and the two
  normalizers agree for the same reason — which is exactly `logPartition_statFamily`.
* Combining `map_stat_P` with the i.i.d. product family `ExpFamily.pow` of
  `ExponentialFamily.Basic` gives the classical corollary that a sum `∑ᵢ T(Xᵢ)` of
  independent natural statistics from a common one-parameter family is again exponentially
  distributed: apply `map_stat_P` to `E.pow n`, whose natural statistic is that sum.

**Bibliographic comments.** That the natural statistic of an exponential family is itself
exponentially distributed, and that the class is therefore closed under convolution of
independent components, is part of the classical theory: R. A. Fisher ("Two new properties of
mathematical likelihood," *Proc. R. Soc. Lond. A* **144** (1934), 285–307), G. Darmois ("Sur
les lois de probabilité à estimation exhaustive," *C. R. Acad. Sci. Paris* **200** (1935),
1265–1266), B. O. Koopman ("On distributions admitting a sufficient statistic," *Trans. Amer.
Math. Soc.* **39** (1936), 399–409), E. J. G. Pitman ("Sufficient statistics and intrinsic
accuracy," *Proc. Camb. Phil. Soc.* **32** (1936), 567–579); see also O. Barndorff-Nielsen
(*Information and Exponential Families in Statistical Theory*, Wiley, 1978, Ch. 8).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

namespace ExpFamily

/-- The **exponential family carried by the natural statistic**: the reference measure is the
push-forward of `E.base` along `E.stat`, and the natural statistic is the identity. The
members of this family are the laws of `E.stat` under the members of `E`
(`ExpFamily.map_stat_P`). -/
noncomputable def statFamily (E : ExpFamily 𝓧 V) : ExpFamily V V :=
  ⟨E.base.map E.stat, id, measurable_id⟩

variable [OpensMeasurableSpace V]

/-- **The natural statistic is exponentially distributed**: the law of `T` under `P_η` is the
member of the statistic's own exponential family at the same natural parameter. -/
theorem map_stat_P (E : ExpFamily 𝓧 V) (η : V) :
    (E.P η).map E.stat = E.statFamily.P η := by
  sorry

/-- The two families have the **same natural parameter set**. -/
theorem natSet_statFamily (E : ExpFamily 𝓧 V) : E.statFamily.natSet = E.natSet := by
  sorry

/-- The two families have the **same log-partition function**: the density of the law of `T`
is `exp(⟨η, t⟩ − A(η))` with the *original* `A`. -/
theorem logPartition_statFamily (E : ExpFamily 𝓧 V) :
    E.statFamily.logPartition = E.logPartition := by
  sorry

end ExpFamily

end StatLean.PointEstimation
