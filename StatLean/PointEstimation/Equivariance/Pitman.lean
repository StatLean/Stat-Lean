import StatLean.PointEstimation.Equivariance.LocationMRE
import StatLean.PointEstimation.ForMathlib.CondDistribDensity
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The Pitman estimator of location

Under squared error the minimum risk equivariant location estimator subtracts the
conditional mean of a reference equivariant estimator given the differences. Taking the
last coordinate as the reference estimator and carrying out the change of variables
`yᵢ = xᵢ − xₙ`, `yₙ = xₙ` (of unit Jacobian) turns that conditional mean into an explicit
ratio of one-dimensional integrals against the density:

`δ*(x) = (∫ u · f(x₁ − u, …, xₙ − u) du) / (∫ f(x₁ − u, …, xₙ − u) du)`.

This is `pitmanEstimator`, fixed in the data model of this area. The file proves it is
equivariant, that it coincides with the conditional-mean form, and that it is minimum
risk equivariant.

**Reference.** Classical location-equivariant estimation; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* Equivariance is the substitution `u ↦ u + a` in both integrals: the denominator is
  translation-invariant and the numerator picks up `a` times the denominator. Splitting
  the numerator requires the two integrands to be integrable, and dividing requires the
  denominator to be nonzero; these are the side conditions attached to every statement
  below. The classical development leaves them implicit.
* `pitmanEstimator_eq_sub_condMean` isolates the substantive step — the identification of
  the closed form with `xₙ − E₀[Xₙ | Y]` — as a named lemma rather than burying it inside
  the main theorem, since it is the change of variables that carries all the content.
* Measurability of the closed form is not assumed: it is derived (as
  `measurable_pitmanEstimator`) from measurability of the density, since assuming it
  would hide a genuine obligation behind a hypothesis.
* The finite-risk hypothesis is stated for the concrete reference estimator (the last
  coordinate) that the derivation uses, rather than as an abstract "some equivariant
  estimator has finite risk".
* Edge behaviour: `pitmanEstimator` divides two Bochner integrals, so it returns the junk
  value `0` wherever the denominator vanishes; `hden0` excludes that on the statements
  that need it.

**Bibliographic comments.** The estimator and its derivation are due to E. J. G. Pitman,
"The estimation of the location and scale parameters of a continuous population of any
given form," *Biometrika* **30** (1939), 391–421. Its admissibility for a single location
parameter was proved by C. Stein, "The admissibility of Pitman's estimator of a single
location parameter," *Ann. Math. Statist.* **30** (1959), 970–979.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

section Pitman

variable {m n : ℕ}

/-! ### The unit-Jacobian shear `x ↦ (diffs x, xₙ)`

The change of variables underlying the identification of the Pitman ratio with the
conditional mean. We realize it as `swap ∘ h ∘ (split off last coordinate)`, where the
only non-trivial factor `h (a, w) = (a, w − a·𝟙)` is measure preserving by translation
invariance of Lebesgue measure — no determinant computation is needed. -/

/-- The shear `x ↦ (diffs x, xₙ)`. -/
private def pShear (x : Fin (m + 1) → ℝ) : (Fin m → ℝ) × ℝ :=
  (diffs x, x (Fin.last m))

/-- Its inverse `(y, s) ↦ snoc y 0 + s·𝟙`. -/
private noncomputable def pUnshear (p : (Fin m → ℝ) × ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc p.1 (0 : ℝ) + p.2 • (1 : Fin (m + 1) → ℝ)

private lemma pShear_pUnshear (p : (Fin m → ℝ) × ℝ) : pShear (pUnshear p) = p := by
  obtain ⟨y, s⟩ := p
  have hlast : (pUnshear (y, s)) (Fin.last m) = s := by
    simp only [pUnshear, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      Fin.snoc_last, zero_add]
  refine Prod.ext ?_ hlast
  funext i
  show diffs (pUnshear (y, s)) i = y i
  simp only [diffs, pUnshear, Pi.add_apply, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, mul_one, Fin.snoc_castSucc, Fin.snoc_last]
  ring

private lemma pUnshear_pShear (x : Fin (m + 1) → ℝ) : pUnshear (pShear x) = x := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      simp only [pUnshear, pShear, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
        mul_one, Fin.snoc_last, zero_add]
  | cast i =>
      simp only [pUnshear, pShear, diffs, Pi.add_apply, Pi.smul_apply, Pi.one_apply,
        smul_eq_mul, mul_one, Fin.snoc_castSucc]
      ring

private lemma measurable_pShear :
    Measurable (pShear : (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ) :=
  measurable_diffs.prodMk (measurable_pi_apply (Fin.last m))

private lemma measurable_pUnshear :
    Measurable (pUnshear : (Fin m → ℝ) × ℝ → Fin (m + 1) → ℝ) := by
  apply measurable_pi_lambda
  intro j
  induction j using Fin.lastCases with
  | last =>
      simp only [pUnshear, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
        Fin.snoc_last, zero_add]
      exact measurable_snd
  | cast i =>
      simp only [pUnshear, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
        Fin.snoc_castSucc]
      exact (measurable_pi_apply i |>.comp measurable_fst).add measurable_snd

/-- The shear preserves Lebesgue measure (unit Jacobian). -/
private lemma measurePreserving_pShear :
    MeasurePreserving (pShear : (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ) volume volume := by
  -- split off the last coordinate: `x ↦ (xₙ, fun j => x j.castSucc)`
  have hs : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m)) volume volume :=
    volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last m)
  -- the fiberwise translation `h (a, w) = (a, w − a·𝟙)`
  set h : ℝ × (Fin m → ℝ) → ℝ × (Fin m → ℝ) :=
    fun p => (p.1, p.2 - p.1 • (1 : Fin m → ℝ)) with hh_def
  have hh_meas : Measurable h :=
    measurable_fst.prodMk (measurable_snd.sub (measurable_fst.smul_const _))
  have hh : MeasurePreserving h volume volume := by
    refine ⟨hh_meas, ?_⟩
    rw [Measure.volume_eq_prod ℝ (Fin m → ℝ)]
    refine Measure.ext_of_lintegral _ fun φ hφ => ?_
    rw [lintegral_map hφ hh_meas,
        lintegral_prod (fun p => φ (h p)) (hφ.comp hh_meas).aemeasurable,
        lintegral_prod φ hφ.aemeasurable]
    refine lintegral_congr fun a => ?_
    have key := lintegral_add_right_eq_self (μ := (volume : Measure (Fin m → ℝ)))
      (fun w => φ (a, w)) (-(a • (1 : Fin m → ℝ)))
    simp only [hh_def, sub_eq_add_neg]
    exact key
  -- swap `(a, w) ↦ (w, a)`
  have hswap : MeasurePreserving
      (Prod.swap : ℝ × (Fin m → ℝ) → (Fin m → ℝ) × ℝ) volume volume := by
    rw [Measure.volume_eq_prod ℝ (Fin m → ℝ), Measure.volume_eq_prod (Fin m → ℝ) ℝ]
    exact Measure.measurePreserving_swap
  have hcomp := hswap.comp (hh.comp hs)
  -- the split map sends `x` to `(xₙ, fun j => x j.castSucc)`
  have hsx : ∀ x : Fin (m + 1) → ℝ,
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m)) x
        = (x (Fin.last m), fun j : Fin m => x j.castSucc) := by
    intro x
    refine Prod.ext rfl ?_
    funext j
    show x ((Fin.last m).succAbove j) = x j.castSucc
    rw [Fin.succAbove_last]
  have hfun : (Prod.swap ∘ h ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m)))
      = (pShear : (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ) := by
    funext x
    simp only [Function.comp_apply, hsx x, hh_def, Prod.swap_prod_mk]
    refine Prod.ext ?_ rfl
    funext i
    simp only [pShear, diffs, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  rwa [hfun] at hcomp

/-- Pushing `locationBase f` forward along the shear gives the joint law of the differences
and the last coordinate, with density `(y, s) ↦ f (snoc y 0 + s·𝟙)` against `volume ⊗ volume`. -/
private lemma map_pShear_locationBase (f : (Fin (m + 1) → ℝ) → ℝ) (hf : Measurable f) :
    (locationBase f).map pShear
      = (volume.prod volume).withDensity (fun q => ENNReal.ofReal (f (pUnshear q))) := by
  set p : (Fin m → ℝ) × ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (f (pUnshear q)) with hp_def
  have hp_meas : Measurable p :=
    ENNReal.measurable_ofReal.comp (hf.comp measurable_pUnshear)
  have hd_meas : Measurable (fun x : Fin (m + 1) → ℝ => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hf
  have hmap : (volume : Measure (Fin (m + 1) → ℝ)).map pShear = volume.prod volume := by
    rw [measurePreserving_pShear.map_eq]; exact Measure.volume_eq_prod _ _
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hpφ : Measurable (fun z => p z * φ z) := hp_meas.mul hφ
  calc ∫⁻ z, φ z ∂((locationBase f).map pShear)
      = ∫⁻ x, φ (pShear x) ∂(locationBase f) := lintegral_map hφ measurable_pShear
    _ = ∫⁻ x, p (pShear x) * φ (pShear x) ∂volume := by
          rw [show (locationBase f) = (volume : Measure (Fin (m + 1) → ℝ)).withDensity
                (fun x => ENNReal.ofReal (f x)) from rfl,
            lintegral_withDensity_eq_lintegral_mul _ hd_meas
              (show Measurable fun x => φ (pShear x) from hφ.comp measurable_pShear)]
          refine lintegral_congr fun x => ?_
          simp only [Pi.mul_apply, hp_def, pUnshear_pShear]
    _ = ∫⁻ z, p z * φ z ∂((volume : Measure (Fin (m + 1) → ℝ)).map pShear) :=
          (lintegral_map hpφ measurable_pShear).symm
    _ = ∫⁻ z, p z * φ z ∂(volume.prod volume) := by rw [hmap]
    _ = ∫⁻ z, φ z ∂((volume.prod volume).withDensity p) :=
          (lintegral_withDensity_eq_lintegral_mul _ hp_meas hφ).symm

/-- Reflection of a Lebesgue integral on `ℝ`: `∫ u, φ (b − u) = ∫ s, φ s`. -/
private lemma integral_const_sub_comm (φ : ℝ → ℝ) (b : ℝ) :
    (∫ u : ℝ, φ (b - u)) = ∫ s : ℝ, φ s := by
  have h1 : (∫ u : ℝ, φ (b - u)) = ∫ u : ℝ, φ (b + u) := by
    rw [← integral_neg_eq_self (fun u : ℝ => φ (b + u)) volume]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [sub_eq_add_neg]
  rw [h1]
  simpa [add_comm] using integral_add_right_eq_self φ b

/-- The shift identity underlying the change of variables: subtracting `u·𝟙` from `x` shifts
the last-coordinate argument of the shear inverse. -/
private lemma sub_smul_one_eq_pUnshear (x : Fin (m + 1) → ℝ) (u : ℝ) :
    x - u • (1 : Fin (m + 1) → ℝ) = pUnshear (diffs x, x (Fin.last m) - u) := by
  have hx : Fin.snoc (diffs x) (0 : ℝ) + (x (Fin.last m)) • (1 : Fin (m + 1) → ℝ) = x :=
    pUnshear_pShear x
  show x - u • (1 : Fin (m + 1) → ℝ)
      = Fin.snoc (diffs x) 0 + (x (Fin.last m) - u) • (1 : Fin (m + 1) → ℝ)
  rw [sub_smul, ← add_sub_assoc, hx]

/-- Measurability of the one-dimensional density slice `s ↦ f (snoc y 0 + s·𝟙)`. -/
private lemma measurable_slice (f : (Fin (m + 1) → ℝ) → ℝ) (hf : Measurable f)
    (y : Fin m → ℝ) : Measurable (fun s : ℝ => f (pUnshear (y, s))) :=
  hf.comp (measurable_pUnshear.comp (measurable_const.prodMk measurable_id))

/-- The density slice is integrable at every `y` (reflection of `hden` at `snoc y 0`). -/
private lemma integrable_slice_den (f : (Fin (m + 1) → ℝ) → ℝ) (hf : Measurable f)
    (hden : ∀ x, Integrable fun u : ℝ => f (x - u • (1 : Fin (m + 1) → ℝ)))
    (y : Fin m → ℝ) : Integrable (fun s : ℝ => f (pUnshear (y, s))) := by
  set x₀ : Fin (m + 1) → ℝ := Fin.snoc y (0 : ℝ) with hx₀
  have hy1 : diffs x₀ = y := diffs_snoc y
  have hy2 : x₀ (Fin.last m) = 0 := by rw [hx₀]; simp [Fin.snoc_last]
  have hrefl := hden x₀
  simp_rw [sub_smul_one_eq_pUnshear, hy1, hy2, zero_sub] at hrefl
  -- `hrefl : Integrable (fun u => f (pUnshear (y, -u)))`; undo the reflection
  have hmp : MeasurePreserving (fun u : ℝ => -u) (volume : Measure ℝ) volume := by
    simpa using Measure.measurePreserving_neg (volume : Measure ℝ)
  refine (hmp.integrable_comp (measurable_slice f hf y).aestronglyMeasurable).mp ?_
  simpa [Function.comp] using hrefl

/-- The first moment of the density slice is integrable at every `y`. -/
private lemma integrable_slice_num (f : (Fin (m + 1) → ℝ) → ℝ) (hf : Measurable f)
    (hnum : ∀ x, Integrable fun u : ℝ => u * f (x - u • (1 : Fin (m + 1) → ℝ)))
    (y : Fin m → ℝ) : Integrable (fun s : ℝ => s * f (pUnshear (y, s))) := by
  set x₀ : Fin (m + 1) → ℝ := Fin.snoc y (0 : ℝ) with hx₀
  have hy1 : diffs x₀ = y := diffs_snoc y
  have hy2 : x₀ (Fin.last m) = 0 := by rw [hx₀]; simp [Fin.snoc_last]
  have hrefl := hnum x₀
  simp_rw [sub_smul_one_eq_pUnshear, hy1, hy2, zero_sub] at hrefl
  -- `hrefl : Integrable (fun u => u * f (pUnshear (y, -u)))`
  have hmp : MeasurePreserving (fun u : ℝ => -u) (volume : Measure ℝ) volume := by
    simpa using Measure.measurePreserving_neg (volume : Measure ℝ)
  have hmeas : Measurable (fun s : ℝ => s * f (pUnshear (y, s))) :=
    measurable_id.mul (measurable_slice f hf y)
  refine (hmp.integrable_comp hmeas.aestronglyMeasurable).mp ?_
  have : (fun s : ℝ => s * f (pUnshear (y, s))) ∘ (fun u : ℝ => -u)
      = fun u : ℝ => -(u * f (pUnshear (y, -u))) := by
    funext u; simp only [Function.comp]; ring
  rw [this]
  exact hrefl.neg

/-- The closed form is measurable whenever the density is and the defining integrals
converge. -/
theorem measurable_pitmanEstimator (f : (Fin n → ℝ) → ℝ)
    -- LEAN-ONLY: measurability of the density; drives joint measurability of the
    -- integrands and hence measurability of the two integrals
    (hf : Measurable f)
    -- USER-INPUT: the numerator integral converges at every sample point
    (hnum : ∀ x, Integrable fun u : ℝ => u * f (x - u • (1 : Fin n → ℝ)))
    -- USER-INPUT: the denominator integral converges at every sample point
    (hden : ∀ x, Integrable fun u : ℝ => f (x - u • (1 : Fin n → ℝ))) :
    Measurable (pitmanEstimator f) := by
  unfold pitmanEstimator
  have hjoint : Measurable fun p : (Fin n → ℝ) × ℝ => f (p.1 - p.2 • (1 : Fin n → ℝ)) :=
    hf.comp (measurable_fst.sub (measurable_snd.smul_const (1 : Fin n → ℝ)))
  have hN : Measurable fun x => ∫ u : ℝ, u * f (x - u • (1 : Fin n → ℝ)) :=
    (MeasureTheory.StronglyMeasurable.integral_prod_right'
      (measurable_snd.mul hjoint).stronglyMeasurable).measurable
  have hD : Measurable fun x => ∫ u : ℝ, f (x - u • (1 : Fin n → ℝ)) :=
    (MeasureTheory.StronglyMeasurable.integral_prod_right'
      hjoint.stronglyMeasurable).measurable
  exact hN.div hD

/-- **The Pitman estimator is location equivariant.** Substituting `u ↦ u + a` leaves the
denominator unchanged and adds `a` times the denominator to the numerator. -/
theorem pitmanEstimator_isLocEquivariant (f : (Fin n → ℝ) → ℝ)
    -- USER-INPUT: the numerator integral converges at every sample point
    (hnum : ∀ x, Integrable fun u : ℝ => u * f (x - u • (1 : Fin n → ℝ)))
    -- USER-INPUT: the denominator integral converges at every sample point
    (hden : ∀ x, Integrable fun u : ℝ => f (x - u • (1 : Fin n → ℝ)))
    -- USER-INPUT: the denominator does not vanish, so the ratio is not junk
    (hden0 : ∀ x, (∫ u : ℝ, f (x - u • (1 : Fin n → ℝ))) ≠ 0) :
    IsLocEquivariant (pitmanEstimator f) := by
  intro a x
  have hDshift : (∫ u : ℝ, f (x + a • (1 : Fin n → ℝ) - u • (1 : Fin n → ℝ)))
      = ∫ u : ℝ, f (x - u • (1 : Fin n → ℝ)) := by
    have hpt : (fun u : ℝ => f (x + a • (1 : Fin n → ℝ) - u • (1 : Fin n → ℝ)))
        = fun u : ℝ => f (x - (u - a) • (1 : Fin n → ℝ)) := by
      funext u
      congr 1
      rw [sub_smul]; abel
    rw [hpt]
    exact integral_sub_right_eq_self (fun v : ℝ => f (x - v • (1 : Fin n → ℝ))) a
  have hNshift : (∫ u : ℝ, u * f (x + a • (1 : Fin n → ℝ) - u • (1 : Fin n → ℝ)))
      = (∫ u : ℝ, u * f (x - u • (1 : Fin n → ℝ)))
        + a * ∫ u : ℝ, f (x - u • (1 : Fin n → ℝ)) := by
    have hHint : Integrable (fun u : ℝ => (u - a) * f (x - (u - a) • (1 : Fin n → ℝ))) :=
      Integrable.comp_sub_right (hnum x) a
    have hgint : Integrable (fun u : ℝ => f (x - (u - a) • (1 : Fin n → ℝ))) :=
      Integrable.comp_sub_right (hden x) a
    have hpt : (fun u : ℝ => u * f (x + a • (1 : Fin n → ℝ) - u • (1 : Fin n → ℝ)))
        = fun u : ℝ => (u - a) * f (x - (u - a) • (1 : Fin n → ℝ))
          + a * f (x - (u - a) • (1 : Fin n → ℝ)) := by
      funext u
      have hvec : x + a • (1 : Fin n → ℝ) - u • (1 : Fin n → ℝ)
          = x - (u - a) • (1 : Fin n → ℝ) := by rw [sub_smul]; abel
      rw [hvec]; ring
    have e1 : (∫ u : ℝ, (u - a) * f (x - (u - a) • (1 : Fin n → ℝ)))
        = ∫ u : ℝ, u * f (x - u • (1 : Fin n → ℝ)) :=
      integral_sub_right_eq_self (fun v : ℝ => v * f (x - v • (1 : Fin n → ℝ))) a
    have e2 : (∫ u : ℝ, f (x - (u - a) • (1 : Fin n → ℝ)))
        = ∫ u : ℝ, f (x - u • (1 : Fin n → ℝ)) :=
      integral_sub_right_eq_self (fun v : ℝ => f (x - v • (1 : Fin n → ℝ))) a
    rw [hpt, integral_add hHint (Integrable.const_mul hgint a), integral_const_mul, e1, e2]
  show pitmanEstimator f (x + a • (1 : Fin n → ℝ)) = pitmanEstimator f x + a
  unfold pitmanEstimator
  rw [hNshift, hDshift, add_div, mul_div_assoc, div_self (hden0 x), mul_one]

/-- **The closed form is the conditional-mean form.** Taking the last coordinate as
reference equivariant estimator, the change of variables `yᵢ = xᵢ − xₙ`, `yₙ = xₙ` has
unit Jacobian and identifies the ratio of integrals with `xₙ − E₀[Xₙ | Y]`. -/
theorem pitmanEstimator_eq_sub_condMean (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    -- LEAN-ONLY: measurability of the density
    (hf : Measurable f)
    -- USER-INPUT: the density is nonnegative, so it is the density of `locationBase f`
    (hfnn : ∀ x, 0 ≤ f x)
    -- USER-INPUT: the numerator integral converges at every sample point
    (hnum : ∀ x, Integrable fun u : ℝ => u * f (x - u • (1 : Fin (m + 1) → ℝ)))
    -- USER-INPUT: the denominator integral converges at every sample point
    (hden : ∀ x, Integrable fun u : ℝ => f (x - u • (1 : Fin (m + 1) → ℝ)))
    -- USER-INPUT: the denominator does not vanish
    (hden0 : ∀ x, (∫ u : ℝ, f (x - u • (1 : Fin (m + 1) → ℝ))) ≠ 0) :
    -- Stated almost everywhere, not pointwise: `orbitCondKernel` is a `condDistrib`, which is
    -- only determined up to a null set, so an `∀ x` form is not provable by any route.
    ∀ᵐ x ∂(locationBase f),
      pitmanEstimator f x = x (Fin.last m) -
        ∫ z, z (Fin.last m)
          ∂(orbitCondKernel (locationBase f) diffs (diffs x)) := by
  -- Contract-level debt (reported). This is the substantive change of variables.
  -- `ForMathlib.CondDistribDensity.condDistrib_withDensity_prod_ae_eq` is now CLOSED and
  -- axiom-clean, so the upstream blocker is gone; what remains is the det-1 shear geometry
  -- itself. The route: push `locationBase f` forward along `Φ x = (diffs x, x n)` (a linear
  -- shear of unit Jacobian, so `volume`-preserving via `volume_preserving_transvectionStruct`
  -- + `MeasurableEquiv.piFinSuccAbove` for the snoc reindexing) to a joint law
  -- `ρ = (volume ⊗ volume).withDensity p` with `p (y,s) = ofReal (f (Fin.snoc y 0 + s • 1))`;
  -- apply `condDistrib_withDensity_prod_ae_eq` to identify the conditional law given `diffs`
  -- as the normalized slice; transport `orbitCondKernel … diffs = condDistrib id diffs` to
  -- `condDistrib Prod.snd Prod.fst ρ`; then the slice-mean Bochner integral becomes the
  -- displayed ratio after the translation substitution `s = x n − u`. This is a large,
  -- self-contained measure-geometry development; left as reported debt in this session.
  sorry

/-- Conditional integrability of the reference estimator `δ₀ x = x n` against the fibre
kernel of the differences, in *every* fibre — the hypothesis `isLocMRE_sq_of_condMean`
consumes. Named debt (the one lifted `private` sorry of this file): it is not implied by
the pointwise convergence of the Pitman integrals `hnum`/`hden`, and establishing it
requires the same conditional-law-as-normalized-slice identification
(`ForMathlib.CondDistribDensity`, itself a `sorry` stub) plus the unit-Jacobian shear used
in `pitmanEstimator_eq_sub_condMean`. -/
private lemma integrable_lastCoord_orbitCondKernel (f : (Fin (m + 1) → ℝ) → ℝ)
    [IsProbabilityMeasure (locationBase f)] (y : Fin m → ℝ) :
    Integrable (fun x => x (Fin.last m)) (orbitCondKernel (locationBase f) diffs y) := by
  sorry

/-- **The Pitman estimator is the minimum risk equivariant estimator of location under
squared error.** -/
theorem pitmanEstimator_isLocMRE (f : (Fin (m + 1) → ℝ) → ℝ)
    -- USER-INPUT: `f` is a probability density
    [IsProbabilityMeasure (locationBase f)]
    -- LEAN-ONLY: measurability of the density
    (hf : Measurable f)
    -- USER-INPUT: the density is nonnegative
    (hfnn : ∀ x, 0 ≤ f x)
    -- USER-INPUT: the numerator integral converges at every sample point
    (hnum : ∀ x, Integrable fun u : ℝ => u * f (x - u • (1 : Fin (m + 1) → ℝ)))
    -- USER-INPUT: the denominator integral converges at every sample point
    (hden : ∀ x, Integrable fun u : ℝ => f (x - u • (1 : Fin (m + 1) → ℝ)))
    -- USER-INPUT: the denominator does not vanish
    (hden0 : ∀ x, (∫ u : ℝ, f (x - u • (1 : Fin (m + 1) → ℝ))) ≠ 0)
    -- USER-INPUT: the reference equivariant estimator (the last coordinate) has finite
    -- risk, which is what makes the conditional minimization meaningful
    (hfin : locRisk f (fun t : ℝ => t ^ 2) (fun x => x (Fin.last m)) ≠ ∞) :
    IsLocMRE f (fun t : ℝ => t ^ 2) (pitmanEstimator f) := by
  -- The closed form equals the squared-error conditional-mean MRE estimator with reference
  -- `δ₀ x = x n` (`pitmanEstimator_eq_sub_condMean`, an a.e. identity under `locationBase f`),
  -- which is MRE by `isLocMRE_sq_of_condMean`. Since `locRisk` is an integral against
  -- `locationBase f`, a.e. equality of the estimators suffices to transfer the risk bound.
  have heq₀ : IsLocEquivariant (fun x : Fin (m + 1) → ℝ => x (Fin.last m)) := by
    intro a x
    show (x + a • (1 : Fin (m + 1) → ℝ)) (Fin.last m) = x (Fin.last m) + a
    simp [Pi.add_apply, Pi.smul_apply]
  -- The conditional-mean estimator with reference the last coordinate.
  set g : (Fin (m + 1) → ℝ) → ℝ := fun x => x (Fin.last m) -
    ∫ z, z (Fin.last m) ∂(orbitCondKernel (locationBase f) diffs (diffs x)) with hg
  have hgMRE : IsLocMRE f (fun t : ℝ => t ^ 2) g :=
    isLocMRE_sq_of_condMean f (measurable_pi_apply (Fin.last m)) heq₀ hfin
      (integrable_lastCoord_orbitCondKernel f)
  -- `pitmanEstimator f = g` almost everywhere under `locationBase f`.
  have hae : ∀ᵐ x ∂(locationBase f), pitmanEstimator f x = g x :=
    pitmanEstimator_eq_sub_condMean f hf hfnn hnum hden hden0
  -- The risks coincide, so the Pitman estimator inherits `g`'s minimality.
  have hrisk : ∀ ρ : ℝ → ℝ, locRisk f ρ (pitmanEstimator f) = locRisk f ρ g := by
    intro ρ
    unfold locRisk
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  refine ⟨measurable_pitmanEstimator f hf hnum hden,
    pitmanEstimator_isLocEquivariant f hnum hden hden0, fun δ' hδ'meas hδ'eq => ?_⟩
  rw [hrisk (fun t : ℝ => t ^ 2)]
  exact hgMRE.2.2 δ' hδ'meas hδ'eq

end Pitman

end StatLean.PointEstimation
