# LANE-REPORT — comp/r1-measure (Lane B: importance sampling + rejection sampling)

## Summary

| target | status |
| --- | --- |
| `integral_importanceWeight_mul` | **closed**, axiom-clean |
| `importanceSampling_unbiased` | **closed** (tainted only by `PiMoments.integral_avg_eval_pi`, other lane) |
| `importanceSampling_variance` | **closed** (tainted only by `PiMoments.variance_avg_eval_pi`, other lane) |
| `lintegral_sq_le_lintegral_sq_div` | **closed**, axiom-clean |
| `lintegral_sq_div_optimalImportance` | **closed**, axiom-clean |
| `isProbabilityMeasure_uniform01` | **closed**, axiom-clean |
| `measurableSet_rejectionAccept` | **closed**, axiom-clean |
| `rejectionSampling_restrict_map` | **closed**, axiom-clean (after the `hq1` repair) |
| `rejectionSampling_acceptProb` | **closed**, axiom-clean (after the `hq1` repair) |
| `rejectionSampling_conditionalLaw` | **closed**, axiom-clean (after the `hq1` repair) |

`ImportanceSampling.lean` and `RejectionSampling.lean` are both **0-sorry**.
The obstruction section below is retained as the record of why the three
rejection-sampling statements carry `hq1 : ∫⁻ z, q z ∂ν = 1`; see the
follow-up section at the end for how they were closed once it was added.

---

## OBSTRUCTION: the three rejection-sampling identities are false as frozen

### The gap

Nothing in the hypotheses of the three theorems excludes `q y = ∞` on a set of
positive `ν`-measure.  `q` is only asked to be measurable and to majorize the
target (`p ≤ c·q`); there is **no** `∫⁻ q dν = 1`, no `∀ᵐ y ∂ν, q y ≠ ∞`, and no
finiteness of `ν.withDensity q`.

At such a `y` the acceptance section degenerates:

```
{u | ENNReal.ofReal u * (c * q y) ≤ p y}  =  {u | ofReal u * ∞ ≤ p y}
                                          =  Set.Iic 0      (whenever p y ≠ ∞)
```

because `ofReal u = 0` exactly for `u ≤ 0` and `0 * ∞ = 0`, while `ofReal u * ∞
= ∞` for `u > 0`.  And `uniform01 (Iic 0) = volume (Icc 0 1 ∩ Iic 0) =
volume {0} = 0`.

So the mass that `y` contributes to the accepted-restricted marginal is

```
q y * uniform01 (section y)  =  ∞ * 0  =  0,
```

whereas the claimed right-hand side contributes `c⁻¹ * p y > 0`.  The two sides
disagree, and the disagreement is not a null-set artefact: it is carried by
exactly the set `{q = ∞} ∩ {0 < p < ∞}`.

### Machine-checked witness (in `RejectionSampling.lean`, `private`, 0 sorries)

Take `𝓧 = Unit`, `ν = Measure.dirac ()`, `p ≡ 1`, `q ≡ ∞`, `c = 1`.  Then every
hypothesis of all three theorems holds:

* `Measurable p`, `Measurable q` — constants;
* `∫⁻ z, p z ∂ν = 1` — `∫⁻ 1 ∂δ = 1`;
* `∀ y, p y ≤ c * q y` — `1 ≤ 1 * ∞`;
* `c ≠ 0`, `c ≠ ∞` — `c = 1`;
* `SigmaFinite ν` — `δ` is a probability measure.

and yet the acceptance region is a **null set** for the joint proposal:

* `rejectionAccept_unit_top_eq_zero` :
  `(((dirac ()).withDensity (fun _ => ∞)).prod uniform01) (rejectionAccept 1 ∞ 1) = 0`.

From that single computation the three refutations follow (all compiled,
axiom-clean — `propext`, `Classical.choice`, `Quot.sound` only):

* `not_rejectionSampling_acceptProb` — acceptance mass is `0`, not `c⁻¹ = 1`;
* `not_rejectionSampling_restrict_map` — evaluating both sides at `univ` gives
  `0 = 1`;
* `not_rejectionSampling_conditionalLaw` — conditioning on a null set gives
  `(0)⁻¹ • 0 = 0`, so the conditional law has total mass `0`, not `1`.

Each is stated as the negation of the frozen conclusion specialised to
`𝓧 = Unit`, `ν = dirac ()`, i.e. as a genuine instance of the general claim.

### The repair (recommended for round 2)

Add to all three statements the proposal-side finiteness that the book has for
free (there `q` *is* a probability density):

```lean
    -- USER-INPUT: the proposal is a genuine density; ECS §2.1
    (hq1 : ∫⁻ z, q z ∂ν = 1)
```

or, minimally, `(hqfin : ∀ᵐ y ∂ν, q y ≠ ∞)`.  Either one is enough: `∫⁻ q dν = 1`
gives `q < ∞` a.e. by `MeasureTheory.ae_lt_top`.

With that hypothesis the workhorse goes through pointwise, ν-a.e.:

* `q y = 0`: envelope gives `p y ≤ c * 0 = 0`, so `p y = 0`; the section is all
  of `ℝ` (`ofReal u * 0 = 0 ≤ 0`), so the integrand is `0 * 1 = 0 = c⁻¹ * p y`.
* `0 < q y < ∞`: put `A := c * q y ∈ (0, ∞)`.  The section is
  `{u | ofReal u ≤ p y / A}` with `p y / A ≤ 1` by the envelope, so
  `uniform01 (section y) = ofReal ((p y / A).toReal) = p y / A`, and the
  integrand is `(p y / (c * q y)) * q y = p y / c = c⁻¹ * p y`
  (`ENNReal.div_mul_cancel`, `q y ≠ 0, ≠ ∞`).
* `q y = ∞`: excluded a.e. by the new hypothesis.

Assembly (unchanged from the lane sketch, and verified to typecheck as far as
the sorry): `Measure.ext fun S hS` → `Measure.map_apply measurable_fst hS` →
`Measure.restrict_apply (measurableSet_rejectionAccept hp hq)` →
`Measure.prod_apply` (only `SFinite uniform01` is needed; `prod_apply` asks
`SFinite` of the *second* factor) → `lintegral_withDensity_eq_lintegral_mul` →
the pointwise identity above → `lintegral_const_mul'` + `withDensity_apply _ hS`
+ `Measure.smul_apply`.  `rejectionSampling_acceptProb` is then the `S = univ`
instantiation, and `rejectionSampling_conditionalLaw` follows from
`ProbabilityTheory.cond`, `Measure.map_smul`, `smul_smul`, `ENNReal.inv_inv`,
`ENNReal.mul_inv_cancel hc0 hcT`.

Note that the module docstring's claim that the multiplicative form of the
acceptance region "is junk-free at `q y = 0`" is right; the junk it does *not*
absorb is at `q y = ∞`, which is where the statements break.

---

## Notes on the closed targets

* `lintegral_sq_le_lintegral_sq_div` — case split on `ν {p = 0 ∧ f ≠ 0}`.  When
  that set is non-null the right-hand side is `∞`
  (`lintegral_eq_top_of_measure_eq_top_ne_zero` + `ENNReal.div_zero`).  Otherwise
  `f = (f²/p)^{1/2} · p^{1/2}` a.e. (`ENNReal.div_mul_cancel'` supplies both junk
  side conditions: `p = 0 ⇒ f² = 0` from the null set, `p = ∞` excluded by
  `ae_lt_top` from `∫⁻ p = 1`), then `ENNReal.lintegral_mul_le_Lp_mul_Lq` at
  `p = q = 2` and square.
* `lintegral_sq_div_optimalImportance` — three cases on `c = ∫⁻ f dν`
  (`0`, `∞`, generic).  In the generic case the pointwise identity
  `f² / (f/c) = f · c` comes from `ENNReal.eq_div_iff` + `ENNReal.div_mul_cancel`,
  and `lintegral_mul_const'` finishes.  Beware: `rw [hc0]` on the `c = 0` branch
  rewrites the integrand too — compute the left-hand side as a separate `have`.
* `importanceSampling_variance` — `exact variance_avg_eval_pi hgw` alone is a
  heartbeat bomb (higher-order unification against `mcEstimate`); insert the
  `rfl`-level `have hfun : mcEstimate _ = fun x => (n:ℝ)⁻¹ * ∑ i, _` and `rw` it
  first.  The `integral` sibling does not need this.

---

## Follow-up session — the three rejection-sampling identities are CLOSED

The laptop session added `hq1 : ∫⁻ z, q z ∂ν = 1` to all three statements (the
repair recommended above).  With it, the route sketched in "The repair" section
goes through verbatim; all three are now proved and **axiom-clean**
(`propext`, `Classical.choice`, `Quot.sound` only).  `RejectionSampling.lean`
is **0-sorry**.

### What was built

One new `private` helper carries the entire mathematical content:

* `uniform01_section_mul (henv) (hc0) (hcT) (hy : q y ≠ ∞) :`
  `q y * uniform01 {u | ofReal u * (c * q y) ≤ p y} = c⁻¹ * p y`.

Its proof is the two-case analysis predicted above:

* `q y = 0`: the envelope forces `p y = 0`, both sides are `0` (the section is
  all of `ℝ`, but it is multiplied by `q y = 0`).
* `0 < q y < ∞`: with `r := (p y / (c * q y)).toReal ∈ [0, 1]` (`≤ 1` from
  `ENNReal.div_le_of_le_mul` applied to `p y ≤ 1 * (c * q y)`, `≠ ∞` from
  `ENNReal.div_ne_top`), the section is **exactly** `Set.Iic r`
  (`ENNReal.le_div_iff_mul_le` one way, `ENNReal.div_mul_cancel` the other; the
  `u ≤ 0` sub-case is absorbed by `0 ≤ r`), and
  `uniform01 (Iic r) = volume (Icc 0 r) = ofReal r = p y / (c * q y)`.
  Finish with `ENNReal.mul_inv` + `ENNReal.mul_inv_cancel`.

The third case `q y = ∞` is the one killed by `hq1`, via
`ae_lt_top hq (hq1 ▸ ENNReal.one_ne_top)`; it is the only place `hq1` is used
in `rejectionSampling_restrict_map`.

### Assembly (all three)

* `rejectionSampling_restrict_map` — `Measure.ext fun S hS` →
  `Measure.map_apply measurable_fst hS` → `Measure.restrict_apply` →
  `Measure.prod_apply` → `lintegral_withDensity_eq_lintegral_mul` (measurability
  of the section function from `measurable_measure_prodMk_left`) →
  a `hsec` lemma identifying the `y`-section of
  `Prod.fst ⁻¹' S ∩ rejectionAccept p q c` as `S.indicator (section y)` →
  `lintegral_congr_ae` against `uniform01_section_mul` →
  `lintegral_indicator hS` + `lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hc0)`
  + `withDensity_apply _ hS`.
* `rejectionSampling_acceptProb` — literally the `S = univ` instance of the
  above (`congrArg (fun μ => μ univ)`), then `setLIntegral_univ` and `hp1`.
* `rejectionSampling_conditionalLaw` — unfold `ProbabilityTheory.cond`,
  `Measure.map_smul`, plug in the two previous theorems, `smul_smul`,
  `inv_inv` (note: **not** `ENNReal.inv_inv`, which does not exist in the pin —
  the general `inv_inv` applies), `ENNReal.mul_inv_cancel hc0 hcT`, `one_smul`.

### Notes / gotchas

* `SigmaFinite ν` is never used: `Measure.prod_apply` and
  `measurable_measure_prodMk_left` only ask `SFinite` of the **second** factor,
  which `uniform01` has as a probability measure.  Since the statement is
  frozen, the resulting `linter.unusedSectionVars` warning is silenced with a
  `set_option linter.unusedSectionVars false in` line placed *before* the
  docstring (same for the `[MeasurableSpace 𝓧]` warning on the helper).
* `ENNReal.one_toReal` does not exist in the pin; the name is
  `ENNReal.toReal_one`.  Likewise there is no `ENNReal.inv_inv`.
* `set r := … with hr` does not fold occurrences created by later `have`s, so
  the `r ≤ 1` step has to `rw [hr]` first rather than `simpa`.
* The falsity witnesses (`rejectionAccept_unit_top_eq_zero`,
  `not_rejectionSampling_*`) are untouched and still compile: they now document
  that `hq1` (or some `q < ∞` a.e. surrogate) is **not removable**.
