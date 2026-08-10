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
| `rejectionSampling_restrict_map` | **left as debt — FALSE as frozen** (witness below) |
| `rejectionSampling_acceptProb` | **left as debt — FALSE as frozen** (witness below) |
| `rejectionSampling_conditionalLaw` | **left as debt — FALSE as frozen** (witness below) |

`ImportanceSampling.lean` is **0-sorry**.  `RejectionSampling.lean` carries **3
sorries**, all three of them the refuted statements.

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
