# Close the 6 sorries in NonparametricStatistics/SmoothnessClasses/{HolderTaylor,NikolskiTaylor}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON the
cluster — iterate with plain `lake build StatLean.NonparametricStatistics.SmoothnessClasses.HolderTaylor`
(then `.SmoothnessClasses.NikolskiTaylor`; no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/SmoothnessClasses/HolderTaylor.lean` and
  `.../SmoothnessClasses/NikolskiTaylor.lean`. Touch nothing else (NOT `SmoothnessClasses/Defs.lean`,
  NOT the `ForMathlib/` files).
- Goal **0 sorries**, 0 errors. Keep theorem signatures, tags, docstrings UNCHANGED. You MAY add
  `import Mathlib.*` lines and `private` helper lemmas. Lines ≤ 100. If a piece resists, lift it
  to a `private lemma` with one `sorry` + `-- TODO(np):` and report. Run plain foreground
  `lake build` only — NEVER background it or poll with pgrep loops.
- After green: `#print axioms` on `MemHolder.taylor_remainder_abs_le`,
  `MemHolderOn.taylor_remainder_abs_le_Icc`, `MemNikolski.lintegral_sq_remainder_le` → only
  `propext, Classical.choice, Quot.sound`.
- Do not weaken statements. If you believe one is false as stated, STOP and report why.

## Frozen definitions (SmoothnessClasses/Defs.lean)
- `holderIndex β = ⌈β⌉₊ - 1` (ℕ). For `0 < β`: `(holderIndex β : ℝ) < β ≤ holderIndex β + 1`
  — prove these as private lemmas first (`Nat.ceil` facts: `Nat.lt_ceil`, `Nat.ceil_lt_add_one`,
  `Nat.le_ceil`, `Nat.one_le_ceil_iff`; ℕ-subtraction is safe since `⌈β⌉₊ ≥ 1`).
- `MemHolderOn β L f T`: fields `contDiffOn : ContDiffOn ℝ (holderIndex β) f T` and
  `deriv_holder : ∀ x ∈ T, ∀ y ∈ T, |iteratedDerivWithin (holderIndex β) f T x − ·… y|
    ≤ L * |x−y| ^ (β − (holderIndex β : ℝ))` (real rpow).
- `MemHolder β L f = MemHolderOn β L f Set.univ`.
- `MemNikolski β L f`: fields `contDiff : ContDiff ℝ (holderIndex β) f` and `translate_sq_le :
  ∀ t, ∫⁻ x, ENNReal.ofReal ((iteratedDeriv ℓ f (x+t) − iteratedDeriv ℓ f x)^2)
    ≤ ENNReal.ofReal ((L * |t| ^ (β−ℓ))^2)` with `ℓ = holderIndex β`.

## Available API (proved in this repo — black boxes)
- `taylor_lagrange_global (hℓ : 1 ≤ ℓ) (hf : ContDiff ℝ ℓ f) (x₀ t : ℝ) (ht : t ≠ 0) :
    ∃ τ ∈ Set.Ioo (0:ℝ) 1, f (x₀+t) = (∑ j ∈ Finset.range ℓ, iteratedDeriv j f x₀ * t^j /
    (Nat.factorial j : ℝ)) + iteratedDeriv ℓ f (x₀ + τ*t) * t^ℓ / (Nat.factorial ℓ : ℝ)`
  (`ForMathlib/TaylorLagrangeTwoSided.lean`).
- `taylor_integral_remainder (hℓ : 1 ≤ ℓ) (hf : ContDiff ℝ ℓ f) (x₀ t : ℝ) :
    f (x₀+t) = (∑ j ∈ Finset.range ℓ, …) + t^ℓ / (Nat.factorial (ℓ-1) : ℝ) *
    ∫ τ in (0:ℝ)..1, (1-τ)^(ℓ-1) * iteratedDeriv ℓ f (x₀ + τ*t)`
  (`ForMathlib/TaylorIntegralRemainder.lean`).
- `lintegral_lintegral_sq_rpow_le (μ ν) [SigmaFinite μ] [SigmaFinite ν]
    (hg : Measurable (Function.uncurry g)) : (∫⁻ x, (∫⁻ u, g u x ∂μ)^2 ∂ν)^(1/2:ℝ)
    ≤ ∫⁻ u, (∫⁻ x, (g u x)^2 ∂ν)^(1/2:ℝ) ∂μ` (`ForMathlib/MinkowskiIntegral.lean`) —
  ⚠ this one is still `sorry`-backed (closes in a parallel work item); using it is FINE and
  expected — your `#print axioms` will show `sorryAx` for `MemNikolski.lintegral_sq_remainder_le`
  until that lands; report that fact, it is planned.
- Mathlib (verified on pin by the A1 session): `taylor_mean_remainder_lagrange_iteratedDeriv`
  (uIcc form, hypothesis `ContDiffOn ℝ (n+1) f (uIcc x₀ x)`, global `iteratedDeriv (n+1)` at the
  interior point), `taylor_within_apply`, `iteratedDerivWithin_eq_iteratedDeriv`
  (needs `UniqueDiffOn` + `ContDiffAt`), `uniqueDiffOn_Icc`, `iteratedDeriv_comp_const_sub`
  (in `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`), `intervalIntegral.integral_comp_sub_left`,
  `integral_pow` / `intervalIntegral.integral_pow`.

## Proofs

### HolderTaylor.lean
1. Private groundwork: `holderIndex_lt_self (hβ : 0 < β) : (holderIndex β : ℝ) < β` and
   `sub_holderIndex_pos`, plus the rpow splitter
   `|t|^(ℓ:ℕ) * |t|^(β−ℓ) = |t|^β` for `t ≠ 0` (`Real.rpow_natCast` backwards +
   `Real.rpow_add (abs_pos.mpr ht)`); `t = 0` cases are handled separately everywhere
   (`Real.zero_rpow` with `β ≠ 0`, `hβ.ne'`).
2. `MemHolder.iteratedDeriv_holder`: `hf.deriv_holder x trivial y trivial` +
   `iteratedDerivWithin_univ` (simp lemma rewriting `iteratedDerivWithin _ _ Set.univ`).
3. `MemHolder.taylor_remainder_abs_le`: rcases on `holderIndex β = 0` vs `1 ≤ ℓ` and `t = 0`
   vs `t ≠ 0`.
   - `ℓ = 0`: sum over `range 1` is `iteratedDeriv 0 f x₀ / 0! = f x₀` (`Finset.sum_range_one`,
     `iteratedDeriv_zero`, `pow_zero`); the claim is the Hölder field via (2) at `(x₀+t, x₀)`
     with `add_sub_cancel_left`-normalization of `|x₀ + t − x₀| = |t|`.
   - `ℓ ≥ 1, t = 0`: LHS `= 0` (sum collapses: `t^j = 0` for `j ≥ 1`, only `j = 0` term
     survives = `f x₀`); RHS `= 0` (`Real.zero_rpow hβ.ne'` after `abs_zero`); `simp`.
   - `ℓ ≥ 1, t ≠ 0`: `obtain ⟨τ, hτ, heq⟩ := taylor_lagrange_global … (hf.contDiffOn → global:
     MemHolder gives ContDiffOn univ; convert via `contDiffOn_univ`)`. Rewrite the goal sum
     with `Finset.sum_range_succ` (target has `range (ℓ+1)`); after `heq` the difference is
     `(iteratedDeriv ℓ f (x₀+τt) − iteratedDeriv ℓ f x₀) * t^ℓ / ℓ!`. Bound via (2):
     `≤ L * |τ*t|^(β−ℓ) * |t|^ℓ / ℓ!`; then `|τ*t|^(β−ℓ) ≤ |t|^(β−ℓ)`
     (`Real.rpow_le_rpow (abs_nonneg _) … (le_of_lt sub_holderIndex_pos)` with
     `|τ*t| ≤ |t|` from `abs_mul`, `hτ.2`, `hτ.1`), assemble with the rpow splitter; `abs_div`,
     `abs_mul`, `Nat.factorial` positivity (`div_le_div_of_nonneg_right`-family / `gcongr`).
4. `MemHolderOn.taylor_remainder_abs_le_Icc`: same skeleton on `Icc a b`.
   - `x = y`: both sides `0` as above.
   - `x ≠ y`: apply `taylor_mean_remainder_lagrange_iteratedDeriv` (n := ℓ−1) on `uIcc x y`
     with `hf.contDiffOn.mono (Set.uIcc_subset_Icc hx hy)` (find the exact inclusion lemma:
     `Set.uIcc_subset_Icc` should exist; else `Set.uIcc_subset_uIcc` on endpoints +
     `Set.Icc_subset_Icc`). The intermediate point `x' ∈ uIoo x y ⊆ Ioo a b` (strict interior:
     `Set.uIoo_subset_…`; derive `a < x'` and `x' < b` from `hx, hy` memberships and `h1`).
     Convert BOTH the polynomial's `iteratedDerivWithin k f (uIcc x y) x` and the remainder's
     global `iteratedDeriv ℓ f x'` to `iteratedDerivWithin · f (Icc a b) ·`:
     * at interior `x'`: `(iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
       (hf.contDiffOn.contDiffAt (Icc_mem_nhds …)) (mem: x' ∈ Icc)).symm` — `ContDiffAt` from
       interior membership.
     * at possibly-endpoint `x`: prove a private congruence
       `iteratedDerivWithin k f (uIcc x y) x = iteratedDerivWithin k f (Icc a b) x` by
       induction with `derivWithin`-subset lemmas (`derivWithin_subset` /
       `iteratedDerivWithin_congr_set`-style; search `loogle '"iteratedDerivWithin"'` for a
       subset lemma — if none fits, use `iteratedFDerivWithin_inter_open` or prove by
       induction on `k` with `DifferentiableWithinAt` from `hf.contDiffOn`). This is the
       fiddliest step; if it truly resists, lift EXACTLY this congruence to a
       `private lemma … := sorry` + TODO and finish the rest.
     Then the Hölder field of `hf` at `(x', x)` (both in `Icc a b`) + `|x' − x| ≤ |y − x|`
     (`x'` between) and the same rpow assembly as (3).
5. `MemHolder.abs_le_growth`: triangle: `|f (x₀+t)| ≤ |f (x₀+t) − ∑ …| + |∑ …|`, apply (3),
   bound `|∑| ≤ ∑ |iteratedDeriv j f x₀| * |t|^j / j!` (`Finset.abs_sum_le_sum_abs`, `abs_div`,
   `abs_mul`, `abs_pow`); `linarith`/`gcongr`.

### NikolskiTaylor.lean
6. `taylor_integral_remainder_sub`: start from `taylor_integral_remainder hℓ hf x t`;
   `Finset.sum_range_succ` on the target's `range (ℓ+1)`; the difference of the two integral
   terms: `∫₀¹ (1−τ)^(ℓ−1) * (F τ − c) dτ = ∫₀¹ (1−τ)^(ℓ−1) F τ − c * ∫₀¹ (1−τ)^(ℓ−1)`
   (`intervalIntegral.integral_sub` — integrands continuous, `Continuous.intervalIntegrable`;
   `intervalIntegral.integral_const_mul`), and `∫₀¹ (1−τ)^(ℓ−1) dτ = 1/ℓ`:
   `intervalIntegral.integral_comp_sub_left` (or substitute `s = 1−τ`) + `integral_pow`,
   with `(ℓ−1)+1 = ℓ` (`Nat.succ_pred_eq_of_pos hℓ`). Then factorial algebra
   `t^ℓ/(ℓ−1)! * (f⁽ℓ⁾(x)/ℓ) = f⁽ℓ⁾(x) * t^ℓ/ℓ!` (`Nat.factorial_succ` via `ℓ = (ℓ−1)+1`,
   `field_simp`, `ring`).
7. `MemNikolski.lintegral_sq_remainder_le`: rcases `holderIndex β = 0` vs `1 ≤ ℓ`; `t = 0`
   handled inside (both sides: LHS integrand `0` after the sum collapses, RHS fine).
   - `ℓ = 0`: the sum is `f x` (as in (3)); the goal IS `hf.translate_sq_le t` modulo
     `Finset.sum_range_one`/`iteratedDeriv_zero` rewriting (`simp only [...]` then exact).
   - `ℓ ≥ 1`: rewrite the integrand a.e. (in fact everywhere) with (6). Set
     `c := |t|^ℓ / (ℓ−1)!` and `Δ τ x := iteratedDeriv ℓ f (x + τ*t) − iteratedDeriv ℓ f x`.
     Chain, all in `ℝ≥0∞`:
     * `ofReal ((c' * I x)^2) = ofReal (c'^2) * ofReal ((I x)^2)` with `I x := ∫₀¹ (1−τ)^(ℓ−1) Δ τ x dτ`
       (`ENNReal.ofReal_mul`, squares nonneg; `c'` is the signed `t^ℓ/(ℓ−1)!` — use
       `(c')² = c²` via `abs`).
     * `(I x)^2 ≤ (∫₀¹ |(1−τ)^(ℓ−1) * Δ τ x| dτ)^2` (`intervalIntegral.abs_integral_le_integral_abs`
       — find exact name, or `intervalIntegral.norm_integral_le_integral_norm` with
       `Real.norm_eq_abs`; square preserves ≤ on nonnegs, `sq_le_sq'`/`pow_le_pow_left`).
     * Convert the inner Bochner to `∫⁻` over `volume.restrict (Set.Icc (0:ℝ) 1)`:
       `ofReal (∫₀¹ |g|) = ∫⁻ τ in Icc 0 1, ofReal |g τ|`
       (`intervalIntegral.integral_of_le` + `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`
       + `integral_Icc_eq_integral_Ioc`-style set juggling; integrand continuous — jointly:
       `hf.contDiff.continuous_iteratedDeriv` gives continuity of `iteratedDeriv ℓ f`).
     * Apply `lintegral_lintegral_sq_rpow_le` with `μ := volume.restrict (Icc 0 1)`,
       `ν := volume`, `g τ x := ofReal |(1−τ)^(ℓ−1) * Δ τ x|`. Joint measurability: continuity
       of `(τ, x) ↦ Δ τ x` (composition of the continuous `iteratedDeriv ℓ f` with continuous
       maps; `Continuous.measurable`, `measurable_uncurry`… via `Continuous.uncurry_left`?
       build with `fun_prop` + `Measurable.ennreal_ofReal`).
     * For each `τ`: `∫⁻ x, (g τ x)^2 ∂volume = ofReal ((1−τ)^(ℓ−1))^2 * ∫⁻ x, ofReal ((Δ τ x)^2)`
       (pull the constant; `abs_mul`, `sq_abs`, `ENNReal.ofReal_mul`, `lintegral_const_mul` —
       measurability as above) `≤ ofReal ((1−τ)^(ℓ−1))^2 * ofReal ((L * |τ*t|^(β−ℓ))^2)`
       (the `translate_sq_le` field at shift `τ*t`).
     * `(…)^(1/2)`: `ENNReal.rpow` algebra: `(a^2)^(1/2) = a` (`ENNReal.rpow_natCast`,
       `ENNReal.rpow_mul`… or `ENNReal.sqrt`-free route: keep everything squared by using the
       lemma in the squared form — RECOMMENDED: derive from the Minkowski lemma the squared
       consequence `∫⁻ x (∫⁻ τ g)² ≤ (∫⁻ τ (∫⁻ x g²)^(1/2))²` by `ENNReal.rpow_le_rpow` with
       exponent `2` and `ENNReal.rpow_natCast` juggling, then bound the RHS bracket.)
     * Finish: `∫⁻ τ in Icc 0 1, ofReal ((1−τ)^(ℓ−1) * L * (τ*|t|)^(β−ℓ)) ≤
       ofReal (L * |t|^(β−ℓ)) * ∫⁻ τ in Icc 0 1, ofReal ((1−τ)^(ℓ−1)))` using
       `τ^(β−ℓ) ≤ 1` on `[0,1]` (`Real.rpow_le_one`), and
       `∫⁻ τ in Icc 0 1, ofReal ((1−τ)^(ℓ−1)) = ofReal (1/ℓ)` (Bochner bridge + the `1/ℓ`
       integral from (6)). Assemble constants: `c * L * |t|^(β−ℓ) * (1/ℓ) = (L/ℓ!) * |t|^β`
       (rpow splitter from HolderTaylor — re-prove privately here or inline), then
       `ENNReal.ofReal_le_ofReal` + `ENNReal.mul_le_mul`.
     This is the hardest lemma of the pair; keep each bullet a `private lemma` so failures are
     isolated; a single lifted sorry + TODO is acceptable as last resort — report it.

Report final `lake build` status + `#print axioms` for the three named theorems (note that
`sorryAx` from `lintegral_lintegral_sq_rpow_le` is EXPECTED until the parallel Minkowski item
lands; note any additional lifted `private` sorry of your own).
