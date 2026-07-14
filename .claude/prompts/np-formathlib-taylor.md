# Close the 2 sorries in NonparametricStatistics/ForMathlib/Taylor{LagrangeTwoSided,IntegralRemainder}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON the
cluster — iterate with plain
`lake build StatLean.NonparametricStatistics.ForMathlib.TaylorLagrangeTwoSided` and
`lake build StatLean.NonparametricStatistics.ForMathlib.TaylorIntegralRemainder` (no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/ForMathlib/TaylorLagrangeTwoSided.lean` and
  `StatLean/NonparametricStatistics/ForMathlib/TaylorIntegralRemainder.lean`. Touch nothing else.
- Goal **0 sorries**, 0 errors. Keep theorem signatures, USER-INPUT/LEAN-ONLY tags, docstrings
  UNCHANGED. You MAY add `import Mathlib.*` lines and `private` helper lemmas. Lines ≤ 100.
  If a piece resists, lift it to a `private lemma` with one `sorry` + `-- TODO(np):` and report.
- After green: `#print axioms StatLean.NonparametricStatistics.taylor_lagrange_global` and
  `#print axioms StatLean.NonparametricStatistics.taylor_integral_remainder` → only
  `propext, Classical.choice, Quot.sound`.
- Do not weaken statements. If you believe a statement is false as stated, STOP and report why.

## Available Mathlib API (verify exact names with `exact?`/loogle; these existed at the pin)
- `taylor_mean_remainder_lagrange {f} {x x₀} {n} (hx : x₀ < x)`
  `(hf : ContDiffOn ℝ n f (Set.Icc x₀ x))`
  `(hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Set.Icc x₀ x)) (Set.Ioo x₀ x)) :`
  `∃ x' ∈ Set.Ioo x₀ x, f x - taylorWithinEval f n (Set.Icc x₀ x) x₀ x`
  `= iteratedDerivWithin (n+1) f (Set.Icc x₀ x) x' * (x - x₀)^(n+1) / (n+1)!` (module
  `Mathlib.Analysis.Calculus.Taylor`).
- `taylor_within_apply : taylorWithinEval f n s x₀ x = ∑ k ∈ Finset.range (n+1),`
  `((x - x₀)^k / k !) • iteratedDerivWithin k f s x₀` (name approximately this; find it in
  `Mathlib.Analysis.Calculus.Taylor`).
- Within→global conversion on an interval: `uniqueDiffOn_Icc` (needs `a < b`),
  `iteratedDerivWithin_eq_iteratedDeriv` / via `iteratedFDerivWithin_eq_iteratedFDeriv` +
  `iteratedDeriv_eq_iteratedFDeriv`, `iteratedDerivWithin_eq_iteratedFDerivWithin`, and
  `(hf.contDiffOn : ContDiffOn ℝ ℓ f s)`, `ContDiff.contDiffAt`. Newer Mathlib has the corollary
  `taylor_mean_remainder_lagrange_iteratedDeriv` on `uIcc` with hypothesis `ContDiffOn (n+1)`; if
  it exists at the pin, use it (with `n + 1 = ℓ`); otherwise replicate its proof:
  ```
  have hu : UniqueDiffOn ℝ (uIcc x₀ x) := uniqueDiffOn_Icc (by ...)
  have hd : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIcc x₀ x) :=
    hf.differentiableOn_iteratedDerivWithin (by norm_cast; simp) hu
  obtain ⟨x', h1, h2⟩ := taylor_mean_remainder_lagrange hx hf.of_succ (hd.mono Ioo_subset_Icc_self)
  rw [h2, iteratedDeriv_eq_iteratedFDeriv, iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv hu _ ⟨le_of_lt h1.1, le_of_lt h1.2⟩]
  ```
- Reflection alternative for `x < x₀`: `iteratedDeriv_comp_neg` (if present at pin; else derive by
  induction with `iteratedDeriv_succ`, `deriv_comp_neg`).
- FTC / integration by parts on intervals: `intervalIntegral.integral_deriv_eq_sub`,
  `intervalIntegral.integral_deriv_eq_sub'`, `intervalIntegral.integral_mul_deriv_eq_deriv_mul`,
  `intervalIntegral.intervalIntegrable_of_continuousOn` / `ContinuousOn.intervalIntegrable`,
  `HasDerivAt.comp`, `Real.hasDerivAt_const_mul...` (chain rule for `τ ↦ x₀ + τ*t`).
- `ContDiff.continuous_iteratedDeriv` (continuity of `iteratedDeriv ℓ f` from `ContDiff ℝ ℓ f`;
  approximately this name), `ContDiff.differentiable_iteratedDeriv`, `iteratedDeriv_succ`.

## Proofs

### A. `taylor_lagrange_global` (TaylorLagrangeTwoSided.lean)
Goal: `∃ τ ∈ Ioo 0 1, f (x₀+t) = ∑_{j<ℓ} f⁽ʲ⁾(x₀)·tʲ/j! + f⁽ℓ⁾(x₀+τt)·tℓ/ℓ!` for `t ≠ 0`,
`ContDiff ℝ ℓ f`, `1 ≤ ℓ`.
- Set `x := x₀ + t`, `hx : x₀ ≠ x` (from `ht`). Work on `uIcc x₀ x` (covers both signs).
- Get the Mathlib remainder at order `n := ℓ - 1` (so `n + 1 = ℓ`, use `Nat.succ_pred_eq_of_pos`
  from `hℓ`): `∃ x' ∈ uIoo x₀ x (or Ioo for one-sided), f x - taylorWithinEval f (ℓ-1) … = …`.
  Either use the `uIcc` corollary if present, or split `rcases lt_or_gt_of_ne hx`:
  - `x₀ < x`: apply `taylor_mean_remainder_lagrange` directly with
    `hf.contDiffOn : ContDiffOn ℝ (ℓ-1) f (Icc x₀ x)` (via `hf.of_le`, cast `ℓ-1 ≤ ℓ`) and the
    differentiability of `iteratedDerivWithin (ℓ-1)` from `hf` (convert global iteratedDeriv:
    on `Icc` with `uniqueDiffOn_Icc`, `iteratedDerivWithin_eq_iteratedDeriv`-style congruence;
    the global `iteratedDeriv (ℓ-1) f` is differentiable by `hf.differentiable_iteratedDeriv`
    with `(ℓ-1 : ℕ∞) < ℓ`).
  - `x < x₀`: same on `Icc x x₀` after reflecting, or apply the lemma to `g := fun y => f (-y)`
    on `Icc (-x₀) (-x)`… the `uIcc` route above avoids this entirely — prefer it.
- Convert the intermediate point: `x' ∈ Ioo x₀ x` (or `uIoo`) means `x' = x₀ + τ*t` with
  `τ := (x' - x₀)/t ∈ Ioo 0 1` — check both sign cases: for `t < 0`, `x' ∈ Ioo x x₀` still gives
  `(x'-x₀)/t ∈ Ioo 0 1` (dividing by negative flips). Provide `τ`, `field_simp` for
  `x₀ + τ*t = x'`.
- Convert `taylorWithinEval` to the stub's explicit sum via `taylor_within_apply`, then
  `iteratedDerivWithin → iteratedDeriv` at `x₀` (endpoint of the interval, member ✓) using
  `uniqueDiffOn` + the `iteratedFDerivWithin_eq_iteratedFDeriv` bridge (template above); note the
  stub's sum runs over `Finset.range ℓ` = orders `0..ℓ-1` and uses `* tʲ / j!` where Mathlib has
  `((x-x₀)^k / k!) • _` — `smul_eq_mul` + `ring`-normal forms; `Finset.range (n+1) = range ℓ` after
  `Nat.succ_pred_eq_of_pos hℓ`.
- Final remainder shape: Mathlib gives `f⁽ℓ⁾(x')·t^ℓ/ℓ!`; matches the stub (with `(n+1)! = ℓ!`).

### B. `taylor_integral_remainder` (TaylorIntegralRemainder.lean)
Goal: `f (x₀+t) = ∑_{j<ℓ} f⁽ʲ⁾(x₀)tʲ/j! + (tℓ/(ℓ-1)!)·∫₀¹ (1-τ)^{ℓ-1}·f⁽ℓ⁾(x₀+τt) dτ`.
Induction on `ℓ` (statement for all `f` simultaneously; `ℓ = m + 1` form avoids `ℓ - 1`
subtraction pain — do `obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, (Nat.succ_pred_eq_of_pos hℓ).symm⟩`
then induct on `m`).
- Base `m = 0` (`ℓ = 1`): claim `f (x₀+t) = f x₀ + t·∫₀¹ f'(x₀+τt) dτ`. Define
  `g : ℝ → ℝ := fun τ => f (x₀ + τ*t)`; `hg : ∀ τ, HasDerivAt g (t * deriv f (x₀+τ*t)) τ` by
  `HasDerivAt.comp` of `f` (differentiable from `hf.differentiable (by norm_num)`) with the affine
  map (`(hasDerivAt_id τ).const_mul t |>.const_add x₀`-style; watch argument order `x₀ + τ*t`).
  Then `intervalIntegral.integral_deriv_eq_sub` (integrand continuous: `iteratedDeriv 1 f = deriv f`
  continuous from `hf`; composition with affine continuous) gives
  `∫₀¹ t·f'(x₀+τt) dτ = g 1 - g 0 = f (x₀+t) - f x₀`. Pull the constant `t` out
  (`intervalIntegral.integral_const_mul`). `iteratedDeriv_one = deriv` (or `iteratedDeriv_succ` +
  `iteratedDeriv_zero`). Match the stub's `(1-τ)^0 = 1` (`pow_zero`) and `0! = 1`.
- Step `m → m+1` (`ℓ = m+2`, given for `ℓ = m+1` and all `C^{m+1}` functions): integrate by parts.
  With `u τ := iteratedDeriv (m+1) f (x₀+τ*t)` (derivative `t·iteratedDeriv (m+2) f (x₀+τ*t)`,
  from `ContDiff` one order up) and `v τ := -(1-τ)^{m+1}/(m+1)` (derivative `(1-τ)^m`):
  `∫₀¹ (1-τ)^m·u = [u·v]₀¹ - ∫₀¹ v·u' = u(0)/(m+1) + (t/(m+1))·∫₀¹ (1-τ)^{m+1}·iteratedDeriv (m+2) f (x₀+τt)`.
  Use `intervalIntegral.integral_mul_deriv_eq_deriv_mul` (all integrands continuous on `[0,1]`).
  Then apply the induction hypothesis at order `m+1` (from `hf.of_le`) and rearrange:
  the new top Taylor coefficient `f^{(m+1)}(x₀)·t^{m+1}/(m+1)!` is exactly the boundary term.
  Factorial algebra: `Nat.factorial_succ`, `field_simp`, `ring` (casts `(Nat.factorial _ : ℝ) ≠ 0`
  via `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`).

Report final `lake build` status + `#print axioms` for both theorems (note any lifted `private`
sorry).
