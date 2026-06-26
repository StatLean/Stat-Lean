# Close the 7 sorries in MEstimator/L1Decomposable.lean (ℓ1/ℓ∞ decomposable regularizer)

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. ON the cluster.

## CRITICAL build discipline
- Check with **plain foreground** `lake build StatLean.HighDimensionalStatistics.MEstimator.L1Decomposable`
  and read the output. **NEVER** background a build (`&`), **NEVER** `until pgrep`/`sleep` loops, **NEVER**
  nested `srun`/`sbatch`. When it shows 0 errors and 0 sorries, STOP — you are done.

## Scope
- **Only edit** `StatLean/HighDimensionalStatistics/MEstimator/L1Decomposable.lean`. Keep all signatures,
  defs, and docstrings; just fill the `sorry`s. Lines ≤ 100. Commit-worthy when 0 sorries.
- `VecNorms.lean` has: `l1Norm x = ∑ i, |x.ofLp i|`, `linfNorm x = ⨆ i, |x.ofLp i|`,
  `abs_inner_le_l1Norm_mul_linfNorm : |⟪x,y⟫_ℝ| ≤ l1Norm x * linfNorm y`, `abs_le_linfNorm`,
  `l1Norm_add_le`, `l1Norm_nonneg`, `linfNorm_nonneg` (check exact names with `./tools/api.sh` or `exact?`).
  Coordinates: `(x + y).ofLp i = x.ofLp i + y.ofLp i`, `(c • x).ofLp i = c * x.ofLp i`,
  `(0 : EuclideanSpace ℝ (Fin d)).ofLp i = 0` — find the exact `WithLp`/`PiLp` simp lemmas (`exact?`/`simp?`).

## The 7 gaps

1. **`suppSubmodule`** (carrier `{θ | ∀ j ∉ S, θ.ofLp j = 0}`): `zero_mem'`, `add_mem'`, `smul_mem'` — each
   `intro … ; simp` using the coordinate lemmas (`(a+b).ofLp j = a.ofLp j + b.ofLp j` etc.); membership is
   `∀ j ∉ S, …`. (`smul_mem'` goal uses `(c • a).ofLp j = c * a.ofLp j`.)

2. **`l1Seminorm`** fields: `map_zero'` (`l1Norm 0 = 0`), `add_le'` (`l1Norm_add_le`), `neg'`
   (`l1Norm (-x) = l1Norm x`, via `|(-x).ofLp i| = |x.ofLp i|`), `smul'`
   (`l1Norm (c • x) = ‖c‖ * l1Norm x`: `∑|c·xᵢ| = |c|∑|xᵢ|`, `abs_mul`, `Finset.mul_sum`, `Real.norm_eq_abs`).

3. **`linfSeminorm`** fields: same four for `linfNorm = ⨆ i, |·.ofLp i|`. `map_zero'`: `⨆ i, |0| = 0`
   (`ciSup_const`/`Real.iSup_const`, handle `Fin d` possibly empty → `Real.ciSup` of `0`). `add_le'`:
   `⨆|xᵢ+yᵢ| ≤ ⨆|xᵢ| + ⨆|yᵢ|` via `ciSup_le` + `abs_add` + `le_ciSup` (need `BddAbove` of a finite range —
   `Set.Finite.bddAbove (Set.finite_range _)`). `smul'`: `⨆|c·xᵢ| = |c|·⨆|xᵢ|` (`Real.mul_iSup_of_nonneg` /
   pull `|c|≥0` through the sup). These sup-manipulations are the fiddliest — `le_antisymm` + `ciSup_le`/`le_ciSup`.

3'. **`l1_linf_holder`** `⟪u,v⟫_ℝ ≤ l1Norm u * linfNorm v`: `le_trans (le_abs_self _) (abs_inner_le_l1Norm_mul_linfNorm u v)`.

4. **`linf_tight`** `(∀ u, l1Norm u ≤ 1 → ⟪u,v⟫ ≤ c) → linfNorm v ≤ c`: first `0 ≤ c` from `h 0 (by simp)`.
   `linfNorm v = ⨆ i |v.ofLp i| ≤ c` by `ciSup_le` (or `Real.iSup_le`): for each `j`, show `|v.ofLp j| ≤ c`.
   Witness `u := |v.ofLp j| • (EuclideanSpace.single j (Real.sign (v.ofLp j)))` — simpler: take
   `u := EuclideanSpace.single j (Real.sign (v.ofLp j))` (or `(if v.ofLp j ≥ 0 then 1 else -1)`); then
   `l1Norm u = |sign| ≤ 1` and `⟪u, v⟫_ℝ = sign(v.ofLp j) * v.ofLp j = |v.ofLp j|`
   (`EuclideanSpace.inner_single_left`/`single`, `Real.sign_mul_abs`/`abs_eq_sign_mul`). So `|v.ofLp j| ≤ c`.
   Handle `v.ofLp j = 0` (then `|·|=0≤c`) separately. (`Fin d` empty ⇒ `linfNorm = 0 ≤ c`.)

5. **`suppSubmodule_orthogonal`** `(suppSubmodule S)ᗮ = suppSubmodule Sᶜ`: `Submodule.ext`; `u ∈ (suppSubmodule S)ᗮ`
   ↔ `∀ w ∈ suppSubmodule S, ⟪w, u⟫ = 0`. The standard basis vectors `EuclideanSpace.single j 1` for `j ∈ S`
   are in `suppSubmodule S`, and `⟪single j 1, u⟫ = u.ofLp j`; conversely any `w ∈ suppSubmodule S` expands as
   `∑_{j∈S} w.ofLp j • single j 1`. So `u ⊥ suppSubmodule S ↔ (∀ j ∈ S, u.ofLp j = 0) ↔ u ∈ suppSubmodule Sᶜ`.
   Use `EuclideanSpace.inner_single_left`/`_right`, `Submodule.mem_orthogonal`.

6. **`l1_decomp`** `α ∈ suppSubmodule S`, `β ∈ (suppSubmodule S)ᗮ` ⟹ `l1Norm (α+β) = l1Norm α + l1Norm β`:
   rewrite `(suppSubmodule S)ᗮ = suppSubmodule Sᶜ` (gap 5) so `β.ofLp j = 0` for `j ∈ S` and `α.ofLp j = 0`
   for `j ∉ S`. Then `l1Norm (α+β) = ∑ i |α.ofLp i + β.ofLp i|`; split `Finset.univ` into `S` and `Sᶜ`
   (`Finset.sum_filter_add_sum_filter_not` / `Finset.sum_ite`...). On `S`: `β.ofLp i = 0` ⇒ `|αᵢ+βᵢ|=|αᵢ|`.
   On `Sᶜ`: `α.ofLp i = 0` ⇒ `|αᵢ+βᵢ|=|βᵢ|`. Recombine to `l1Norm α + l1Norm β` (each is the full sum since the
   off-support coords are 0). `Finset.sum_congr` + `add_zero`/`zero_add`.

Report the final `lake build` line (0 sorries) and `#print axioms l1DecomposableReg`.
