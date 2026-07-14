# Close the 5 sorries in NonparametricStatistics/Projection/{CoefficientRisk,MISEDecomposition}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain
`lake build StatLean.NonparametricStatistics.Projection.CoefficientRisk` (then
`.Projection.MISEDecomposition`; no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/Projection/CoefficientRisk.lean` and
  `.../Projection/MISEDecomposition.lean`. Touch nothing else (NOT `Projection/Defs.lean`).
- Goal **0 sorries**, 0 errors. Signatures/tags/docstrings frozen. You MAY add `import
  Mathlib.*` and `private` helpers. Lines ≤ 100. Escape hatch: one lifted `private` sorry +
  TODO + report. Foreground `lake build` only; never background/poll.
- After green: `#print axioms` on `coeffEstimator_mean`, `coeffEstimator_sq_error`,
  `proj_mise_decomposition` → only `propext, Classical.choice, Quot.sound`.
- Do not weaken statements; if false as stated, STOP and report.

## Available API (proved, black boxes)
- `trigBasis_discrete_orthonormal (hj : 1 ≤ j) (hj' : j ≤ n − 1) (hk : 1 ≤ k) (hk' : k ≤ n − 1) :
   (n:ℝ)⁻¹ * ∑ i : Fin n, trigBasis j (regularDesign n i) * trigBasis k (regularDesign n i)
   = if j = k then 1 else 0` — Projection/DiscreteOrthogonality.
- `trigBasis_orthonormal (hj : 1 ≤ j) (hk : 1 ≤ k) :
   ∫ x in (0:ℝ)..1, trigBasis j x * trigBasis k x = if j = k then 1 else 0`,
  `trigBasis_abs_le (j x) : |trigBasis j x| ≤ √2`, `trigBasis_measurable (j)` —
  Projection/TrigOrthogonality. (If the C2 work item has not merged when you start, these
  files may still carry sorries — your results are then `sorryAx`-tainted transitively; that
  is EXPECTED and clears when C2 lands; report it.)
- Defs: `coeffEstimator Y j = (n:ℝ)⁻¹ * ∑ i, Y i * trigBasis j (regularDesign n i)`;
  `projEstimator Y N x = ∑ j ∈ Finset.Icc 1 N, coeffEstimator Y j * trigBasis j x`;
  `seriesFun θ x = ∑' j, θ j * trigBasis j x`;
  `riemannResidual θ n j = (n:ℝ)⁻¹ * (∑ i, seriesFun θ (regularDesign n i) * trigBasis j
  (regularDesign n i)) − θ j`; `tailEnergy θ N = ∑' m, θ (N + 1 + m)^2`.

## Proofs

### CoefficientRisk.lean
1. `seriesFun_abs_le (hθ1 : Summable fun j => |θ j|) (x) : |seriesFun θ x| ≤ √2 * ∑' j, |θ j|`:
   `|∑' j, θ j * trigBasis j x| ≤ ∑' j, |θ j * trigBasis j x|` — summability of the product
   from `hθ1` + uniform bound (`Summable.of_abs`? direction: prove
   `Summable fun j => |θ j * trigBasis j x|` by comparison `|θ j * φ| ≤ √2 |θ j|`
   (`Summable.of_nonneg_of_le`, `hθ1.mul_left`); then `abs_tsum_le_tsum_abs`? — find name;
   or `norm_tsum_le_tsum_norm` with `Real.norm_eq_abs`), then termwise
   `tsum_le_tsum` against `√2 * |θ j|` and `tsum_mul_left`.
2. `summable_sq_of_summable_abs (hθ1) : Summable fun j => (θ j)^2`: eventually `|θ j| ≤ 1`?
   — cleaner: `(θ j)^2 = |θ j| * |θ j| ≤ C * |θ j|` with `C := ⨆?` — simplest: `hθ1.tendsto_atTop_zero`
   gives `|θ|` bounded (`Summable.bounded`? — a summable sequence is bounded: use
   `hθ1.tendsto_atTop_zero.bddAbove`-style or `Filter.Tendsto.isBoundedUnder`): obtain `C`
   with `∀ j, |θ j| ≤ C` (e.g. from `Summable.le_tsum`?? — DIRECT: `|θ j| ≤ ∑' i, |θ i|` by
   `le_tsum hθ1 j (fun i _ => abs_nonneg _)` ✓ elegant). Then
   `Summable.of_nonneg_of_le (sq_nonneg) (fun j => by rw sq; exact mul_le_mul_of_nonneg_right
   (le_tsum …) (abs_nonneg)…)` — careful shapes: `(θ j)^2 = |θ j|·|θ j| ≤ (∑'|θ|)·|θ j|`,
   summable RHS = `hθ1.mul_left` ✓.
3. `coeffEstimator_mean`: LHS `∫ ω, (n:ℝ)⁻¹ ∑ i (f (xᵢ) + ξ i ω) φⱼ(xᵢ) ∂P` with
   `f := seriesFun θ`, `xᵢ := regularDesign n i`. Integrability: constants + `ξ i`
   integrable — derive `Integrable (ξ i)` from `hξ2 i`: `∫⁻ ofReal (ξᵢ²) = ofReal σξ2 < ⊤` ⇒
   `MemLp (ξ i) 2 P` (AESM from `hξm`; `eLpNorm` bridge as in
   `KernelDensity/Variance.lean:kernel_summand_memLp` — replicate privately) ⇒
   `MemLp.integrable (one_le_two)`. Then `integral_finset_sum` + `integral_add` +
   `integral_const` + `hξ0 i` kills the noise; the remaining deterministic sum matches
   `θ j + riemannResidual θ n j` by DEFINITION (`riemannResidual` unfold: `ring`).
4. `coeffEstimator_sq_error`: write `θ̂ⱼ(ω) − θⱼ = αⱼ + Zⱼ(ω)` with
   `αⱼ := riemannResidual θ n j` and `Z ω := (n:ℝ)⁻¹ ∑ i, ξ i ω * φⱼ(xᵢ)`
   (algebra from the Defs; `funext`-level `have` + `lintegral_congr`).
   `∫⁻ ofReal ((αⱼ + Z)²) = ofReal (αⱼ² + ∫ Z²)`: all pieces integrable (Z ∈ L² as a finite
   sum of L² noise × consts), expand `(α + Z)² = α² + 2αZ + Z²`, `∫ Z = 0` (from `hξ0` as in
   (3)), bridge Bochner↔lintegral (`ofReal_integral_eq_lintegral_ofReal`, nonneg integrand;
   `ENNReal.ofReal_add` for the split — do it as `= ofReal (∫ (α+Z)²)` then compute the
   Bochner integral).
   `∫ Z² = (n:ℝ)⁻² * ∑ i, φⱼ(xᵢ)² * ∫ ξᵢ²`: expand the square (`Finset.sum_mul_sum`),
   off-diagonals vanish by independence + centering (`hξi.indepFun hij` +
   `IndepFun.integral_mul_eq…`; products L¹ via `MemLp.integrable_mul`); diagonal:
   `∫ ξᵢ² = σξ2` — from the EQUALITY `hξ2 i` via `ofReal_integral_eq_lintegral_ofReal`
   (integrable_sq from MemLp 2 ✓) + `ENNReal.ofReal_eq_ofReal_iff` (both sides ≥ 0 — needs
   `hσ`; alternatively `ENNReal.ofReal_injOn`… use `ENNReal.ofReal_eq_ofReal_iff
   (integral_nonneg (sq_nonneg)) hσ`).
   Then `(n:ℝ)⁻² * σξ2 * ∑ i φⱼ(xᵢ)² = σξ2/n`: the diagonal case of
   `trigBasis_discrete_orthonormal hj hj' hj hj'` gives `(n:ℝ)⁻¹ ∑ᵢ φⱼ(xᵢ)² = 1` (`if_pos`,
   `sq` vs `mul_self` massage), so `∑ᵢ φⱼ(xᵢ)² = n` (`n ≠ 0` from `1 ≤ j ≤ n−1` ⇒ `n ≥ 2`,
   `omega` + cast); `field_simp`.

### MISEDecomposition.lean
5. `proj_mise_decomposition`: with `f := seriesFun θ`, `D ω x := projEstimator (Y ω) N x − f x`.
   Setup (`hθ2 := summable_sq_of_summable_abs hθ1`; `n ≥ 2` from ranges; probability space).
   - Pointwise decomposition (∀ ω x): `D ω x = ∑ j ∈ Icc 1 N, (θ̂ⱼ ω − θⱼ) φⱼ x − g x` where
     `g x := ∑' m, θ (N+1+m) * trigBasis (N+1+m) x` (tail function): from
     `f x = ∑ j ∈ Icc 1 N?…` — CAREFUL: `f x = ∑' over ALL j` including `j = 0` (inert:
     `trigBasis 0 = 0`) and `j > N`. Establish
     `f x = (∑ j ∈ Finset.Icc 1 N, θ j * φ j x) + g x`:
     `tsum` split: `∑'_{j} = ∑_{j < N+1} + ∑'_{m} (at N+1+m)` (`Summable.sum_add_tsum_nat_add`
     — the ℕ-shifted split lemma: `(hsum).sum_add_tsum_nat_add (N+1)`; summability of
     `j ↦ θ j φ j x` by comparison with `√2|θ|` as in (1)); then `∑_{j ∈ range (N+1)} =
     θ 0·0 + ∑_{j ∈ Icc 1 N}` (`Finset.range_eq_Ico`, `Finset.sum_Ico_eq_sum_range`-free:
     `Finset.sum_range_succ'`? — simplest: `Finset.range (N+1) = insert 0 (Finset.Icc 1 N)`
     (`Finset.ext`, `omega`) + `Finset.sum_insert` + `trigBasis 0 = 0` kill).
   - L²(Icc 0 1) expansion: `∫⁻ x in Icc 0 1, ofReal ((D ω x)²)` — go Bochner first for
     fixed ω: all functions are bounded measurable on a finite measure ⇒ integrable:
     `|g x| ≤ √2 ∑'|θ|`-tail (as (1)); finite sums bounded. `∫ (∑ᵢ aᵢ φᵢ − g)² =
     ∑ᵢ aᵢ² + ∫ g² − 2∑ᵢ aᵢ ∫ φᵢ g + cross(finite×finite via orthonormality)`:
     * finite×finite: `∫ φⱼφₖ = δⱼₖ` (`trigBasis_orthonormal` — mind
       intervalIntegral `∫ x in (0)..(1)` vs set integral `∫ x in Icc 0 1`:
       `intervalIntegral.integral_of_le zero_le_one` + `integral_Icc_eq_integral_Ioc` bridges).
     * `∫ φⱼ g = ∑'ₘ θ_{N+1+m} ∫ φⱼ φ_{N+1+m} = 0` for `j ≤ N`: interchange
       `∫`–`∑'` by dominated convergence / `MeasureTheory.integral_tsum`
       (`integral_tsum` needs `∑' ∫ ‖·‖ < ∞`: `∫ |θₘ φⱼ φₘ| ≤ 2|θₘ|` summable ✓); each
       `∫ φⱼ φ_{N+1+m} = 0` (`trigBasis_orthonormal`, `j ≠ N+1+m` since `j ≤ N`, `if_neg`).
     * `∫ g² = tailEnergy θ N`: `g² = (∑'ₘ …)²` — expand via `integral_tsum` twice OR the
       cleaner route: `g` is the uniform limit of partial sums; `∫ g² = ∑'ₘ ∑'ₖ θₘθₖ ∫φφ`…
       To keep it elementary: define `g_M` partial sums, `∫ g_M² = ∑_{m<M} θ_{N+1+m}²`
       (finite orthonormality), `g_M → g` uniformly on `[0,1]`
       (`tendstoUniformlyOn_tsum_nat` with envelope `√2|θ_{N+1+m}|`), hence
       `∫ g_M² → ∫ g²` (uniform convergence on finite measure:
       `MeasureTheory.tendsto_integral_of_dominated_convergence` with constant envelope, or
       `TendstoUniformlyOn.integral_tendsto`? — check `intervalIntegral`-side name
       `intervalIntegral.tendsto_integral_of_dominated_convergence`), and
       `∑_{m<M} θ² → tailEnergy` (`HasSum.tendsto_sum_nat` of `hθ2`-shifted). Conclude by
       `tendsto_nhds_unique`.
   - Take `∫⁻ ω … ∂P`: `∫ (D ω ·)² = ∑ⱼ (θ̂ⱼ ω − θⱼ)² + tailEnergy − 0` (per-ω real identity);
     `∫⁻ ω ofReal (…) = ∑ⱼ ∫⁻ ω ofReal ((θ̂ⱼ−θⱼ)²) + ofReal (tailEnergy)`
     (`ENNReal.ofReal_add`/`ofReal_sum` on nonnegs, `lintegral_add_right`-of-const,
     `lintegral_finset_sum'` — measurability of `ω ↦ (θ̂ⱼ ω − θⱼ)²` from `hξm`);
     apply `coeffEstimator_sq_error` per `j ∈ Icc 1 N` (`1 ≤ j`, `j ≤ N ≤ n−1` ✓) and sum:
     `∑ⱼ ofReal (σξ2/n + αⱼ²) = ofReal (σξ2·N/n + ∑ αⱼ²)` (`Finset.card_Icc`, `Nat.card_Icc`:
     `card (Icc 1 N) = N` ✓, `ENNReal.ofReal_sum_of_nonneg`, algebra). Mind the outer/inner
     integral ORDER in the goal: goal has `∫⁻ ω (∫⁻ x …)` — do the per-ω x-integral first as
     above (bridge Bochner: `ofReal_integral_eq_lintegral_ofReal` per ω needs integrability
     per ω ✓ bounded), i.e. rewrite the inner `∫⁻ x` as `ofReal (real x-integral)` via
     `lintegral_congr` in ω, THEN integrate in ω. (No Tonelli needed — good, since this
     avoids joint-measurability of `projEstimator` in `(ω, x)`… it is jointly fine anyway,
     but the per-ω route is simpler.)

Report final `lake build` status for both modules + `#print axioms` for the three named
theorems (note any lifted `private` sorry and any C2-sorryAx transitive taint).
