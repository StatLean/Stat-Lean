# Close the 1 remaining `sorry` (hproxy) in MEstimator/ScoreSubGaussian.lean

Lean 4 / Mathlib on `StatLean` (read `CLAUDE.md`). Pin `v4.29.1`. ON the cluster.

## CRITICAL discipline (a prior session STALLED violating this)
- Check with **plain foreground** `lake build StatLean.HighDimensionalStatistics.MEstimator.ScoreSubGaussian`,
  read the output directly. **NEVER** background a build (`&`), **NEVER** `until pgrep`/`sleep`/poll loops,
  **NEVER** nested `srun`/`sbatch`. **NEVER** leave `trace_state`/`set_option`/`#print` in the final file.
  When the build shows **0 errors and 0 sorries**, STOP immediately — do not run anything else.

## Scope
- **Only edit** the single `sorry` in the `hproxy` `have` (inside `score_coord_isSubGaussian`, ~line 148,
  marked `-- TODO(me):`). The ENTIRE rest of the file is correct and 0-sorry — do not touch it.

## The exact goal
`hproxy` must prove this `ℝ≥0` inequality (in scope: `hC : IsColumnNormalized M.X C` i.e.
`∀ j, ∑ᵢ (M.X i j)² ≤ ↑n * C²`; `hn : 0 < n`; `hn_pos : (0:ℝ) < ↑n`; `hB2 : 0 ≤ M.B^2`; `j : Fin d`):
```
(⟨(1/↑n)², _⟩ : ℝ≥0) * ∑ i, (⟨M.B² * (M.X i j)², _⟩ : ℝ≥0)  ≤  (⟨M.B²*C²/↑n, _⟩ : ℝ≥0)
```
After `refine NNReal.coe_le_coe.mp ?_` the goal is (confirmed by `trace_state`):
`↑(⟨(1/↑n)², _⟩ * ∑ i, ⟨M.B²*(M.X i j)², _⟩) ≤ M.B²*C²/↑n`.
The blocker: distributing the LHS `↑(p * ∑ᵢ qᵢ)` — `rw [NNReal.coe_mul]`, `simp only [NNReal.coe_mul,
NNReal.coe_sum]`, and `push_cast` ALL fail to fire on it ("did not find pattern"/"unused").

## Suggested routes (try in order; use `exact?`/`apply?`/`loogle` to confirm names in this pin)
1. **Find the right coercion lemmas.** `loogle "NNReal" "coe" "mul"` / `exact?` on a scratch
   `example (a b : ℝ≥0) : ((a*b:ℝ≥0):ℝ) = a*b := by exact?` and same for `∑`. The names may be
   `NNReal.coe_mul`, `NNReal.coe_sum`, or generic `map_sum`/`map_mul` via `NNReal.toRealHom`. Then a
   `rw`/`simp` that actually matches.
2. **Stay in `ℝ≥0`, avoid the outer coercion.** Prove a sum bound
   `hsum_le : ∑ i, (⟨M.B²*(M.X i j)², _⟩ : ℝ≥0) ≤ ⟨M.B² * (↑n*C²), _⟩` (via `← NNReal.coe_le_coe` then
   `NNReal.coe_sum`/`push_cast` — the SUM coercion may distribute even though the product one didn't —
   then `Finset.mul_sum` + `mul_le_mul_of_nonneg_left (hC j) hB2`). Then
   `calc ⟨(1/↑n)²,_⟩ * ∑… ≤ ⟨(1/↑n)²,_⟩ * ⟨M.B²*(↑n*C²),_⟩ := mul_le_mul_of_nonneg_left hsum_le (zero_le _)`
   `  _ = ⟨M.B²*C²/↑n, _⟩ := by rw [← NNReal.coe_inj]; push_cast; field_simp; ring` (drop `ring` if
   `field_simp` closes it — the “No goals” gotcha).
3. **Last resort:** `apply le_of_eq_of_le`/`Subtype.coe_le_coe`, or `NNReal.coe_le_coe` + prove the `ℝ`
   value of the LHS by a separate `have hval : (↑(…):ℝ) = (1/↑n)²*∑ᵢ(M.B²*(M.X i j)²) := by …` using the
   lemmas from route 1, then `rw [hval]` and finish in `ℝ` with `Finset.mul_sum` + `div_le_div_iff₀` + `nlinarith`.

Underlying `ℝ` fact: `(1/↑n)²·∑ᵢ(B²xᵢⱼ²) = B²·(∑xᵢⱼ²)/n² ≤ B²·(nC²)/n² = B²C²/n`.
Report the final `lake build` line (must be 0 sorries, 0 errors).
