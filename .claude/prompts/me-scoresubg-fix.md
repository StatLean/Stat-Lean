# Fix the `hproxy` proof in MEstimator/ScoreSubGaussian.lean (NNReal coercion + algebra)

Lean 4 / Mathlib on `StatLean` (read `CLAUDE.md`). Pin `v4.29.1`. ON the cluster.

## CRITICAL build discipline (a prior session STALLED by violating this)
- Check with **plain foreground** `lake build StatLean.HighDimensionalStatistics.MEstimator.ScoreSubGaussian`,
  read the output directly. **NEVER** background a build (`&`), **NEVER** `until pgrep`/`sleep`/poll loops,
  **NEVER** nested `srun`/`sbatch`, **NEVER** `trace_state`/`set_option` left in committed code. When the build
  shows 0 errors + 0 sorries, STOP immediately.

## The situation
The whole file compiles EXCEPT the `hproxy` `have` inside `score_coord_isSubGaussian` (~line 148). Everything
else (`score_term_hasSubgaussianMGF`, the `y_*` helpers, independence, sum, mean-zero, final assembly) is DONE
and correct — **do not touch anything except the `hproxy` block.** `hproxy` must prove (in `ℝ≥0`):

`(⟨(1/n)², _⟩ : ℝ≥0) * ∑ i, (⟨B²·(M.X i j)², _⟩ : ℝ≥0) ≤ (⟨B²·C²/n, _⟩ : ℝ≥0)`

i.e. after coercion to `ℝ`: `(1/n)² · ∑ᵢ (B²·(M.X i j)²) ≤ B²·C²/n`, which follows from
`hC j : ∑ᵢ (M.X i j)² ≤ n·C²` (G1), `hn : 0 < n`, `hB2 : 0 ≤ B²`.

The failure is the NNReal-coercion step: `rw`/`simp only [NNReal.coe_mul, NNReal.coe_sum, NNReal.coe_mk]`
does not distribute the `↑(a * ∑ …)` on the LHS (the lemmas come back "unused" / "pattern not found").

## How to fix
1. Replace the `hproxy` proof body. First **inspect the goal**: temporarily add `trace_state` right after
   you enter the proof and run the build to read the exact coercion shape — THEN **delete the `trace_state`
   before your final build** (do not commit it).
2. Robust route to try (in order):
   - `rw [← NNReal.coe_le_coe]` then `push_cast [NNReal.coe_sum]` (push_cast handles `coe_mul`/`coe_mk`/`coe_pow`
     as norm_cast lemmas; pass `NNReal.coe_sum` explicitly). Then the `ℝ` goal should be
     `(1/n)² * ∑ᵢ (B² * (M.X i j)²) ≤ B² * C² / n`.
   - If the `⟨_, _⟩` literals block push_cast, first `simp only [NNReal.coe_mk]` then `push_cast`/`norm_cast`,
     or prove the `ℝ` inequality as a separate `have hr : … ≤ …` and lift with
     `NNReal.coe_le_coe.mp (by …)` / `by exact_mod_cast hr`.
   - Finish the `ℝ` inequality: `rw [← Finset.mul_sum]` to get `(1/n)² * (B² * ∑ᵢ (M.X i j)²) ≤ B²C²/n`,
     then clear denominators (`rw [div_le_div_iff₀ (by positivity) (by positivity)]` or
     `rw [le_div_iff₀, ...]`) and `nlinarith [mul_le_mul_of_nonneg_left (hC j) hB2, hn_pos, sq_nonneg ...]`.
     If division fights `nlinarith`, multiply through `n²` manually with `field_simp` first, or feed
     `nlinarith` the products it needs (`mul_pos`, `mul_le_mul_of_nonneg_left`).

Keep the `hproxy` statement (its type) UNCHANGED — only its proof. Lines ≤ 100. Report the final `lake build`
line (0 sorries, 0 errors).
