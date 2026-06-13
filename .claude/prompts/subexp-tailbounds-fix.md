The file `StatLean/ConcentrationInequalities/SubExponential/TailBounds.lean` ALREADY EXISTS on this
branch with both theorems written (`measure_sub_integral_lt_le_quadratic`,
`measure_sub_integral_lt_le_linear`, plus private `isFiniteMeasure`) but a preemption killed the
session before it verified. `lake build StatLean.ConcentrationInequalities.SubExponential.TailBounds`
currently FAILS with these errors — fix ALL to a clean ZERO-error, ZERO-sorry build. Obey CLAUDE.md
§7 (esp. §7.2 inner, §7.10 stray-tactic). Do NOT change theorem statements; keep the names.

ERRORS:
1. line ~41 and ~136: `Unknown identifier 'one_nonneg'` → use `zero_le_one` (i.e.
   `div_nonneg zero_le_one (NNReal.coe_nonneg α)` and `div_nonneg zero_le_one hα.le`).
2. line ~164: `Unknown identifier 'le_div_iff'` → Mathlib renamed it; use `le_div_iff₀` (check
   `./tools/check.sh 'le_div_iff₀'`; the order-of-args/`one_le_div_iff` form may fit better — verify).
3. line ~143: `No goals to be solved` inside `(by rwa [abs_of_nonneg hs_nn])` — the `rw` already
   closes the goal so `rwa`'s trailing `assumption` errors; replace with just `(by rw [abs_of_nonneg hs_nn])`
   or `(abs_of_nonneg hs_nn ▸ hs_le)`, whichever builds.
4. lines ~107 and ~177: `Type mismatch` in the final `calc` (the
   `measure_mono (fun ω hω => le_of_lt hω)` step into the `ENNReal.ofReal …` bound). The working
   pattern is in `StatLean/ConcentrationInequalities/SubGaussian/TailBounds.lean` — READ IT: it uses
   an explicit `have hsub : {ω | t < …} ⊆ {ω | t ≤ …}` then
   `rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]; exact ENNReal.ofReal_le_ofReal hbrick`
   to bridge the Mathlib `μ.real` bound to the `ENNReal`-valued measure. Mirror that bridge exactly
   (the type mismatch is the `μ.real`(ℝ) vs `μ`(ℝ≥0∞) gap). The Chernoff engine is
   `measure_ge_le_exp_mul_mgf`; the mgf bound comes from `IsSubExponential.mgf_le_of_mem_Icc`.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/SubExponential/TailBounds.lean`.
# BUILD: srun -p shared -c 8 --mem=24G -t 0:40:00 lake build StatLean.ConcentrationInequalities.SubExponential.TailBounds
# DONE = build exits 0, ZERO sorries. Commit (`conc(subexp): fix two-regime tail build (Lu-BDA §3.2)`).
# Report build status + sorry count (must be 0).
