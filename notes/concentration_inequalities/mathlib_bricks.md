# Mathlib bricks — verification table (work item V1)

**Status: NOT YET VERIFIED against the pin.** The names below come from LeanExplore semantic search, whose index may be newer than the pinned Mathlib (rev `5e932f97…`, Lean v4.29.1). **Every name must be re-checked on the cluster** with `./tools/check.sh '<name>'` / `./tools/loogle.sh '"<substr>"'` before any scaffold statement references it. A 0-hit is not proof of absence — try type-shape loogle and `#leansearch`/`explore.sh` for folk names.

Fill the **Pinned?** column with ✓ / ✗ / signature notes as each is confirmed.

| Concept | Candidate Mathlib name | Pinned? |
|---|---|---|
| Sub-Gaussian MGF | `ProbabilityTheory.HasSubgaussianMGF` (+ `.measure_ge_le`, `.cgf_le`, `.neg`, closure) | |
| Hoeffding sum bound | `ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun` | |
| Hoeffding lemma (bounded⇒sub-G) | `mgf_le_of_mem_Icc_of_integral_eq_zero` / `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` | |
| Azuma (cond. sub-G) | `ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF` + `HasCondSubgaussianMGF` | |
| Chernoff-from-MGF | `ProbabilityTheory.measure_ge_le_exp_mul_mgf` (+ `mgf`, `cgf` API) | |
| condExp kernel bridge | `condExpKernel`, `condExp` partial-integral lemmas (for McDiarmid Doob) | |
| Covering numbers | `Metric.coveringNumber` / `externalCoveringNumber` / `IsCover` — **HIGH pin risk**; fallback = define ourselves in a ForMathlib file | |
| Strong LLN | `ProbabilityTheory.strong_law_ae` (exact name/signature) | |
| i.i.d. CLT | `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub` | |
| Markov | `MeasureTheory.mul_meas_ge_le_integral_of_nonneg` (or `meas_ge_le_…`) | |
| McDiarmid / bounded-difference | (check whether a PR landed; expected ✗) | |
| Euclidean ball volume / Haar scaling | `EuclideanSpace.volume_ball`, `MeasureTheory.Measure.addHaar_smul` | |
| `∫ tsum` / series MGF | `MeasureTheory.integral_tsum` variant (for Bernstein MGF) | |
| Jensen for `exp` | (name for finite-maximal `E max ≤ …`) | |

Decompose-don't-despair: for any composite that 2–3 substring/type-shape misses, rewrite in Mathlib-constructor language and assemble from bricks (CLAUDE.md §6). Record reusable bricks as `ForMathlib`-layer lemmas.
