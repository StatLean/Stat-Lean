# Mathlib bricks — verification table (work item V1)

**Status: VERIFIED against the pin** (rev `5e932f97…`, Lean v4.29.1) on 2026-06-12, by `grep`-ing the pinned Mathlib source in the shared cache (`rg` is NOT installed on the cluster — use `grep -rlF`). `check.sh` is authoritative but ~330s cold; `grep` over `…/mathlib/<rev>/Mathlib` is the fast pin-accurate method. Re-confirm a name's exact *signature* with `./tools/check.sh '<name>'` when you wire it into a proof.

| Concept | Mathlib name | Pinned? (module) |
|---|---|---|
| Sub-Gaussian MGF | `ProbabilityTheory.HasSubgaussianMGF` | ✓ `Probability/Moments/SubGaussian.lean` |
| Hoeffding sum bound | `…HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun` | ✓ same |
| bounded⇒sub-G | `hasSubgaussianMGF_of_mem_Icc…` (Hoeffding lemma) | ✓ same |
| Hoeffding lemma (mgf) | `mgf_le_of_mem_Icc_of_integral_eq_zero` | ✓ same |
| cond. sub-G MGF | `HasCondSubgaussianMGF` | ✓ same |
| Azuma | `measure_sum_ge_le_of_hasCondSubgaussianMGF` | ✓ same |
| Chernoff-from-MGF | `ProbabilityTheory.measure_ge_le_exp_mul_mgf` | ✓ `Probability/Moments/Basic.lean` |
| condExp kernel (McDiarmid Doob) | `condExpKernel` | ✓ `Probability/Independence/Conditional.lean` |
| **Covering numbers** | `Metric.coveringNumber` | ✓ `Topology/MetricSpace/CoveringNumbers.lean` — **present; no fallback needed** |
| Strong LLN | `…strong_law_ae` | ✓ `Probability/StrongLaw.lean` |
| i.i.d. CLT | `…tendstoInDistribution_inv_sqrt_mul_sum_sub` | ✓ `Probability/CentralLimitTheorem.lean` |
| Markov | `mul_meas_ge_le_integral_of_nonneg` | ✓ `MeasureTheory/Integral/Bochner/Basic.lean` |
| Euclidean ball volume | `…volume_ball` | ✓ `MeasureTheory/Measure/Lebesgue/Basic.lean` |
| Haar scaling | `…addHaar_smul` | ✓ `MeasureTheory/Constructions/HaarToSphere.lean` |
| `∫ tsum` (Bernstein MGF) | `integral_tsum` | ✓ `MeasureTheory/Function/ConditionalLExpectation.lean` |
| orthogonal projection (OLS) | `orthogonalProjection` | ✓ `Analysis/InnerProductSpace/Adjoint.lean` |

**Still to build ourselves** (confirmed NOT a single decl in the pin): McDiarmid bounded-differences (build from `condExpKernel` + cond-subG Azuma); sub-exponential / Bernstein tails; the `(1+2/ε)^d` ball-covering count (from `coveringNumber` + Haar scaling). Decompose-don't-despair per CLAUDE.md §6; extract reusable bricks as `ForMathlib`-layer lemmas.
