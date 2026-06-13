Read CLAUDE.md (repo root) first and obey it — §2, §6, §7. Use the search tools. Never `lake update`.
You are ALREADY inside an srun allocation — build with plain `lake build`. This is a self-contained
REAL-ANALYSIS algebra task (no measure theory in the core lemma).

# CONTEXT
`StatLean/ConcentrationInequalities/Maximal/L2Maximal.lean` builds with ONE named sorry:
`private lemma l2_tail_numerical` (~line 298) and its consumer `theorem l2_max_tail`. The expectation
half `l2_max_expectation` is DONE — do not touch it. Close the file to ZERO sorry.

# THE SORRY (numerical core)
`l2_tail_numerical {d}[NeZero d]{σ2:ℝ≥0}{k:ℕ}{δ:ℝ}(hδ:0<δ)(hk_pos:0<k)(hk_le:k ≤ 5^d)(t)
   (ht : t = 4√σ2·√d + 2√σ2·√(2 log(1/δ))) : (k:ℝ)·exp(−(t/2)²/(2σ2)) ≤ δ`.

# FIX + PROOF
1. The lemma is FALSE for `σ2 = 0` (then `√σ2=0 ⇒ t=0 ⇒ exp(0)=1 ⇒ k·1=k > δ` possible). ADD a
   hypothesis `(hσ : 0 < (σ2:ℝ))` to `l2_tail_numerical`. At its call site in `l2_max_tail`, handle
   `σ2 = 0` SEPARATELY: when `σ2 = 0`, the sub-Gaussian vector is `0` a.e., so the event
   `{t < ‖X‖}` (with `t ≥ 0`) has μ-measure `0 ≤ ENNReal.ofReal δ` (use `rcases eq_or_lt` on `σ2`,
   the `MGF`/`IsSubGaussian` proxy `0` forcing `X = 0` a.e., or bound the event measure by `0`).
2. For `σ2 > 0`, the algebra (book sketch, already in the file's docstring):
   - `(t/2)² = σ2·(2√d + √(2 log(1/δ)))² = σ2·(4d + 4√d·√(2 log(1/δ)) + 2 log(1/δ))`
     (expand `(a+b)²`; `√σ2² = σ2` via `Real.sq_sqrt hσ.le`).
   - `(t/2)²/(2σ2) = 2d + 2√d·√(2 log(1/δ)) + log(1/δ)`. The cross term `2√d·√(2log(1/δ)) ≥ 0`.
     (If `log(1/δ) < 0`, i.e. `δ > 1`: then `√(2 log(1/δ))` is `√` of a negative = `0` in Mathlib,
     so the cross term and the `2log(1/δ)` handling need `Real.sqrt` of nonneg; just bound
     `(t/2)²/(2σ2) ≥ 2d + log(1/δ)` using `cross ≥ 0` and split on the sign of `log(1/δ)` —
     `nlinarith`/`positivity` with `Real.sq_sqrt`, `Real.sqrt_nonneg`.)
   - So `exp(−(t/2)²/(2σ2)) ≤ exp(−2d − log(1/δ)) = exp(−2d)·δ` (`Real.exp_le_exp`, `Real.exp_log hδ`,
     `Real.exp_neg`).
   - `k ≤ 5^d ≤ exp(2d)` since `5 ≤ exp 2` (`Real.add_one_le_exp`/`Real.exp_one_…`, or
     `Real.log 5 ≤ 2` ⇒ `5 ≤ exp 2`; then `5^d ≤ (exp 2)^d = exp(2d)`).
   - Multiply: `k·exp(−(t/2)²/(2σ2)) ≤ exp(2d)·exp(−2d)·δ = δ`.
   Close with `Real.exp_add`/`Real.exp_neg`, `Real.rpow`/`pow` monotonicity, and `nlinarith`/`gcongr`.

ZERO sorry. Keep `l2_max_tail`'s STATEMENT intact (only its proof may change to thread `hσ`/the
`σ2=0` split). Tag any added hypothesis appropriately.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/Maximal/L2Maximal.lean`.
# BUILD: lake build StatLean.ConcentrationInequalities.Maximal.L2Maximal
# DONE = build exits 0; ZERO sorries; commit (`conc(maximal): close l2_max_tail numerical core (Lu-BDA §4.2 thm:l2)`).
# Report build + sorry count (must be 0).
