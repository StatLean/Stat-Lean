# MultipleTesting area — status

## STATUS: milestone — `mt/area` **green, 0 errors, 3 named sorries** (BH + Holm complete; knockoff
*assembly* `knockoff_fdr_le` + the **binomial initial reduction** complete; the 3 knockoff
supermartingale-core residuals remain — and the **construction audit** ([construction_audit.md](construction_audit.md))
shows they are entangled in a filtration-soundness issue, not mere bookkeeping).

Branch `mt/area` (worktree `../Stat-Lean-mt`). Reference: Lu, *Big Data Analysis* ch. 18–19;
Holm–Bonferroni from Holm (1979).

> **2026-06-14 (laptop-driven closure).** The three parallel cluster-Claude proof sessions
> (`bh-cores`, `ko-super-f`, `ko-init-f`) all failed on a **Sonnet usage limit (resets Jun 20)** —
> the cluster-side `claude` quota is exhausted. `lean-fasrc-build` needs no Claude quota, so the
> laptop (Opus) session closed the tractable residuals directly and verified on the cluster:
> **`knockoff_fdr_le`**, **`bh_loo_indep_mul`**, **`bh_claim`** all proven this session ⇒ BH is a
> complete theorem. The 4 remaining are the genuinely-hard knockoff cores (2 research-level
> probability, 2 intricate bookkeeping); none alone makes `knockoff_fdr_le` sorry-free.

## Fully proven (verified by fresh build)

* **ForMathlib** — `orderStat` / `orderStat_monotone`; the `thm:optstop` supermartingale
  optional-stopping bridge (`supermartingale_expected_stoppedValue_antitone`,
  `supermartingale_integral_stoppedValue_le`).
* **Holm–Bonferroni** (§17 / Holm 1979) — `holm_fwer_le`, `bonferroni_fwer_le`,
  `holm_rejects_true_null_imp`. **COMPLETE (0 sorry).**
* **Benjamini–Hochberg** (§18) — **COMPLETE (0 sorry).** The deterministic leave-one-out crux
  `bh_count_eq_leaveOneOut` + measurability lemmas, the independence factorization
  `bh_loo_indep_mul` (`iIndepFun.indepFun_finset` + the point-version count `bhNumRejPt` reusing
  `measurable_numRejections_bhRejects` + `IndepFun.measure_inter_preimage_eq_mul`), and `bh_claim`
  (forward-only crux `bh_mem_imp_le` + tower decomposition + disjoint-events `measure_biUnion_finset`
  sum bound) ⇒ `benjamini_hochberg_fdr_le`.
* **Knock-off** (§19):
  * `knockoff_fdr_le` (final FDR assembly) — **done** (`integral_mono` + `integral_const_mul` +
    `knockoff_fdp_le` + `knockoff_ratio_stopped_le_one`).
  * `knockoff_fdp_le` (deterministic FDP bound) — **done**.
  * `binom_ratio_sum_le_one` (telescoping `Nat.choose_mul_succ_eq`) — **done**.
  * Supermartingale: `θ`/`Yproc` construction, `Yproc_nonneg`, `Yproc_zero_eq`,
    `Yproc_stronglyMeasurable` (via order-statistic rank condition), `𝒢rev`, `tauStar`,
    `knockoff_supermartingale` (`supermartingale_nat`), and **`knockoff_ratio_stopped_le_one`**
    (master inequality) — all assembled. `KnockoffScore.meas` added (statistic ⇒ measurable).
  * Initial: `Splus_zero`/`Sminus_zero`/`vplus_add_vminus_le`, local binomial identity,
    `knockoff_initial_le` assembled.

## Residuals (4 named sorries) — all in the knockoff martingale, none completing `knockoff_fdr_le`

| Lemma | File | Kind | Tier |
|---|---|---|---|
| `step_condExp_le` | Knockoff/Supermartingale | one-step `μ[X_{n+1}∣𝒢ₙ] ≤ Xₙ` (Ber(½) sign field: `condExp` reductions → finite `nlinarith`) | research |
| `knockoff_initial_integral_le_binom_sum` | Knockoff/Initial | reduce `E[(N₀−V₋)/(1+V₋)]` to the `Binomial(N₀,½)` sum (law of ∑ i.i.d. fair signs) | research |
| `ratio_eq_Yproc_hittingIdx` | Knockoff/Supermartingale | `stoppedValue` ↔ `tStar` order-stat bridge (procedure threshold ↔ θ-indexing) | bookkeeping |
| `FDPhat_atTheta_adapted` | Knockoff/Supermartingale | adaptedness of the `tauStar` driver to the natural filtration of `Yproc` (comap measurability) | bookkeeping |

Closing **any subset short of all four** still leaves `knockoff_fdr_le`'s transitive cone with a
`sorry` — the knockoff theorem is sorry-free only when all four land. The two **research** cores
need the binomial law of a sum of i.i.d. `Ber(½)` indicators (`KnockoffScore.signs_iIndep` +
`signs_fair`), which has thin direct Mathlib API; the two **bookkeeping** lemmas are intricate but
non-probabilistic. Best closed by a cluster-Claude session once the Sonnet quota resets (Jun 20),
or by continued laptop sessions.

## Lessons (see memory `cluster-claude-failure-modes`)

* Cluster proof sessions **over-report build success** — every merged branch needed a fresh
  `lean-fasrc-build` that caught renamed lemmas (`div_le_iff₀`, `div_le_div_iff₀`,
  `div_le_one_of_le₀`, `lt_of_mul_lt_mul_right`), missing imports
  (`BigOperators.Field`, `Order.Group.Lattice` for `Measurable.abs`), and `field_simp`+`ring`
  "no goals". Never merge a branch unbuilt.
* Auth (401) expiry + the 64000 output-token cap blocked long/hard sessions; fixed via a
  long-lived `ANTHROPIC_API_KEY` and per-file decomposition + commit-after-each prompts.
* **Sonnet quota exhaustion (2026-06): all cluster-Claude sessions die at launch** with
  "You've hit your Sonnet limit · resets Jun 20". The cluster-side `claude` shares that quota.
  **Workaround:** `lean-fasrc-build` needs **no** Claude quota (pure sbatch), so the laptop (Opus)
  session can prove residuals directly and verify on the cluster — exactly how BH + `knockoff_fdr_le`
  closed this session.
* **Do not `tail` the build output** when checking errors — `lean-fasrc-build … | tail -N` drops
  the *earlier* `error:` lines (they scroll off), so a "rc=1, 0 sorries" with no visible error means
  you truncated it. Capture full: `lean-fasrc-build … > log 2>&1; grep 'error:' log`.

## Next steps to close the residuals

1. `knockoff_fdr_le` (tractable assembly) + `FDPhat_atTheta_adapted` + `ratio_eq_Yproc_hittingIdx`.
2. The 4 hard cores (`bh_loo_indep_mul`, `bh_claim`, `knockoff_initial_integral_le_binom_sum`,
   `step_condExp_le`) — `condExp_indep_eq` / `iIndepFun.condExp_natural_ae_eq_of_lt` + the finite
   inequality.
