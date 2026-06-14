# MultipleTesting area — status

## STATUS: milestone — `mt/area` builds **green, 0 errors, 7 named sorries** (2613 jobs).

Branch `mt/area` (worktree `../Stat-Lean-mt`). Reference: Lu, *Big Data Analysis* ch. 18–19;
Holm–Bonferroni from Holm (1979).

## Fully proven (verified by fresh build)

* **ForMathlib** — `orderStat` / `orderStat_monotone`; the `thm:optstop` supermartingale
  optional-stopping bridge (`supermartingale_expected_stoppedValue_antitone`,
  `supermartingale_integral_stoppedValue_le`).
* **Holm–Bonferroni** (§17 / Holm 1979) — `holm_fwer_le`, `bonferroni_fwer_le`,
  `holm_rejects_true_null_imp`. **COMPLETE (0 sorry).**
* **Benjamini–Hochberg** (§18) — the deterministic **leave-one-out crux**
  `bh_count_eq_leaveOneOut` + its ~9 supporting lemmas; all 3 **measurability** lemmas; the FDP
  decomposition; `benjamini_hochberg_fdr_le` assembled. *Residual:* `bh_loo_indep_mul`, `bh_claim`.
* **Knock-off** (§19):
  * `knockoff_fdp_le` (deterministic FDP bound) — **done**.
  * `binom_ratio_sum_le_one` (telescoping `Nat.choose_mul_succ_eq`) — **done**.
  * Supermartingale: `θ`/`Yproc` construction, `Yproc_nonneg`, `Yproc_zero_eq`,
    `Yproc_stronglyMeasurable` (via order-statistic rank condition), `𝒢rev`, `tauStar`,
    `knockoff_supermartingale` (`supermartingale_nat`), and **`knockoff_ratio_stopped_le_one`**
    (master inequality) — all assembled. `KnockoffScore.meas` added (statistic ⇒ measurable).
  * Initial: `Splus_zero`/`Sminus_zero`/`vplus_add_vminus_le`, local binomial identity,
    `knockoff_initial_le` assembled.

## Residuals (7 named sorries) — the genuinely-hard probabilistic cores + assemblies

| Lemma | File | Kind |
|---|---|---|
| `bh_loo_indep_mul` | BenjaminiHochberg | leave-one-out ⟂ via `iIndepFun` → product of measures |
| `bh_claim` | BenjaminiHochberg | `E[ψᵢ/(R∨1)] ≤ α/N` (tower property; uses the above) |
| `knockoff_initial_integral_le_binom_sum` | Knockoff/Initial | integral→`Binomial(N₀,½)` reduction |
| `step_condExp_le` | Knockoff/Supermartingale | **the one-step `μ[X_{n+1}∣𝒢ₙ] ≤ Xₙ`** (Ber(½) sign field) |
| `FDPhat_atTheta_adapted` | Knockoff/Supermartingale | `tauStar` adaptedness (measurability) |
| `ratio_eq_Yproc_hittingIdx` | Knockoff/Supermartingale | `stoppedValue` ↔ `tStar` order-stat bridge |
| `knockoff_fdr_le` | Knockoff (final) | assembly: `fdp_le` + `ratio_stopped_le_one` + `integral_mono` |

`step_condExp_le` is the lone research-level nugget (inside it, a finite `nlinarith` after the
`condExp` reductions). The rest are measure-theoretic plumbing / assembly.

## Lessons (see memory `cluster-claude-failure-modes`)

* Cluster proof sessions **over-report build success** — every merged branch needed a fresh
  `lean-fasrc-build` that caught renamed lemmas (`div_le_iff₀`, `div_le_div_iff₀`,
  `div_le_one_of_le₀`, `lt_of_mul_lt_mul_right`), missing imports
  (`BigOperators.Field`, `Order.Group.Lattice` for `Measurable.abs`), and `field_simp`+`ring`
  "no goals". Never merge a branch unbuilt.
* Auth (401) expiry + the 64000 output-token cap blocked long/hard sessions; fixed via a
  long-lived `ANTHROPIC_API_KEY` and per-file decomposition + commit-after-each prompts.

## Next steps to close the residuals

1. `knockoff_fdr_le` (tractable assembly) + `FDPhat_atTheta_adapted` + `ratio_eq_Yproc_hittingIdx`.
2. The 4 hard cores (`bh_loo_indep_mul`, `bh_claim`, `knockoff_initial_integral_le_binom_sum`,
   `step_condExp_le`) — `condExp_indep_eq` / `iIndepFun.condExp_natural_ae_eq_of_lt` + the finite
   inequality.
