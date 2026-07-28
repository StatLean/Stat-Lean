# bayes4-bpe-aux — posterior tails (10.9) + deterministic argmin consistency [wave 2]

Branch `bay/bpe-aux`. The shared rules above apply.

## Touch-set (ONLY these files)

- `StatLean/Bayesian/BayesEstimators/PosteriorTails.lean`
- `StatLean/Bayesian/BayesEstimators/ArgminConsistency.lean`

Gate: `lake build StatLean.Bayesian.BayesEstimators.PosteriorTails StatLean.Bayesian.BayesEstimators.ArgminConsistency`

Context: `PosteriorConcentration.lean` (parallel/earlier lane) contains the unweighted
Step-A machinery (`mixture_posterior_test_bound`, `posterior_mass_compl_ball_tendsto`,
`bvmLocalPosterior_compl_ball`) and `PriorSmallBall.lean` the prior bounds
(`prior_ball_inv_sqrt_lower`, `prior_tail_split`, `prior_smallBall_upper`) — use their
FROZEN statements freely (proofs may be sorries in your worktree; fine).
`MixtureContiguity.lean` provides `bvmMixture`, `bvmMixture_absolutelyContinuous`,
`mutuallyContiguous_mixture_base`, `measure_tendsto_zero_of_predictive_null`.

## Per-file targets

### PosteriorTails.lean — display (10.9)
- `posterior_tail_lintegral_tendsto`: follow the `posterior_mass_compl_ball_tendsto`
  architecture with the weight `w(h) := ofReal (1 + ‖h‖^p)` inserted:
  (i) Markov under `P^n_{θ₀}` splits off the `{φₙ ≥ 1/2}` event (typeI) — for the damped
  part note the weighted posterior integral is measurable in `ω`
  (`Kernel.measurable_lintegral`-style on the local posterior kernel).
  (ii) The weighted mixture bound: adapt `mixture_posterior_test_bound` — you cannot edit
  that file; prove the weighted variant as a `private` lemma HERE (same Fubini route with
  `Post`-lintegral of `w·1_{tail}` instead of the set mass; use
  `posterior_lintegral_eq_div` / the joint disintegration
  `ProbabilityTheory.compProd_posterior_eq_map_swap` + `Measure.lintegral_compProd`).
  The parameter-side weight after unscaling is `1 + (√n ‖θ−θ₀‖)^p`.
  (iii) The prior-side tail estimate: a `private` weighted version of `prior_tail_split` —
  `(√n)^k ∫_{tail} (1 + (√n‖θ−θ₀‖)^p) e^{−cn(‖θ−θ₀‖²∧1)} dπ → 0`; moderate zone: the
  substitution `h = √n(θ−θ₀)` gives `∫_{‖h‖≥Mₙ}(1+‖h‖^p)e^{−c‖h‖²}dh → 0`; far zone:
  `(√n)^k (1 + (√n)^p ‖θ−θ₀‖^p) e^{−c'n}` integrated against π — HERE the prior moment
  `hmom` absorbs `‖θ−θ₀‖^p` (vdV p. 148: "use the fact that ∫‖θ‖^p dΠ < ∞");
  `(√n)^{k+p} e^{−c'n} → 0`.
  (iv) Transfer back by `mutuallyContiguous_mixture_base`.

### ArgminConsistency.lean — pure analysis (no measure theory)
- `exists_gap_of_unique_argmin`: the annulus `K := {u | ‖u‖ ≤ R ∧ ρ ≤ ‖u − u₀‖}` is
  compact (closed + bounded in `EuclideanSpace`, `isCompact_closedBall`-based; it is
  `closedBall 0 R \ ball u₀ ρ` — closed subset of a compact set); if `K = ∅` any `η = 1`
  works; else `g` continuous on `K` attains its inf (`IsCompact.exists_isMinOn` for
  ℝ≥0∞-valued? — `ℝ≥0∞` is a complete linear order with continuous… use
  `IsCompact.exists_forall_le`-variant for `ℝ≥0∞`-valued continuous maps — loogle
  '"IsCompact" "exists_forall_le"'; if the ℝ≥0∞ version is missing, use
  `sInf (g '' K)` + `IsCompact.sInf_mem`-style via lower-semicontinuity, or transfer to
  `ℝ≥0∞`-order topology facts: `Continuous.exists_forall_le` on compacts exists for
  `LinearOrder` + `ClosedIciTopology` — check); the attained min `g u₁ > g u₀`
  (`hunique`, `u₁ ≠ u₀` since `ρ ≤ ‖u₁ − u₀‖`, `ρ > 0`); take
  `η := (g u₁ − g u₀) /2`-style in ℝ≥0∞ — careful with `∞`: if `g u₁ = ∞` and
  `g u₀ < ∞` take `η := 1`; in general `η := min 1 ((g u₁ − g u₀)/2)` with truncated sub;
  verify `g u₀ + η ≤ g u` for all `u ∈ K` via `g u ≥ g u₁ = attained min` — WAIT the min
  over K is what we bound BY; correct: `g u ≥ inf_K g = g u₁ ≥ g u₀ + η` by the choice of
  `η ≤ g u₁ − g u₀` (truncated-sub algebra: `a + (b − a) ≥ b`… in ℝ≥0∞
  `g u₀ + (g u₁ − g u₀) = g u₁` requires `g u₀ ≤ g u₁` ✓ and `g u₀ ≠ ∞` ✓ since
  `g u₀ < g u₁ ≤ ∞`; use `tsub_add_cancel_of_le`/`add_tsub_cancel_of_le`).
- `argmin_tendsto_of_uniform_approx`: metric-space convergence: fix `ρ > 0` (wlog
  `ρ < R − ‖u₀‖`); get `η` from the gap lemma; choose `m₀` with `εseq m + 2·δseq m < η`
  for `m ≥ m₀` (both → 0; ℝ≥0∞ order-topology: `Filter.Tendsto.add` + eventually-lt of a
  positive constant — `ENNReal.tendsto_nhds_zero`-style `∀ ε > 0, ∀ᶠ, x ≤ ε`); for
  `m ≥ m₀`, if `ρ ≤ ‖τ m − u₀‖` then chain:
  `g (τ m) ≤ z m (τ m) + δ ≤ z m u₀ + ε + δ ≤ g u₀ + ε + 2δ < g u₀ + η ≤ g (τ m)` —
  contradiction (strictness needs care in ℝ≥0∞: `g u₀ < ∞` as above; all terms finite
  along the chain since `g u₀ + ε + 2δ < g u₀ + η ≤ ∞`… ensure `g u₀ ≠ ∞` first — from
  `hunique` + `Nonempty` of points `≠ u₀` when `k ≥ 1`; for `k = 0` the space is a
  singleton and `τ m = u₀` trivially — case on `Subsingleton`).
  Conclude `‖τ m − u₀‖ < ρ` eventually; `Metric.tendsto_atTop`.

## Done

Gate green. Report per-target closed/left. No sanctioned debts in this lane — both files
should close fully.
