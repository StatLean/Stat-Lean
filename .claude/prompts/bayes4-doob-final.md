# bayes4-doob-final — Theorem 10.10 (Doob's consistency theorem) [wave 2/3]

Branch `bay/doob-final`. The shared rules above apply.

## Touch-set (ONLY this file)

- `StatLean/Bayesian/DoobConsistency/Theorem10_10.lean`

(If `bay/doob-core` left named debts in `PosteriorMartingale.lean` / `Accessible.lean`,
you may ALSO close those two files — check their sorry counts first and report what you
found. Do not touch `Defs.lean` or `Basic.lean`.)

Gate: `lake build StatLean.Bayesian.DoobConsistency.Theorem10_10`

Available on your base branch (closed in wave 1 — trust the statements):
- `posterior_ae_tendsto_indicator` (`PosteriorMartingale.lean`): given a measurable
  a.e.-retraction `g` with `g ω.1 = ω.2` `doobJoint`-a.s., for every measurable `A ⊆ Θ`,
  `doobJoint`-a.s. `((iidKernel K n)†π) (doobData n ω) A → 1_A(ω.2)` (as reals);
- `exists_measurable_retraction` (`Accessible.lean`): identifiability + standard Borel ⇒
  such a `g` exists;
- `condDistrib_doobData_eq_posterior`, `iSup_doobSigma_eq_comap_fst`,
  `doobJoint_map_data_param` (same file);
- `iidSeqKernel`, `iidSeqKernel_map_restrict` (`Bayesian/ForMathlib/IIDSeqKernel.lean`);
- `doobJoint`, `doobData`, `doobSigma`, `StronglyConsistentAt` (`Defs.lean`) — the
  consistency predicate is the BALL form: `∀ᵐ ω ∂(K θ)^⊗ℕ, ∀ ε > 0,
  Post_n(ball θ ε) → 1`.

## Target: `doob_consistency`

`∀ᵐ θ ∂π, StronglyConsistentAt K π θ`.

Route:
1. Obtain `g` from `exists_measurable_retraction` (instances: `Θ` is `MetricSpace` +
   `PolishSpace` + `BorelSpace` ⇒ `StandardBorelSpace` by
   `standardBorel_of_polish`; `Nonempty Θ` given; `𝓧` standard Borel given).
2. **Countable family of balls.** `Θ` is Polish ⇒ separable: take a dense sequence
   `(dᵢ)` (`TopologicalSpace.denseSeq` / `exists_dense_seq`) and rational radii `qⱼ > 0`;
   the countable family `Bᵢⱼ := ball dᵢ qⱼ` is measurable (open) and has the key property:
   for every `θ` and every `ε > 0` there are `i, j` with `θ ∈ Bᵢⱼ ⊆ ball θ ε`
   (density + triangle: pick `qⱼ < ε/2` and `dᵢ` within `qⱼ/2` of `θ`).
3. Apply `posterior_ae_tendsto_indicator` to each `Bᵢⱼ` (countably many) and intersect the
   a.s. sets (`MeasureTheory.ae_all_iff` over a countable index).
4. On the resulting full-measure set: for `ω` with parameter `θ := ω.2`, given `ε > 0`
   choose `(i,j)` as in 2; then `1_{Bᵢⱼ}(θ) = 1` so `Post_n(Bᵢⱼ) → 1`; monotonicity
   `Post_n(ball θ ε) ≥ Post_n(Bᵢⱼ)` (`measure_mono`) and `≤ 1` (probability kernel) give
   `Post_n(ball θ ε) → 1` (squeeze: `tendsto_of_tendsto_of_tendsto_of_le_of_le'` with the
   constant-1 upper bound; work in `ℝ≥0∞` or via `.toReal` consistently with the
   `StronglyConsistentAt` statement — check whether it is stated in `ℝ≥0∞` (it is:
   `Tendsto (fun n => ((iidKernel K n)†π) … (ball θ ε)) atTop (𝓝 1)` in `ℝ≥0∞`), so
   convert the `.toReal` conclusion of `posterior_ae_tendsto_indicator` back with
   `ENNReal.tendsto_toReal_iff`-style lemmas + `measure_ne_top`).
5. **Disintegrate to `π`-a.e. θ.** The statement obtained in 4 is `doobJoint`-a.s. on
   `(ℕ→𝓧) × Θ`. `doobJoint K π = (π ⊗ₘ iidSeqKernel K).map Prod.swap`, so
   `∀ᵐ` under `doobJoint` transfers to `∀ᵐ` under `π ⊗ₘ iidSeqKernel K` through
   `Measure.ae_map_iff` (`Prod.swap` is a `MeasurableEquiv`; the event must be measurable —
   it is a countable intersection of `Tendsto` events, measurable by
   `measurableSet_tendsto`-type lemmas + measurability of
   `ω ↦ Post_n(doobData n ω)(ball θ ε)` in BOTH coordinates: the ball depends on `θ = ω.2`,
   so use the countable-family version from step 2/3 where the sets are FIXED — this is
   why the reduction to `Bᵢⱼ` must happen BEFORE the disintegration; keep the measurable
   event as `⋂_{i,j} {ω | 1_{Bᵢⱼ}(ω.2) = 1 → Tendsto … (𝓝 1)}`).
   Then `Measure.ae_ae_of_ae_compProd` gives: for `π`-a.e. `θ`,
   `(iidSeqKernel K θ)`-a.e. data sequence satisfies the property — and
   `iidSeqKernel K θ = Measure.infinitePi (fun _ => K θ)`, exactly the measure in
   `StronglyConsistentAt`. Note `doobData n (ω, θ) = fun i => ω i.val` matches the
   `StronglyConsistentAt` argument `fun i : Fin n => ω i.val` definitionally.

## Done

Gate green + `#print axioms doob_consistency` clean (expect only
`propext, Classical.choice, Quot.sound`). Report closed/left and, if you also worked on
`PosteriorMartingale.lean`/`Accessible.lean`, their before/after sorry counts.
