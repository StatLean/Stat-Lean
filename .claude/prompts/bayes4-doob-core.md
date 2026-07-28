# bayes4-doob-core — Doob consistency: kernel, martingale, accessibility [wave 1]

Branch `bay/doob-core`. The shared rules above apply.

## Touch-set (ONLY these files)

- `StatLean/Bayesian/ForMathlib/IIDSeqKernel.lean`
- `StatLean/Bayesian/DoobConsistency/Basic.lean`
- `StatLean/Bayesian/DoobConsistency/PosteriorMartingale.lean`
- `StatLean/Bayesian/DoobConsistency/Accessible.lean`
- (`StatLean/Bayesian/DoobConsistency/Theorem10_10.lean` — ONLY if everything else closes
  early; it is scheduled for a later lane otherwise.)

Gate: `lake build StatLean.Bayesian.ForMathlib.IIDSeqKernel StatLean.Bayesian.DoobConsistency.PosteriorMartingale StatLean.Bayesian.DoobConsistency.Accessible`

Provided 0-sorry (verified on the pin — reuse, do not reprove):
- `MeasureTheory.Measure.infinitePi` + `infinitePi_cylinder`, `infinitePi_pi`,
  `infinitePi_map_eval`, `IsProbabilityMeasure (infinitePi …)` instance
  (`Mathlib/Probability/ProductMeasure.lean`).
- `MeasureTheory.measurableCylinders`: `generateFrom_measurableCylinders` (line ~351),
  `isPiSystem_measurableCylinders` (line ~323) in
  `Mathlib/MeasureTheory/Constructions/Cylinders.lean`;
  `MeasurableSpace.induction_on_inter`; `Measure.measurable_of_measurable_coe`
  (`Mathlib/MeasureTheory/Measure/GiryMonad.lean:54`).
- `StatLean.Bayesian.measurable_pi_fintype_const_kernel` (same file, already proved) and
  `iidKernel`/`iidKernel_apply` (`Bayesian/ForMathlib/IIDKernel.lean`).
- `AsymptoticStatistics.pi_const_eq_infinitePi_map`
  (`AsymptoticStatistics/ForMathlib/IIdJointLaw.lean:101`):
  `Measure.pi (fun _ : Fin n => ν) = (Measure.infinitePi (fun _ : ℕ => ν)).map
   (fun ω (i : Fin n) => ω i.val)`.
- `MeasureTheory.Integrable.tendsto_ae_condExp` (Lévy upward,
  `Mathlib/Probability/Martingale/Convergence.lean:360`): needs a `Filtration ℕ`,
  `[SigmaFiniteFiltration]`, integrable `g`, `StronglyMeasurable[⨆ n, ℱ n] g`; conclusion
  `∀ᵐ x, Tendsto (μ[g | ℱ n] x) atTop (𝓝 (g x))`.
- `ProbabilityTheory.condDistrib` (def: `(μ.map fun a => (X a, Y a)).condKernel`) and
  `condDistrib_ae_eq_condExp` (`Mathlib/Probability/Kernel/CondDistrib.lean:321`):
  `(fun a => (condDistrib Y X μ (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s | mβ.comap X⟧`.
- `ProbabilityTheory.posterior` (def: `((μ ⊗ₘ κ).map Prod.swap).condKernel`,
  `Mathlib/Probability/Kernel/Posterior.lean`).
- `ProbabilityTheory.strong_law_ae` (`Mathlib/Probability/StrongLaw.lean:788`);
  `ProbabilityTheory.iIndepFun_infinitePi` (`Mathlib/Probability/Independence/InfinitePi.lean:83`).
- `Measurable.measurableEmbedding` (Lusin–Souslin: injective measurable map from a standard
  Borel space is a measurable embedding; `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:875`);
  `MeasurableEmbedding.measurableSet_range`, `measurable_rangeSplitting`
  (`Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`).
- `MeasureTheory.Measure.ae_compProd_of_ae_ae`, `ae_ae_of_ae_compProd`
  (`Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:113/118`);
  `Measure.ae_map_iff` for the `Prod.swap` pushforward.
- `MeasurableSpace.CountablyGenerated` for standard Borel spaces;
  `MeasureTheory.ext_of_generate_finite` (π-system uniqueness);
  `MeasurableSpace.generatePiSystem` + `isPiSystem_generatePiSystem` +
  `generateFrom_generatePiSystem_eq` (`Mathlib/MeasureTheory/PiSystem.lean:241-274`).

## Per-file targets

### IIDSeqKernel.lean
- `measurable_infinitePi_const_kernel`: `Measure.measurable_of_measurable_coe` +
  `MeasurableSpace.induction_on_inter` with `h_eq := generateFrom_measurableCylinders.symm`,
  `h_inter := isPiSystem_measurableCylinders`; basic case: a cylinder is
  `(restrict to s) ⁻¹' S`; `infinitePi_cylinder` reduces its measure to a finite product
  over the `Finset` index — measurable in `θ` by `measurable_pi_fintype_const_kernel`
  (already proved above in the same file); compl/iUnion cases as in
  `measurable_pi_const_kernel` (probability measure ⇒ `measure_ne_top`).
- `iidSeqKernel_map_restrict`: `Kernel.ext` + `Kernel.map_apply` (restriction map is
  measurable: `measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)`); pointwise
  it is `pi_const_eq_infinitePi_map` applied at `ν := K θ` (needs
  `IsProbabilityMeasure (K θ)` — from `IsMarkovKernel`), symmetrized.

### Basic.lean (DoobConsistency)
- `measurable_doobData`: `measurable_pi_lambda` + `measurable_fst` + `measurable_pi_apply`.
- `doobSigma_mono`: `doobData m = (restrict₂) ∘ doobData n` for `m ≤ n` (compose with
  `Fin.castLE`); `MeasurableSpace.comap_comp` + `MeasurableSpace.comap_mono`-direction
  (comap of a composition factors; the restriction is measurable).
- `doobSigma_le`: `Measurable.comap_le (measurable_doobData n)`.

### PosteriorMartingale.lean
- `iSup_comap_data_eq_pi`: `≤`: each comap ≤ pi by measurability. `≥`: `MeasurableSpace.pi`
  is `⨆ i, comap (eval i)`; each `eval i` factors through the first `i+1` coordinates:
  `eval i = (eval ⟨i, _⟩ : (Fin (i+1) → 𝓧) → 𝓧) ∘ (data (i+1))`, so
  `comap (eval i) ≤ comap (data (i+1)) ≤ ⨆`. Use `MeasurableSpace.comap_comp` and
  `iSup_le`/`le_iSup`.
- `iSup_doobSigma_eq_comap_fst`: `doobData n = (restrict) ∘ Prod.fst`;
  `comap_comp` turns each `doobSigma n` into `(comap fst) ∘ comap(restrict)`; push the
  `⨆` inside comap (`MeasurableSpace.comap_iSup` — check exact name/direction with
  loogle '"comap_iSup"') and finish with `iSup_comap_data_eq_pi`.
- `doobJoint_map_data_param`: both sides are pushforwards of `π ⊗ₘ iidSeqKernel K`;
  compute with `Measure.map_map` (measurable components) and reduce to
  `(π ⊗ₘ iidSeqKernel K).map (fun p => (restrict p.2, p.1)) =
   (π ⊗ₘ iidKernel K n).map Prod.swap`, which follows from
  `Measure.compProd`-map-right: `(π ⊗ₘ κ).map (Prod.map id g) = π ⊗ₘ (κ.map g)`
  (find: loogle '"compProd" "map"' — e.g. `Measure.compProd_map`-shape or prove via
  `Measure.ext` + `Measure.compProd_apply` + `Kernel.map_apply`) + `iidSeqKernel_map_restrict`.
- `condDistrib_doobData_eq_posterior`: unfold `condDistrib` (`condDistrib_def`-style; it is
  an `irreducible_def` — use its `_def` equation lemma) and `posterior` (same); both are
  `Measure.condKernel` applied to measures equal by `doobJoint_map_data_param`
  (note `(doobJoint K π).map (fun ω => (doobData n ω, ω.2))` IS the condDistrib input for
  `Y := Prod.snd`, `X := doobData n`); finish with `congrArg`.
- `posterior_ae_tendsto_indicator`: build `ℱ : Filtration ℕ _` from `doobSigma` +
  `doobSigma_mono` + `doobSigma_le`; `g := A.indicator 1 ∘ Prod.snd` is integrable
  (bounded, probability measure) and `StronglyMeasurable[⨆ n, ℱ n]`: by `hrec`, `Prod.snd`
  agrees a.e. with `g₀ ∘ Prod.fst` (comap-fst-measurable); `⨆ ℱ = comap fst`
  (`iSup_doobSigma_eq_comap_fst`) — use the a.e.-version of Lévy: apply
  `Integrable.tendsto_ae_condExp` to the honest `comap fst`-measurable modification
  `A.indicator 1 ∘ g ∘ Prod.fst` and transfer along the a.e.-equality
  (`condExp_congr_ae` + `Filter.EventuallyEq.tendsto_iff`-style pointwise transfer);
  identify `μ[g | ℱ n]` with the posterior mass via `condDistrib_ae_eq_condExp` +
  `condDistrib_doobData_eq_posterior` (a.e. per `n`, countably many `n`).

### Accessible.lean
- `exists_countable_measure_determining`: `CountablyGenerated 𝓧` gives a countable
  generating family `b`; close under finite intersections
  (`MeasurableSpace.generatePiSystem` of a countable set is countable — if no library lemma,
  enumerate finite subsets of ℕ (`Encodable`) and intersect); determining by
  `ext_of_generate_finite` (needs `univ` handled: probability measures agree on `univ`).
- `empirical_freq_ae_tendsto`: `strong_law_ae` with `X i ω := A.indicator 1 (ω i)` (real
  valued, integrable: bounded); `iIndepFun_infinitePi` + `iIndepFun.comp`; identify
  `E[X 0] = (K θ A).toReal` (`integral_indicator_one`-style + `infinitePi_map_eval`);
  match the `n⁻¹ * ∑` normalization with `strong_law_ae`'s `(n:ℝ)⁻¹ • ∑` (real smul =
  mul).
- `exists_measurable_retraction`: with `(A m)` from the determining lemma, define
  `F : Θ → ℕ → ℝ`, `F θ m := (K θ (A m)).toReal` — measurable
  (`Kernel.measurable_coe` + `Measure.measurable_measure`… per-m + `measurable_pi_lambda`,
  `ENNReal.measurable_toReal`), injective (`hK_inj` + determining). `ℕ → ℝ` is standard
  Borel; `Measurable.measurableEmbedding F` (Lusin–Souslin). Define the empirical-limit map
  `E : (ℕ → 𝓧) → ℕ → ℝ`, `E ω m := limsup (fun n => n⁻¹ ∑_{i<n} 1_{A m}(ω i))` —
  measurable (countable limsup; use `Real.toNNReal`-free route via `Filter.limsup` on ℝ
  with `measurable_limsup`-style lemmas — loogle '"measurable" "limsup"'; if ℝ-limsup
  measurability is awkward, take `E ω m := limsup` in `ℝ≥0∞` of `ofReal`s and convert).
  Retraction: `g := (rangeSplitting-style inverse of F) ∘ E` with default value via
  `Function.extend`/`piecewise` on `MeasurableEmbedding.measurableSet_range`;
  a.e.-identity: for π-a.e. θ (in fact all θ), `K θ`-iid-a.s. `E ω = F θ`
  (`empirical_freq_ae_tendsto`, countably many m; limsup of a convergent sequence is its
  limit — `Filter.Tendsto.limsup_eq`), hence `g ω = θ`; lift to `doobJoint` via
  `ae_compProd_of_ae_ae` + `Measure.ae_map_iff` through `Prod.swap` (the identity event is
  measurable: `{p | g p.1 = p.2}` needs measurable diagonal — `Θ` standard Borel ⇒
  `MeasurableSingletonClass` + separated: use `measurableSet_eq_fun` variants for
  countably-separated codomains — loogle '"measurableSet_eq_fun"').

## Done

Gate green; per-target closed/left. Sanctioned NAMED DEBTS (max 2):
`posterior_ae_tendsto_indicator` (if the condExp bookkeeping resists),
`exists_measurable_retraction` (if the limsup-measurability detour resists). Close all of
IIDSeqKernel and Basic regardless.
