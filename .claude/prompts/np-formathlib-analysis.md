# Close the 4 sorries in NonparametricStatistics/ForMathlib/{MinkowskiIntegral,TranslationL2,TailSumRpow}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON the
cluster — iterate with plain `lake build StatLean.NonparametricStatistics.ForMathlib.MinkowskiIntegral`
(then `.ForMathlib.TranslationL2`, `.ForMathlib.TailSumRpow`; no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/ForMathlib/MinkowskiIntegral.lean`,
  `.../TranslationL2.lean`, `.../TailSumRpow.lean`. Touch nothing else.
- Goal **0 sorries**, 0 errors. Keep theorem signatures, tags, docstrings UNCHANGED. You MAY add
  `import Mathlib.*` lines and `private` helper lemmas. Lines ≤ 100. If a piece resists, lift it
  to a `private lemma` with one `sorry` + `-- TODO(np):` and report. Run plain foreground
  `lake build` only — NEVER background it or poll with pgrep loops.
- After green: `#print axioms` on `lintegral_lintegral_sq_rpow_le`,
  `tendsto_lintegral_sq_sub_translate`, `tsum_nat_add_rpow_neg_le` → only
  `propext, Classical.choice, Quot.sound`.
- Do not weaken statements. If you believe one is false as stated, STOP and report why.

## Proofs

### A. `lintegral_lintegral_sq_rpow_le` (MinkowskiIntegral.lean) — generalized Minkowski, L²
Goal: `(∫⁻ x, (∫⁻ u, g u x ∂μ)^2 ∂ν)^(1/2:ℝ) ≤ ∫⁻ u, (∫⁻ x, (g u x)^2 ∂ν)^(1/2:ℝ) ∂μ`
for `g : α → β → ℝ≥0∞` jointly measurable, `μ ν` σ-finite.
- FIRST search Mathlib for an existing Minkowski integral inequality at `eLpNorm`/`lintegral`
  level: `loogle 'ENNReal.lintegral'` + `'"Minkowski"'`, `'"lintegral_Lp"'`,
  `MeasureTheory.lintegral_prod_norm_pow_le` (a known Hölder-type iterated-product lemma —
  check what exists near `Mathlib/MeasureTheory/Integral/MeanInequalities.lean`; that file has
  `ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr` and possibly a `lintegral_Lp_norm...`-style Minkowski
  for double integrals — `MeasureTheory.lintegral_Lp_norm_le`?? explore `api` of
  `MeasureTheory/Integral/MeanInequalitiesPow.lean` and `MeanInequalities.lean`). If a usable
  form exists, this is a wrapper; adapt exponents (`p = 2`).
- If not found, the self-contained duality proof (all in `ℝ≥0∞`, no integrability side
  conditions): let `S x := ∫⁻ u, g u x ∂μ` and `A := (∫⁻ x, (S x)^2 ∂ν)^(1/2)`.
  * If `A = 0` trivial. If `A = ⊤`: show RHS `= ⊤` too — this needs care; alternative that
    avoids the ⊤ case entirely: prove the TRUNCATED version first — for every measurable
    `φ : β → ℝ≥0∞` with `∫⁻ x, (φ x)^2 ∂ν ≤ 1`:
    `∫⁻ x, S x * φ x ∂ν = ∫⁻ u, (∫⁻ x, g u x * φ x ∂ν) ∂μ` (Tonelli,
    `MeasureTheory.lintegral_lintegral_swap`, joint measurability of `(u,x) ↦ g u x * φ x`)
    `≤ ∫⁻ u, (∫⁻ x, (g u x)^2 ∂ν)^(1/2) * (∫⁻ x, (φ x)^2 ∂ν)^(1/2) ∂μ`
    (Cauchy–Schwarz for `∫⁻`: `ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2` —
    check its exact form/hypotheses (conjugate exponents `.IsConjExponent`), in
    `Mathlib.MeasureTheory.Integral.MeanInequalities`) `≤ RHS` (since the φ-factor `≤ 1`).
  * Then take the supremum over φ: the sharp choice is `φ := S^{p-1}/A^{...}`-style; for `p = 2`
    take `φ x := S x / A` when `0 < A < ⊤` (measurable since `S` is — `Measurable.lintegral_prod_right'`
    for measurability of `S`!): `∫⁻ (φ)^2 = (∫⁻ S^2)/A^2 = 1` (`ENNReal.div_pow`,
    `lintegral_div_const'`-style — division algebra: `ENNReal.div_le_iff`/`ENNReal.le_div_iff_mul_le`
    with `A ≠ 0, A ≠ ⊤`), and `∫⁻ S·φ = (∫⁻ S²)/A = A`. Conclude `A ≤ RHS`.
  * Remaining `A = ⊤` case: truncate — apply the finite case to `gₙ := fun u x => min (g u x) n`
    restricted to a σ-finite exhaustion (`SigmaFinite` spanning sets) so that `Sₙ` has finite
    square integral; let `n → ∞` by `lintegral_iSup`/monotone convergence
    (`MeasureTheory.lintegral_iSup` with monotonicity, `ENNReal.rpow`-continuity via
    `ENNReal.rpow_le_rpow` monotone sup). If the truncation bookkeeping gets heavy, an
    acceptable alternative: prove the SQUARED form
    `∫⁻ x, (S x)^2 ∂ν ≤ (∫⁻ u, (∫⁻ x, (g u x)^2 ∂ν)^(1/2) ∂μ)^2` by the same duality (this is
    what consumers use anyway — but do NOT change the stub statement; derive the stub from the
    squared form via `ENNReal.rpow_le_rpow … (by norm_num : (0:ℝ) ≤ 1/2)` +
    `ENNReal.rpow_natCast`/`ENNReal.rpow_mul` to cancel `(·^2)^(1/2)`).

### B. `tendsto_lintegral_sq_sub_translate` (TranslationL2.lean)
Goal: `Tendsto (fun t => ∫⁻ x, ofReal ((f (x+t) − f x)^2)) (𝓝 0) (𝓝 0)` for measurable
`f ∈ L²(volume)`.
- FIRST search Mathlib for continuity of translation on `Lp`:
  `loogle '"Lp"' '"translate"'`, `'"comp_add"'`, `Mathlib/MeasureTheory/Function/LpSpace` dir,
  `Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean` (its proof uses exactly this fact —
  check what lemma it invokes; something like `tendsto_integral_comp_add_right...` or
  `MeasureTheory.Lp.continuous_comp_add`?). If found, bridge `eLpNorm`² ↔ the `∫⁻ ofReal` form:
  `eLpNorm (g) 2 volume = (∫⁻ x, ‖g x‖ₑ^2)^(1/2)` (`eLpNorm_eq_lintegral_rpow_enorm`,
  `toReal 2 = 2`, `‖a‖ₑ^2 = ofReal (a^2)` via `Real.enorm_eq_ofReal_abs`, `sq_abs`,
  `ENNReal.ofReal_pow`); convergence of the square from convergence of the norm
  (`ENNReal.Tendsto.pow` / continuity of `x ↦ x^2` at `0`).
- Self-contained fallback (3ε via continuous compactly supported density):
  `hf2.exists_hasCompactSupport_eLpNorm_sub_le` (exists on pin? verify; else
  `MeasureTheory.Memℒp/MemLp.exists_hasCompactSupport…` family) gives `φ` continuous compactly
  supported with `eLpNorm (f − φ) 2 ≤ ε'`. Then split
  `f(·+t) − f = (f−φ)(·+t) + (φ(·+t) − φ) + (φ − f)`; the translated term has the SAME
  `eLpNorm` (translation invariance: `eLpNorm_comp_add_right`?? — derive via
  `lintegral_add_right_eq_self`/`Measure.map_add_right_eq_self` and `lintegral_map'`); the
  middle term → 0 as `t → 0`: `φ` uniformly continuous with compact support (`HasCompactSupport.uniformContinuous_of_continuous`?
  — `Continuous.uniformContinuous_of_hasCompactSupport`?), sup bound `≤ δ(t)` on a FIXED
  compact `K' = thickening 1 (tsupport φ)` and `0` outside, so
  `∫⁻ ≤ δ(t)^2 * volume K' → 0`. Assemble with the `eLpNorm` triangle inequality
  (`eLpNorm_add_le`, `1 ≤ 2`) and squeeze (`tendsto_of_tendsto_of_tendsto_of_le_of_le'`,
  `Filter.Tendsto` ε-characterization `ENNReal.tendsto_nhds_zero`).

### C. `summable_nat_add_rpow_neg` + `tsum_nat_add_rpow_neg_le` (TailSumRpow.lean)
- Summability: `Real.summable_nat_rpow_inv`/`Real.summable_nat_rpow` (`↔ s < -1` form) gives
  `Summable (fun m : ℕ => (m:ℝ)^(-s))`; our sequence is a tail/comp-injection of it:
  `(Summable.comp_injective … (add_right_injective n))` or
  `((Real.summable_nat_rpow.mpr (by linarith)).subtype …)`; easiest:
  `(summable_nat_add_iff n).mpr`-style lemma (`summable_nat_add_iff : Summable (fun m => f (m+n)) ↔ Summable f`
  — exists in Mathlib; mind `n + m` vs `m + n`, `add_comm` congruence).
- Tail bound: sum-integral comparison. Route: for `m ≥ 1`,
  `((n+m : ℕ):ℝ)^(-s) ≤ ∫ x in (n+m-1 : ℝ)..(n+m), x^(-s)` (integrand antitone on `[n-1, ∞)`,
  values `≥` right endpoint value); summing,
  `∑' m, ((n+m):ℝ)^(-s) ≤ ((n:ℝ))^(-s) + ∫ x in (n:ℝ)..∞?` — cleaner Mathlib route: look for
  `sum_le_integral`-style: `AntitoneOn.sum_le_integral_Ico` (finite-range version; take limits)
  or the ready-made `Real.tsum_one_div_nat_rpow`-adjacent tail lemmas; ALSO check
  `sum_Ioc_inv_sq_le`-style patterns in `Mathlib/Analysis/PSeries.lean` — that file has
  `Real.tsum_nat_rpow`?? and `Nat.tsum...`. A fully elementary alternative avoiding
  integrals: the CONDENSATION-free bound via comparison with the telescoping integral of
  `x^{1-s}`: for `m ≥ 0`, `((n+m):ℝ)^(-s) ≤ (1/(s-1)) * ((n+m-1:ℝ)^(1-s) − ((n+m):ℝ)^(1-s))`
  — prove by MVT or convexity? (this is `∫_{n+m-1}^{n+m} x^{-s} dx` computed in closed form:
  `intervalIntegral.integral_rpow` (exists for `r ≠ -1` on positive intervals) — USE IT:
  per-term `((n+m):ℝ)^(-s) ≤ ∫ x in ((n+m-1:ℕ):ℝ)..((n+m:ℕ):ℝ), x^(-s) ∂volume`
  by `intervalIntegral.integral_mono`-free reasoning: the integrand is `≥` the constant
  right-endpoint value on the interval (`Real.rpow_le_rpow_left_iff_of_base_lt_one`? no —
  antitone in the BASE for negative exponent: `Real.rpow_le_rpow_of_exponent…` wrong one;
  use `Real.rpow_natCast`-free `Real.rpow_le_rpow_left`… the right lemma:
  `Real.rpow_le_rpow_iff_left`? For fixed negative exponent, `x ≤ y → y^(-s) ≤ x^(-s)`:
  `Real.rpow_le_rpow_of_base_le`?? — search: `Real.rpow_le_rpow_left_of_le_one`… simplest is
  `Real.rpow_natCast`-free: `Real.rpow_le_rpow_of_exponent_le` is exponent-side; base-side
  antitonicity for negative exponents: `Real.rpow_le_rpow_of_nonpos` (check) — find with
  loogle type-shape `0 < ?x → ?x ≤ ?y → ?y ^ ?z ≤ ?x ^ ?z`). Then telescope with
  `intervalIntegral.integral_rpow` closed form and sum: partial sums
  `∑_{m<M} ≤ (1/(s-1))((n-1:ℝ)^(1-s) − (n+M-1)^(1-s)) ≤ (1/(s-1))(n-1)^(1-s)`;
  conclude for the tsum by `tsum_le_of_sum_range_le` (summability from part 1; note
  `1/(s-1) ≤ s/(s-1)` gives the generous stated constant).
  Watch ℕ-cast arithmetic (`n + m - 1` as a REAL expression: write `((n:ℝ) + m - 1)`;
  `n ≥ 2` keeps everything `≥ 1 > 0`).

Report final `lake build` status for all three modules + `#print axioms` for the three named
theorems (note any lifted `private` sorry).
