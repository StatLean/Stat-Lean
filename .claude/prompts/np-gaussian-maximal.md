# Close the 4 sorries in NonparametricStatistics/ForMathlib/{GaussianExpSq,MaxExpSquare}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain
`lake build StatLean.NonparametricStatistics.ForMathlib.GaussianExpSq` (then
`.ForMathlib.MaxExpSquare`; no `srun`).

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/ForMathlib/GaussianExpSq.lean` and
  `.../ForMathlib/MaxExpSquare.lean`. Touch nothing else.
- Goal **0 sorries**, 0 errors. Signatures/tags/docstrings frozen. You MAY add `import
  Mathlib.*` and `private` helpers. Lines ≤ 100. Escape hatch: one lifted `private` sorry +
  TODO + report. Foreground `lake build` only; never background/poll.
- After green: `#print axioms` on all four theorems → only
  `propext, Classical.choice, Quot.sound`.
- Do not weaken statements; if false as stated, STOP and report.

## Proofs

### GaussianExpSq.lean
1. `lintegral_exp_mul_sq_gaussianReal_le (v : ℝ≥0) {a : ℝ} (ha : a * (4 * v) ≤ 1) :
    ∫⁻ x, ofReal (exp (a * x²)) ∂(gaussianReal 0 v) ≤ ofReal (√2)`.
   Case `v = 0`: `gaussianReal 0 0 = Measure.dirac 0` (`gaussianReal_zero_var` — check exact
   name in `Mathlib/Probability/Distributions/Gaussian/Real.lean` via
   `./tools/api.sh .lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Real.lean`);
   `lintegral_dirac` gives `ofReal (exp 0) = 1 ≤ ofReal √2` (`Real.one_le_sqrt`… or
   `Real.le_sqrt` with `1 ≤ 2`; `ENNReal.ofReal_le_ofReal`).
   Case `v ≠ 0`, `a ≤ 0`: integrand `exp(a x²) ≤ 1` pointwise (`Real.exp_le_one_iff`,
   `mul_nonpos`), so `∫⁻ ≤ ∫⁻ 1 = 1 ≤ ofReal √2` (`lintegral_mono`, `lintegral_one`,
   probability measure).
   Case `v ≠ 0`, `0 < a` (then from `ha`: `a ≤ 1/(4v)`, and `1 − 2*a*v ≥ 1/2 > 0`):
   `gaussianReal 0 v = volume.withDensity (gaussianPDF 0 v)` (`gaussianReal_of_var_ne_zero`
   or the `.rnDeriv`/`withDensity` characterization — find it), so
   `∫⁻ x, ofReal (exp (a x²)) * gaussianPDF 0 v x` (`lintegral_withDensity_eq_lintegral_mul`;
   `gaussianPDF μ v x = ofReal (gaussianPDFReal μ v x)`,
   `gaussianPDFReal 0 v x = (√(2πv))⁻¹ * exp (−x²/(2v))`).
   Merge: `exp(a x²) * (√(2πv))⁻¹ exp(−x²/(2v)) = (√(2πv))⁻¹ * exp(−(1/(2v) − a) x²)`
   (`← Real.exp_add`, `ring_nf` in the exponent; positivity of the coefficient
   `c := 1/(2v) − a ≥ 1/(4v) > 0`).
   `ENNReal.ofReal_mul` (nonnegs) to split; convert to Bochner:
   `∫⁻ ofReal (…) = ofReal (∫ …)` via `ofReal_integral_eq_lintegral_ofReal` (backwards) with
   `Integrable (fun x => exp (−c * x²))` = `integrable_exp_neg_mul_sq hc`;
   `∫ x, exp (−c x²) = √(π/c)` = `integral_gaussian c` (check exact form:
   `integral_gaussian : ∫ x, exp (−b * x²) = √(π / b)`).
   Final real inequality: `(√(2πv))⁻¹ * √(π/c) ≤ √2` ⟸ square both sides
   (`Real.sq_sqrt`, `Real.sqrt_mul_self`, `Real.sqrt_inv`, `Real.sqrt_div`?):
   `(π/c)/(2πv) = 1/(2vc) ≤ 2` ⟸ `2*v*c = 1 − 2*a*v ≥ 1/2` ✓ (`nlinarith` from `ha`,
   `v > 0`). Assemble with `Real.sqrt_le_sqrt` on `1/(2vc) ≤ 2` and
   `√((2πv))⁻¹·√(π/c) = √(π/(c·2πv))` (`Real.sqrt_mul'`/`sqrt_inv` algebra; keep all factors
   nonneg, `Real.pi_pos`).
2. `hasLaw_sum_mul_gaussianReal (c : Fin n → ℝ) (hmeas) (hindep : iIndepFun ξ P)
    (hlaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 v) P) :
    HasLaw (fun ω => ∑ i, c i * ξ i ω) (gaussianReal 0 ((∑ i, (c i)^2).toNNReal * v)) P`.
   FIRST search for ready-made helpers ON THE PIN:
   `loogle '"gaussianReal_map_const_mul"'`, `'"gaussianReal_conv"'`,
   `'"HasGaussianLaw"'`, `'"iIndepFun"' '"gaussianReal"'` and grep this repo:
   `MultipleTesting/ForMathlib/GaussianMoments.lean`, `AsymptoticStatistics/ForMathlib/
   MultivariateGaussianConv.lean` — earlier areas may already have "sum of independent
   gaussians" bricks you can import (importing OTHER AREAS' ForMathlib is allowed).
   Route (induction on `n`):
   * `n = 0`: sum is `0`; `HasLaw (fun _ => 0) (gaussianReal 0 0)`: `Measure.map_const`,
     `gaussianReal 0 0 = dirac 0`; `(∑ over Fin 0 …).toNNReal = 0` (`Finset.sum_empty`,
     `Real.toNNReal_zero`, `zero_mul`).
   * `n+1`: `∑_{Fin (n+1)} c i ξ i = c 0 * ξ 0 + ∑_{i : Fin n} c i.succ * ξ i.succ`
     (`Fin.sum_univ_succ`). Tail: apply IH to `ξ ∘ Fin.succ`, `c ∘ Fin.succ` — restrict
     `iIndepFun` along the injective `Fin.succ` (search `iIndepFun.comp_right`,
     `iIndepFun.precomp`, or `iIndepFun.reindex`-style; if missing, derive from the
     definitional `iIndepFun` via `Kernel.iIndepFun`-composition or use
     `hindep.iIndepFun_of_injective`?? — one of these exists; worst case use
     `iIndepFun.indepFun_finset_sum_of_notMem` directly on `Fin (n+1)` and skip the
     reindexing: independence of `ξ 0` from `∑_{i ∈ univ.erase 0} c i ξ i`).
   * Scalar: `HasLaw (fun ω => c₀ * ξ 0 ω) (gaussianReal 0 ((c₀^2).toNNReal * v))`:
     `hlaw 0 |>.map_eq` + `Measure.map_map` with `(c₀ * ·)`;
     `gaussianReal_map_const_mul` (`(gaussianReal μ v).map (c * ·) = gaussianReal (c*μ) (…)`
     — verify the variance parameter form: likely `⟨c^2, _⟩ * v` or `(c^2).toNNReal * v`;
     `c₀ * 0 = 0` ✓). Case `c₀ = 0` may need care if the map lemma requires `c ≠ 0`
     (then `map (0 * ·) = dirac 0 = gaussianReal 0 0` ✓ handle separately).
   * Sum of independents: need `map (X + Y) P = map X P ∗ map Y P` for `IndepFun X Y`:
     search `IndepFun.map_add_eq_conv`? / `ProbabilityTheory.IndepFun` + `Measure.conv`
     (`loogle 'Measure.conv'` and `'"conv"' '"IndepFun"'`); then
     `gaussianReal_conv_gaussianReal : gaussianReal m₁ v₁ ∗ gaussianReal m₂ v₂ =
     gaussianReal (m₁+m₂) (v₁+v₂)` (pin-verified name). NNReal bookkeeping:
     `(∑_{n+1} c²).toNNReal * v = (c₀²).toNNReal * v + (∑_tail c²).toNNReal * v`
     (`Real.toNNReal_add` on nonnegs `sq_nonneg`, sum nonneg; `add_mul`).
     Measurability side goals from `hmeas`.

### MaxExpSquare.lean
3. `lintegral_iSup_sq_le_log` (`hM : 1 ≤ M`, `hα : 0 < α₀`, `hexp j : ∫⁻ ofReal (exp (α₀ ηⱼ²)) ≤ ofReal C₀`):
   `∫⁻ ω, ofReal (⨆ j, (η j ω)^2) ∂P ≤ ofReal (log (C₀ * M) / α₀)`.
   Groundwork: `haveI : Nonempty (Fin M) := Fin.pos_iff_nonempty.mp hM`.
   `hC₀ : 1 ≤ C₀` DERIVED: from `hexp ⟨0, hM⟩`… precisely: `∫⁻ ofReal (exp (α₀ η²)) ≥
   ∫⁻ ofReal (exp 0) = 1` FAILS pointwise (η² ≥ 0 ⇒ exp(α₀η²) ≥ 1 ✓ pointwise!) —
   `lintegral_mono` + probability measure ⇒ `1 ≤ ofReal C₀` ⇒ `1 ≤ C₀`
   (`ENNReal.one_le_ofReal`).
   Define `Z ω := ∑ j, exp (α₀ * (η j ω)^2)` (real). Pointwise:
   `⨆ j, (η j ω)^2 = (1/α₀) * log (exp (α₀ * ⨆ j, (η j ω)^2))` (`Real.log_exp`) and
   `exp (α₀ * ⨆ j (η j ω)^2) = ⨆ j, exp (α₀ (η j ω)^2)` (monotone exp comm with finite sup —
   over `Fin M` nonempty finite: `Real.iSup`… use `Finset`-sup instead of `⨆` internally:
   `⨆ j, f j = Finset.univ.sup' (Finset.univ_nonempty) f` for finite nonempty
   (`Finset.sup'_eq_ciSup`?? direction — find `Finset.sup'_eq_csSup`/`ciSup_eq_finsetSup'`…;
   or `Finset.Nonempty.ciSup_eq_max'`?) then `Finset.sup' ≤ Finset.sum` for nonneg terms
   (`Finset.sup'_le` with each term `≤ Z ω` since all summands positive:
   `Finset.single_le_sum (fun j _ => (Real.exp_pos _).le)`) ⇒
   pointwise `⨆ j (η j ω)^2 ≤ (1/α₀) * log (Z ω)` (log monotone `Real.log_le_log`).
   Tangent-line trick for `E log Z ≤ log (E Z)` WITHOUT Jensen machinery — actually avoid
   even that: we only need the ∫⁻ bound. Pointwise for any `c > 0`:
   `log (Z ω) ≤ log c + Z ω / c − 1` (`Real.log_le_sub_one_of_pos` applied to `Z ω / c`:
   `log (Z/c) ≤ Z/c − 1`, `Real.log_div` with `Z ω > 0` (sum of exps, `Finset.sum_pos`,
   nonempty) and `c ≠ 0`). Take `c := C₀ * M` (`> 0` from `hC₀`, `hM`). Then
   `∫⁻ ofReal (⨆ …) ≤ ∫⁻ ofReal ((1/α₀) * (log c + Z ω / c − 1))` (`lintegral_mono`,
   `ENNReal.ofReal_le_ofReal`, nonneg factors `hα`).
   Now bound `∫⁻ ofReal (Z ω)`: `ofReal (Z ω) = ∑ j, ofReal (exp (α₀ (η j ω)^2))`
   (`ENNReal.ofReal_sum_of_nonneg`), `lintegral_finset_sum` (measurability from `hmeas`,
   `Measurable.ennreal_ofReal`, `Real.measurable_exp.comp`, `fun_prop`) ⇒
   `∫⁻ ofReal Z ≤ M * ofReal C₀ = ofReal (C₀ * M)` (`Finset.sum_le_card_nsmul`-style with
   `hexp j`, `Finset.card_univ`, `Fintype.card_fin`; ENNReal `nsmul`/cast juggling).
   Assemble: `∫⁻ ofReal ((1/α₀)(log c + Z/c − 1)) ≤ (1/α₀)(log c + (∫⁻-bound)/c − 1)`-shape:
   work additively in ℝ≥0∞: split `ofReal (x + y − 1) ≤ ofReal x + ofReal (y − 1) ≤ …` —
   CLEANER: bound pointwise-in-expectation the REAL function first? `Z` may not be Bochner
   integrable a priori — it IS: `0 ≤ Z`, `∫⁻ ofReal Z ≤ ofReal (C₀ M) < ⊤` + AESM ⇒
   `Integrable Z` (`integrable_of_lintegral_ofReal_lt_top`?? — the standard bridge:
   `MeasureTheory.integrable_of...`; or `MemLp`-1 route). Then everything Bochner:
   `∫ (⨆ …) ≤ (1/α₀) * (log c + (∫ Z)/c − 1) ≤ (1/α₀) * (log c + (C₀ M)/(C₀ M) − 1)
   = log (C₀ M)/α₀` (`∫ Z ≤ C₀ M` from the ∫⁻ bound via `ofReal_integral_eq_lintegral_ofReal`
   + `ENNReal.ofReal_le_ofReal_iff`; integral monotone `integral_mono` with integrable
   majorant; sup measurable: finite sup of measurables `Finset.measurable_sup'`?/
   `Measurable.iSup` fin; sup integrable: dominated by `(1/α₀) log Z + …`? — simpler majorant:
   `⨆ j ηⱼ² ≤ ∑ j ηⱼ²`?? NOT integrable-known… use the log-majorant: sup ≤ (1/α₀) log Z ≤
   (1/α₀)(log c + Z/c − 1) which IS integrable ✓, and sup ≥ 0 ⇒ integrable by squeeze
   (`Integrable.mono'`)). Finish: `∫⁻ ofReal (sup) = ofReal (∫ sup) ≤ ofReal (log (C₀ M)/α₀)`.
4. `lintegral_iSup_normSq_gaussian_le` (`hgauss j k : ∃ v ≤ vmax, HasLaw (η j · k) (gaussianReal 0 v) P`):
   Case `vmax = 0`: every coordinate has law `gaussianReal 0 0 = dirac 0` ⇒ `η j · k = 0` a.e.
   (`HasLaw.map_eq` + map to dirac ⇒ ae-equality: `Measure.map_eq_dirac_iff_ae_eq`?? — or:
   `∫⁻ ofReal ((η j ω k)^2) = ∫⁻ x², x ∂dirac 0 = 0` via `HasLaw.lintegral_comp`-style map
   rewrite ⇒ each coordinate ae-zero ⇒ sup of sums ae-0 ⇒ LHS 0; RHS `= ofReal (4·d·0·log …)
   = 0` ✓ equality; mind `log` sign — RHS is `ofReal 0 = 0` ✓).
   Case `0 < vmax`: apply (3) with the family `η' : Fin (M*d) → Ω → ℝ` reindexed via
   `finProdFinEquiv : Fin M × Fin d ≃ Fin (M*d)` (or state a private ι-indexed
   [Fintype ι] [Nonempty ι] version of (3) and instantiate at `Fin M × Fin d` — RECOMMENDED,
   avoids equiv juggling; keep the public (3) statement as the `Fin M` special case),
   `α₀ := 1/(4*vmax)` (`> 0`), `C₀ := √2`: per coordinate,
   `∫⁻ ofReal (exp ((1/(4vmax)) * η²)) = ∫⁻ ofReal (exp ((1/(4vmax)) x²)) ∂(gaussianReal 0 v)`
   (law transfer: `HasLaw.map_eq ▸ lintegral_map` with measurable integrand) `≤ ofReal √2`
   by `lintegral_exp_mul_sq_gaussianReal_le` (`ha : (1/(4vmax)) * (4v) ≤ 1` from `v ≤ vmax`).
   Pointwise `⨆ j, ∑ k, η²  ≤ d * ⨆ (jk), η²`: `∑_k ≤ d * max_k` (`Finset.sum_le_card_nsmul`)
   then sups. So LHS `≤ d * ∫⁻ ofReal (⨆ (jk) η²)`?? — mind `ofReal (d * x) = d * ofReal x`
   (`ENNReal.ofReal_mul`, `d ≥ 0`) and `lintegral_const_mul`. Apply (3)-ι at `M*d` variables:
   `≤ d * ofReal (log (√2 * (M*d)) / (1/(4vmax))) = ofReal (4*d*vmax * log (√2*M*d))`
   (real algebra `div_div_eq_mul_div`, `field_simp`; `Nat.cast_mul`,
   `Fintype.card_prod`). Watch: (3)'s `C₀*M` becomes `√2 * (M*d)` with card `M*d` ✓ matches
   the target `log (√2*M*d)` (`mul_assoc` in the log argument — `congr`/`ring_nf`).

Report final `lake build` status for both modules + `#print axioms` for all four theorems
(note any lifted `private` sorry).
