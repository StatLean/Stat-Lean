# CONTINUATION: close the 2 remaining sorries in KernelDensity/MISEBias.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain
`lake build StatLean.NonparametricStatistics.KernelDensity.MISEBias` (no `srun`).

A PREVIOUS session closed `MISEVariance.lean` and `ExactMISE.lean` (0 sorries) and reduced
`MISEBias.lean` to exactly TWO `private` sorries. READ THE FILE FIRST — the whole scaffold is
there: `kmBias`/`kmSurr` definitions, `second_order_remainder`, `triangle_double_integral`,
`kmBias_eq` (bias identity), `lintegral_ofReal_sq_eq_eLpNorm_sq`, and the assembled
`kmBias_asymptotic` + main theorem, all proved modulo:

1. `eLpNorm_kmSurr` (line ~323) — EASY, do it first, commit:
   `eLpNorm (fun x => kmSurr w K h x) 2 volume = ofReal (h²·(|∫u²K|/2)·(∫w²).sqrt)`.
   `kmSurr w K h x = h^2 * (∫ u, u^2 * K u) / 2 * w x`-shaped (check its exact definition in
   the file): a CONSTANT times `w`. Route: `eLpNorm_const_smul`/`eLpNorm_const_mul` (find the
   pin name; possibly via `(c • w)` massage and `eLpNorm_const_smul` with `Real.enorm`/
   `‖c‖ₑ = ofReal |c|`), then `eLpNorm w 2 volume = ofReal ((∫ x, (w x)^2).sqrt)`:
   from `lintegral_ofReal_sq_eq_eLpNorm_sq` (already in the file!) applied to `w`, plus the
   bridge `∫⁻ ofReal (w²) = ofReal (∫ w²)` (`ofReal_integral_eq_lintegral_ofReal`,
   `hw2.integrable_sq`), so `(eLpNorm w 2)² = ofReal (∫w²)` ⇒ `eLpNorm w 2 = (ofReal (∫w²))^(1/2)
   = ofReal ((∫w²).sqrt)` (`ENNReal.rpow` juggling + `ENNReal.ofReal_rpow_of_nonneg` +
   `Real.sqrt_eq_rpow`; both sides finite). Mind `|c| = h²·|S_K|/2` for `h > 0`… the statement
   has NO `0 < h` hypothesis — `h²  ≥ 0` always, `|h²| = h²` ✓ fine.
2. `stepC_bound` (line ~310) — THE analytic core; budget most of the session here; commit as
   soon as it compiles. Statement: ∃ κ ≥ 0 tending to 0 at 0 with
   `eLpNorm (kmBias p K h · − kmSurr w K h ·) 2 ≤ ofReal (h²·κ h)` for all `h > 0`.
   Ingredients already available:
   * `kmBias_eq` (in file): `kmBias p K h x = h² ∫ u, K u·u²·(∫₀¹ (1−τ)·w (x+τuh) dτ) du`-shaped
     (read its exact form) — and `kmSurr` is the same with `w(x)` in place of `w(x+τuh)`
     (since `∫ u²K·∫₀¹(1−τ)dτ = S_K/2`). So the difference is
     `h² ∫ u, K u·u²·(∫₀¹ (1−τ)·(w (x+τuh) − w x) dτ) du`.
   * `tendsto_lintegral_sq_sub_translate` (ForMathlib/TranslationL2, CLOSED):
     `∫⁻ x ofReal((w(x+t) − w x)²) → 0` as `t → 0`. Define the modulus
     `ω t := ((∫⁻ x, ofReal ((w (x+t) − w x)^2)).toReal).sqrt` — measurable/nonneg, `ω → 0`
     at `0` (via `ENNReal.toReal`-continuity at finite limits: the lintegral is eventually
     finite — in fact ALWAYS ≤ 4∫w² by translation invariance + (a−b)² ≤ 2a²+2b²; prove
     `hωbdd : ∀ t, ω t ≤ 2·(∫w²).sqrt`-ish and `Tendsto ω (𝓝 0) (𝓝 0)` from the ForMathlib
     lemma + `ENNReal.tendsto_toReal` + `Real.sqrt`-continuity).
   * Minkowski (ForMathlib `lintegral_lintegral_sq_rpow_le`, CLOSED) twice: L²(dx)-norm of the
     double integral over (u, τ) bounded by
     `h² ∫ u |K u| u² (∫₀¹ (1−τ)·ω(τuh) dτ) du` — as in the D1/B2 files (mimic
     `IntegratedBias.lean`'s Minkowski usage, and `NikolskiTaylor.lean`'s two-variable
     handling; you may flatten (u,τ) into one product measure or nest two applications).
   * Define `κ h := sup`-free explicit: `κ h := ∫ u-integral above / (normalizer)`… simplest
     CHOICE (the ∃ gives freedom): κ h := the exact value
     `κ h := (∫ u, |K u| * u ^ 2 * (∫ τ in (0:ℝ)..1, (1 - τ) * ω (τ * u * h)) du)`-shaped
     REAL function (nonneg ✓). Then the required `Tendsto κ (𝓝 0) (𝓝 0)`: dominated
     convergence along `h → 0` (`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
     with dominating `|K u|·u²·(sup-bound of ω)` — integrable by `hKu2`; a.e.-pointwise:
     for fixed (u, τ ∈ (0,1)), `ω(τuh) → 0` as `h → 0` by composition with the continuous-at-0
     `ω` — `Tendsto.comp` with `tendsto_const_nhds.mul`-shaped `τuh → 0`; push the τ-integral
     through with ANOTHER dominated convergence or monotonicity + interval integral bounds —
     if the nested DCT gets heavy, bound `∫₀¹(1−τ)ω(τuh)dτ ≤ sup_{|s|≤|u|h} ω s`?? — sup is
     messier; prefer nested DCT: inner `intervalIntegral.tendsto_integral_of_dominated_convergence`).
   Escape hatch: if the full ε-machinery resists, you may leave ONE final lifted private sorry
   with `-- TODO(np):` and a precise statement of what remains — but try hard; everything is
   staged.

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/KernelDensity/MISEBias.lean`. Signatures/
  tags/docstrings of the PUBLIC theorem frozen; private helpers are yours (you may restate the
  two sorried privates if an equivalent-but-easier form still lets the downstream proofs in
  the file compile unchanged — check consumers `kmBias_asymptotic` before changing shapes).
- Foreground `lake build` only; never background/poll. Commit after EACH sorry closes.
- After green: `#print axioms StatLean.NonparametricStatistics.kde_integrated_sq_bias_asymptotic`
  and `...kde_exact_mise` (in ExactMISE) → only `propext, Classical.choice, Quot.sound`.

Report final `lake build` status + `#print axioms` for the two public theorems.
