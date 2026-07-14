# Close the 4 sorries in NonparametricStatistics/KernelDensity/{MISEVariance,MISEBias,ExactMISE}.lean

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. You are ON
the cluster — iterate with plain
`lake build StatLean.NonparametricStatistics.KernelDensity.MISEVariance` (then `.MISEBias`,
`.ExactMISE`; no `srun`). THIS IS THE HARDEST ITEM OF THE BATCH — budget your effort: close
MISEVariance first, then the ExactMISE decomposition, then MISEBias (the analytic core), then
the assembly. Commit after EACH file compiles 0-sorry (git add <file>; git commit) so work is
banked.

## Hard constraints
- **Only edit** `StatLean/NonparametricStatistics/KernelDensity/MISEVariance.lean`,
  `.../MISEBias.lean`, `.../ExactMISE.lean`. Touch nothing else.
- Goal **0 sorries**, 0 errors. Signatures/tags/docstrings frozen. You MAY add `import
  Mathlib.*` and `private` helpers. Lines ≤ 100. Escape hatch: lifted `private` sorries +
  TODO + report (acceptable here given difficulty — but each must be a NAMED, well-scoped
  sub-lemma). Foreground `lake build` only; never background/poll.
- After green: `#print axioms` on `kde_integrated_variance_ge`,
  `kde_integrated_sq_bias_asymptotic`, `kdeMise_eq_integrated`, `kde_exact_mise` → only
  `propext, Classical.choice, Quot.sound`.
- Do not weaken statements. If one is genuinely false as stated, STOP and report why
  (renegotiation is the laptop's call).

## Available API (proved, black boxes)
- LawTransfer: `lintegral_comp_law_densityMeasure`, `integral_comp_law_densityMeasure`,
  `kdeMeanAt_eq_integral_kernel`, `isProbabilityMeasure_densityMeasure`.
- Variance.lean: `kde_memLp_two`, `kdeVarianceAt_eq_ofReal_variance`,
  `kdeMseAt_eq_bias_sq_add_variance`, `kde_variance_le` + its private-lemma patterns
  (`integral_scale_shift'`, `integrable_affine`, `integrable_comp_law'`,
  `kernel_summand_memLp`, `kernel_summand_sq_le`) — REPLICATE privates as needed.
- IntegratedVariance: `kde_integrated_variance_le` (D1 item; may still be sorried when you
  start — transitive `sorryAx` is then expected and clears when D1 lands; report).
- ForMathlib (all closed): `lintegral_lintegral_sq_rpow_le` (Minkowski L²),
  `tendsto_lintegral_sq_sub_translate` (L²-translation continuity),
  `taylor_integral_remainder`, and in SmoothnessClasses: `taylor_integral_remainder_sub`
  (centered form: `f (x+t) − ∑_{j≤ℓ} f⁽ʲ⁾(x)tʲ/j! = t^ℓ/(ℓ−1)!·∫₀¹(1−τ)^{ℓ−1}(f⁽ℓ⁾(x+τt) −
  f⁽ℓ⁾(x))dτ` for `ContDiff ℝ ℓ f`, `1 ≤ ℓ`).
- Bias.lean (closed): `integrable_kernel_mul_holder`, `abs_integral_kernel_taylor_le`,
  `kde_bias_abs_le`.

## Mathematical setup for MISEBias (the hard file)
Hypotheses give: `p` a density, differentiable, `hpw : ∀ a b, deriv p b − deriv p a =
∫ s in a..b, w s` (a.e. second derivative `w`, measurable, `MemLp w 2`), kernel `K` of
order 1 with `∫ u²|K| < ∞`. Note: `p` is NOT `C²` — only `deriv p` is an integral of `w`.
So the polished `taylor_integral_remainder_sub` (which wants `ContDiff ℝ 2`) does NOT apply
directly. Derive instead the FTC-based second-order identity (private):
`p (x+t) − p x − t·deriv p x = t²·∫ τ in (0:ℝ)..1, (1−τ)·w (x + τ*t) dτ` — proof: for fixed
`x t`, `deriv p (x+s) = deriv p x + ∫ y in x..(x+s), w y` (`hpw`), and
`p (x+t) − p x = ∫ s in (0:ℝ)..t, deriv p (x+s) ds` (FTC-2:
`intervalIntegral.integral_deriv_eq_sub`-style — `p` differentiable everywhere and `deriv p`
is CONTINUOUS? NO — `deriv p` is an antiderivative of a locally-integrable `w` hence
continuous ✓ (`intervalIntegral.continuous_primitive`-family + `hpw` rewriting: from `hpw`,
`deriv p b = deriv p a + ∫ a..b w` and `w` is locally integrable — `MemLp w 2 volume` on
finite intervals ⇒ `IntervalIntegrable` (`MemLp.integrableOn_of_measure_finite`?? — route:
`(hw2.restrict _).integrable`? use `MemLp.integrable_on` forms / `Integrable.intervalIntegrable`
— w ∈ L² ⇒ w ∈ L¹loc: `hw2.locallyIntegrable`?? hmm — `MemLp.locallyIntegrable` might not
exist; go through Cauchy–Schwarz on the finite interval: `MemLp.mono_exponent`-on-restrict?
The standard name: `MeasureTheory.MemLp.integrableOn_of_measure_lt_top`?? — search; fallback
`Integrable.mono'` with `|w| ≤ (w² + 1)/2` on the interval: `w²` integrable globally
(`MemLp.integrable_sq`) + const on finite interval ✓ ROBUST — use this trick for ALL
local-integrability needs of `w`). Then `deriv p` continuous ⇒ FTC applies ⇒ Fubini on the
triangle (`intervalIntegral.integral_integral_swap`?? or direct: substitute the `hpw` display
and swap the double interval integral — `∫₀ᵗ ∫ₓ^{x+s} w = ∫₀ᵗ (t−…)`… cleanest: prove for
`t ≠ 0` via the change of variables `y = x + τ t`, reducing the double integral to
`t² ∫₀¹ (1−τ) w(x+τt) dτ` — spell the Fubini carefully; alternatively verify the identity by
differentiating both sides in `t` (both vanish at `t = 0`; derivatives agree by FTC +
Leibniz — `intervalIntegral.deriv_integral…`; the `∫₀¹(1−τ)w(x+τt)dτ`-side needs
parameter-differentiation — heavier; prefer the Fubini route).

## Proofs

### 1. MISEVariance — `kde_integrated_variance_ge`:
`ofReal ((nh)⁻¹·∫K² − n⁻¹·(∫|K|)²·∫p²) ≤ ∫⁻ x, kdeVarianceAt P X K h x`.
- If the `ofReal` argument is `≤ 0`, LHS is `0` ✓ trivial (`ENNReal.ofReal_of_nonpos`… note
  `ofReal_le` split: `rcases le_or_lt (arg) 0`). Main case `arg > 0`.
- Per `x`, from iid + `kernel_summand_memLp`-replica (needs `p ≤ pmax`?? NOT available here —
  `hp2 : MemLp p 2` instead! Second moment `E K₁² = ∫ K²((z−x)/h)·p z dz` may be ∞ for bad x;
  as in the D1-style route restrict to a.e.-good x via Tonelli (the double lintegral is
  `h·∫K²·1 < ∞`); on good x, variance is exact:
  `kdeVarianceAt = ofReal ((nh²)⁻¹·(E K₁²(x) − (E K₁(x))²))` — hmm mind `n` scaling:
  `Var(kde(x)) = (nh)⁻²·n·(E K₁² − (E K₁)²) = (n h²)⁻¹·(E K₁² − (E K₁)²)`.
- Integrate: `∫⁻ (good x), … = (n h²)⁻¹·(∫⁻ E K₁²(x) dx − ∫⁻ (E K₁(x))² dx)`-shape — work
  with the REAL identity and `ofReal` bridges (both x-integrals finite: first `= h∫K²` by
  Tonelli; second `≤ (∫|K|)²·h²·∫p²`?? CHECK the exact scaling: `E K₁(x) = ∫ K((z−x)/h) p z dz`;
  `∫ (E K₁(x))² dx = ∫ (K_h ⋆̃ p)²` where the convolution-type integral carries NO `1/h`; by
  Minkowski (`lintegral_lintegral_sq_rpow_le` with `g z x := ofReal (|K ((z−x)/h)| * p z)`,
  μ = ν = volume): `(∫ (∫ |K((z−x)/h)| p z dz)² dx)^(1/2) ≤ ∫ (∫ K((z−x)/h)² … wait the roles:
  bound `‖∫ dz‖_{L²(dx)} ≤ ∫ dz ‖·‖_{L²(dx)}`: inner `L²(dx)`-norm of `x ↦ |K((z−x)/h)| p z`
  = `p z · (∫ K((z−x)/h)² dx)^(1/2) = p z ·√h·(∫K²)^{1/2}`?? — that yields
  `√h‖K‖₂·∫p = √h‖K‖₂` — SQUARED: `h·∫K²` — that's the same size as the main term — WRONG
  DIRECTION (this is the crude bound). Use the OTHER factorization (as the stub docstring
  says): `g z x := ofReal (|K((z−x)/h)|·p x)`?? no… The correct Young-type split for
  `‖K_h ⋆ p‖₂ ≤ ‖K_h‖₁·‖p‖₂`: Minkowski with the substitution `u = (z−x)/h` FIRST:
  `E K₁(x) = h·∫ K(u)·p(x+u h) du` — NO wait: `∫ K((z−x)/h) p z dz = h ∫ K(u) p (x+uh) du` ✓
  (scale-shift). Then `‖x ↦ h∫K(u)p(x+uh)du‖_{L²(dx)} ≤ h·∫ |K u|·‖p(·+uh)‖₂ du
  = h·∫|K|·‖p‖₂` (translation invariance!) — Minkowski lemma with `g u x :=
  ofReal (|K u| · p (x + u*h))`; inner norm: `∫⁻ x ofReal((|K u| p (x+uh))²) =
  ofReal(K u²)·∫⁻ ofReal(p²)` (translation invariance of the x-lintegral:
  `lintegral_add_right_eq_self`-com composed with scaling-free shift `x ↦ x + uh` — pure
  translation ✓ no h-Jacobian) `= ofReal (K u² · ∫ p²)` (`hp2` bridges). So
  `∫ (E K₁)² dx ≤ h²·(∫|K|)²·∫p²` ✓ and the correction `(n h²)⁻¹·h²·(∫|K|)²∫p²
  = n⁻¹(∫|K|)²∫p²` ✓ matches the statement.
- Careful with `Integrable K`?? `∫|K|` appears in the STATEMENT via `∫ u, |K u|` — hypothesis
  `hK1 : Integrable K` ✓ is in the signature. Assemble the two-sided real algebra with
  `ofReal` monotonicity; the exact identity `E K₁² − (E K₁)²` needs per-good-x
  `variance_def'`-style rewriting (as in Variance.lean).

### 2. ExactMISE — `kdeMise_eq_integrated`:
`kdeMise = ∫⁻ ofReal(bias²) + ∫⁻ kdeVarianceAt` — Tonelli-free per-x decomposition:
`kdeMise = ∫⁻ ω ∫⁻ x … ∂P`; SWAP to x-outer (`lintegral_lintegral_swap` — joint measurability:
kde is a finite sum of `K`-compositions, `hK : Measurable K`, `hX i` ✓, `p` measurable ✓) then
per-x `∫⁻ ω ofReal((kde−p x)²) = ofReal(bias²) + variance(x)` — that is EXACTLY
`kdeMseAt_eq_bias_sq_add_variance` (needs `MemLp 2` at x — a.e.-good x as usual; on the null
bad set both sides… the identity might fail on a null set — use `lintegral_congr_ae`).
Then `lintegral_add_left/right` (measurability of `x ↦ kdeVarianceAt` — lintegral of a
jointly measurable kernel: `Measurable.lintegral_prod_right'` after expressing
`kdeVarianceAt` as `∫⁻ ω F (ω,x)`; `kdeMeanAt` measurable in x by
`StronglyMeasurable.integral_prod_right'`/`measurable_integral_prod_right`?? — if the
measurability of the Bochner `kdeMeanAt` in `x` fights, use
`MeasureTheory.stronglyMeasurable_integral_prod_right`-family; it's standard).

### 3. MISEBias — `kde_integrated_sq_bias_asymptotic` (∀ ε > 0, ∃ h₀ > 0, two-sided
`ofReal (M(h) − ε h⁴) ≤ ∫⁻ x ofReal(bias²) ≤ ofReal (M(h) + ε h⁴)` with
`M h := h⁴/4·S_K²·∫w²`, uniformly over samples with density `p`):
- a.e.-x bias identity (`kdeMeanAt_eq_integral_kernel` + a.e. integrability as usual):
  `bias x = ∫ K u · (p (x+uh) − p x) du` (`∫K = 1`; order-1: `∫ uK = 0` kills the
  `t·deriv p x` term) `= ∫ K u · (u h)²·∫₀¹ (1−τ) w (x + τ u h) dτ du` (the private
  second-order identity above) `= h²·∫ K u · u²·(∫₀¹ (1−τ) w (x+τuh) dτ) du`.
- Target `b* x := h²·(S_K/2)·w x` — indeed `∫ K u u² (∫₀¹(1−τ)dτ) w x du = S_K·w x/2` ✓.
- `‖bias − b*‖_{L²(dx)} ≤ h²·∫ |K u| u² (∫₀¹ (1−τ)·‖w(·+τuh) − w‖₂ dτ) du` — TWO nested
  Minkowski applications (the closed ForMathlib lemma, με τ-restrict and u-volume) with the
  translation modulus `ω(s) := (∫⁻ x ofReal((w(x+s) − w x)²))^(1/2)`.
- `tendsto_lintegral_sq_sub_translate hw_meas hw2` gives `ω(s) → 0` as `s → 0`; extract
  `δ` for the ε-target; split the u-integral at `|u| ≤ δ/h₀`… the classical bookkeeping:
  choose `h₀` s.t. for `h < h₀`: near-range `|τuh| ≤ δ` contributes `≤ small·∫u²|K|`;
  far range `|u| > δ/h`: bound `ω ≤ 2‖w‖₂` (triangle + translation invariance) and
  `∫_{|u|>δ/h} u²|K| → 0` as `h → 0` (dominated convergence on the tail of the FIXED
  integrable `u²|K|`: `tendsto_setIntegral_of_monotone`?-free — use
  `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` along `h → 0` or a direct
  ε-argument: `Integrable (u²|K|)` ⇒ tails vanish (`Integrable.tendsto_setIntegral_nhds_zero`??
  — the standard: for integrable F, `∀ε ∃R, ∫_{|u|>R} F < ε` — derive via
  `MeasureTheory.exists_… `/monotone convergence on `⋃ R, {|u| ≤ R}`)).
- From the L²-DISTANCE bound conclude the two-sided bound on `∫⁻ (bias)²` vs
  `∫⁻ (b*)² = M h` (`‖b*‖₂² = h⁴/4 S_K² ∫w²` ✓ exact): reverse-triangle in L²:
  `|‖bias‖₂ − ‖b*‖₂| ≤ ‖bias − b*‖₂ ≤ κ(h)·h²` with `κ(h) → 0`; choose `h₀` so
  `κ² + 2κ·(√(S_K²∫w²)/2) ≤ ε` — do all of this at the `ℝ≥0∞`-rpow level or bridge to real
  `eLpNorm`s (everything finite for `h < h₀` ✓); square out. (If the two-sided ε-algebra in
  ℝ≥0∞ gets heavy, bridge to real numbers early: all three L²-norms are finite reals.)
- The `∀ n` uniformity is FREE: nothing in the bias depends on `n` (bias is deterministic —
  `kdeMeanAt` integrates out ω; make sure your a.e.-identity lemma states this).

### 4. ExactMISE — `kde_exact_mise`: assembly.
Given ε: obtain `h₀` from (3) at `ε' := ε/2` (bias part in `h⁴`), and for the variance part:
upper `∫⁻ var ≤ ofReal((nh)⁻¹∫K²)` (D1's `kde_integrated_variance_le` — usable even while
sorried, with the taint caveat), lower `≥ ofReal((nh)⁻¹∫K² − n⁻¹(∫|K|)²∫p²)` (1). The
correction `n⁻¹(∫|K|)²∫p² ≤ (ε/2)·(nh)⁻¹` ⟺ `h·(∫|K|)²∫p² ≤ ε/2` — ANOTHER smallness in
`h`: shrink `h₀` further (`min`), i.e. `h₀' := min h₀ (ε/(2·((∫|K|)²∫p²+1)))`. Then combine:
`|MISE − A| ≤ ε/2·h⁴ + ε/2·(nh)⁻¹ ≤ ε((nh)⁻¹ + h⁴)` ✓ via `kdeMise_eq_integrated` (2) and
`ENNReal` addition monotonicity (`add_le_add`, `ofReal_add` on nonnegs — keep all six
quantities as reals with finiteness from the bounds; assemble two-sided).

Report final `lake build` status for all three modules + `#print axioms` for the four named
theorems (note any lifted `private` sorry and any D1 transitive taint).
