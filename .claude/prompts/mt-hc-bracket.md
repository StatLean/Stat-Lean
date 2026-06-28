# mt-hc-bracket — close HC cruxes 1+2: half-line bracketing entropy + J_pos (vdV §19.2)

You are a Lean 4 proof subagent on branch `mt/hc-bracket` (based on `mt/batch8`). Project: **StatLean**
— read `CLAUDE.md` first (§2,§6,§7,§9). In an `srun` allocation: plain `lake build`, ITERATE to a GREEN
build (exit 0, NO tactic errors — a `sorry` is acceptable on the one crux you don't close, a tactic
error is NOT). Never `lake update`.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/GoodnessOfFit/HigherCriticism.lean`

Close exactly TWO of the three `sorry`'d cruxes. **LEAVE `halfLineClass_chain_bound` UNTOUCHED** (it is
the framework's maximal inequality, being removed upstream in a separate unit). Do NOT change
`rhoStar`/`hcStat`/`halfLineClass`/`halfLineClass_measurable`/`halfLine_isPDonsker` or the module
docstring. After your work the file builds green with exactly 1 sorry (`halfLineClass_chain_bound`).

## Crux 2 — `halfLineClass_J_pos` (do FIRST; elementary)
`∀ δ' > 0, 0 < bracketingEntropyIntegral δ' halfLineClass P`. The integrand of
`bracketingEntropyIntegral` is `√(log (bracketingNumber ε halfLineClass 2 P))` (via `ENat.recTopCoe`).
Show `bracketingNumber ε halfLineClass 2 P ≥ 2` for every `ε`: the two indicators `f₋ = 𝟙_{(−∞,t]}`
with `t → −∞` (a.e. `0`) and `f₊ = 𝟙_{(−∞,s]}` with `s → +∞` (a.e. `1`) — concretely take any
`a < b` with `P(a, b] > 0` if `P` is nondegenerate, else handle the point-mass/degenerate case — cannot
both lie in one `ε`-bracket of `L²(P)`-width `< ε ≤` something, OR more robustly: `bracketingNumber ≥ 1`
always and a single bracket cannot cover a class whose `L²` diameter is positive, forcing `≥ 2`. If a
fully general `≥ 2` is fiddly, the SAFE route: `bracketingNumber ε F 2 P ≥ 1` whenever `F` is nonempty
(`halfLineClass` is nonempty), and the integrand `√log` is `≥ 0`; but `> 0` needs `≥ 2`. Use
`bracketingNumber` `≥ 2` ⟹ integrand `≥ √log 2 > 0` on `Ioc 0 δ'` ⟹ `lintegral > 0` via
`lintegral_pos_iff`/`setLIntegral_pos`. Search the project's `Bracketing.lean` for any
`bracketingNumber` lower-bound or positivity helper first (`./tools/api.sh
StatLean/AsymptoticStatistics/EmpiricalProcess/Bracketing.lean`).

## Crux 1 — `halfLineClass_bracketingEntropyIntegral_lt_top` (the substantive one)
`bracketingEntropyIntegral 1 halfLineClass P < ⊤`. Prove `bracketingNumber ε halfLineClass 2 P ≤
⌈1/ε²⌉ + 1` (a finite ε-bracketing cover), then the integrand `≤ √(log (⌈1/ε²⌉+1))` is Lebesgue-
integrable on `Ioc 0 1`.

**Construction of the cover (`HasFiniteBracketingCover`/`IsEpsBracket`, see `Bracketing.lean`):**
Let `F = MeasureTheory.cdf P` (a `StieltjesFunction`, monotone right-continuous, `F(−∞)=0`, `F(+∞)=1`).
Pick grid points `t₀ < t₁ < … < t_m` (with `t₀=−∞`, `t_m=+∞` handled as `±` large / the `Iic`/`Iio`
limits) such that `P((t_{i−1}, t_i]) ≤ ε²` and `m ≤ ⌈1/ε²⌉ + 1`: walk the quantiles `F⁻¹(jε²)`,
`j = 0,…,⌈1/ε²⌉` (an atom of mass `> ε²` becomes its own block, adding at most the `+1`). Brackets are
`l_i = 𝟙_{(−∞,t_{i−1}]}`, `u_i = 𝟙_{(−∞,t_i]}` (both in `halfLineClass`-style; as functions
`Set.indicator (Set.Iic t) 1`). For any `f = 𝟙_{(−∞,t]} ∈ halfLineClass` with `t ∈ [t_{i−1}, t_i)`:
pointwise `l_i ≤ f ≤ u_i` (monotonicity of `Iic`). The `L²(P)`-width:
`eLpNorm (u_i − l_i) 2 P = (P((t_{i−1}, t_i]))^{1/2} ≤ (ε²)^{1/2} = ε`, so `IsEpsBracket ε l_i u_i 2 P`
holds (also need `MemLp` of the bounded indicators — immediate, they're `≤ 1`).
Hence `HasFiniteBracketingCover halfLineClass ε 2 P` with `≤ ⌈1/ε²⌉+1` brackets ⇒
`bracketingNumber ε halfLineClass 2 P ≤ ⌈1/ε²⌉+1`.

**Integrability:** `√(log(⌈1/ε²⌉+1)) ≤ √(log(2/ε²)) = √(log 2 + 2 log(1/ε)) ≤ √(log 2) + √2·√(log(1/ε))`
(subadditivity of `√`), and `∫₀¹ √(log(1/ε)) dε < ∞` (e.g. bound `√(log(1/ε)) ≤ 1/√ε` for `ε ≤ 1` since
`log(1/ε) ≤ 1/ε`, and `∫₀¹ ε^{-1/2} dε = 2`). So `bracketingEntropyIntegral 1 < ⊤` by
`lintegral_mono` to the integrable envelope + `setLIntegral_lt_top`-style. Search
`Real.add_pow_le_pow_mul_pow_of_sqrt`/`Real.sqrt_le_sqrt`, `integrableOn_rpow`/`MeasureTheory` rpow
integrability, and `lintegral` finiteness lemmas.

**If the exact quantile grid is painful:** the construction only needs SOME monotone grid with `P`-mass
`≤ ε²` per block — use `StieltjesFunction.measure`/`cdf` and a finite partition of `[0,1]` (the CDF
range) into `⌈1/ε²⌉` levels, pulled back. If one measure-theoretic step (e.g. the exact atom handling)
resists, isolate it as ONE named `private` `sorry` lemma — but the target is to close crux 1 fully.

## Constraints
No `axiom`/`admit`/new hypotheses; keep `-- Candès`/`-- vdV` citation comments + docstrings. Named
`private` helpers only. **Finish on `lake build StatLean.MultipleTesting.GoodnessOfFit.HigherCriticism`
exit 0.** Commit to `mt/hc-bracket`
(`mt(hc): close half-line bracketing-entropy + J_pos cruxes (vdV §19.2)`).

## DONE
Build exits 0; sorry count = 1 (only `halfLineClass_chain_bound`). Report build status, the two cruxes'
closure status, and the bracketing-number bound + integrability lemmas used.
