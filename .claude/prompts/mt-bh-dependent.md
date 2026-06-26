# mt-bh-dependent — BH FDR under arbitrary dependence (Candès L5/L6, Thm 3)

You are a Lean 4 proof subagent on branch `mt/bh-dependent` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with
plain `lake build`, ITERATE. Never `lake update`. **Time-box** the Abel-summation core; if it
resists after real effort, lift it to ONE named `sorry`'d private lemma (see DONE) rather than
leave the file broken.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/BHDependence.lean`

`BenjaminiHochberg.lean` (which defines `bhRejects`), `FDP/Defs.lean`, `PValues/Defs.lean` are
imported but **read-only**. You MAY add `private` helper lemmas within the touch-set. Do NOT change
the public theorem signature (no added/weakened hypotheses — in particular do **not** add any
independence hypothesis; arbitrary dependence is the whole point).

## Goal
Prove `benjamini_hochberg_dependent_fdr_le` (0-sorry ideal). Verify
`lake build StatLean.MultipleTesting.BHDependence` green.

## The theorem (Candès L5 §5.5 / L6 §6.6, Thm 3 — Benjamini–Yekutieli)
Null p-values super-uniform, **no independence**. BH at level `α` (`bhRejects α p`) has
`FDR ≤ (N₀/N)·α·Hₙ`, `Hₙ = harmonic N = ∑_{k=1}^N 1/k`, `N₀ = |H₀|`.

## Proof roadmap (Benjamini–Yekutieli layer-cake + Abel summation)
Write `R(ω) = (bhRejects α p ω).card`, `ψᵢ(ω) = 𝟙(i ∈ bhRejects α p ω)`. Then
`FDP = ∑_{i∈H₀} ψᵢ/(R∨1)` and `FDR = ∑_{i∈H₀} E[ψᵢ/(R∨1)]` (`integral_finset_sum`;
each summand integrable as it is in `[0,1]`). **It suffices to show, per null `i`:
`E[ψᵢ/(R∨1)] ≤ (α/N)·Hₙ`** (then sum over `H₀`, `N₀` terms).

Per-null argument (the crux — make it a `private` lemma):
1. **Discretize `R`.** `ψᵢ/(R∨1) = ∑_{k=1}^N (1/k)·ψᵢ·𝟙(R=k)` (R∨1 ∈ {1,…,N}; the `R=0` case has
   `ψᵢ=0`). `Finset.sum_range` / partition over the value of `R`.
2. **Deterministic BH fact.** On `{R=k}`, a rejected `i` has `pᵢ ≤ kα/N` — directly from the
   definition of `bhRejects` (`i ∈ bhRejects α p ω` ⟺ `pᵢ ω ≤ k̂α/N` with `k̂ = R` there). So
   `ψᵢ·𝟙(R=k) ≤ 𝟙(pᵢ ≤ kα/N)·𝟙(R=k)`. Hence
   `E[ψᵢ/(R∨1)] ≤ ∑_{k=1}^N (1/k)·P(pᵢ ≤ kα/N, R=k)`.
3. **Bands + reorder.** Let `F(j) = P(pᵢ ≤ jα/N)`, bands `C_j = {(j−1)α/N < pᵢ ≤ jα/N}`, so
   `{pᵢ ≤ kα/N} = ⊔_{j=1}^k C_j` and `P(pᵢ ≤ kα/N, R=k) = ∑_{j=1}^k P(C_j, R=k)`. Swap the double
   sum and bound `1/k ≤ 1/j` for `k ≥ j`:
   `∑_{k}(1/k)∑_{j≤k}P(C_j,R=k) = ∑_j ∑_{k≥j}(1/k)P(C_j,R=k) ≤ ∑_j (1/j)·P(C_j, R≥j) ≤ ∑_j(1/j)P(C_j)`.
   (`P(C_j) = F(j) − F(j−1)`.)
4. **Abel summation — this is where `Hₙ` appears.** With `F(0)=0`, `F(j) ≤ jα/N` (super-uniformity),
   `∑_{j=1}^N (1/j)(F(j)−F(j−1)) = (1/N)F(N) + ∑_{j=1}^{N−1} F(j)·(1/j − 1/(j+1))`
   `= (1/N)F(N) + ∑_{j=1}^{N−1} F(j)/(j(j+1)) ≤ α/N + ∑_{j=1}^{N−1} (jα/N)/(j(j+1))`
   `= α/N + (α/N)∑_{j=1}^{N−1} 1/(j+1) = α/N + (α/N)(Hₙ − 1) = (α/N)·Hₙ.`
   Abel/summation-by-parts: `Finset.sum_range_succ`, `Finset.sum_Ioo`-style telescoping, or
   `Finset.sum_range_by_parts`. `harmonic` recurrence: `harmonic_succ`
   (`harmonic (n+1) = harmonic n + 1/(n+1)`); `harmonic` is `ℚ`-valued — cast with
   `Rat.cast_sum`/`push_cast`. Note `∑_{j=1}^{N−1} 1/(j+1) = Hₙ − 1`.

You may reshape steps 1–3 freely (e.g. prove the per-null bound in whatever exact indicator form is
cleanest) as long as the public conclusion is unchanged.

## Lean guidance
- `bhRejects`/`bhKmax` and their helper lemmas are in `BenjaminiHochberg.lean` — reuse the public
  `bhRejects`; you may re-derive any `private` fact you need *inside your file*. Search
  `./tools/where.sh 'bhRejects'`, `./tools/api.sh StatLean/MultipleTesting/BenjaminiHochberg.lean`.
- `SuperUniform p μ : ∀ t ≥ 0, μ{p ≤ t} ≤ ENNReal.ofReal t` — convert to real `P(pᵢ ≤ c) ≤ c` via
  `ENNReal.toReal`/`measure` of a measurable set; `FDP`/`FDR` are real Bochner integrals.
- Indicator/integral algebra: `MeasureTheory.integral_finset_sum`, `integral_indicator`,
  `Finset.sum_le_sum`. Measurability of `{pᵢ ≤ c}` / `{R = k}` from `hmeas` (see
  `ForMathlib/EmpiricalCDF.measurable_countLE` for the `R`-measurability pattern — re-derive if you
  import it, or inline).

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + `-- USER-INPUT` tags. Named `private` helpers
only; any residual `sorry` must be ONE named private lemma (the Abel-summation per-null bound) with
a one-line note. Commit to `mt/bh-dependent`
(`mt(bhdep): BH FDR ≤ (N₀/N)αHₙ under arbitrary dependence (Candès L5/L6 Thm 3)`).

## DONE
`lake build StatLean.MultipleTesting.BHDependence` exits 0. Report build status, sorry count (0
ideal; if time-boxed, exactly 1 named private `sorry` on the Abel core), and any deviation from the
roadmap.
