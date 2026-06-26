# mt-storey — Storey's q-value FDR control (Candès L7 §7.4 Thm 3)

You are a Lean 4 proof subagent on branch `mt/storey` (based on `mt/batch8`). Project: **StatLean**
— read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain
`lake build`, ITERATE. Never `lake update`. This unit has a **documented hard core** — read carefully.

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/Storey.lean`

Merged & read-only: `ForMathlib/EmpiricalCDF` (`countLE`, `nullCountLE`),
`ForMathlib/BinomialRatio`, `ForMathlib/OptionalStopping`, `FDP/Defs`, `PValues/Defs`. Do not change
public signatures or the `def`s.

## The two sorries — different dispositions
1. **`storey_reverseMG_ost` — LEAVE AS `sorry`.** This is the continuous-time backwards-martingale
   optional-stopping step (`E[V(τ)/τ] = E[V(1/2)/(1/2)]`), for which Mathlib has no support. It is a
   **documented named debt** (a self-contained development of its own — the uniform-null analogue of
   the knock-off `condExp_coord_eq_count_div`). Keep its `sorry` and its docstring. Do NOT attempt it.
2. **`storey_fdr_le` — ATTEMPT to close it 0-sorry USING `storey_reverseMG_ost`.** If, after real
   effort, the surrounding algebra/binomial does not fully assemble, leave it as a named `sorry` too
   with a one-line note on the blocking step.

## `storey_fdr_le` proof (assemble from the OST lemma + the binomial identity)
`FDP(τ) = V(τ)/(R(τ)∨1)` with `τ = storeyThreshold p q`. By the threshold definition,
`storeyFDRhat q τ ≤ q`, i.e. `π̂₀·nτ/(R(τ)∨1) ≤ q`, giving `(R(τ)∨1) ≥ π̂₀·nτ/q`, hence
`FDP(τ) = V(τ)/(R(τ)∨1) ≤ q·V(τ)/(π̂₀·nτ)`. With `π̂₀ = 2(1+n−R(1/2))/n` (so `π̂₀·n = 2(1+n−R(1/2))`):
`E[FDP(τ)] ≤ q·E[ V(τ)/τ · 1/(2(1+n−R(1/2))) ]`. Bound `1+n−R(1/2) ≥ 1+n₀−V(1/2)` (since
`R(1/2) = V(1/2)+S(1/2) ≤ V(1/2)+(n−n₀)` as `S(1/2) ≤ n−n₀`), and apply **`storey_reverseMG_ost`**
to replace `E[V(τ)/τ·g]`-style by the `t=1/2` value, reducing to
`E[FDP(τ)] ≤ q·E[ V(1/2)/(1+n₀−V(1/2)) ]`. Finally the **binomial identity**
`E[V(1/2)/(1+n₀−V(1/2))] = 1−2^{−n₀} < 1` (`V(1/2) ∼ Bin(n₀,1/2)` — independent uniform nulls;
`∑ᵢ (i/(1+n₀−i))·C(n₀,i)·2^{−n₀} = 2^{−n₀}(2^{n₀}−1)`): reuse `ForMathlib/BinomialRatio`
(`./tools/api.sh StatLean/MultipleTesting/ForMathlib/BinomialRatio.lean` — find the exact lemma).
Conclude `FDR ≤ q·(1−2^{−n₀}) ≤ q`.

(Note: the exact `g`-factor handling in the OST step may require restating `storey_reverseMG_ost`
slightly — you MAY adjust ITS statement to the precise form `storey_fdr_le` needs, as long as it
stays a faithful "backwards-MG optional stopping" statement and keeps its `sorry` + documenting
docstring. Do not weaken `storey_fdr_le`.)

## Constraints
No `axiom`/`admit`/new hypotheses on `storey_fdr_le`; keep docstrings + `-- USER-INPUT` tags. Named
`private` helpers only. Commit to `mt/storey`
(`mt(storey): Storey q-value FDR≤q via reverse-MG OST (debt) + binomial (Candès L7 Thm 3)`).

## DONE
`lake build StatLean.MultipleTesting.Storey` exits 0. Report build status, sorry count (1 = only the
documented `storey_reverseMG_ost`, ideal; 2 if `storey_fdr_le` also blocked + which step), and which
`BinomialRatio` lemma you used.
