# mt-bh-martingale — BH FDR exact identity FDR=(N₀/N)α (Candès L7 §7.2 Thm 2)

You are a Lean 4 proof subagent on branch `mt/bh-martingale` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with
plain `lake build`, ITERATE. Never `lake update`. **Time-box**; this re-derives a large proof — if it
does not fully close after real effort, leave `benjamini_hochberg_fdr_eq` as the single named
`sorry` with a one-line reason (which step blocked).

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/BHMartingale.lean`

`BenjaminiHochberg.lean` (defines `bhRejects`, and — *private* to that file — the leave-one-out crux
`bh_count_eq_leaveOneOut`, `bh_claim`, and the proof of `benjamini_hochberg_fdr_le`) is imported,
read-only. `FDP/Defs`, `PValues/Defs` likewise. **READ `BenjaminiHochberg.lean` carefully** — you
will re-derive its leave-one-out argument here, strengthened from `≤` to `=`. Do not change the
public theorem signature.

## Goal
Prove `benjamini_hochberg_fdr_eq` (0-sorry ideal). `lake build StatLean.MultipleTesting.BHMartingale` green.

## The theorem
Independent p-values, every null **exactly** uniform (`μ{pⱼ≤t}=ofReal t` on `[0,1]`). Then
`FDR H₀ (bhRejects α p) μ = (N₀/N)·α`.

## Proof (leave-one-out, equality — mirror `benjamini_hochberg_fdr_le`, replace `≤` by `=`)
`FDP = ∑_{i∈H₀} ψᵢ/(R∨1)` (`ψᵢ = 𝟙(i∈bhRejects)`, `R = card`); `FDR = ∑_{i∈H₀} E[ψᵢ/(R∨1)]`
(`integral_finset_sum`; each summand in `[0,1]`, integrable). **It suffices to show, per null `i`,
`E[ψᵢ/(R∨1)] = α/N`** (sum gives `N₀·α/N = (N₀/N)·α`).

Per-null (the `bh_claim` argument, now with equality):
1. **Leave-one-out** (`bh_count_eq_leaveOneOut` in `BenjaminiHochberg.lean` — re-derive privately):
   `ψᵢ·𝟙(R=k) = 𝟙(pᵢ ≤ kα/N)·𝟙(R₍ᵢ→0₎=k)`, where `R₍ᵢ→0₎` is the BH count with `pᵢ` set to `0`
   (use `Function.update p i 0`), which is **independent of `pᵢ`**.
2. Decompose `ψᵢ/(R∨1) = ∑_{k=1}^N (1/k)·ψᵢ·𝟙(R=k)`, so
   `E[ψᵢ/(R∨1)] = ∑_k (1/k)·E[𝟙(pᵢ ≤ kα/N)·𝟙(R₍ᵢ→0₎=k)]`.
3. **Independence factorization**: `pᵢ ⟂ R₍ᵢ→0₎` (from `iIndepFun`, as in `bh_claim` —
   `iIndepFun.indepFun_finset` / conditioning on `𝓕ᵢ = σ(pⱼ:j≠i)`), so
   `E[𝟙(pᵢ≤kα/N)·𝟙(R₍ᵢ→0₎=k)] = P(pᵢ≤kα/N)·P(R₍ᵢ→0₎=k)`.
4. **Exact uniformity ⇒ equality**: `P(pᵢ ≤ kα/N) = kα/N` (the hypothesis `hnull` at `t = kα/N`;
   note `0 ≤ kα/N ≤ 1` from `k ≤ N`, `α ≤ 1`). Hence
   `E[ψᵢ/(R∨1)] = ∑_k (1/k)(kα/N)·P(R₍ᵢ→0₎=k) = (α/N)·∑_k P(R₍ᵢ→0₎=k) = (α/N)·1 = α/N`
   (the `∑_k P(R₍ᵢ→0₎=k) = 1` because `R₍ᵢ→0₎ ∈ {0,…,N}` and the `k=0` term drops via the `1/k`/`ψᵢ`).
   This is exactly where `bh_claim`'s `≤` becomes `=`: super-uniformity gave `P ≤ kα/N`, exact
   uniformity gives `P = kα/N`.

Reuse the structure of `bh_claim` verbatim where possible; the ONLY change is using `hnull`'s
equality instead of `SuperUniform`'s inequality. You may copy its private helpers into this file.

## Constraints
No `axiom`/`admit`/new hypotheses; keep docstrings + `-- USER-INPUT` tags. Named `private` helpers
only; any residual `sorry` is the single `benjamini_hochberg_fdr_eq`. Commit to `mt/bh-martingale`
(`mt(bhm): BH FDR=(N₀/N)α exact identity via leave-one-out (Candès L7 Thm 2)`).

## DONE
`lake build StatLean.MultipleTesting.BHMartingale` exits 0. Report build status, sorry count (0 ideal;
if time-boxed, 1 named sorry + which step), and how much of `bh_claim` you reused vs re-derived.
