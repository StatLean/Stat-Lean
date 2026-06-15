# mt-bh — prove Benjamini–Hochberg FDR control

You are a Lean 4 proof subagent on branch `mt/bh` (based on `mt/area`, which already has the
proven `mt/foundations`). Project: **StatLean** — read its `CLAUDE.md` (§2 hypothesis discipline,
§6 search, §7 gotchas).

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/BenjaminiHochberg.lean`

Do **not** touch `FDP/Defs.lean`, `PValues/Defs.lean` (laptop-only), the umbrella, or any other
file. You MAY reshape the `bhRejects` definition and add helper lemmas *within this file* if it
helps, as long as `bhRejects` stays a faithful formalization of the BH procedure and the public
theorem statements/hypotheses are unchanged (do not weaken hypotheses or strengthen conclusions).

## Goal
Prove `bh_count_eq_leaveOneOut`, `bh_claim`, and `benjamini_hochberg_fdr_le` (0 sorry, 0 error).
Verify: `lean-fasrc-build StatLean.MultipleTesting.BenjaminiHochberg` green.

## The theorem (Lu-BDA §18, `\label{BH}`)
If `p₁,…,p_N` are independent and each null `pⱼ` (`j ∈ H₀`) is super-uniform, the BH procedure at
level `α` has `FDR ≤ (N₀/N)·α ≤ α`, where `N₀ = |H₀|`. (Book states `=`; we prove the honest `≤`
that holds under `SuperUniform`.)

## Verbatim book proof (translate to Lean)
Let `R = Σⱼ ψⱼ` (rejections), `FDP = Σ_{i∈H₀} ψᵢ/(R∨1)`. It suffices to show, for each `i ∈ H₀`,
`E[ψᵢ/(R∨1)] ≤ α/N` (`bh_claim`); summing over `H₀` gives `FDR ≤ N₀α/N`.

For `bh_claim`, decompose `ψᵢ/(R∨1) = Σ_{k=1}^N ψᵢ·𝟙(R=k)/k`. Two key observations:
1. When `R = k`, `ψᵢ = 1 ⟺ pᵢ ≤ αk/N` (BH rejects the `k` smallest, and `p₍ₖ₎ ≤ αk/N`).
2. **Leave-one-out** (`bh_count_eq_leaveOneOut`): if `pᵢ ≤ αk/N`, replacing `pᵢ` by `0` leaves the
   rejection count unchanged: `ψᵢ·𝟙(R=k) = 𝟙(pᵢ ≤ αk/N)·𝟙(R(pᵢ→0)=k)`, where `R(pᵢ→0)` is the BH
   count on `p` with coordinate `i` set to `0` — crucially independent of `pᵢ`.

Condition on `𝓕ᵢ = σ(pⱼ : j ≠ i)`. Since `pᵢ ⟂ 𝓕ᵢ` (independence) and `pᵢ` is super-uniform,
`E[𝟙(pᵢ ≤ αk/N) ∣ 𝓕ᵢ] = P(pᵢ ≤ αk/N) ≤ αk/N`. As `R(pᵢ→0)` is `𝓕ᵢ`-measurable,
`E[ψᵢ/(R∨1) ∣ 𝓕ᵢ] = Σₖ (αk/N)·𝟙(R(pᵢ→0)=k)/k = (α/N)·Σₖ 𝟙(R(pᵢ→0)=k) = α/N`. Tower property ⇒
`E[ψᵢ/(R∨1)] ≤ α/N`.

## Lean guidance
- `bh_count_eq_leaveOneOut` is deterministic/combinatorial — prove it first; it's the crux. Work
  directly with `bhRejects` and `Function.update p i 0`. You may restate it in whatever exact form
  makes the analytic step cleanest (e.g. the indicator-product identity), keeping it a named lemma.
- Conditional expectation: `MeasureTheory.condExp` (notation `μ[f|m]`), import
  `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`. The σ-algebra `𝓕ᵢ` is the iSup of
  `MeasurableSpace.comap (p j)` over `j ≠ i`, or `comap (Function.update p i 0 ω-vector)`.
  `iIndepFun` ⇒ `pᵢ` independent of `𝓕ᵢ`: use `ProbabilityTheory.iIndepFun.indepFun` /
  `…condExp…` lemmas; search with loogle (`"condExp"`, `"indepFun"`, `"condExp_indep"`).
- Super-uniform enters only as `E[𝟙(pᵢ ≤ c) ∣ 𝓕ᵢ] ≤ c`; combined with independence this is
  `P(pᵢ ≤ c) ≤ c` = the `SuperUniform` hypothesis.
- Finite sum over `k ∈ {1,…,N}`: `Finset.sum`; `numRejections (bhRejects …) ω ∈ {0,…,N}`.

## Constraints
No `axiom`/`admit`; keep every `-- USER-INPUT:`/`-- LEAN-ONLY:` tag and the docstrings; do not add
hypotheses to the public theorems. If you must split out sub-lemmas, make them named (no anonymous
`sorry`). Commit to `mt/bh`.
