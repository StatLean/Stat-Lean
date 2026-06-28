# as-maximal-tight — prove the tight empirical-process maximal inequality (vdV 19.34) [THE CORE]

You are a Lean 4 proof subagent on branch `as/maximal-tight` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` (§2,§6,§7,§9). In an `srun` allocation: plain `lake build`, ITERATE to
GREEN (exit 0, no tactic errors). Never `lake update`. **This is the largest single proof in the plan
(~500–800 lines).** Work statement-first: decompose into named sub-lemmas, stub with `sorry`, build
green, then fill bottom-up. A `sorry` on a clearly-named sub-lemma is acceptable mid-way; a tactic
error is not.

## Touch-set (edit ONLY this file)
- `StatLean/AsymptoticStatistics/EmpiricalProcess/Maximal.lean`

Namespace `AsymptoticStatistics.EmpiricalProcess`; `open MeasureTheory ENNReal Filter`;
`variable {Ω : Type*} [MeasurableSpace Ω]`.

## The goal — a NEW theorem with NO laundered hypothesis
Add `tight_maximal_inequality` whose **conclusion is byte-for-byte the body of `hChainBound_outer`**
(the hypothesis currently laundered into `chaining_integral_universal_K` ~L1372 and
`isPDonsker_of_finite_bracketing_entropy_integral` in DonskerBracketing.lean), proved from the iid
sample — NOT taken as a hypothesis:
```
theorem tight_maximal_inequality
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (hΦ_env : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ) (hΦ_L2 : MemLp Φ 2 P)
    {δq : ℝ} (hδq : 0 < δq) (n : ℕ) :
    ∫⁻ ξ, supNormOver F (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
      ≤ ENNReal.ofReal 2 * bracketingEntropyIntegral δq F P
        + ENNReal.ofReal 2 * (ENNReal.ofReal (Real.sqrt n)
            * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                * Set.indicator {x | δq * Real.sqrt n < |Φ x|} 1 ω ∂P)
```
If you find the proof needs `1 ≤ n` or a `J < ⊤` side-condition, you MAY add them as hypotheses
**only if** they are available at the use site (`chaining_integral_universal_K` has `h_int :
bracketingEntropyIntegral 1 F P < ⊤` and handles `n`); prefer matching the shape exactly. Handle `n = 0`
as a trivial case (empirical process degenerate). The constant `2` is illustrative — if the honest
chaining constant is some other explicit `K`, state `K` and adjust; the downstream consumer only needs
*some* finite multiple of `J(δq) + √n·tail` (check what `chaining_integral_universal_K` actually needs
at ~L1648 and match it).

## Why this is NOT already proved (read first)
`grep -n` these in the file. The three **leaves are fully proved** (your building blocks):
- `tight_chain_level_bound` (~L523): finite-class per-level sup `∫⁻ ⨆_{i∈ι}|G_n g_i| ≤ K·ε·√log(1+|ι|)`
  given per-link bounds `|g_i| ≤ √n·ε/(1+√log(1+|ι|))` and `∫g_i² ≤ (2ε)²`.
- `tight_chain_telescope_bound` (~L633): `∑_q S_q ≤ K·J` given `S_q ≤ B_q` and `∑_q B_q ≤ J`.
- `tight_envelope_truncation_bound` (~L672): `∫⁻ supNormOver F (G_n of the truncated part) ≤
  4·√n·∫|Φ|·𝟙{|Φ|>δ√n}`.
But every **assembler above them launders** the bound: `tight_chain_full_assembly_brick` (~L1005),
`maximal_inequality_bracketing_tight_core` (~L1095), `maximal_inequality_bracketing_tight` (~L1150) all
take `hAbsorb : 1 ≤ J + √n·tail`; `chain_supnorm_integral_bound_at_delta_q` (~L1330) is a pure
passthrough (`:= hChainBound`). The `+1` they cannot remove is the artifact of the CRUDE single-bracket
bound `maximal_inequality_bracketing` (~L135, `K=2nδ+2`). **Your job is the genuine dyadic chaining that
yields `J(δq)` directly with no `+1`, so no `hAbsorb` is needed.**

## Proof roadmap — dyadic chaining (vdV §19.6 proof of Lem 19.34)
Decompose into these named sub-lemmas (stub first, fill bottom-up):
1. **Dyadic bracket sequence.** From `h_int`/finite bracketing at each scale `δ_q = δq·2^{-q}`,
   `q = 0,1,2,…`, get finite `ε`-bracket covers `{[l_i^q, u_i^q]}` of `F` in `L²(P)` with
   `δ_q`-width and cardinality `N_q = N_[](δ_q)`. Use `chaining_envelope_from_bracket` (~L1236) and
   `Bracketing.lean`'s `bracketingNumber`/`HasFiniteBracketingCover`.
2. **Link functions + per-level bound.** Between consecutive scales, each `f ∈ F` is approximated by its
   bracket midpoints `π_q f`; the links `π_q f − π_{q−1} f` have `L²`-norm `≲ δ_{q−1}` and (after
   truncation at `√n·δ_q`) sup `≤ √n·δ_q/(1+√log(1+N_q))`, so `tight_chain_level_bound` gives
   `S_q := ∫⁻ supNormOver F |G_n(π_q − π_{q−1})| ≤ K·δ_q·√log(1+N_q) =: B_q`.
3. **Dyadic-to-integral comparison (THE one new estimate).** `∑_q B_q = K·∑_q δq·2^{-q}·√log(1+N_[](δq·2^{-q}))
   ≤ K'·∫₀^{δq} √log N_[](ε) dε = K'·bracketingEntropyIntegral δq F P`. This is the dyadic Riemann-sum
   bound: `δq·2^{-q}·√log N_[](δq·2^{-q}) ≤ 2·∫_{δq·2^{-(q+1)}}^{δq·2^{-q}} √log N_[](ε) dε` (since
   `N_[]` is monotone decreasing in `ε`, lower-bound the integrand on each dyadic interval). Sum + the
   bracketing-integral `lintegral` over `Ioc`.
4. **Telescope.** `tight_chain_telescope_bound` with `S_q ≤ B_q` (step 2) and `∑ B_q ≤ K'·J` (step 3)
   gives `∑_q S_q ≤ K''·J(δq)`; the chained sum `∑_q (π_q − π_{q−1}) = (lim π_q) − π_0` reconstructs the
   full `supNormOver F G_n` minus the truncated tail.
5. **Envelope tail.** Add `tight_envelope_truncation_bound` for the part of `F` exceeding the
   `√n·δq` truncation ⇒ the `+ 2·√n·∫|Φ|𝟙{|Φ|>δq√n}` term.
6. **Assemble** ⇒ the target. NO `+1`, NO `hAbsorb`.

Study `tight_chain_full_assembly_brick` (~L1005) and `chaining_integral_universal_K` (~L1372) closely —
they already wire steps 1,2,4,5 *modulo* `hAbsorb`/`hChainBound_outer`; step 3 (the genuine dyadic-
Riemann comparison) is what replaces the laundering. You may be able to reuse most of their body.

## Fallback (graded)
If the full assembly resists after serious effort, isolate **step 3 (the dyadic-Riemann comparison)** as
the SINGLE named `sorry`'d lemma and prove `tight_maximal_inequality` from it — that is far sharper than
the current whole-inequality laundering and is a real win. But aim for 0-sorry.

## Constraints
No `axiom`/`admit`. Do NOT weaken/delete the three leaves, `maximal_inequality_bracketing` (crude), or
any existing public theorem. Named `private` helpers for the new sub-lemmas. **Finish on `lake build
StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal` exit 0.** Commit to `as/maximal-tight`
(`as(empirical): prove tight_maximal_inequality (vdV 19.34) by dyadic chaining — de-launder the bound`).

## DONE
`lake build StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal` exits 0. Report: build status,
final sorry count (0 ideal; if not, the single named debt = step 3), the exact final statement of
`tight_maximal_inequality` (so I can verify it matches `hChainBound_outer`), and which leaves/helpers
you reused.
