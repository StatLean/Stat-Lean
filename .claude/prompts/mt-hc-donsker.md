# mt-hc-donsker — Higher Criticism: formalize the H₀ Donsker half (Candès L3 §3.3.3)

You are a Lean 4 proof subagent on branch `mt/hc-donsker` (based on `mt/batch8`). Project:
**StatLean** — read `CLAUDE.md` first (§2, §6, §7, §9). Inside an `srun` allocation: build with plain
`lake build`, ITERATE. Never `lake update`. **The full Donoho–Jin detection theorem is multi-month
research; your job is the REACHABLE real progress** — the H₀ empirical-process (Donsker) half — plus a
sharpened statement of what remains. Do NOT add a laundered detection theorem (CLAUDE.md §2).

## Touch-set (edit ONLY this file)
- `StatLean/MultipleTesting/GoodnessOfFit/HigherCriticism.lean`

`rhoStar` (+ properties) and `hcStat` are proved 0-sorry; keep them and the deferral docstring. Add
the H₀ Donsker result below them.

## Goal — the empirical-CDF class is P-Donsker
The project HAS the Donsker framework: **READ**
`StatLean/AsymptoticStatistics/EmpiricalProcess/Donsker.lean` (`IsPDonsker`, `IsMarginalCLT`,
`IsAsymptoticallyEquicontinuous`) and `DonskerBracketing.lean`
(`isPDonsker_of_finite_bracketing_entropy_integral`), plus `GlivenkoCantelli.lean`,
`FunctionClass.lean` (`IsEnvelope`, bracketing), `MaximalOrlicz.lean`. Use `./tools/api.sh` on these.

Formalize: **the class of half-line indicators `F_cdf = { 𝟙(−∞,t] : t ∈ ℝ }` (equivalently the
empirical-CDF process) is `P`-Donsker for any law `P` on ℝ.** Concretely state and prove a theorem

```
theorem halfLine_isPDonsker (P : Measure ℝ) [IsProbabilityMeasure P] :
    IsPDonsker {f | ∃ t : ℝ, f = Set.indicator (Set.Iic t) (fun _ => (1:ℝ))} P
```

(adjust to the exact `IsPDonsker` signature you find). **Proof:** apply
`isPDonsker_of_finite_bracketing_entropy_integral` — the half-line class has bracketing number
`N_[](ε) ≲ 1/ε` (so `∫₀¹ √(log N_[](ε)) dε < ∞`, the Donsker entropy condition holds): construct the
ε-brackets `[𝟙(−∞,tᵢ], 𝟙(−∞,tᵢ₊₁]]` from a grid of the quantiles of `P` (monotone, so a partition of
`[0,1]` into `⌈1/ε⌉` `P`-mass-ε pieces gives the brackets). The envelope is `1`. Search the exact
bracketing/entropy definitions in `FunctionClass.lean` / `DonskerBracketing.lean` and match them.

If the full `isPDonsker_of_finite_bracketing_entropy_integral` application has a gap (e.g. a
measurability or entropy-integral side condition you cannot discharge), prove as much as you can and
isolate the gap as a single NAMED `sorry` with a precise note — a proved `halfLine_isPDonsker`
modulo one named entropy lemma is a real result.

## Then: sharpen the deferral docstring
Update the module docstring's "Deferred" section: with `halfLine_isPDonsker` proved, the H₀
empirical-process convergence for `hcStat` is now in the library; the residual gaps for Theorem 3 are
ONLY (i) the empirical-process LIL `max Wₙ(t)/√(2 log log n) →ᵈ 1` (the threshold calibration) and
(ii) the H₁ sparse-mixture large deviations. Keep it honest prose; do NOT state the full theorem.

## Constraints
No `axiom`/`admit`; no laundered detection theorem. Named `private`/named-`theorem` helpers only.
Commit to `mt/hc-donsker`
(`mt(hc): empirical-CDF class is P-Donsker (H₀ half of Donoho-Jin) via bracketing entropy (Candès L3)`).

## DONE
`lake build StatLean.MultipleTesting.GoodnessOfFit.HigherCriticism` exits 0. Report: build status,
whether `halfLine_isPDonsker` closed (0-sorry / 1 named entropy lemma / blocked), the project Donsker
lemmas used, and the sharpened residual gap.
