# mt-foundations — prove the MultipleTesting ForMathlib foundations

You are a Lean 4 proof subagent on branch `mt/foundations` (based on `mt/area`). Project:
**StatLean** — read its `CLAUDE.md` (esp. §2 hypothesis discipline, §6 search tools, §7 gotchas)
before starting.

## Touch-set (edit ONLY these two files)
- `StatLean/MultipleTesting/ForMathlib/OrderStatistics.lean`
- `StatLean/MultipleTesting/ForMathlib/OptionalStopping.lean`

Do **not** touch any other file (no `*/Defs.lean`, no umbrella, no assembly files, no
`lakefile.lean`/`lean-toolchain`/`lake-manifest.json`).

## Goal
Replace every `sorry` in those two files with a complete proof. Success = both files build
0-sorry, 0-error: `lean-fasrc-build StatLean.MultipleTesting.ForMathlib.OptionalStopping` green
(it pulls in `OrderStatistics`).

## OrderStatistics.lean
`orderStat_monotone v : Monotone (orderStat v)`. By definition `orderStat v i = v (Tuple.sort v i)`,
defeq to `v ∘ ⇑(Tuple.sort v)`. Mathlib has `Tuple.monotone_sort v : Monotone (v ∘ ⇑(Tuple.sort v))`
(`Mathlib.Data.Fin.Tuple.Sort`). Try `by intro i j h; simpa [orderStat] using Tuple.monotone_sort v h`
or `by unfold orderStat; exact Tuple.monotone_sort v`.

## OptionalStopping.lean (the `thm:optstop` discharge — Lu-BDA §19)
Bridge to Mathlib's `MeasureTheory.Submartingale.expected_stoppedValue_mono`
(`Mathlib.Probability.Martingale.OptionalStopping`): for stopping times `τ ≤ π`, `π` bounded by
`N`, a submartingale `g` satisfies `∫ stoppedValue g τ ≤ ∫ stoppedValue g π`.

1. `supermartingale_expected_stoppedValue_antitone` — supermartingale `f`, `τ ≤ π`, `π` bounded ⇒
   `∫ stoppedValue f π ≤ ∫ stoppedValue f τ`. Proof: `Supermartingale.neg` gives `Submartingale (-f)`;
   apply `expected_stoppedValue_mono` to `-f` (same `τ ≤ π`, same bound) to get
   `∫ stoppedValue (-f) τ ≤ ∫ stoppedValue (-f) π`; `stoppedValue (-f) σ = -(stoppedValue f σ)`
   (push `Pi.neg`/`stoppedValue` through), and `∫ -(·)` flips the inequality (`integral_neg`,
   `neg_le_neg_iff`). Supermartingale values are integrable (`Supermartingale.integrable`), which the
   Mathlib lemma needs internally.
2. `supermartingale_integral_stoppedValue_le` — `∫ stoppedValue f τ ≤ ∫ f 0`. Specialize lemma 1
   with the *earlier* stopping time `≡ 0` (constant `0` is a stopping time) and `π := τ`. Then
   `stoppedValue f (fun _ => 0) ω = f 0 ω` (unfold `stoppedValue`; `WithTop`/`ℕ∞` `0` coerces to
   index `0`). Rewrite the RHS integrand to `f 0` and close.

Use `loogle`/`#leansearch`/`exact?` for exact names (`Supermartingale.neg`,
`Supermartingale.integrable`, `stoppedValue`, the constant stopping time, `integral_neg`). If a
lemma STATEMENT must change slightly to be provable (e.g. it genuinely needs an integrability
hypothesis), make the minimal change and document it in the docstring — but first try to derive
the side-condition internally from `Supermartingale`.

## Constraints
No `axiom`/`admit`. No new free hypotheses beyond what's derivable. Keep all docstrings and the
`thm:optstop` / Lu-BDA citations. Commit your work to `mt/foundations`.
