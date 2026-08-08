# Close the analytic core of the Lindeberg CLT, then the randomization asymptotics

Lean 4 / Mathlib proof engineer on `StatLean`. Pin `v4.29.1`. (`CLAUDE.md` is gitignored and absent here; everything you need is below. Never `lake update`; `sorry` is planned debt tied to a named lemma; do not launder unproven content into hypotheses.)

**CRITICAL — how to build.** Run `lake build <module>` as an ordinary FOREGROUND command and read its output in the same step. Do **not** background it, do **not** wait for a "build notification" — there is no notification channel and you will stall and lose the session.

## Hard constraints

- **Only edit** `StatLean/HypothesisTesting/ForMathlib/LindebergCLT.lean` and `.../Randomization/{Asymptotics,SignChange}.lean`. `LindebergCLT` keeps **Mathlib-only imports**.
- Signatures FROZEN. Add `import Mathlib.*`, closed modules (in the `Randomization` files), and `private` helpers freely. Lines ≤ 100 chars.
- Goal: **0 sorries, 0 errors**. Escape hatch: at most one lifted `private` sorry per file with a precise `-- TODO:`.
- **Do not weaken any statement.** If one is wrong, STOP and report precisely.
- Commit after each lemma compiles.

## Priority 1 — the one missing ingredient (this is the whole item)

`lindeberg_clt` and `lindeberg_clt_of_bounded` are **already closed**, resting on a single private lemma:

```
private lemma tendsto_prod_charFun_lindeberg … :
    Tendsto (fun n => ∏ i, charFun (P.map (X n i)) t) atTop (𝓝 (charFun (gaussianReal 0 1) t))
```

Your predecessor did the Lévy-continuity skeleton and identified **exactly** what is missing: the quantitative pointwise remainder bound

```
‖exp (I * y) − (1 + I * y − y^2 / 2)‖ ≤ min (|y|^3 / 6) (y^2)      (y : ℝ)
```

Mathlib has only the non-uniform `taylor_charFun_two` (`o(t²)` near 0), which is not enough. **Prove this bound as a `private` lemma first.** Both halves are elementary: the `|y|³/6` half by integrating the remainder form of the Taylor expansion of `exp (I·y)` three times (or `Complex.abs_exp_sub_one_sub_id_le`-style induction), the `y²` half from `‖exp (I y) − 1 − I y‖ ≤ y²/2` plus the triangle inequality with `‖y²/2‖`.

With that in hand the classical argument closes:
1. Telescope: `|∏ᵢ aᵢ − ∏ᵢ bᵢ| ≤ ∑ᵢ |aᵢ − bᵢ|` when all `|aᵢ|, |bᵢ| ≤ 1` (`Finset.prod` induction).
2. Take `aᵢ = φₙᵢ(t)`, `bᵢ = 1 − t²σₙᵢ²/2`; bound each `|aᵢ − bᵢ| ≤ E[min(|t Xₙᵢ|³/6, t² Xₙᵢ²)]` using centering (`hmean`) and the bound above.
3. Split the expectation at `|Xₙᵢ| = ε`: small part `≤ |t|³ ε ∑ᵢ σₙᵢ² / 6`, large part `≤ t² ∑ᵢ E[Xₙᵢ² 1{|Xₙᵢ| > ε}]` — the Lindeberg sum, which `hlin` sends to 0.
4. `∏ᵢ (1 − t²σₙᵢ²/2) → exp(−t²/2)` from `hvar` and `log(1−u) = −u + O(u²)` with the row terms uniformly small (which the Lindeberg condition gives).

## Priority 2 — the randomization asymptotics that consume it

`Randomization/Asymptotics` (3) and `SignChange` (4). `SlutskyRandomization` is closed (note `cdf_map_affine` is stated for `0 < a` because the source's "a ≠ 0" parenthetical is false for negative scaling — keep that). `ForMathlib/QuantileFunction` is closed, including `tendsto_quantile_of_tendsto` and `tendstoInMeasure_quantile`. In `SignChange`, do **not** add `E[ψ(X)] = 0`: it is forced by "ψ odd" + "P symmetric" + square-integrability, so assuming it would be laundering.

## Closed, axiom-clean — black boxes

`Randomization.{ExactLevel, OrbitConditional}`; `ForMathlib.{QuantileFunction, CriticalFunction, GroupAverageMeasure, HypergeometricMoments}`; `Tests.{PValue, Confidence}`; `NeymanPearson.Lemma.{exists_mostPowerful, isMostPowerful_npTest}`; `MLR.{hasMLR_expFamily, integral_mono_of_hasMLR}`.

## Report

Final `lake build` status per module, per-file sorry counts, `#print axioms lindeberg_clt`, and for anything left open the precise obstruction.
