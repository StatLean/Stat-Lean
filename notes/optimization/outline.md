# Optimization area — outline (Lu, *Big Data Analysis* ch. 10–12)

Ambient space: real inner product space `E` (`[NormedAddCommGroup E]
[InnerProductSpace ℝ E] [CompleteSpace E]`); book's `ℝ^d` is the special case.
`gradient` = Mathlib Riesz gradient (`∇`), notation `⟪·,·⟫_ℝ`.

## Dependency DAG

```
ForMathlib/FirstOrderConvex   ForMathlib/GradientCalc
   (gradient inequality)        (min ⟹ ∇=0)
        │   │                         │
        │   └─────────────┐           │
        ▼                 ▼           ▼
 Convex/Subgradient   Smoothness/CoCoercive (Lem 11.1)
   (∇f ∈ ∂f)                 │
        │                    ├──────────────┐
        ▼                    ▼              ▼
 LocalGlobal (Prop 10.1)  GradientDescent  FrankWolfe
                            (Thm 11.1)      (Thm 11.2)

 Prox/Defs ─▶ Prox/Pillar (Lem 12.1) ─▶ ProximalGradient (Thm 12.1)
   (Smoothness/Defs, FirstOrderConvex)  └▶ AcceleratedProximal (Thm 12.2)
```

Concept defs (laptop-only): `Convex/Defs` (`IsSubgradient`, `subdifferential`),
`Smoothness/Defs` (`IsLSmooth`), `Prox/Defs` (`proxObj`, `IsProxMinimizer`).

## Targets (8) and supporting lemmas

| File | Decl | Book | Status |
|------|------|------|--------|
| Convex/Defs | `IsSubgradient`, `subdifferential` | Def 10.2 | def (done) |
| Smoothness/Defs | `IsLSmooth` | Def 11.1 (`def:lsmooth`) | def (done) |
| Prox/Defs | `proxObj`, `IsProxMinimizer` | Def 12.1 | def (done) |
| ForMathlib/FirstOrderConvex | `inner_gradient_le_sub_of_convexOn` | §10.2 | sorry |
| ForMathlib/GradientCalc | `gradient_eq_zero_of_forall_le` | §11.1 | sorry |
| Convex/Subgradient | `gradient_mem_subdifferential` | §10.2 | sorry |
| Smoothness/CoCoercive | `cocoercive`, `inner_gradient_sub_nonneg` | Lem 11.1 | sorry |
| Prox/Pillar | `prox_variational_inequality`, `pillar` | Lem 12.1 | sorry |
| LocalGlobal | `isGlobalMin_iff_zero_mem_subdifferential`, `forall_le_of_isLocalMin` | Prop 10.1 | sorry |
| GradientDescent | `gradientDescent_rate` | Thm 11.1 (`thm:gd`) | sorry |
| FrankWolfe | `frankWolfe_rate` | Thm 11.2 (`thm:fw-rate`) | sorry |
| ProximalGradient | `proximalGradient_rate` | Thm 12.1 (`thm:cvg-prox`) | sorry |
| AcceleratedProximal | `nesterov_lambda_lower`, `acceleratedProximalGradient_rate` | Thm 12.2 (`thm:cvg-aprox`) | sorry |

## Book-vs-Lean constants

| Result | Book constant | Lean constant to prove | Note |
|--------|---------------|------------------------|------|
| Thm 11.1 GD | `2L‖x₀-x*‖²/t` | TBD at proof time | book is loose; expect `L‖x₀-x*‖²/(2t)` |
| Thm 11.2 FW | `2L·d_X²/(t+2)` | `2L·D/(t+2)` | `D ≥ sup‖x-y‖²` as hypothesis |
| Thm 12.1 PGD | `L‖x₀-x*‖²/(2t)` | same | standard |
| Thm 12.2 APGD | `2L‖x₀-x*‖²/(t+1)²` | same | standard |

## Deliberate hypothesis decisions (audit notes)

* **Lemma 11.1 (`cocoercive`)** adds `ConvexOn` to the book's "L-smooth f"
  hypothesis — the book proof uses convexity. Genuine correction, documented.
* **FW LMO** (`hlmo`) and **prox steps** (`IsProxMinimizer` recurrences) are
  genuine external oracle inputs (the algorithm definitions), not laundered
  derivations — analogous to "the statistic T" pattern. Tag `-- USER-INPUT`.
* **`IsLSmooth`** is the quadratic upper bound itself (book's primary form), so
  the descent inequality is definitional; differentiability carried separately
  where `gradient` must be the true derivative.
