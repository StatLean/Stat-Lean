import StatLean.Optimization.Convex.Defs
import StatLean.Optimization.Convex.Subgradient
import StatLean.Optimization.Smoothness.Defs
import StatLean.Optimization.Smoothness.CoCoercive
import StatLean.Optimization.Prox.Defs
import StatLean.Optimization.Prox.Pillar
import StatLean.Optimization.ForMathlib.FirstOrderConvex
import StatLean.Optimization.ForMathlib.GradientCalc
import StatLean.Optimization.LocalGlobal
import StatLean.Optimization.GradientDescent
import StatLean.Optimization.FrankWolfe
import StatLean.Optimization.ProximalGradient
import StatLean.Optimization.AcceleratedProximal

/-!
# Optimization — area umbrella

Convex optimization theory, formalized from Lu, *Big Data Analysis*, ch. 10–12:

* **Convexity & subgradients** (ch. 10): `IsSubgradient` / `subdifferential`;
  the gradient is a subgradient; local-minima-are-global (Prop 10.1).
* **First-order methods** (ch. 11): `IsLSmooth`; co-coercivity (Lemma 11.1);
  gradient-descent rate (Thm 11.1); Frank–Wolfe rate (Thm 11.2).
* **Proximal methods** (ch. 12): `proxObj` / `IsProxMinimizer`; the pillar
  inequality (Lemma 12.1); proximal-gradient rate (Thm 12.1); accelerated
  proximal-gradient rate (Thm 12.2).

Everything lives over a real inner product space `E` (`[InnerProductSpace ℝ E]`,
with `[CompleteSpace E]` where the Riesz `gradient` is used); the book's `ℝ^d`
is the special case. Modules are imported above as each lands.
-/
