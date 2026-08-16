import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional

/-!
# Conditional independence — the disintegration predicate

The keystone of the graphical-models area: a conditional-independence predicate
`X ⫫ Y ∣ Z` that works on **arbitrary** measurable spaces, with no standard-Borel
side condition, so that the same vocabulary carries the discrete (mass-function) theory,
the Gaussian theory, and any future semiparametric/causal consumer.

The idiom is the repo's existence-of-a-kernel one (`Coarsening.IsMAR`,
`Operators.IsCoarseningAtRandom`): rather than *invoking* a regular conditional
distribution, we *assert that a product disintegration exists*.

* `CondIndep μ f g h` — the joint law of `(h, (f, g))` under `μ` factors as
  `(law of h) ⊗ₘ (κ ×ₖ η)` for two Markov kernels `κ`, `η` out of the conditioning space;
* `CondIndep.symm` — Lauritzen (C1), *symmetry*: swap the two kernels;
* `CondIndep.comp` — Lauritzen (C2), *decomposition* in its functional form
  `U = φ(X), W = ψ(Y)`: push the kernels through measurable maps;
* `CondIndep.const_right` / `condIndep_const_of_indepFun` — conditioning on a **constant**
  is ordinary independence, in both directions;
* `condIndepFun_of_condIndep` — the **export bridge** to Mathlib's
  `ProbabilityTheory.CondIndepFun`. Stated so that our results are exportable; **no**
  theorem of this area depends on it.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, 1996, §3.1, pp. 28–29, equations (3.1)–(3.7) — in particular the
symmetric density identity (3.2)
`f_{XYZ}(x,y,z) f_Z(z) = f_{XZ}(x,z) f_{YZ}(y,z)` and the factorisation criterion (3.6)
`f(x,y,z) = h(x,z) k(y,z)`; the properties (C1)–(C4) are the unnumbered labelled list on
p. 29 (`Lauritzen §3.1`).

**Proof formalization notes.** *Book vs Lean:* Lauritzen states conditional independence
through densities with respect to a product measure (3.1); we state the equivalent
measure-theoretic disintegration, which needs no dominating measure and no standard Borel
hypothesis. The repo deliberately does **not** build on Mathlib's `CondIndepFun` (see
`CausalInference/Core/PopulationDefs.lean:47`): `CondIndepFun` carries a
`StandardBorelSpace Ω` burden on the *sample* space, which the model-level statements here
must not inherit. Two consequences of the chosen shape are worth recording.

* Symmetry (C1) and the functional form of decomposition (C2) are **structural** — swap the
  kernel pair, push the kernels forward — hence hold in this generality. Weak union (C3),
  contraction (C4) and intersection (C5) need essential uniqueness of disintegrations and are
  therefore proved in the discrete layer only, never assumed here (roadmap §3).
* `const_right` genuinely needs `IsProbabilityMeasure μ`, not merely `IsFiniteMeasure μ`: for
  a finite measure of total mass `m`, the disintegration identity gives
  `μ.map (f, g) = m · (κ c).prod (η c)` while `(μ.map f).prod (μ.map g) = m² · (κ c).prod (η c)`,
  so the two agree exactly when `m ∈ {0, 1}`.

**Reuse (binding).** Nothing measure-theoretic is re-derived here; every proof is an
assembly of existing Mathlib kernel algebra, and each theorem's docstring names its route.

* swap the kernel pair — `ProbabilityTheory.Kernel.map_prod_swap`
  (`Kernel/Composition/Prod.lean:198`);
* push kernels through maps — `ProbabilityTheory.Kernel.map_prod_map` (`Prod.lean:174`) and
  `ProbabilityTheory.Kernel.IsMarkovKernel.map` (`MapComap.lean:118`);
* move a `Kernel.map` across `⊗ₘ` — `MeasureTheory.Measure.compProd_map`
  (`Kernel/Composition/Lemmas.lean:120`);
* constant conditioning variable — `MeasureTheory.Measure.map_const` (`Measure/Dirac.lean:91`);
* land on Mathlib's independence — `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`
  (`Independence/Basic.lean:701`);
* uniqueness of the disintegrating kernel —
  `ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd` (`Kernel/CondDistrib.lean:163`);
* Mathlib's conditional independence already in our shape —
  `ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib`
  (`Independence/Conditional.lean:817`), with
  `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` (`:867`) as the alternative.

In particular the bridge `condIndepFun_of_condIndep` is a *citation*: the right-hand side of
`condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib` is literally our definition
with `κ := condDistrib f h μ`, `η := condDistrib g h μ` (modulo
`Measure.compProd_eq_comp_prod`), and `condDistrib_ae_eq_of_measure_eq_compProd` identifies
our anonymous witnesses with those two after marginalising the product kernel.

**Bibliographic comments.** The axiomatic treatment of conditional independence as a
free-standing relation is A. P. Dawid, "Conditional independence in statistical theory,"
*J. Roy. Statist. Soc. Ser. B* **41** (1979), 1–31. The names *symmetry / decomposition /
weak union / contraction / intersection* for the properties Lauritzen labels (C1)–(C5) are
J. Pearl's, *Probabilistic Reasoning in Intelligent Systems*, Morgan Kaufmann, 1988. The
kernel (disintegration) formulation is the modern regular-conditional-probability reading of
Lauritzen's density identity (3.2).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels.GraphicalModels

/-- **Conditional independence** `f ⫫ g ∣ h` under `μ` (Lauritzen §3.1, p. 28): the joint law
of `(h, (f, g))` disintegrates over `h` as a *product* of two Markov kernels.

Edge behaviour: the predicate quantifies existentially over the disintegrating kernels, so it
is meaningful for an arbitrary measure `μ` on an arbitrary measurable space — no
standard-Borel hypothesis, no dominating measure. For `μ = 0` it holds vacuously (both sides
are `0`), and for non-measurable `f`, `g` or `h` it is a statement about the junk pushforward
`Measure.map`, which is `0` there; substantive theorems therefore carry explicit measurability
hypotheses. -/
def CondIndep {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure Ω) (f : Ω → α) (g : Ω → β) (h : Ω → γ) : Prop :=
  ∃ κ : Kernel γ α, ∃ η : Kernel γ β, IsMarkovKernel κ ∧ IsMarkovKernel η ∧
    μ.map (fun ω => (h ω, (f ω, g ω))) = (μ.map h) ⊗ₘ (κ ×ₖ η)

variable {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω → β} {h : Ω → γ}

/-- **(C1), symmetry** (Lauritzen p. 29; Pearl 1988 calls it *symmetry*): conditional
independence is symmetric in its two arguments. Structural — swap the kernel pair.

Route (do not re-derive): map both sides of the disintegration through `Prod.map id Prod.swap`
using `MeasureTheory.Measure.map_map` on the left and
`MeasureTheory.Measure.compProd_map measurable_swap` on the right, then
`ProbabilityTheory.Kernel.map_prod_swap` turns `(κ ×ₖ η).map Prod.swap` into `η ×ₖ κ`. -/
theorem CondIndep.symm
    -- USER-INPUT: the conditional independence to be reversed; Lauritzen §3.1 (C1)
    (hci : CondIndep μ f g h) :
    CondIndep μ g f h := by
  sorry

/-- **(C2), decomposition in functional form** (Lauritzen p. 29: `X ⫫ Y ∣ Z` and `U = φ(X)`
imply `U ⫫ Y ∣ Z`; Pearl 1988 calls it *decomposition*): measurable transformations of the two
independent arguments preserve conditional independence. Structural — push each kernel forward
through the corresponding map.

Route (do not re-derive): the witnesses are `κ.map φ` and `η.map ψ`, Markov by
`ProbabilityTheory.Kernel.IsMarkovKernel.map`; `ProbabilityTheory.Kernel.map_prod_map hφ hψ`
rewrites their product as `(κ ×ₖ η).map (Prod.map φ ψ)`, and
`MeasureTheory.Measure.compProd_map (hφ.prodMap hψ)` moves that map outside `⊗ₘ`, where it
matches the left-hand side by `MeasureTheory.Measure.map_map`. -/
theorem CondIndep.comp {α' β' : Type*} [MeasurableSpace α'] [MeasurableSpace β']
    {φ : α → α'} {ψ : β → β'}
    -- LEAN-ONLY: Lauritzen (C2) allows an arbitrary function `U = φ(X)`; measurability is
    -- what makes the pushforward kernel `κ.map φ` a kernel at all
    (hφ : Measurable φ)
    -- LEAN-ONLY: same for the second argument
    (hψ : Measurable ψ)
    -- USER-INPUT: the conditional independence to be transformed; Lauritzen §3.1 (C2)
    (hci : CondIndep μ f g h) :
    CondIndep μ (φ ∘ f) (ψ ∘ g) h := by
  sorry

/-- Conditioning on a **constant** is ordinary independence (Lauritzen §3.1: `X ⫫ Y ∣ Z` with
`Z` degenerate is `X ⫫ Y`). Forward direction, landing on Mathlib's
`ProbabilityTheory.IndepFun` — no new independence notion. The probability-measure hypothesis
is essential, not cosmetic — see the module docstring.

Route (do not re-derive): `MeasureTheory.Measure.map_const` collapses `μ.map (fun _ => c)` to
`dirac c`; pushing the disintegration through `Prod.snd` gives
`μ.map (fun ω => (f ω, g ω)) = (κ c).prod (η c)`, and pushing further through `Prod.fst` /
`Prod.snd` identifies `κ c = μ.map f` and `η c = μ.map g`; conclude with
`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`. -/
theorem CondIndep.const_right
    -- LEAN-ONLY: `IndepFun` compares `μ(A ∩ B)` with `μ(A)·μ(B)`, which is scale-sensitive;
    -- a finite measure of mass `m ∉ {0,1}` satisfies the disintegration but not `IndepFun`
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: needed to identify the marginals of the joint pushforward
    (hf : Measurable f)
    -- LEAN-ONLY: same for `g`
    (hg : Measurable g) {c : γ}
    -- USER-INPUT: conditional independence given a degenerate conditioning variable;
    -- Lauritzen §3.1
    (hci : CondIndep μ f g (fun _ => c)) :
    IndepFun f g μ := by
  sorry

/-- Converse of `CondIndep.const_right`: independence is conditional independence given a
constant, witnessed by the two constant kernels carrying the marginal laws.

Route (do not re-derive): take `κ := Kernel.const _ (μ.map f)` and `η := Kernel.const _ (μ.map g)`
(Markov by `MeasureTheory.Measure.isProbabilityMeasure_map`), unfold the independence with
`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`, and use
`MeasureTheory.Measure.map_const` on the conditioning variable. -/
theorem condIndep_const_of_indepFun
    -- LEAN-ONLY: see `CondIndep.const_right`; also makes `μ.map f` a probability measure, so
    -- that `Kernel.const _ (μ.map f)` is a Markov kernel
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: needed for `μ.map f` to be the law of `f`
    (hf : Measurable f)
    -- LEAN-ONLY: same for `g`
    (hg : Measurable g) (c : γ)
    -- USER-INPUT: unconditional independence of the two variables; Lauritzen §3.1
    (hind : IndepFun f g μ) :
    CondIndep μ f g (fun _ => c) := by
  sorry

/-- **Export bridge (ours ⇒ Mathlib's).** On a standard Borel sample space with a finite
measure and standard Borel nonempty value spaces, our disintegration predicate implies
Mathlib's `ProbabilityTheory.CondIndepFun` given the σ-algebra generated by `h`.

Route: `ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib`
states `CondIndepFun` as exactly this identity with `κ := condDistrib f h μ` and
`η := condDistrib g h μ`; essential uniqueness of disintegration identifies the anonymous
witnesses of `CondIndep` with those two kernels (marginalising the product kernel through
`Prod.fst` / `Prod.snd`). The instance burden is inherited verbatim from that lemma plus the
`StandardBorelSpace Ω`/`IsFiniteMeasure μ` burden of `CondIndepFun` itself.

**No theorem in this area depends on this bridge** (roadmap §3): it exists so that results
proved with `CondIndep` are exportable to Mathlib-facing consumers. -/
theorem condIndepFun_of_condIndep
    -- LEAN-ONLY: `ProbabilityTheory.CondIndepFun` is defined through `condExpKernel`, which
    -- requires the sample space to be standard Borel; our predicate does not
    [StandardBorelSpace Ω]
    -- LEAN-ONLY: `condExpKernel`/`condDistrib` are defined for finite measures
    [IsFiniteMeasure μ]
    -- LEAN-ONLY: `condDistrib f h μ` exists only for a standard Borel nonempty target
    [StandardBorelSpace α] [Nonempty α]
    -- LEAN-ONLY: same for the second value space
    [StandardBorelSpace β] [Nonempty β]
    -- LEAN-ONLY: measurability of the two variables, demanded by the Mathlib lemma
    (hf : Measurable f) (hg : Measurable g)
    -- LEAN-ONLY: measurability of the conditioning variable; also what makes
    -- `MeasurableSpace.comap h inferInstance` a sub-σ-algebra
    (hh : Measurable h)
    -- USER-INPUT: conditional independence in our sense; Lauritzen §3.1
    (hci : CondIndep μ f g h) :
    f ⟂ᵢ[h, hh; μ] g := by
  sorry

end StatLean.StatisticalModels.GraphicalModels
