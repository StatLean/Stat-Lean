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
  `U = φ(X), W = ψ(Y)`: push the kernels through measurable maps. **As frozen this statement is
  false** — see its docstring and the machine-checked
  `CondIndep.CompCounterexample.comp_is_false`; `CondIndep.comp_of_sfinite` is the same theorem
  with the missing `[SFinite (μ.map h)]` restored, and is proved;
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
  kernel pair, push the kernels forward. (C1) does hold in this generality; (C2) does *not*,
  because `⊗ₘ` is `0` by fiat when the conditioning law is not s-finite
  (`MeasureTheory.Measure.compProd_of_not_sfinite`), and the swap of (C1) is an involution while
  a general `φ` is not — see `CondIndep.comp`. Weak union (C3),
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

/-- Pushing a law forward through a map with a measurable left inverse commutes with `Measure.map`
**unconditionally** — no measurability of `T` is needed, because a left inverse transports the
failure of `AEMeasurable` back, so both sides are the junk `0` in that case.

LEAN-ONLY: a bookkeeping lemma, not a mathematical hypothesis; `MeasureTheory.Measure.map_map`
only applies to a.e. measurable `T`, and the frozen statements of this file carry no
measurability hypothesis on `f`, `g`, `h`. -/
private theorem map_comp_of_leftInverse {δ ε : Type*} [MeasurableSpace δ] [MeasurableSpace ε]
    {e : δ → ε} {e' : ε → δ} (he : Measurable e) (he' : Measurable e')
    (hee : Function.LeftInverse e' e) (T : Ω → δ) :
    μ.map (e ∘ T) = (μ.map T).map e := by
  by_cases hT : AEMeasurable T μ
  · exact (AEMeasurable.map_map_of_aemeasurable he.aemeasurable hT).symm
  · have hT' : ¬ AEMeasurable (e ∘ T) μ := by
      intro hc
      have hTc : (fun ω => e' (e (T ω))) = T := funext fun ω => hee (T ω)
      exact hT (hTc ▸ he'.comp_aemeasurable hc)
    rw [Measure.map_of_not_aemeasurable hT', Measure.map_of_not_aemeasurable hT, Measure.map_zero]

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
  obtain ⟨κ, η, hκ, hη, hmap⟩ := hci
  refine ⟨η, κ, hη, hκ, ?_⟩
  have he : Measurable (Prod.map (id : γ → γ) (Prod.swap : α × β → β × α)) :=
    measurable_id.prodMap measurable_swap
  have he' : Measurable (Prod.map (id : γ → γ) (Prod.swap : β × α → α × β)) :=
    measurable_id.prodMap measurable_swap
  have hcomp : (fun ω => (h ω, (g ω, f ω)))
      = (Prod.map (id : γ → γ) (Prod.swap : α × β → β × α)) ∘ (fun ω => (h ω, (f ω, g ω))) := rfl
  rw [hcomp, map_comp_of_leftInverse he he' (fun p => rfl), hmap]
  -- the swap is an involution, so no measurability of `f`, `g`, `h` is needed; the `⊗ₘ`-junk
  -- regime (`μ.map h` not s-finite) is closed off by `Measure.compProd_of_not_sfinite`
  by_cases hs : SFinite (μ.map h)
  · rw [← Kernel.map_prod_swap κ η, Measure.compProd_map measurable_swap]
  · rw [Measure.compProd_of_not_sfinite _ _ hs, Measure.compProd_of_not_sfinite _ _ hs,
      Measure.map_zero]

/-- **(C2), decomposition in functional form** (Lauritzen p. 29: `X ⫫ Y ∣ Z` and `U = φ(X)`
imply `U ⫫ Y ∣ Z`; Pearl 1988 calls it *decomposition*): measurable transformations of the two
independent arguments preserve conditional independence. Structural — push each kernel forward
through the corresponding map.

Route (do not re-derive): the witnesses are `κ.map φ` and `η.map ψ`, Markov by
`ProbabilityTheory.Kernel.IsMarkovKernel.map`; `ProbabilityTheory.Kernel.map_prod_map hφ hψ`
rewrites their product as `(κ ×ₖ η).map (Prod.map φ ψ)`, and
`MeasureTheory.Measure.compProd_map (hφ.prodMap hψ)` moves that map outside `⊗ₘ`, where it
matches the left-hand side by `MeasureTheory.Measure.map_map`.

**REFUTED AS FROZEN — this statement is FALSE; the `sorry` is deliberate.** The route above
needs `SFinite (μ.map h)`, which `MeasureTheory.Measure.compProd_map` demands and which the
statement does not supply, and the gap is not an artefact of the route: see
`CondIndep.CompCounterexample.comp_is_false`, a machine-checked derivation of `False` from this
very statement. The counterexample lives in the `⊗ₘ`-junk regime that the module docstring warns
about for `Measure.map`, and reads:

* `Pt := ℝ × Bool` carrying the σ-algebra `MeasurableSpace.comap fst' ⊤`, which sees only the
  first coordinate, and `mu := ∑ₓ dirac (x, true)`;
* `mu` is **not s-finite** (the uncountably many fibres `fst' ⁻¹' {x}` all have positive mass,
  contradicting `MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion`), so *every*
  `mu ⊗ₘ K` collapses to `0` by `MeasureTheory.Measure.compProd_of_not_sfinite`;
* `snd'` is not a.e. measurable (`mu` has no nonempty null set), so the law of
  `(id, (snd', snd'))` is the junk `0` as well: the hypothesis `CondIndep mu snd' snd' id`
  **holds**, with any pair of Markov kernels as witnesses;
* transforming by the constant `φ = ψ = (fun _ => ())` makes the triple `(id, ((), ()))`
  measurable, so its law has mass `mu Set.univ ≠ 0` — while the right-hand side is still `0`.
  The conclusion `CondIndep mu (φ ∘ snd') (ψ ∘ snd') id` therefore **fails**.

`CondIndep.comp_of_sfinite` below is the same theorem with the one missing hypothesis
`[SFinite (μ.map h)]` restored, and is fully proved; it is free at every intended instance,
since `SFinite (μ.map h)` is an instance whenever `μ` is (in particular for any probability or
σ-finite `μ`). Repairing the frozen statement is a scope decision and is left to the user. -/
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

/-- **(C2), decomposition in functional form — the repaired statement.** Identical to
`CondIndep.comp` except for the one hypothesis that makes it true; see the refutation in
`CondIndep.comp`'s docstring and `CondIndep.CompCounterexample.comp_is_false`.

No measurability of `f`, `g`, `h` is needed: when the joint map is not a.e. measurable, its law
is `0`, `MeasureTheory.Measure.fst_compProd` forces `μ.map h = 0`, and the transformed law is `0`
as well (either `μ = 0`, or `h` is not a.e. measurable and neither is the transformed triple). -/
theorem CondIndep.comp_of_sfinite {α' β' : Type*} [MeasurableSpace α'] [MeasurableSpace β']
    {φ : α → α'} {ψ : β → β'}
    -- LEAN-ONLY: the hypothesis missing from `CondIndep.comp`, which is false without it.
    -- `⊗ₘ` is *defined* to be `0` when the left measure is not s-finite
    -- (`MeasureTheory.Measure.compProd_of_not_sfinite`), so the frozen statement equates a
    -- possibly nonzero law with `0`. Free at every intended instance: `SFinite (μ.map h)` is
    -- an instance as soon as `SFinite μ` is
    [SFinite (μ.map h)]
    -- LEAN-ONLY: Lauritzen (C2) allows an arbitrary function `U = φ(X)`; measurability is
    -- what makes the pushforward kernel `κ.map φ` a kernel at all
    (hφ : Measurable φ)
    -- LEAN-ONLY: same for the second argument
    (hψ : Measurable ψ)
    -- USER-INPUT: the conditional independence to be transformed; Lauritzen §3.1 (C2)
    (hci : CondIndep μ f g h) :
    CondIndep μ (φ ∘ f) (ψ ∘ g) h := by
  obtain ⟨κ, η, hκ, hη, hmap⟩ := hci
  refine ⟨κ.map φ, η.map ψ, Kernel.IsMarkovKernel.map _ hφ, Kernel.IsMarkovKernel.map _ hψ, ?_⟩
  rw [Kernel.map_prod_map κ η hφ hψ, Measure.compProd_map (hφ.prodMap hψ), ← hmap]
  change μ.map ((Prod.map (id : γ → γ) (Prod.map φ ψ)) ∘ (fun ω => (h ω, (f ω, g ω)))) = _
  by_cases hT : AEMeasurable (fun ω => (h ω, (f ω, g ω))) μ
  · exact (AEMeasurable.map_map_of_aemeasurable
      (measurable_id.prodMap (hφ.prodMap hψ)).aemeasurable hT).symm
  · have hzero : μ.map (fun ω => (h ω, (f ω, g ω))) = 0 := Measure.map_of_not_aemeasurable hT
    rw [hzero, Measure.map_zero]
    have hfst : μ.map h = 0 := by
      have hc := Measure.fst_compProd (μ.map h) (κ ×ₖ η)
      rw [← hmap, hzero] at hc
      simpa using hc.symm
    by_cases hh : AEMeasurable h μ
    · have hμ : μ = 0 := (Measure.map_eq_zero_iff hh).1 hfst
      simp [hμ]
    · exact Measure.map_of_not_aemeasurable fun hc => hh (measurable_fst.comp_aemeasurable hc)

/-- Marginalising a `dirac`-conditioned disintegration: pushing `(dirac c) ⊗ₘ K` forward through
`Prod.snd` returns the kernel's value at `c`.

LEAN-ONLY: bookkeeping. Mathlib's `MeasureTheory.Measure.dirac_compProd_apply` is the same fact
but assumes `MeasurableSingletonClass` on the conditioning space, which the frozen statements
here do not carry; the proof below uses `lintegral_dirac'` instead, which only needs
measurability of the integrand. -/
private theorem map_snd_dirac_compProd {δ : Type*} [MeasurableSpace δ] (c : γ) (K : Kernel γ δ)
    [IsSFiniteKernel K] : ((Measure.dirac c) ⊗ₘ K).map Prod.snd = K c := by
  ext S hS
  rw [Measure.map_apply measurable_snd hS, Measure.compProd_apply (measurable_snd hS)]
  simp only [show ∀ a : γ, (Prod.mk a ⁻¹' (Prod.snd ⁻¹' S)) = S from fun _ => rfl]
  exact lintegral_dirac' _ (K.measurable_coe hS)

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
  obtain ⟨κ, η, hκ, hη, hmap⟩ := hci
  rw [Measure.map_const, measure_univ, one_smul] at hmap
  have hT : Measurable (fun ω => (c, (f ω, g ω))) := measurable_const.prodMk (hf.prodMk hg)
  have h2 : μ.map (fun ω => (f ω, g ω)) = (κ c).prod (η c) := by
    have h3 := congrArg (fun ν : Measure (γ × (α × β)) => ν.map Prod.snd) hmap
    simp only at h3
    rwa [Measure.map_map measurable_snd hT, map_snd_dirac_compProd, Kernel.prod_apply] at h3
  refine (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).2 ?_
  have hfc : μ.map f = κ c := by
    have h4 := congrArg (fun ν : Measure (α × β) => ν.map Prod.fst) h2
    simp only [Measure.map_fst_prod, measure_univ, one_smul] at h4
    rwa [Measure.map_map measurable_fst (hf.prodMk hg)] at h4
  have hgc : μ.map g = η c := by
    have h4 := congrArg (fun ν : Measure (α × β) => ν.map Prod.snd) h2
    simp only [Measure.map_snd_prod, measure_univ, one_smul] at h4
    rwa [Measure.map_map measurable_snd (hf.prodMk hg)] at h4
  rw [hfc, hgc, h2]

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
  have hpf : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hpg : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  refine ⟨Kernel.const _ (μ.map f), Kernel.const _ (μ.map g), inferInstance, inferInstance, ?_⟩
  rw [Kernel.prod_const, Measure.map_const, measure_univ, one_smul, Measure.compProd_const,
    Measure.dirac_prod, ← (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable
      hg.aemeasurable).1 hind, Measure.map_map measurable_prodMk_left (hf.prodMk hg)]
  rfl

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
  obtain ⟨κ, η, hκ, hη, hmap⟩ := hci
  have hT : Measurable (fun ω => (h ω, (f ω, g ω))) := hh.prodMk (hf.prodMk hg)
  -- marginalise the disintegration onto each of the two variables ...
  have hfst : μ.map (fun ω => (h ω, f ω)) = μ.map h ⊗ₘ κ := by
    have h3 := congrArg
      (fun ν : Measure (γ × (α × β)) => ν.map (Prod.map (id : γ → γ) (Prod.fst : α × β → α))) hmap
    simp only at h3
    rw [Measure.map_map (measurable_id.prodMap measurable_fst) hT,
      ← Measure.compProd_map measurable_fst,
      show (κ ×ₖ η).map Prod.fst = κ from (Kernel.fst_eq _).symm.trans (Kernel.fst_prod κ η)] at h3
    exact h3
  have hsnd : μ.map (fun ω => (h ω, g ω)) = μ.map h ⊗ₘ η := by
    have h3 := congrArg
      (fun ν : Measure (γ × (α × β)) => ν.map (Prod.map (id : γ → γ) (Prod.snd : α × β → β))) hmap
    simp only at h3
    rw [Measure.map_map (measurable_id.prodMap measurable_snd) hT,
      ← Measure.compProd_map measurable_snd,
      show (κ ×ₖ η).map Prod.snd = η from (Kernel.snd_eq _).symm.trans (Kernel.snd_prod κ η)] at h3
    exact h3
  -- ... and identify the anonymous witnesses with the two conditional distributions
  have h1 : condDistrib f h μ =ᵐ[μ.map h] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd h hf.aemeasurable hfst
  have h2 : condDistrib g h μ =ᵐ[μ.map h] η :=
    condDistrib_ae_eq_of_measure_eq_compProd h hg.aemeasurable hsnd
  rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hf hg hh,
    ← Measure.compProd_eq_comp_prod, hmap]
  refine Measure.compProd_congr ?_
  filter_upwards [h1, h2] with a ha1 ha2
  rw [Kernel.prod_apply, Kernel.prod_apply, ha1, ha2]

namespace CondIndep.CompCounterexample

/-! ### Refutation of `CondIndep.comp` as frozen

A machine-checked counterexample to `CondIndep.comp`, living in the `⊗ₘ`-junk regime: the
conditioning law is not s-finite, so *every* `⊗ₘ` on the right-hand side is `0`, while a constant
transformation of the two variables turns a non-a.e.-measurable triple into a measurable one and
so makes the left-hand side nonzero. See `CondIndep.comp`'s docstring for the narrative, and
`comp_is_false` for the derivation of `False` from the frozen statement. Nothing else in the
area depends on this section. -/

/-- Sample space: the plane `ℝ × Bool`. -/
def Pt : Type := ℝ × Bool

/-- A point of the sample space. -/
def pt (x : ℝ) (b : Bool) : Pt := (x, b)

/-- The first coordinate. -/
def fst' : Pt → ℝ := fun p => (Prod.fst : ℝ × Bool → ℝ) p

/-- The second coordinate. -/
def snd' : Pt → Bool := fun p => (Prod.snd : ℝ × Bool → Bool) p

@[simp] theorem fst'_pt (x : ℝ) (b : Bool) : fst' (pt x b) = x := rfl

@[simp] theorem snd'_pt (x : ℝ) (b : Bool) : snd' (pt x b) = b := rfl

/-- The σ-algebra sees only the first coordinate. -/
instance : MeasurableSpace Pt := MeasurableSpace.comap fst' ⊤

/-- The measurable sets are exactly the first-coordinate preimages. -/
theorem measurableSet_iff {s : Set Pt} :
    MeasurableSet s ↔ ∃ t : Set ℝ, fst' ⁻¹' t = s := by
  constructor
  · rintro ⟨t, -, rfl⟩; exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩; exact ⟨t, trivial, rfl⟩

/-- One unit of mass on each point `(x, true)`. -/
noncomputable def mu : Measure Pt :=
  Measure.sum fun x : ℝ => Measure.dirac (pt x true)

/-- Every nonempty measurable set has positive mass: being a first-coordinate preimage, it
contains a point of the form `(x, true)`. In particular `mu` has no nonempty null set. -/
theorem mu_ne_zero {s : Set Pt} (hs : MeasurableSet s) (hne : s.Nonempty) : mu s ≠ 0 := by
  obtain ⟨t, rfl⟩ := measurableSet_iff.1 hs
  obtain ⟨p, hp⟩ := hne
  have h1 := Measure.le_sum (fun x : ℝ => Measure.dirac (pt x true)) (fst' p) (fst' ⁻¹' t)
  rw [Measure.dirac_apply' _ hs,
    Set.indicator_of_mem (show pt (fst' p) true ∈ fst' ⁻¹' t from hp)] at h1
  intro h0
  rw [show (Measure.sum fun x : ℝ => Measure.dirac (pt x true)) = mu from rfl, h0] at h1
  simp at h1

theorem mu_ne_zero' : mu ≠ 0 := fun h =>
  mu_ne_zero MeasurableSet.univ ⟨pt 0 true, trivial⟩ (by rw [h]; rfl)

/-- `mu` is **not s-finite**: the uncountably many fibres all carry positive mass, which
`MeasureTheory.Measure.countable_meas_pos_of_disjoint_iUnion` forbids for an s-finite measure. -/
theorem not_sfinite_mu : ¬ SFinite mu := by
  intro hs
  have hmble : ∀ x : ℝ, MeasurableSet (fst' ⁻¹' {x}) := fun x => measurableSet_iff.2 ⟨{x}, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint (fun x : ℝ => fst' ⁻¹' {x})) := by
    intro x y hxy
    simp only [Function.onFun, Set.disjoint_left, Set.mem_preimage, Set.mem_singleton_iff]
    intro p h1 h2
    exact hxy (h1.symm.trans h2)
  have hcount := Measure.countable_meas_pos_of_disjoint_iUnion (μ := mu) hmble hdisj
  have huniv : {x : ℝ | 0 < mu (fst' ⁻¹' {x})} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, pos_iff_ne_zero]
    exact mu_ne_zero (hmble x) ⟨pt x true, rfl⟩
  rw [huniv] at hcount
  exact (not_countable_iff.2 inferInstance) (Set.countable_univ_iff.1 hcount)

/-- `mu` has no nonempty null set, so a.e. measurability is measurability outright. -/
theorem measurable_of_aemeasurable {δ : Type*} [MeasurableSpace δ] {F : Pt → δ}
    (h : AEMeasurable F mu) : Measurable F := by
  obtain ⟨g, hg, hae⟩ := h
  have hnull : mu {p : Pt | F p ≠ g p} = 0 := ae_iff.1 hae
  have hempty : {p : Pt | F p ≠ g p} = ∅ := by
    by_contra hne
    exact mu_ne_zero (measurableSet_toMeasurable mu {p : Pt | F p ≠ g p})
      ((Set.nonempty_iff_ne_empty.2 hne).mono (subset_toMeasurable mu _))
      (by rw [measure_toMeasurable]; exact hnull)
  have : F = g := funext fun p => not_not.1 fun hp => (Set.eq_empty_iff_forall_notMem.1 hempty p) hp
  exact this ▸ hg

/-- The half-plane `{snd' = true}` is **not** measurable: it is not a first-coordinate
preimage. This is the single source of non-measurability in the counterexample. -/
theorem not_measurableSet_snd'_true : ¬ MeasurableSet (snd' ⁻¹' {true}) := by
  intro hm
  obtain ⟨t, ht⟩ := measurableSet_iff.1 hm
  have h1 : pt 0 true ∈ fst' ⁻¹' t := by rw [ht]; rfl
  have h2 : pt 0 false ∈ fst' ⁻¹' t := h1
  rw [ht] at h2
  exact Bool.noConfusion h2

/-- The second coordinate is not measurable, and — `mu` having no nonempty null set — not even
a.e. measurable. -/
theorem not_aemeasurable_snd' : ¬ AEMeasurable snd' mu := fun h =>
  not_measurableSet_snd'_true (measurable_of_aemeasurable h (measurableSet_singleton true))

/-- The frozen (C2) **hypothesis** holds here: the law of the triple is the junk `0` (the triple
is not a.e. measurable), and so is the right-hand side (`mu` is not s-finite). -/
theorem condIndep_snd' : CondIndep mu snd' snd' id := by
  refine ⟨Kernel.const _ (Measure.dirac true), Kernel.const _ (Measure.dirac true),
    inferInstance, inferInstance, ?_⟩
  rw [Measure.map_id, Measure.compProd_of_not_sfinite _ _ not_sfinite_mu]
  refine Measure.map_of_not_aemeasurable ?_
  intro hc
  exact not_aemeasurable_snd'
    (measurable_fst.comp_aemeasurable (measurable_snd.comp_aemeasurable hc))

/-- But the (C2) **conclusion** fails after the constant transformation `_ ↦ ()`: the triple is
now measurable, so its law has mass `mu Set.univ ≠ 0`, while the right-hand side is still `0`. -/
theorem not_condIndep_comp_snd' :
    ¬ CondIndep mu ((fun _ : Bool => ()) ∘ snd') ((fun _ : Bool => ()) ∘ snd') id := by
  rintro ⟨κ, η, -, -, hmap⟩
  have hm : Measurable (fun ω : Pt =>
      (id ω, (((fun _ : Bool => ()) ∘ snd') ω, ((fun _ : Bool => ()) ∘ snd') ω))) :=
    measurable_id.prodMk (measurable_const.prodMk measurable_const)
  rw [Measure.map_id, Measure.compProd_of_not_sfinite _ _ not_sfinite_mu,
    Measure.map_eq_zero_iff hm.aemeasurable] at hmap
  exact mu_ne_zero' hmap

/-- **`CondIndep.comp` is false as frozen**: its statement, taken as a hypothesis, yields `False`.
The missing hypothesis is `SFinite (μ.map h)`; with it the theorem is true, and proved, as
`CondIndep.comp_of_sfinite`. -/
theorem comp_is_false
    (comp : ∀ {Ω α β γ : Type} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω → β} {h : Ω → γ}
      {α' β' : Type} [MeasurableSpace α'] [MeasurableSpace β'] {φ : α → α'} {ψ : β → β'},
      Measurable φ → Measurable ψ → CondIndep μ f g h → CondIndep μ (φ ∘ f) (ψ ∘ g) h) :
    False :=
  not_condIndep_comp_snd' (comp measurable_const measurable_const condIndep_snd')

end CondIndep.CompCounterexample

end StatLean.StatisticalModels.GraphicalModels
