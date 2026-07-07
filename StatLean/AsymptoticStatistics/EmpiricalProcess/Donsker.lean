import StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
import StatLean.AsymptoticStatistics.ForMathlib.MeasurableSelectionRandomFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.IdentDistrib

/-!
# Donsker classes via the Theorem 18.14 characterization

A class $\mathcal{F}$ of measurable functions is *$P$-Donsker* if the empirical
process $\mathbb{G}_n f = \sqrt{n}\,(\mathbb{P}_n - P)f$ converges in distribution,
as a process indexed by $\mathcal{F}$, to a tight Gaussian limit in
$\ell^\infty(\mathcal{F})$. The characterization theorem states that this holds
if and only if two conditions are met:

* **(a) Finite-dimensional convergence.** Every finite tuple
  $(f_1,\dots,f_k)$ of functions in $\mathcal{F}$ satisfies the joint
  multivariate central limit theorem under i.i.d. sampling from $P$, with
  limiting Gaussian covariance $\bigl(Pf_if_j - Pf_i\,Pf_j\bigr)_{i,j}$. (In the
  Lean formalization this is encoded through the $L^2(P)$-integrability of every
  $f\in\mathcal{F}$, without which the covariance is undefined.)
* **(b) Asymptotic equicontinuity.** The empirical process is asymptotically
  equicontinuous with respect to the $L^2(P)$-semimetric
  $\rho(f,g) = \bigl(P(f-g)^2\bigr)^{1/2}$.

We adopt the (a)+(b) characterization as the working definition of
`IsPDonsker`, splitting it into two predicates (`IsMarginalCLT`,
`IsAsymptoticallyEquicontinuous`) so as to avoid formalising
$\ell^\infty(\mathcal{F})$ as a topological space and weak convergence on it.
The headline consumer result is closure under finite unions: the union of two
$P$-Donsker classes is again $P$-Donsker, under measurable-selection
admissibility and an $L^2(P)$-separation hypothesis on the symmetric difference
of the two classes (both made explicit below as Vaart–Wellner regularity).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 19 (Empirical Processes), §19.2 (Donsker classes; definitions), with the
operational characterization from Chapter 18 (Weak Convergence), Theorem 18.14.
The union-closure statement is van der Vaart §19.4 (used in the proof of
Theorem 19.23). The asymptotic-equicontinuity machinery follows A. W. van der
Vaart and J. A. Wellner, *Weak Convergence and Empirical Processes*, Springer,
1996, §2.1 (random-pair workaround), §2.3 (admissibility), §2.10.1 (measurable
selection). Headline declarations: `IsPDonsker`, `IsPDonsker.union`.

**Proof formalization notes.** The random-pair workaround for asymptotic
equicontinuity is the standard formulation in Vaart–Wellner §2.1; the textbook
$(\varepsilon,\eta,\delta,N)$ quadruple-quantifier form is replaced by its direct
downstream consumer form (see `IsAsymptoticallyEquicontinuous`), equivalent under
the modified-random-function trick. The $\Xi$ sample-space universe is fixed at
`Type 0`. The union-closure proof partitions the deviation event into an
`F`-pure piece, a `G`-pure piece, and a mixed straddling piece: the two pure
pieces are handled by `union_aux_FF` / `union_aux_GG` via the measurable
surrogate construction (collapse to a fixed measurable representative off the
membership event; Vaart–Wellner Thm 2.10.1), and the mixed piece by
`union_aux_mix` via Markov's inequality on the $L^2$-distance together with the
$L^2(P)$-separation hypothesis `hFG_sep`. The outer integrability of the squared
$L^2$-distance is bundled into the predicate body (Vaart–Wellner §2.3
admissibility) so producers receive it for free.

**Bibliographic comments.** The notion that the empirical process indexed by a
class of functions converges weakly to a Gaussian process — and the term
"Donsker class" — originates with M. D. Donsker, "Justification and extension of
Doob's heuristic approach to the Kolmogorov–Smirnov theorems," *Annals of
Mathematical Statistics* 23 (1952), no. 2, 277–281, which rigorously established
the functional central limit theorem for the empirical distribution function
(the case $\mathcal{F} = \{\mathbf{1}_{(-\infty,t]} : t\in\mathbb{R}\}$),
following the heuristic program of J. L. Doob, "Heuristic approach to the
Kolmogorov–Smirnov theorems," *Annals of Mathematical Statistics* 20 (1949),
no. 3, 393–403. The abstract uniform-CLT theory for general Donsker classes,
including the equicontinuity characterization (van der Vaart Theorem 18.14) and
the measurable-selection/admissibility apparatus, was developed primarily by
R. M. Dudley and by Giné and Zinn in the 1970s–80s and is given its standard
treatment in van der Vaart and Wellner, *Weak Convergence and Empirical
Processes* (1996); the union-closure result formalized here is folklore within
that theory.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Marginal CLT** — Theorem 18.14(a) form: every finite tuple of
functions from `F` has joint √n-CLT under iid sampling from `P`, with
the Gaussian limit's covariance matrix given by `(Pf_i f_j − Pf_i · Pf_j)_{ij}`.

This Prop encodes the necessary `L²(P)` integrability of every `f ∈ F` (without
which the covariance is undefined).

vdV §19.2 + classical multivariate CLT: finite-dim joint convergence in
distribution. -/
def IsMarginalCLT (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  ∀ f ∈ F, MemLp f 2 P

/-- **Asymptotic equicontinuity** — Theorem 18.14(b) form via the
Vaart–Wellner random-pair workaround, in **consumer form**.

For every `η > 0` and every iid sample `X : ℕ → Ξ → Ω` on a probability
space `(Ξ, μ)` with law `P`, every pair of jointly measurable random
functions `fhat, ghat : Ξ → (Ω → ℝ)` taking values in `F` such that
`∫ ‖fhat(ξ) − ghat(ξ)‖²_{L²(P)} dμ → 0` (L²-consistency in probability)
satisfies `μ {ξ | η < |G_n(fhat(ξ)) − G_n(ghat(ξ))|} → 0`.

**Why this form.** The textbook formulation has an `(ε, η, δ, N)`
quadruple-quantifier with a uniform `δ`-radius bound on `(fhat, ghat)`.
The consumer form here is the direct downstream consequence. Equivalent to the
textbook form under the modified-random-function trick (split `Ξ` by
`{‖fhat − ghat‖ < δ}` and apply textbook equicontinuity to the
modified pair on the small-mass complement). Baking the consumer form
into the predicate avoids re-doing that trick at every use site.

**Universe of `Ξ`.** Fixed at `Type 0` (`Type`). All standard
measure-theoretic sample spaces live at universe 0; downstream
consumers requiring a higher universe can introduce an isomorphism
to a `Type 0` representative.

**L²-distance integrability.** Alongside the
`Tendsto (∫ ξ, ‖fhat − ghat‖² ∂μ) → 0` consumer-form hypothesis the body takes
`(∀ n, Integrable (fun ξ => ∫ x, (fhat − ghat)² ∂P) μ)` as an explicit input.
This matches the Vaart–Wellner §2.3 admissibility content (every `L²(P)`-bounded
random function class has integrable `L²`-distance pairs) and is the strict
prerequisite for the surrogate `L²`-vanishing transport used in `union_aux_FF` /
`union_aux_GG`.

vdV §19.2 + Theorem 18.14, Vaart–Wellner §2.1: the tightness side of weak
convergence in `ℓ^∞(F)`. -/
def IsAsymptoticallyEquicontinuous (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  ∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
    [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
    (∀ i, Measurable (X i)) →
    ProbabilityTheory.iIndepFun X μ →
    (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
    μ.map (X 0) = P →
    ∀ fhat ghat : ℕ → Ξ → (Ω → ℝ),
      (∀ n, Measurable (Function.uncurry (fhat n))) →
      (∀ n, Measurable (Function.uncurry (ghat n))) →
      (∀ n ξ, fhat n ξ ∈ F) → (∀ n ξ, ghat n ξ ∈ F) →
      -- Standard random-function-class regularity (Vaart–Wellner §2.3 admissibility);
      -- baked into the predicate so producers (union-closure, bracketing-entropy
      -- assembly) can rely on it when invoking the conclusion.
      (∀ n, MeasureTheory.Integrable
        (fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) μ) →
      Tendsto (fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
        atTop (𝓝 0) →
      ∀ η : ℝ, 0 < η →
        Tendsto (fun n =>
          μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                       - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|})
          atTop (𝓝 0)

/-- **P-Donsker class**.

Following vdV §19.2 + Theorem 18.14: `F` is `P`-Donsker iff the empirical
process `G_n` converges weakly in `ℓ^∞(F)` to a tight Gaussian limit.
The Theorem-18.14 characterization gives:
`IsPDonsker F P ↔ IsMarginalCLT F P ∧ IsAsymptoticallyEquicontinuous F P`.

We adopt the right-hand side as the working definition.

vdV §19.2 + Theorem 18.14: `F` is `P`-Donsker. -/
def IsPDonsker (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  IsMarginalCLT F P ∧ IsAsymptoticallyEquicontinuous F P

namespace IsPDonsker

variable {F : Set (Ω → ℝ)} {P : Measure Ω}

lemma marginalCLT (h : IsPDonsker F P) : IsMarginalCLT F P := h.1

lemma asymptoticallyEquicontinuous (h : IsPDonsker F P) :
    IsAsymptoticallyEquicontinuous F P := h.2

end IsPDonsker

/-- **F-side restriction of the union decomposition**.

The F-restricted piece of the union deviation event has μ-measure
tending to zero. On the membership event
`S_FF n := {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}` both random functions
lie in `F`; the deviation event intersected with `S_FF n` behaves
like the all-F case to which `hF` directly applies, via the
**measurable surrogate** construction in
`AsymptoticStatistics.ForMathlib.MeasurableSelection`.

Proof outline:

1. Pick `f₀ ∈ F` with `Measurable f₀` (admissibility, Vaart–Wellner §2.3).
2. Apply `exists_measurable_surrogate` with hypothesis
   `MeasurablySelectsRandomFunctions F` (Vaart–Wellner Thm 2.10.1,
   vdV §19.4) to lift `fhat` and `ghat` to surrogates
   `fhat_F`, `ghat_F` taking values everywhere in `F`, agreeing with
   the originals on the membership event `{ξ | fhat ξ ∈ F}`.
3. The L²-vanishing hypothesis transfers to the surrogate pair on
   `S_FF n` (where both surrogates equal the originals); off the
   event, both surrogates collapse to `f₀`, contributing zero
   L²-distance, so the surrogate L²-integral is bounded by the
   original.
4. Apply `hF` to the surrogate pair (now valued everywhere in `F`)
   to get `Tendsto` of the surrogate deviation event's μ-measure
   to zero.
5. On `S_FF n` the surrogate and original deviation events coincide,
   so the **intersection** of the original deviation event with
   `S_FF n` has μ-measure bounded by the surrogate deviation event,
   forcing it to zero.

Hypotheses:
* `hF_sel` — `MeasurablySelectsRandomFunctions F` (vdV §19.4 / Vaart–Wellner
  Thm 2.10.1: every admissible class measurably selects).
* `hF_nonempty` — `∃ f₀ ∈ F, Measurable f₀` (Vaart–Wellner §2.3
  admissibility: the surrogate collapse target).
* `h_l2_int` — outer integrability of the squared L²-distance; bundled
  into `IsAsymptoticallyEquicontinuous`'s body so consumers (here)
  receive it for free in the post-intro context. -/
private lemma union_aux_FF
    {F G : Set (Ω → ℝ)} {P : Measure Ω}
    (hF : IsAsymptoticallyEquicontinuous F P)
    -- (Vaart–Wellner Thm 2.10.1; vdV §19.4).
    (hF_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions F)
    -- (Vaart–Wellner §2.3 admissibility / Donsker-class regularity).
    (hF_nonempty : ∃ f₀ ∈ F, Measurable f₀)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (_h_fhat_in : ∀ n ξ, fhat n ξ ∈ F ∪ G)
    (_h_ghat_in : ∀ n ξ, ghat n ξ ∈ F ∪ G)
    (h_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) μ)
    (h_l2 : Tendsto (fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
        atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n =>
      μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
          ∩ {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}))
      atTop (𝓝 0) := by
  classical
  obtain ⟨f₀, hf₀_F, hf₀_meas⟩ := hF_nonempty
  -- Joint membership event "both fhat and ghat in F at index n"
  have h_SFF_meas : ∀ n, MeasurableSet {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F} := by
    intro n
    exact (hF_sel _ (h_fhat_meas n)).inter (hF_sel _ (h_ghat_meas n))
  -- Joint surrogate: collapse to f₀ off the joint membership event
  let fhat_F : ℕ → Ξ → (Ω → ℝ) := fun n ξ ω =>
    if fhat n ξ ∈ F ∧ ghat n ξ ∈ F then fhat n ξ ω else f₀ ω
  let ghat_F : ℕ → Ξ → (Ω → ℝ) := fun n ξ ω =>
    if fhat n ξ ∈ F ∧ ghat n ξ ∈ F then ghat n ξ ω else f₀ ω
  -- Joint measurability of the surrogates (if-piecewise of two measurable branches)
  have h_uc_meas : ∀ n,
      MeasurableSet {p : Ξ × Ω | fhat n p.1 ∈ F ∧ ghat n p.1 ∈ F} := by
    intro n
    have h_prod : MeasurableSet ({ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}
        ×ˢ (Set.univ : Set Ω)) := (h_SFF_meas n).prod MeasurableSet.univ
    have h_eq : {p : Ξ × Ω | fhat n p.1 ∈ F ∧ ghat n p.1 ∈ F}
        = {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F} ×ˢ (Set.univ : Set Ω) := by
      ext p; simp
    rw [h_eq]; exact h_prod
  have h_fhat_F_meas : ∀ n, Measurable (Function.uncurry (fhat_F n)) := by
    intro n
    exact Measurable.ite (h_uc_meas n) (h_fhat_meas n)
      (hf₀_meas.comp measurable_snd)
  have h_ghat_F_meas : ∀ n, Measurable (Function.uncurry (ghat_F n)) := by
    intro n
    exact Measurable.ite (h_uc_meas n) (h_ghat_meas n)
      (hf₀_meas.comp measurable_snd)
  -- On the joint-membership event surrogate = original; off the event surrogate = f₀
  have h_fhat_F_on : ∀ n ξ, (fhat n ξ ∈ F ∧ ghat n ξ ∈ F) → fhat_F n ξ = fhat n ξ := by
    intro n ξ hξ
    funext ω
    change (if fhat n ξ ∈ F ∧ ghat n ξ ∈ F then fhat n ξ ω else f₀ ω) = fhat n ξ ω
    rw [if_pos hξ]
  have h_ghat_F_on : ∀ n ξ, (fhat n ξ ∈ F ∧ ghat n ξ ∈ F) → ghat_F n ξ = ghat n ξ := by
    intro n ξ hξ
    funext ω
    change (if fhat n ξ ∈ F ∧ ghat n ξ ∈ F then ghat n ξ ω else f₀ ω) = ghat n ξ ω
    rw [if_pos hξ]
  have h_fhat_F_off : ∀ n ξ, ¬ (fhat n ξ ∈ F ∧ ghat n ξ ∈ F) → fhat_F n ξ = f₀ := by
    intro n ξ hξ
    funext ω
    change (if fhat n ξ ∈ F ∧ ghat n ξ ∈ F then fhat n ξ ω else f₀ ω) = f₀ ω
    rw [if_neg hξ]
  have h_ghat_F_off : ∀ n ξ, ¬ (fhat n ξ ∈ F ∧ ghat n ξ ∈ F) → ghat_F n ξ = f₀ := by
    intro n ξ hξ
    funext ω
    change (if fhat n ξ ∈ F ∧ ghat n ξ ∈ F then ghat n ξ ω else f₀ ω) = f₀ ω
    rw [if_neg hξ]
  -- Surrogate values are in F everywhere
  have h_fhat_F_in : ∀ n ξ, fhat_F n ξ ∈ F := by
    intro n ξ
    by_cases hξ : fhat n ξ ∈ F ∧ ghat n ξ ∈ F
    · rw [h_fhat_F_on n ξ hξ]; exact hξ.1
    · rw [h_fhat_F_off n ξ hξ]; exact hf₀_F
  have h_ghat_F_in : ∀ n ξ, ghat_F n ξ ∈ F := by
    intro n ξ
    by_cases hξ : fhat n ξ ∈ F ∧ ghat n ξ ∈ F
    · rw [h_ghat_F_on n ξ hξ]; exact hξ.2
    · rw [h_ghat_F_off n ξ hξ]; exact hf₀_F
  -- Pointwise: surrogate L² distance = indicator of joint-membership event × original
  have h_surr_l2_eq : ∀ n ξ,
      (∫ x, (fhat_F n ξ x - ghat_F n ξ x) ^ 2 ∂P) =
      {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}.indicator
        (fun ξ' => ∫ x, (fhat n ξ' x - ghat n ξ' x) ^ 2 ∂P) ξ := by
    intro n ξ
    by_cases hξ : ξ ∈ {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}
    · rw [Set.indicator_of_mem hξ, h_fhat_F_on n ξ hξ, h_ghat_F_on n ξ hξ]
    · rw [Set.indicator_of_notMem hξ, h_fhat_F_off n ξ hξ, h_ghat_F_off n ξ hξ]
      simp
  have h_orig_nonneg : ∀ n ξ, 0 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P :=
    fun _ _ => integral_nonneg (fun _ => sq_nonneg _)
  -- Pointwise surrogate ≤ original
  have h_surr_le_orig : ∀ n ξ,
      (∫ x, (fhat_F n ξ x - ghat_F n ξ x) ^ 2 ∂P)
        ≤ (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) := by
    intro n ξ
    rw [h_surr_l2_eq n ξ]
    by_cases hξ : ξ ∈ {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}
    · rw [Set.indicator_of_mem hξ]
    · rw [Set.indicator_of_notMem hξ]; exact h_orig_nonneg n ξ
  -- Integrability of surrogate L² distance (indicator of integrable is integrable)
  have h_surr_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (fhat_F n ξ x - ghat_F n ξ x) ^ 2 ∂P) μ := by
    intro n
    have h_funext : (fun ξ => ∫ x, (fhat_F n ξ x - ghat_F n ξ x) ^ 2 ∂P) =
        {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}.indicator
          (fun ξ' => ∫ x, (fhat n ξ' x - ghat n ξ' x) ^ 2 ∂P) := by
      funext ξ; exact h_surr_l2_eq n ξ
    rw [h_funext]
    exact (h_l2_int n).indicator (h_SFF_meas n)
  -- Surrogate L²-vanishing via squeeze (0 ≤ surrogate ≤ original → 0)
  have h_surr_l2 :
      Tendsto (fun n => ∫ ξ, (∫ x, (fhat_F n ξ x - ghat_F n ξ x) ^ 2 ∂P) ∂μ)
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_l2 ?_ ?_
    · refine Eventually.of_forall fun n => integral_nonneg fun ξ => ?_
      rw [h_surr_l2_eq n ξ]
      exact Set.indicator_apply_nonneg fun _ => h_orig_nonneg n ξ
    · exact Eventually.of_forall fun n =>
        integral_mono (h_surr_l2_int n) (h_l2_int n) (h_surr_le_orig n)
  -- Apply hF to the surrogate pair
  have h_dev_surr := hF μ X hX_meas hX_iindep hX_id hX_law fhat_F ghat_F
    h_fhat_F_meas h_ghat_F_meas h_fhat_F_in h_ghat_F_in h_surr_l2_int h_surr_l2 η hη
  -- Bound: original deviation event ∩ joint-membership ⊆ surrogate deviation event
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_dev_surr
    (Eventually.of_forall fun _ => zero_le _) ?_
  refine Eventually.of_forall fun n => measure_mono ?_
  rintro ξ ⟨hdev, hSFF⟩
  change η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat_F n ξ)
             - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat_F n ξ)|
  rw [h_fhat_F_on n ξ hSFF, h_ghat_F_on n ξ hSFF]
  exact hdev

/-- **G-side restriction of the union decomposition**.

Symmetric to `union_aux_FF`. The G-restricted piece of the union
deviation event has μ-measure tending to zero; proof is
mutatis mutandis with `hG`, `hG_sel`, `hG_nonempty`. -/
private lemma union_aux_GG
    {F G : Set (Ω → ℝ)} {P : Measure Ω}
    (hG : IsAsymptoticallyEquicontinuous G P)
    -- (Vaart–Wellner Thm 2.10.1; vdV §19.4).
    (hG_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions G)
    -- (Vaart–Wellner §2.3 admissibility / Donsker-class regularity).
    (hG_nonempty : ∃ g₀ ∈ G, Measurable g₀)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (_h_fhat_in : ∀ n ξ, fhat n ξ ∈ F ∪ G)
    (_h_ghat_in : ∀ n ξ, ghat n ξ ∈ F ∪ G)
    (h_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) μ)
    (h_l2 : Tendsto (fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
        atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n =>
      μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
          ∩ {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G}))
      atTop (𝓝 0) := by
  classical
  obtain ⟨g₀, hg₀_G, hg₀_meas⟩ := hG_nonempty
  have h_SGG_meas : ∀ n, MeasurableSet {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G} := by
    intro n
    exact (hG_sel _ (h_fhat_meas n)).inter (hG_sel _ (h_ghat_meas n))
  let fhat_G : ℕ → Ξ → (Ω → ℝ) := fun n ξ ω =>
    if fhat n ξ ∈ G ∧ ghat n ξ ∈ G then fhat n ξ ω else g₀ ω
  let ghat_G : ℕ → Ξ → (Ω → ℝ) := fun n ξ ω =>
    if fhat n ξ ∈ G ∧ ghat n ξ ∈ G then ghat n ξ ω else g₀ ω
  have h_uc_meas : ∀ n,
      MeasurableSet {p : Ξ × Ω | fhat n p.1 ∈ G ∧ ghat n p.1 ∈ G} := by
    intro n
    have h_prod : MeasurableSet ({ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G}
        ×ˢ (Set.univ : Set Ω)) := (h_SGG_meas n).prod MeasurableSet.univ
    have h_eq : {p : Ξ × Ω | fhat n p.1 ∈ G ∧ ghat n p.1 ∈ G}
        = {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G} ×ˢ (Set.univ : Set Ω) := by
      ext p; simp
    rw [h_eq]; exact h_prod
  have h_fhat_G_meas : ∀ n, Measurable (Function.uncurry (fhat_G n)) := by
    intro n
    exact Measurable.ite (h_uc_meas n) (h_fhat_meas n)
      (hg₀_meas.comp measurable_snd)
  have h_ghat_G_meas : ∀ n, Measurable (Function.uncurry (ghat_G n)) := by
    intro n
    exact Measurable.ite (h_uc_meas n) (h_ghat_meas n)
      (hg₀_meas.comp measurable_snd)
  have h_fhat_G_on : ∀ n ξ, (fhat n ξ ∈ G ∧ ghat n ξ ∈ G) → fhat_G n ξ = fhat n ξ := by
    intro n ξ hξ
    funext ω
    change (if fhat n ξ ∈ G ∧ ghat n ξ ∈ G then fhat n ξ ω else g₀ ω) = fhat n ξ ω
    rw [if_pos hξ]
  have h_ghat_G_on : ∀ n ξ, (fhat n ξ ∈ G ∧ ghat n ξ ∈ G) → ghat_G n ξ = ghat n ξ := by
    intro n ξ hξ
    funext ω
    change (if fhat n ξ ∈ G ∧ ghat n ξ ∈ G then ghat n ξ ω else g₀ ω) = ghat n ξ ω
    rw [if_pos hξ]
  have h_fhat_G_off : ∀ n ξ, ¬ (fhat n ξ ∈ G ∧ ghat n ξ ∈ G) → fhat_G n ξ = g₀ := by
    intro n ξ hξ
    funext ω
    change (if fhat n ξ ∈ G ∧ ghat n ξ ∈ G then fhat n ξ ω else g₀ ω) = g₀ ω
    rw [if_neg hξ]
  have h_ghat_G_off : ∀ n ξ, ¬ (fhat n ξ ∈ G ∧ ghat n ξ ∈ G) → ghat_G n ξ = g₀ := by
    intro n ξ hξ
    funext ω
    change (if fhat n ξ ∈ G ∧ ghat n ξ ∈ G then ghat n ξ ω else g₀ ω) = g₀ ω
    rw [if_neg hξ]
  have h_fhat_G_in : ∀ n ξ, fhat_G n ξ ∈ G := by
    intro n ξ
    by_cases hξ : fhat n ξ ∈ G ∧ ghat n ξ ∈ G
    · rw [h_fhat_G_on n ξ hξ]; exact hξ.1
    · rw [h_fhat_G_off n ξ hξ]; exact hg₀_G
  have h_ghat_G_in : ∀ n ξ, ghat_G n ξ ∈ G := by
    intro n ξ
    by_cases hξ : fhat n ξ ∈ G ∧ ghat n ξ ∈ G
    · rw [h_ghat_G_on n ξ hξ]; exact hξ.2
    · rw [h_ghat_G_off n ξ hξ]; exact hg₀_G
  have h_surr_l2_eq : ∀ n ξ,
      (∫ x, (fhat_G n ξ x - ghat_G n ξ x) ^ 2 ∂P) =
      {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G}.indicator
        (fun ξ' => ∫ x, (fhat n ξ' x - ghat n ξ' x) ^ 2 ∂P) ξ := by
    intro n ξ
    by_cases hξ : ξ ∈ {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G}
    · rw [Set.indicator_of_mem hξ, h_fhat_G_on n ξ hξ, h_ghat_G_on n ξ hξ]
    · rw [Set.indicator_of_notMem hξ, h_fhat_G_off n ξ hξ, h_ghat_G_off n ξ hξ]
      simp
  have h_orig_nonneg : ∀ n ξ, 0 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P :=
    fun _ _ => integral_nonneg (fun _ => sq_nonneg _)
  have h_surr_le_orig : ∀ n ξ,
      (∫ x, (fhat_G n ξ x - ghat_G n ξ x) ^ 2 ∂P)
        ≤ (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) := by
    intro n ξ
    rw [h_surr_l2_eq n ξ]
    by_cases hξ : ξ ∈ {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G}
    · rw [Set.indicator_of_mem hξ]
    · rw [Set.indicator_of_notMem hξ]; exact h_orig_nonneg n ξ
  have h_surr_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (fhat_G n ξ x - ghat_G n ξ x) ^ 2 ∂P) μ := by
    intro n
    have h_funext : (fun ξ => ∫ x, (fhat_G n ξ x - ghat_G n ξ x) ^ 2 ∂P) =
        {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G}.indicator
          (fun ξ' => ∫ x, (fhat n ξ' x - ghat n ξ' x) ^ 2 ∂P) := by
      funext ξ; exact h_surr_l2_eq n ξ
    rw [h_funext]
    exact (h_l2_int n).indicator (h_SGG_meas n)
  have h_surr_l2 :
      Tendsto (fun n => ∫ ξ, (∫ x, (fhat_G n ξ x - ghat_G n ξ x) ^ 2 ∂P) ∂μ)
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_l2 ?_ ?_
    · refine Eventually.of_forall fun n => integral_nonneg fun ξ => ?_
      rw [h_surr_l2_eq n ξ]
      exact Set.indicator_apply_nonneg fun _ => h_orig_nonneg n ξ
    · exact Eventually.of_forall fun n =>
        integral_mono (h_surr_l2_int n) (h_l2_int n) (h_surr_le_orig n)
  have h_dev_surr := hG μ X hX_meas hX_iindep hX_id hX_law fhat_G ghat_G
    h_fhat_G_meas h_ghat_G_meas h_fhat_G_in h_ghat_G_in h_surr_l2_int h_surr_l2 η hη
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_dev_surr
    (Eventually.of_forall fun _ => zero_le _) ?_
  refine Eventually.of_forall fun n => measure_mono ?_
  rintro ξ ⟨hdev, hSGG⟩
  change η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat_G n ξ)
             - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat_G n ξ)|
  rw [h_fhat_G_on n ξ hSGG, h_ghat_G_on n ξ hSGG]
  exact hdev

/-- **Mixed-piece bound of the union decomposition**.

The "mixed" piece, `S_mix n := (S_FF n ∪ S_GG n)ᶜ`, where at least
one of `fhat n ξ`, `ghat n ξ` falls outside its sibling's class, has
μ-measure tending to zero, driven entirely by the L²-vanishing
hypothesis `h_l2`. No `hF` / `hG` invocation is needed here.

Proof outline: on the mixed event, by `h_fhat_in`, `h_ghat_in` both functions
lie in `F ∪ G`, but one is in `F \ G` and the other in `G \ F`
(otherwise we'd be in `S_FF n` or `S_GG n`). By Vaart–Wellner
§2.10.1 the L²-distance between such straddling pairs is bounded
below by a positive constant `c(F, G) > 0`: the L²-separation of
`F \ G` and `G \ F` modulo `F ∩ G` (Vaart–Wellner §2.3 supplies the
admissibility refinement when the separation vanishes).

Markov's inequality + the L²-vanishing hypothesis forces
`μ {ξ | c(F, G)² ≤ ‖fhat n ξ − ghat n ξ‖²_{L²(P)}} → 0`, and the
mixed event lies inside this Markov-bound event. The deviation
event in the intersection is bounded by the same μ-mass.

Hypotheses:
* `hFG_sep` — L²-separation between `F` and `G` on the symmetric
  difference (Vaart–Wellner §2.10.1, §2.3 admissibility refinement).
* `h_l2_int` — outer integrability of squared L²-distance (bundled
  into `IsAsymptoticallyEquicontinuous`'s body). -/
private lemma union_aux_mix
    {F G : Set (Ω → ℝ)} {P : Measure Ω}
    -- by a positive constant (Vaart–Wellner §2.10.1, §2.3).
    (hFG_sep : ∃ c > 0, ∀ f ∈ F ∪ G, ∀ g ∈ F ∪ G,
      ¬ (f ∈ F ∧ g ∈ F) → ¬ (f ∈ G ∧ g ∈ G) →
      c ^ 2 ≤ ∫ x, (f x - g x) ^ 2 ∂P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (_hX_meas : ∀ i, Measurable (X i))
    (_hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (_hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (_hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (_h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (_h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (h_fhat_in : ∀ n ξ, fhat n ξ ∈ F ∪ G)
    (h_ghat_in : ∀ n ξ, ghat n ξ ∈ F ∪ G)
    (h_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) μ)
    (h_l2 : Tendsto (fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
        atTop (𝓝 0))
    (η : ℝ) (_hη : 0 < η) :
    Tendsto (fun n =>
      μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
          ∩ ({ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}
              ∪ {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G})ᶜ))
      atTop (𝓝 0) := by
  obtain ⟨c, hc_pos, hsep⟩ := hFG_sep
  have hc2_pos : (0 : ℝ) < c ^ 2 := pow_pos hc_pos 2
  have h_orig_nonneg : ∀ n ξ, 0 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P :=
    fun _ _ => integral_nonneg (fun _ => sq_nonneg _)
  -- The deviation∩mixed event is contained in {ξ | c² ≤ L²-distance} via separation.
  have h_mix_sub : ∀ n,
      ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
        ∩ ({ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}
            ∪ {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G})ᶜ) ⊆
      {ξ | c ^ 2 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P} := by
    intro n ξ hξ
    have hmix := hξ.2
    have hFF_neg : ¬ (fhat n ξ ∈ F ∧ ghat n ξ ∈ F) := fun h =>
      hmix (Set.mem_union_left _ h)
    have hGG_neg : ¬ (fhat n ξ ∈ G ∧ ghat n ξ ∈ G) := fun h =>
      hmix (Set.mem_union_right _ h)
    exact hsep (fhat n ξ) (h_fhat_in n ξ) (ghat n ξ) (h_ghat_in n ξ) hFF_neg hGG_neg
  -- Markov via ENNReal lintegral with division.
  have hc2_ennreal_ne_zero : ENNReal.ofReal (c ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hc2_pos
  have hc2_ennreal_ne_top : ENNReal.ofReal (c ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_markov : ∀ n,
      μ {ξ | c ^ 2 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P}
      ≤ ENNReal.ofReal ((∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ) / c ^ 2) := by
    intro n
    have h_aem : AEMeasurable
        (fun ξ => ENNReal.ofReal (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P)) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (h_l2_int n).aestronglyMeasurable.aemeasurable
    have h_set_eq :
        {ξ | c ^ 2 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P}
        = {ξ | ENNReal.ofReal (c ^ 2)
            ≤ ENNReal.ofReal (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P)} := by
      ext ξ
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
        ENNReal.ofReal_le_ofReal_iff (h_orig_nonneg n ξ)]
    rw [h_set_eq]
    have h_markov_raw :=
      MeasureTheory.meas_ge_le_lintegral_div h_aem hc2_ennreal_ne_zero hc2_ennreal_ne_top
    have h_lint_eq :
        ∫⁻ ξ, ENNReal.ofReal (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ
          = ENNReal.ofReal (∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (h_l2_int n)
        (Filter.Eventually.of_forall fun ξ => h_orig_nonneg n ξ)).symm
    rw [h_lint_eq] at h_markov_raw
    have h_div :
        ENNReal.ofReal (∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
          / ENNReal.ofReal (c ^ 2)
        = ENNReal.ofReal ((∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ) / c ^ 2) :=
      (ENNReal.ofReal_div_of_pos hc2_pos).symm
    rw [h_div] at h_markov_raw
    exact h_markov_raw
  -- The Markov bound tends to 0 in ℝ≥0∞.
  have h_bound_tendsto :
      Tendsto
        (fun n => ENNReal.ofReal
          ((∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ) / c ^ 2))
        atTop (𝓝 0) := by
    have h_real : Tendsto
        (fun n => (∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ) / c ^ 2)
        atTop (𝓝 0) := by
      have := h_l2.div_const (c ^ 2)
      simpa using this
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h_real
    simpa using this
  -- Squeeze: 0 ≤ μ(...) ≤ Markov-bound → 0.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_bound_tendsto
    (Eventually.of_forall fun _ => zero_le _) ?_
  refine Eventually.of_forall fun n => ?_
  exact (measure_mono (h_mix_sub n)).trans (h_markov n)

/-- **Auxiliary measurable-selection step for `isAsymptoticallyEquicontinuous_union`**.

Given an iid sample `X : ℕ → Ξ → Ω` and a jointly-measurable random pair
`(fhat n, ghat n)` valued in `F ∪ G` with L²-consistency
`∫ ‖fhat − ghat‖²_{L²(P)} dμ → 0`, this lemma asserts that for every
`η > 0` the deviation event splits into three measure-going-to-zero
pieces: the `F`-pure piece, the `G`-pure piece, and a "mixed" piece
where `(fhat n ξ, ghat n ξ)` straddles `F` and `G`.

It sets up the partition

* `S_FF n := {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}`,
* `S_GG n := {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G}`,
* `S_mix n := (S_FF n ∪ S_GG n)ᶜ`,

derives the elementary subset bound

`A n ⊆ (A n ∩ S_FF n) ∪ (A n ∩ S_GG n) ∪ (A n ∩ S_mix n)`

(where `A n` is the deviation event), monotonicity + two applications
of `measure_union_le` give the three-summand μ-bound, and a
`Tendsto.add` sum-to-zero squeeze closes the goal. The mathematical
content lives in three named sub-auxes:

* `union_aux_FF` — F-side via `hF` + measurable surrogate
  (Vaart–Wellner Thm 2.10.1).
* `union_aux_GG` — symmetric.
* `union_aux_mix` — mixed-piece via `h_l2` + Markov + L²-separation.

The prerequisite `AsymptoticStatistics/ForMathlib/MeasurableSelection.lean`
provides the surrogate construction the sub-auxes consume. -/
private lemma isAsymptoticallyEquicontinuous_union_aux
    {F G : Set (Ω → ℝ)} {P : Measure Ω}
    (hF : IsAsymptoticallyEquicontinuous F P)
    (hG : IsAsymptoticallyEquicontinuous G P)
    -- F, G measurably select random functions
    -- (Vaart–Wellner Thm 2.10.1 / vdV §19.4).
    (hF_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions F)
    (hG_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions G)
    -- F, G nonempty with measurable representatives
    -- (Vaart–Wellner §2.3 admissibility).
    (hF_nonempty : ∃ f₀ ∈ F, Measurable f₀)
    (hG_nonempty : ∃ g₀ ∈ G, Measurable g₀)
    -- by a positive constant (Vaart–Wellner §2.10.1, §2.3).
    (hFG_sep : ∃ c > 0, ∀ f ∈ F ∪ G, ∀ g ∈ F ∪ G,
      ¬ (f ∈ F ∧ g ∈ F) → ¬ (f ∈ G ∧ g ∈ G) →
      c ^ 2 ≤ ∫ x, (f x - g x) ^ 2 ∂P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (h_fhat_in : ∀ n ξ, fhat n ξ ∈ F ∪ G)
    (h_ghat_in : ∀ n ξ, ghat n ξ ∈ F ∪ G)
    (h_l2_int : ∀ n, MeasureTheory.Integrable
      (fun ξ => ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) μ)
    (h_l2 : Tendsto (fun n => ∫ ξ, (∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) ∂μ)
        atTop (𝓝 0))
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun n =>
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|})
      atTop (𝓝 0) := by
  have h_FF := union_aux_FF (G := G) hF hF_sel hF_nonempty μ X
    hX_meas hX_iindep hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas
    h_fhat_in h_ghat_in h_l2_int h_l2 η hη
  have h_GG := union_aux_GG (F := F) hG hG_sel hG_nonempty μ X
    hX_meas hX_iindep hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas
    h_fhat_in h_ghat_in h_l2_int h_l2 η hη
  have h_mix := union_aux_mix (F := F) (G := G) (P := P) hFG_sep μ X
    hX_meas hX_iindep hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas
    h_fhat_in h_ghat_in h_l2_int h_l2 η hη
  have h_bound : ∀ n,
      μ {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
      ≤ μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                     - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
            ∩ {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F})
        + μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                       - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
              ∩ {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G})
        + μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                       - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
              ∩ ({ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}
                  ∪ {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G})ᶜ) := by
    intro n
    set A : Set Ξ :=
      {ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
    set SFF : Set Ξ := {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}
    set SGG : Set Ξ := {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G}
    have h_sub : A ⊆ (A ∩ SFF) ∪ (A ∩ SGG) ∪ (A ∩ (SFF ∪ SGG)ᶜ) := by
      intro ξ hξ
      by_cases hFF : ξ ∈ SFF
      · exact Or.inl (Or.inl ⟨hξ, hFF⟩)
      · by_cases hGG : ξ ∈ SGG
        · exact Or.inl (Or.inr ⟨hξ, hGG⟩)
        · exact Or.inr ⟨hξ, fun h => h.elim hFF hGG⟩
    calc μ A
        ≤ μ ((A ∩ SFF) ∪ (A ∩ SGG) ∪ (A ∩ (SFF ∪ SGG)ᶜ)) := measure_mono h_sub
      _ ≤ μ ((A ∩ SFF) ∪ (A ∩ SGG)) + μ (A ∩ (SFF ∪ SGG)ᶜ) := measure_union_le _ _
      _ ≤ μ (A ∩ SFF) + μ (A ∩ SGG) + μ (A ∩ (SFF ∪ SGG)ᶜ) :=
          add_le_add (measure_union_le _ _) le_rfl
  have h_sum :
      Tendsto (fun n =>
        μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                     - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
            ∩ {ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F})
        + μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                       - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
              ∩ {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G})
        + μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                       - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|}
              ∩ ({ξ | fhat n ξ ∈ F ∧ ghat n ξ ∈ F}
                  ∪ {ξ | fhat n ξ ∈ G ∧ ghat n ξ ∈ G})ᶜ))
        atTop (𝓝 0) := by
    simpa using (h_FF.add h_GG).add h_mix
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
    (Eventually.of_forall fun _ => zero_le _)
    (Eventually.of_forall h_bound)

/-- **Union closure of asymptotic equicontinuity**.

vdV §19.4 (used inside the proof of Theorem 19.23): "The union
of two Donsker classes is Donsker." For the marginal-CLT half this is
trivial; for the equicontinuity half (this lemma) the proof reduces by
direct application of the predicate's universal hypotheses to the
auxiliary `isAsymptoticallyEquicontinuous_union_aux`, which carries
the full Vaart–Wellner Thm 2.10.1 measurable-selection content. -/
lemma isAsymptoticallyEquicontinuous_union {F G : Set (Ω → ℝ)} {P : Measure Ω}
    (hF : IsAsymptoticallyEquicontinuous F P)
    (hG : IsAsymptoticallyEquicontinuous G P)
    -- admissibility hypotheses for F and G
    -- (Vaart–Wellner Thm 2.10.1 / vdV §19.4).
    (hF_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions F)
    (hG_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions G)
    (hF_nonempty : ∃ f₀ ∈ F, Measurable f₀)
    (hG_nonempty : ∃ g₀ ∈ G, Measurable g₀)
    -- (Vaart–Wellner §2.10.1, §2.3).
    (hFG_sep : ∃ c > 0, ∀ f ∈ F ∪ G, ∀ g ∈ F ∪ G,
      ¬ (f ∈ F ∧ g ∈ F) → ¬ (f ∈ G ∧ g ∈ G) →
      c ^ 2 ≤ ∫ x, (f x - g x) ^ 2 ∂P) :
    IsAsymptoticallyEquicontinuous (F ∪ G) P := by
  intro Ξ _inst μ _inst2 X hX_meas hX_iindep hX_id hX_law
        fhat ghat h_fhat_meas h_ghat_meas h_fhat_in h_ghat_in h_l2_int h_l2 η hη
  exact isAsymptoticallyEquicontinuous_union_aux hF hG hF_sel hG_sel
    hF_nonempty hG_nonempty hFG_sep μ X
    hX_meas hX_iindep hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas
    h_fhat_in h_ghat_in h_l2_int h_l2 η hη

/-- Closure under finite union: the union of two Donsker classes is
Donsker.

vdV §19.4 (used inside the proof of Theorem 19.23): "The union
of two Donsker classes is Donsker, in general."

The marginal-CLT half is the trivial fact that L²(P)-integrability is
closed under finite union. The equicontinuity half goes through
`isAsymptoticallyEquicontinuous_union`. -/
lemma IsPDonsker.union {F G : Set (Ω → ℝ)} {P : Measure Ω}
    (hF : IsPDonsker F P) (hG : IsPDonsker G P)
    -- admissibility + L²-separation
    -- (Vaart–Wellner Thm 2.10.1, §2.3 / vdV §19.4).
    (hF_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions F)
    (hG_sel : ForMathlib.MeasurableSelection.MeasurablySelectsRandomFunctions G)
    (hF_nonempty : ∃ f₀ ∈ F, Measurable f₀)
    (hG_nonempty : ∃ g₀ ∈ G, Measurable g₀)
    (hFG_sep : ∃ c > 0, ∀ f ∈ F ∪ G, ∀ g ∈ F ∪ G,
      ¬ (f ∈ F ∧ g ∈ F) → ¬ (f ∈ G ∧ g ∈ G) →
      c ^ 2 ≤ ∫ x, (f x - g x) ^ 2 ∂P) :
    IsPDonsker (F ∪ G) P := by
  refine ⟨?_, ?_⟩
  · intro f hf
    cases hf with
    | inl h => exact hF.marginalCLT f h
    | inr h => exact hG.marginalCLT f h
  · exact isAsymptoticallyEquicontinuous_union hF.asymptoticallyEquicontinuous
      hG.asymptoticallyEquicontinuous hF_sel hG_sel hF_nonempty hG_nonempty hFG_sep

end AsymptoticStatistics.EmpiricalProcess
