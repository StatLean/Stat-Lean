import StatLean.StatisticalModels.FactorModels.Gaussian
import StatLean.StatisticalModels.GraphicalModels.Core.CondIndep
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.Covariance

/-!
# Local independence — the bridge between factor models and graphical models

`BKM`'s **axiom of conditional (local) independence**, Eq. (1.9): once the latent factors are
held fixed, the observed coordinates carry no dependence left over. In the linear model
`x = μ + Λ y + e` with Gaussian specific factors and a **diagonal** specific-factor covariance
`Ψ`, this is a theorem rather than an axiom, and it is the point at which the two new areas
meet: the conclusion is stated with `GraphicalModels.CondIndep`, the conditional-independence
predicate of the graphical slice, applied to the factor model of `FactorModels.Defs`.

* `factorJointLaw P F E` — the joint law of the pair `(y, x)`, i.e. the latent law composed
  with the measurement kernel; `factorJointLaw_fst` / `factorJointLaw_snd` identify its two
  marginals as `F` and `factorLaw P F E`;
* `indepFun_eval_measurementKernel` — at a **fixed** factor value, two distinct observed
  coordinates are independent (`BKM` Eq. (1.9), pairwise form);
* `iIndepFun_eval_measurementKernel` — the **family** version: at a fixed factor value the
  whole family `(x₁, …, x_p)` is jointly independent;
* `map_measurementKernel_eq_pi` — `BKM` Eq. (1.9) verbatim, as the product formula
  `g(x ∣ y) = ∏ᵢ gᵢ(xᵢ ∣ y)` with `gᵢ(· ∣ y) = N((μ + Λy)ᵢ, ψᵢ)`;
* **`condIndep_eval_factorJointLaw` (HEADLINE)** — local independence in the graphical
  vocabulary: `xᵢ ⫫ xⱼ ∣ y` under the joint law, for `i ≠ j`;
* `factorCovariance_apply_of_oneFactor`, `factorCovariance_apply_ne_zero_of_oneFactor`,
  `not_indepFun_eval_gaussianFactorModel` — **the contrast**. After the factor is marginalised
  out, the off-diagonal entry of `Σ = Λ Φ Λᵀ + Ψ` is `λᵢ Φ λⱼ`, which is non-zero as soon as
  two loadings on a common factor are; so the observed coordinates are *dependent* even though
  they were conditionally independent given the factor.

**The moral.** Conditional independence *given the latent variables* and dependence *in the
observed marginal* are two different statements, and a factor model is precisely a device that
produces the second from the first: the common factor manufactures the observed correlations,
and `Ψ` diagonal says that nothing else does. A graphical model describes dependence by which
conditional independences hold **among the observed variables themselves**; a factor model
describes it by positing latent variables that **explain the dependence away**. The two are
therefore complementary descriptions of the same phenomenon (roadmap §1), and this file is the
one place where both vocabularies are used in a single statement.

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, §1.4, **Eq. (1.9)** (p. 7):
`g(x ∣ y) = ∏_{i=1}^{p} gᵢ(xᵢ ∣ y)` — note this is a **chapter 1** equation, not a chapter 2
one — together with the surrounding passage (pp. 7–8): "if the dependencies among the *x*s are
induced by a set of latent variables **y** then when all **y**s are accounted for, the *x*s
will be independent if all the **y**s are held fixed. If this were not so the set of **y**s
would not be *complete*"; and, on p. 8, "It is better regarded as a definition of what we mean
when we say that the set of latent variables **y** is complete. In other words, that **y** is
sufficient to explain the dependencies among the *x*s." Eq. (1.10) (p. 8),
`f(x) = ∫ h(y) ∏ᵢ gᵢ(xᵢ ∣ y) dy`, is the marginalisation that the contrast section is about.
The linear-Gaussian instance is §3.2, Eq. (3.1)–(3.3) and Eq. (3.12) (`BKM`).

**Proof formalization notes.**

*Book vs Lean, three points.*

1. **Diagonality of `Ψ` is only uncorrelatedness in general; Gaussianity is what upgrades it to
   independence.** `BKM` Eq. (1.9) is an assumption about the conditional *density*, and
   Eq. (3.1) supplies it by taking `x ∣ y ∼ N_p(μ + Λ y, Ψ)` with `Ψ` diagonal. Our statements
   therefore fix the specific-factor law to be `multivariateGaussian 0 Ψ`: for a non-Gaussian
   `E` with diagonal covariance the conclusion is **false**, and no theorem below is stated at
   that generality. Diagonality alone is `HasDiagonalUniqueness`; it is not enough.
2. **The conditioning variable is the factor itself, not another block of coordinates.** So the
   statement uses the general `GraphicalModels.CondIndep μ f g h` and *not* the contracted
   `CondIndepCoords`, whose three arguments are all blocks of one vector.
3. **The family version lives at the kernel level.** `GraphicalModels.CondIndep` is a binary
   predicate; a *family* conditional-independence predicate (an `iIndepFun` conditioned on a
   third variable) is not part of the round-1 `Core` API. `iIndepFun_eval_measurementKernel`
   and `map_measurementKernel_eq_pi` therefore state the joint independence of all `p`
   coordinates **under the conditional law at each factor value** — which is exactly what
   `BKM` Eq. (1.9) asserts, since (1.9) is a statement about `g(· ∣ y)` for each `y`. Lifting
   it to a family predicate on the joint space is deferred to the round-2 `Core` extension.

*Routes (do not re-derive).*

| Step | Consumed from |
|---|---|
| `x ∣ y ∼ N(μ + Λy, Ψ)` | `measurementKernel_multivariateGaussian` (`FactorModels.Gaussian`) |
| uncorrelated ⇒ independent, jointly Gaussian | `HasGaussianLaw.indepFun_of_covariance_eq_zero`, family version `.iIndepFun_of_covariance_eq_zero`; in block form `Gaussian.multivariateGaussian_fromBlocks_prod` (G2.9) |
| covariance entries of a Gaussian | `ProbabilityTheory.covariance_eval_multivariateGaussian` |
| the one-dimensional coordinate marginals | `measurePreserving_eval_multivariateGaussian` |
| `iIndepFun` as a product of marginals | `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map` |
| marginals of the joint law | `Measure.fst_compProd`, `Measure.snd_compProd` |
| pushing a map through `⊗ₘ` | `Measure.compProd_map` : `μ ⊗ₘ (κ.map f) = (μ ⊗ₘ κ).map (Prod.map id f)` |
| the product kernel `κ ×ₖ η` | `Kernel.prod_apply`, `Kernel.map_prod_map`, `Kernel.IsMarkovKernel.map` |
| independence forces zero covariance | `ProbabilityTheory.IndepFun.covariance_eq_zero` |
| `Σ = Λ Φ Λᵀ + Ψ`, and that it is PSD | `factorCovariance`, `posSemidef_factorCovariance` (`FactorModels.Moments`) |

Nothing about Gaussian independence, and nothing about the covariance decomposition, is
re-derived here; the entries above are the whole content of every proof in this file.

*Route for the headline.* `Measure.compProd_map` at `f := fun x => (x i, x j)` turns
`(factorJointLaw P F E).map (fun z => (z.1, (z.2 i, z.2 j)))` into
`F ⊗ₘ ((measurementKernel P E).map f)`; `Measure.fst_compProd` identifies `μ.map Prod.fst` with
`F`; and `Kernel.ext` plus `indepFun_eval_measurementKernel` (in its
`indepFun_iff_map_prod_eq_prod_map_map` form) identifies `(measurementKernel P E).map f` with
the product kernel `κ ×ₖ η`, where `κ := (measurementKernel P E).map (fun x => x i)` and
`η := (measurementKernel P E).map (fun x => x j)` are Markov by `Kernel.IsMarkovKernel.map`.
Those two kernels are the witnesses `CondIndep` asks for.

*Junk values.* `multivariateGaussian m S` collapses to `Measure.dirac m` off the
positive-semidefinite cone, so every statement carries `P.uniqueCov.PosSemidef` (or
`IsProperFactorParams`) explicitly; without it the "conditional law" is a point mass and the
covariance statements are false.

**Bibliographic comments.** The conditional-independence formulation of a latent-variable model
is P. F. Lazarsfeld's, in S. A. Stouffer et al., *Measurement and Prediction*, Princeton Univ.
Press, 1950, ch. 10–11, where it appears as the *axiom of local independence* for latent
structure analysis; `BKM` §1.4 is the modern statement, and `BKM` p. 8 makes the point recorded
above, that local independence is better read as a *definition of completeness* of the latent
vector than as a testable assumption. The observation that a common factor manufactures
observed correlation is Spearman's original argument for a general factor (C. Spearman,
"'General intelligence', objectively determined and measured," *Amer. J. Psychol.* **15**
(1904), 201–292): the *tetrad differences* vanish exactly because the observed covariances
factor through a single latent variable. The complementary reading — describing dependence by
conditional independences among the observed variables — is the graphical-models programme of
S. L. Lauritzen, *Graphical Models*, Clarendon Press, 1996.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

variable {p q : ℕ}

/-! ### The joint law of factor and observation -/

/-- The **joint law of the pair `(y, x)`** in the linear factor model (`BKM` Eq. (3.3)): the
latent law `F` composed with the measurement kernel `y ↦ law of (μ + Λ y + e)`. This is the
sample space on which "conditionally independent **given the factor**" can be said at all —
`factorLaw` has already marginalised the factor away.

*Edge behaviour:* a probability measure exactly when `F` and `E` are (instance below); for
non-s-finite `F` or a non-s-finite kernel, `⊗ₘ` degenerates to `0`, matching the usual junk
convention of `Measure.compProd`. -/
noncomputable def factorJointLaw (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p))) :
    Measure (EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin p)) :=
  F ⊗ₘ measurementKernel P E

instance (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure F]
    [IsProbabilityMeasure E] : IsProbabilityMeasure (factorJointLaw P F E) := by
  rw [factorJointLaw]; infer_instance

/-- The **latent marginal** of the joint law is the latent law `F` (`BKM` Eq. (3.2)). -/
theorem factorJointLaw_fst (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p)))
    -- LEAN-ONLY: `Measure.fst_compProd` is stated for an s-finite first factor; without it
    -- `⊗ₘ` is junk and the identity carries no content
    [SFinite F]
    -- LEAN-ONLY: makes `measurementKernel P E` a Markov kernel, which is what
    -- `Measure.fst_compProd` needs to leave the first marginal untouched
    [IsProbabilityMeasure E] :
    (factorJointLaw P F E).fst = F := by
  rw [factorJointLaw, Measure.fst_compProd]

/-- The **observed marginal** of the joint law is `factorLaw P F E` (`BKM` Eq. (3.3)/(1.10)):
integrating the factor out of the joint law returns the observed law. This is the identity that
makes the contrast at the end of the file a statement about the *same* model. -/
theorem factorJointLaw_snd (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p)))
    -- LEAN-ONLY: s-finiteness of the latent law, demanded by `Measure.snd_compProd`
    [SFinite F]
    -- LEAN-ONLY: makes `measurementKernel P E` Markov, hence s-finite — the side condition of
    -- `Measure.snd_compProd`
    [IsProbabilityMeasure E] :
    (factorJointLaw P F E).snd = factorLaw P F E := by
  sorry

/-! ### `BKM` Eq. (1.9) — local independence at a fixed factor value -/

/-- **`BKM` Eq. (1.9), pairwise form.** With Gaussian specific factors and a **diagonal**
specific-factor covariance `Ψ`, two distinct observed coordinates are independent under the
conditional law given the factor — for *every* value `y` of the factor.

Route (do not re-derive): `measurementKernel_multivariateGaussian` rewrites the conditional law
as `N(μ + Λ y, Ψ)`; `covariance_eval_multivariateGaussian` reads its `(i, j)` covariance entry
off as `Ψ i j`, which is `0` by diagonality; and
`HasGaussianLaw.indepFun_of_covariance_eq_zero` converts a vanishing covariance of jointly
Gaussian variables into independence. -/
theorem indepFun_eval_measurementKernel (P : FactorParams p q)
    -- USER-INPUT: the specific factors are uncorrelated across coordinates, i.e. `Ψ` diagonal;
    -- BKM §3.2 Eq. (3.1), the hypothesis that makes Eq. (1.9) hold in the linear model
    (hΨdiag : HasDiagonalUniqueness P)
    -- USER-INPUT: `Ψ` is a genuine covariance matrix; BKM Eq. (3.1). Without it
    -- `multivariateGaussian 0 Ψ` is a Dirac mass and the conditional law is degenerate
    (hΨ : P.uniqueCov.PosSemidef) {i j : Fin p}
    -- USER-INPUT: two distinct observed coordinates; BKM Eq. (1.9)
    (hij : i ≠ j) (y : EuclideanSpace ℝ (Fin q)) :
    IndepFun (fun x : EuclideanSpace ℝ (Fin p) => x i) (fun x : EuclideanSpace ℝ (Fin p) => x j)
      (measurementKernel P (multivariateGaussian 0 P.uniqueCov) y) := by
  sorry

/-- **`BKM` Eq. (1.9), family form.** All `p` observed coordinates are *jointly* independent
under the conditional law at a fixed factor value — the statement `BKM` actually makes, since
Eq. (1.9) is a product over all `i = 1, …, p`.

Route (do not re-derive): as for the pairwise form, but through
`HasGaussianLaw.iIndepFun_of_covariance_eq_zero`, whose hypothesis is exactly
"`cov(xᵢ, xⱼ) = 0` for all `i ≠ j`", i.e. diagonality of `Ψ`. -/
theorem iIndepFun_eval_measurementKernel (P : FactorParams p q)
    -- USER-INPUT: `Ψ` diagonal; BKM §3.2 Eq. (3.1)
    (hΨdiag : HasDiagonalUniqueness P)
    -- USER-INPUT: `Ψ` a genuine covariance matrix; BKM Eq. (3.1)
    (hΨ : P.uniqueCov.PosSemidef) (y : EuclideanSpace ℝ (Fin q)) :
    iIndepFun (fun (i : Fin p) (x : EuclideanSpace ℝ (Fin p)) => x i)
      (measurementKernel P (multivariateGaussian 0 P.uniqueCov) y) := by
  sorry

/-- **`BKM` Eq. (1.9) verbatim**: `g(x ∣ y) = ∏_{i=1}^{p} gᵢ(xᵢ ∣ y)`, with the univariate
conditional laws `gᵢ(· ∣ y) = N((μ + Λ y)ᵢ, ψᵢ)` read off the diagonal of `Ψ`. The pushforward
along `WithLp.ofLp` is only the passage from `EuclideanSpace ℝ (Fin p)` to the bare product
`Fin p → ℝ` on which `Measure.pi` lives; it changes nothing measure-theoretically.

Route (do not re-derive): `iIndepFun_eval_measurementKernel` in the form
`iIndepFun_iff_map_fun_eq_pi_map`, with the coordinate marginals supplied by
`measurePreserving_eval_multivariateGaussian` after
`measurementKernel_multivariateGaussian`. -/
theorem map_measurementKernel_eq_pi (P : FactorParams p q)
    -- USER-INPUT: `Ψ` diagonal; BKM §3.2 Eq. (3.1)
    (hΨdiag : HasDiagonalUniqueness P)
    -- USER-INPUT: `Ψ` a genuine covariance matrix; BKM Eq. (3.1)
    (hΨ : P.uniqueCov.PosSemidef) (y : EuclideanSpace ℝ (Fin q)) :
    (measurementKernel P (multivariateGaussian 0 P.uniqueCov) y).map (fun x => WithLp.ofLp x)
      = Measure.pi fun i : Fin p =>
          gaussianReal ((P.μ + Matrix.toEuclideanLin (𝕜 := ℝ) P.loading y) i)
            (P.uniqueCov i i).toNNReal := by
  sorry

/-! ### The headline — local independence in the graphical vocabulary -/

/-- **HEADLINE — local independence** (`BKM` §1.4, Eq. (1.9); linear-Gaussian instance §3.2,
Eq. (3.1)). In the Gaussian linear factor model with a **diagonal** specific-factor covariance
`Ψ`, two distinct observed coordinates are conditionally independent given the latent factor:
`xᵢ ⫫ xⱼ ∣ y` under the joint law of `(y, x)`.

This is the bridge between the two areas: the conclusion is `GraphicalModels.CondIndep`, the
disintegration predicate of the graphical slice, and the model is `FactorModels.factorJointLaw`.
The witnesses `CondIndep` asks for are the two coordinate marginals of the measurement kernel;
see the module docstring for the route.

*Book vs Lean:* `BKM` Eq. (1.9) states local independence for the whole family and for an
arbitrary conditional density; here it is a **theorem** in the Gaussian linear model, in the
pairwise form that `CondIndep` can express. The family form is
`iIndepFun_eval_measurementKernel` / `map_measurementKernel_eq_pi`, stated at the kernel level
because round 1 has no family conditional-independence predicate. -/
theorem condIndep_eval_factorJointLaw (P : FactorParams p q)
    (F : Measure (EuclideanSpace ℝ (Fin q)))
    -- LEAN-ONLY: the latent law is a probability measure — needed for `⊗ₘ` to be the joint law
    -- of a pair of random variables and for `Measure.fst_compProd` to return `F`
    [IsProbabilityMeasure F]
    -- USER-INPUT: the specific factors are uncorrelated across coordinates, i.e. `Ψ` diagonal;
    -- BKM §3.2 Eq. (3.1) — this is what makes Eq. (1.9) true here, and it is *not* enough
    -- without the Gaussianity built into the error law below
    (hΨdiag : HasDiagonalUniqueness P)
    -- USER-INPUT: `Ψ` is a genuine covariance matrix; BKM Eq. (3.1)
    (hΨ : P.uniqueCov.PosSemidef) {i j : Fin p}
    -- USER-INPUT: two distinct observed coordinates; BKM Eq. (1.9)
    (hij : i ≠ j) :
    GraphicalModels.CondIndep
        (factorJointLaw P F (multivariateGaussian 0 P.uniqueCov))
        (fun z => z.2 i) (fun z => z.2 j) Prod.fst := by
  sorry

/-! ### The contrast — dependence in the observed marginal

Local independence says nothing about the *observed* law. Marginalising the factor out
(`BKM` Eq. (1.10), `factorJointLaw_snd`) leaves `Σ = Λ Φ Λᵀ + Ψ`, whose off-diagonal entries
are the common part alone — the specific factors contribute only to the diagonal. In the
one-factor model `Σᵢⱼ = λᵢ φ λⱼ`, so any two coordinates loading on the same factor are
correlated, hence (being jointly Gaussian) dependent. This is the precise sense in which a
common factor *manufactures* the observed dependence that local independence has removed from
the conditional law. -/

section Contrast

/-- The **off-diagonal entries of the one-factor covariance**: for `q = 1` and `Ψ` diagonal,
`Σᵢⱼ = λᵢ φ λⱼ` whenever `i ≠ j` — the specific factors drop out entirely off the diagonal
(contrast `Communality.variance_eq_common_add_specificVariance`, which is the diagonal case).

Route: `factorCovariance_eq` plus `Matrix.mul_apply` twice, the sums over `Fin 1` collapsing by
`Finset.sum_singleton` / `Fin.sum_univ_one`, and `hΨdiag hij : Ψ i j = 0`. -/
theorem factorCovariance_apply_of_oneFactor (P : FactorParams p 1)
    -- USER-INPUT: `Ψ` diagonal — the factor-analytic restriction; BKM Eq. (3.1), (3.12)
    (hΨdiag : HasDiagonalUniqueness P) {i j : Fin p}
    -- USER-INPUT: two distinct observed coordinates; BKM Eq. (3.12)
    (hij : i ≠ j) :
    factorCovariance P i j = P.loading i 0 * P.factorCov 0 0 * P.loading j 0 := by
  sorry

/-- **The common factor induces observed correlation** (`BKM` §1.4, p. 7: "if `x₁` and `x₂` both
depend on `y₁` we may expect the common influence of `y₁` to induce a correlation between `x₁`
and `x₂`"). For a standardized one-factor model, the observed covariance between two
coordinates with non-zero loadings is non-zero — despite their conditional independence given
the factor. -/
theorem factorCovariance_apply_ne_zero_of_oneFactor (P : FactorParams p 1)
    -- USER-INPUT: standardized latent factor, `Φ = I`; BKM Eq. (3.2)
    (hΦ : IsStandardized P)
    -- USER-INPUT: `Ψ` diagonal; BKM Eq. (3.1)
    (hΨdiag : HasDiagonalUniqueness P) {i j : Fin p}
    -- USER-INPUT: two distinct observed coordinates; BKM Eq. (3.12)
    (hij : i ≠ j)
    -- USER-INPUT: coordinate `i` genuinely loads on the factor; BKM §1.4, p. 7
    (hi : P.loading i 0 ≠ 0)
    -- USER-INPUT: coordinate `j` genuinely loads on the same factor; BKM §1.4, p. 7
    (hj : P.loading j 0 ≠ 0) :
    factorCovariance P i j ≠ 0 := by
  sorry

/-- **The contrast, as a negative statement about the observed law.** In the Gaussian
one-factor model with two non-zero loadings, the two observed coordinates are **not**
independent — even though `condIndep_eval_factorJointLaw` makes them conditionally independent
given the factor. Together the two theorems are the conceptual payload of this file.

Route (do not re-derive): `gaussianFactorModel_eq_multivariateGaussian` identifies the observed
law as `N(μ, Σ)`; `IndepFun.covariance_eq_zero` (with `MemLp` supplied by
`IsGaussian.memLp_two_id`) would force `cov(xᵢ, xⱼ) = 0`;
`covariance_eval_multivariateGaussian`, applicable since `posSemidef_factorCovariance` holds,
identifies that covariance with `Σᵢⱼ`; and
`factorCovariance_apply_ne_zero_of_oneFactor` contradicts it. -/
theorem not_indepFun_eval_gaussianFactorModel (P : FactorParams p 1)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2) — without them
    -- `gaussianFactorModel` degenerates to a Dirac mass, under which every pair of coordinates
    -- *is* independent, so the hypothesis is essential
    (hP : IsProperFactorParams P)
    -- USER-INPUT: standardized latent factor, `Φ = I`; BKM Eq. (3.2)
    (hΦ : IsStandardized P)
    -- USER-INPUT: `Ψ` diagonal; BKM Eq. (3.1)
    (hΨdiag : HasDiagonalUniqueness P) {i j : Fin p}
    -- USER-INPUT: two distinct observed coordinates; BKM Eq. (3.12)
    (hij : i ≠ j)
    -- USER-INPUT: coordinate `i` genuinely loads on the factor; BKM §1.4, p. 7
    (hi : P.loading i 0 ≠ 0)
    -- USER-INPUT: coordinate `j` genuinely loads on the same factor; BKM §1.4, p. 7
    (hj : P.loading j 0 ≠ 0) :
    ¬ IndepFun (fun x : EuclideanSpace ℝ (Fin p) => x i)
        (fun x : EuclideanSpace ℝ (Fin p) => x j) (gaussianFactorModel p 1 P) := by
  sorry

end Contrast

end StatLean.StatisticalModels.FactorModels
