FIRST: read `.claude/prompts/np-rkhs-header.md` in this worktree and obey every rule in
it for the whole session.  It is the contract of this lane.

# Lane: np/rkhs-sqrt — close the square-root section (FINAL lane of the batch)

Touch-set (the ONLY file you may edit):
- StatLean/NonparametricStatistics/RKHS/Mercer/SquareRoot.lean  (11 sorries)

Build target: `lake build StatLean.NonparametricStatistics.RKHS.Mercer.SquareRoot`.

Everything else in the batch is 0-sorry, including ALL of Mercer/Theorem.lean
(`exists_mercerEigensystem`, `MercerEigensystem.hasSum_kernel`,
`tendstoUniformly_kernel`, `summable_eigval`, `hasSum_eigval`) — use them freely.
The previous session refuted the old pointwise-`tsum` definition of `sqrtSymbol`
(counterexample preserved in the docstring); the CURRENT definition is the repaired one:
`sqrtSectionLp d x : Lp 𝕜 2 μ` is an `L²`-space `tsum` of the orthogonal family
`(√λₙ eₙ(x)) • toLp (star (eₙ))`, and `sqrtSymbol d x = ⇑(sqrtSectionLp d x)`.
Every remaining `sorry` carries a `-- Route` comment written against exactly this
definition — follow them.  Statements are frozen (header rule 5).

Key working facts about the new definition:
- The family `n ↦ (√λₙ eₙ x) • toLp (star (eₙ))` is orthogonal (from `d.orthonormal`;
  conjugation preserves orthogonality with conjugated inner products — prove a private
  lemma `⟪toLp (star eₙ), toLp (star eₘ)⟫ = conj ⟪toLp eₙ, toLp eₘ⟫` via `L2.inner_def`
  + `integral_conj`), with `∑ₙ ‖(√λₙ eₙ x) • toLp (star eₙ)‖² = ∑ₙ λₙ ‖eₙ x‖²`,
  summable with sum `re K(x,x)` (diagonal of the PROVED `hasSum_kernel`).  Hence the
  defining `tsum` converges (`Orthogonal family: summable iff norm-sq summable` — search
  `OrthogonalFamily` `summable` in `Mathlib/Analysis/InnerProductSpace/l2Space.lean`,
  e.g. `OrthogonalFamily.summable_iff_norm_sq_summable`? verify the exact name; the
  orthogonal family here is over `Fin`-free index `d.ι` with `Countable d.ι` — if the
  Mathlib lemma needs `HilbertSpace`-completeness only, `Lp` is complete ✓).
- `isL2Symbol_sqrtSymbol` is `fun x => Lp.memLp _` (definitional).
- Pairings: `⟪sqrtSectionLp d x, g⟫ = ∑ₙ conj (√λₙ eₙ x) * ⟪toLp (star eₙ), g⟫`…
  CAREFUL with conjugation: `⟪toLp (star eₙ), g⟫ = ∫ eₙ y * g y dμ` (unfold via
  `L2.inner_def`, `ContinuousMap.coeFn_toLp`, `star` coe) — NOT `⟪toLp eₙ, g⟫`.
  Meanwhile `integralOp μ (sqrtSymbol d) g x = ∫ (sqrtSectionLp d x) y * g y dμ`.
  Derive the master identity first (private lemma):
  `integralOp μ (sqrtSymbol d) g x = ∑ₙ √λₙ (eₙ x) * ⟪toLp (eₙ), g⟫` — via
  `HasSum.mapL` of the continuous functional `h ↦ ∫ h y * g y dμ`(= `⟪star ?, ?⟫`-form;
  cleanest: `fun h => ⟪(starL? h), g⟫`… if bundling star is awkward, use the functional
  `h ↦ ⟪toLp-free…` — note `∫ h y * g y = ⟪star h, g⟫` where `star` on `Lp 𝕜 2 μ` exists
  (`Lp.instStarAddMonoid`?) — if the `Lp` star instance is missing at the pin, work with
  the CONJUGATED sections from the start: `⟪sqrtSectionLp d x, ·⟫` is already continuous
  linear in the second slot and
  `integralOp … g x = ⟪star-section…` — mirror how `integralOp_eq_inner`
  (IntegralOperator.lean, PROVED) handles exactly this bookkeeping and reuse
  `symbolConjLp`: in fact `symbolConjLp μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK) x`
  IS the class of `conj ∘ sqrtSymbol d x`, and `integralOp_eq_inner` gives
  `integralOp μ (sqrtSymbol d) g x = ⟪that, g⟫` — then identify `that` with the
  `L²`-tsum `∑ₙ (√λₙ conj (eₙ x)) • toLp (eₙ)` (a private lemma: conj of an Lp-tsum is
  the tsum of conj's — continuity of the conjugation as an ℝ-linear isometry of `Lp`, or
  do it via `Lp.ext` + a.e. pointwise identification of both sides through
  `MemLp.coeFn_toLp`).
- From the master identity: `sqrtCLM_hasSum`, then `isPositive` (diagonal form),
  `comp_self` (apply master twice + `d.opExpansion`), `range_integralOp_sqrtSymbol_eq`
  (S □ S* = K by the master identity + orthonormality, then `rangeSpace_scalarKernel` +
  `range_integralOp_eq_range_coe` + `exists_isometryEquiv_of_scalarKernel_eq`
  (Uniqueness, PROVED) transports to `H`), `isometry` (rangeSpace norm), then the two
  documented three-step routes for `exists_orthonormalBasis_sqrt_eigfun` and
  `mem_range_coe_iff_summable`, and finally `range_mercerCLM_subset` (its full
  Bochner-integral route is in its comment; `hKc` is now included via `include hKc in`).

Suggested order: isL2Symbol → memLp → sqrtCLM fields → master identity →
sqrtCLM_hasSum → isPositive → comp_self → range_mercerCLM_subset (independent, easy) →
range_eq → isometry → ONB → membership.  Commit after EVERY closed lemma; if one
resists, document and move on — a clean partial close beats a broken sweep.
