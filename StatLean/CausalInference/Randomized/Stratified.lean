import StatLean.CausalInference.Randomized.CompleteRandomization

/-!
# Stratified randomized experiments — the design and unbiasedness

In a stratified randomized experiment (SRE) the units are grouped by a discrete covariate
into `K` strata and an independent complete randomization is run inside each stratum, with
`m k` treated units in stratum `k`. The stratified estimator is the size-weighted average
of the within-stratum difference in means,

$$\hat\tau_S=\sum_k \frac{n_{[k]}}{n}\,\hat\tau_{[k]},$$

and it is unbiased for the finite-population average causal effect.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Definition 5.1 (§5.1, p. 60: the SRE as `K`
independent CREs); §5.3.1 (pp. 66–67: the stratified estimator, its unbiasedness and its
variance — stated in the running text, with no theorem number); §5.4 with eq. (5.5)
(pp. 72–75: a CRE conditioned on the within-stratum treated counts *is* an SRE, the basis
of post-stratification). (`Ding Definition 5.1; §5.3.1; §5.4 eq. (5.5)`.) Stratified
randomized experiments are ch. 9 of G. W. Imbens and D. B. Rubin, *Causal Inference for
Statistics, Social, and Biomedical Sciences*, Cambridge University Press, 2015.
(`IR ch. 9`.)

**Scope.** Formalized here: the design, the conditioning relation to complete
randomization (eq. (5.5)'s combinatorial content, `stratifiedSupport_subset_completeSupport`),
the within-stratum inclusion probabilities, and **unbiasedness** of the stratified
estimator. The exact stratified *variance* `∑ π²_[k] Var(τ̂_[k])` is **not** formalized in
this release: it needs the full product-design factorization across strata (each stratum's
assignment independent of the others), which is a substantially larger piece of
combinatorial infrastructure than everything else in this file, and Ding himself states it
by applying Theorem 4.1 stratum-wise rather than proving it afresh. The per-stratum
variance identity is already available as `Neyman.differenceInMeans_variance`.

**Proof formalization notes.** The unbiasedness proof deliberately avoids the product
structure. It uses only two facts: (i) on the SRE support, the number of treated units in
stratum `k` is constant (`= m k`) — true by definition of the support; and (ii) the design
is invariant under transpositions of two units *within* a stratum, so the inclusion
probability `E[Zᵢ]` is the same for all `i` in a stratum. Summing (ii) over the stratum and
using (i) forces `E[Zᵢ] = m k / n_k`. That is the whole argument, and it is exactly why
stratification preserves unbiasedness whatever the allocation.

**Bibliographic comments.** Stratification (blocking) in experimental design goes back to
R. A. Fisher, *The Design of Experiments*, Oliver & Boyd, 1935.
-/

namespace StatLean.CausalInference

variable {n K : ℕ}

/-- The set of units in stratum `k`. -/
def stratum (g : Fin n → Fin K) (k : Fin K) : Finset (Fin n) :=
  Finset.univ.filter fun i => g i = k

/-- The support of a **stratified randomized experiment**: assignments treating exactly
`m k` units inside each stratum `k` (Ding Definition 5.1). -/
def stratifiedSupport (g : Fin n → Fin K) (mk : Fin K → ℕ) : Finset (Assignment n) :=
  Finset.univ.filter fun z => ∀ k, ((stratum g k) ∩ armIdx z true).card = mk k

/-- The stratified support is nonempty when each stratum can supply its treated units. -/
theorem stratifiedSupport_nonempty {g : Fin n → Fin K} {mk : Fin K → ℕ}
    -- USER-INPUT: each stratum is large enough for its allocation; Ding Definition 5.1
    (h : ∀ k, mk k ≤ (stratum g k).card) :
    (stratifiedSupport g mk).Nonempty := by
  sorry

/-- The **stratified randomized experiment** as a design (Ding Definition 5.1). -/
noncomputable def stratifiedDesign (g : Fin n → Fin K) (mk : Fin K → ℕ)
    (h : ∀ k, mk k ≤ (stratum g k).card) : Design n :=
  ⟨stratifiedSupport g mk, stratifiedSupport_nonempty h⟩

/-- **A stratified assignment is a completely randomized assignment with the given total**
(Ding §5.4, eq. (5.5)): the SRE support sits inside the CRE support with `n₁ = ∑ₖ m k`.
Conditioning a CRE on the within-stratum counts is what produces the SRE. -/
theorem stratifiedSupport_subset_completeSupport {g : Fin n → Fin K} {mk : Fin K → ℕ}
    {z : Assignment n} (hz : z ∈ stratifiedSupport g mk) :
    z ∈ completeSupport n (∑ k, mk k) := by
  sorry

/-- **Within-stratum exchangeability**: the stratified design is invariant under swapping
two units of the same stratum, so their inclusion probabilities agree. -/
theorem stratifiedDesign_expect_ind_eq {g : Fin n → Fin K} {mk : Fin K → ℕ}
    (h : ∀ k, mk k ≤ (stratum g k).card) {i j : Fin n}
    -- USER-INPUT: two units of the same stratum; Ding Definition 5.1
    (hij : g i = g j) :
    (stratifiedDesign g mk h).expect (fun z => ind (z i))
      = (stratifiedDesign g mk h).expect (fun z => ind (z j)) := by
  sorry

/-- **The within-stratum inclusion probability** (Ding Definition 5.1): a unit of stratum
`k` is treated with probability `m k / n_k`. -/
theorem stratifiedDesign_expect_ind {g : Fin n → Fin K} {mk : Fin K → ℕ}
    (h : ∀ k, mk k ≤ (stratum g k).card) (i : Fin n)
    -- LEAN-ONLY: the unit's stratum is nonempty (it contains `i`), stated for the divisor
    (hne : 0 < (stratum g (g i)).card) :
    (stratifiedDesign g mk h).expect (fun z => ind (z i))
      = (mk (g i) : ℝ) / ((stratum g (g i)).card : ℝ) := by
  sorry

/-- The **within-stratum difference in means** `τ̂_[k]`. Junk value `0` if an arm of the
stratum is empty. -/
noncomputable def stratumDiffInMeans (S : ScienceTable n) (g : Fin n → Fin K) (k : Fin K)
    (z : Assignment n) : ℝ :=
  (((stratum g k ∩ armIdx z true).card : ℝ)⁻¹
      * ∑ i ∈ stratum g k ∩ armIdx z true, S.observed z i)
  - (((stratum g k ∩ armIdx z false).card : ℝ)⁻¹
      * ∑ i ∈ stratum g k ∩ armIdx z false, S.observed z i)

/-- The **stratified estimator** `τ̂_S = ∑ₖ (n_[k]/n) τ̂_[k]` (Ding §5.3.1). -/
noncomputable def stratifiedEstimator (S : ScienceTable n) (g : Fin n → Fin K)
    (z : Assignment n) : ℝ :=
  ∑ k, (((stratum g k).card : ℝ) / (n : ℝ)) * stratumDiffInMeans S g k z

/-- The **within-stratum average causal effect** `τ_[k]`. -/
noncomputable def stratumATE (S : ScienceTable n) (g : Fin n → Fin K) (k : Fin K) : ℝ :=
  ((stratum g k).card : ℝ)⁻¹ * ∑ i ∈ stratum g k, S.unitEffect i

/-- **The within-stratum estimator is unbiased for the within-stratum effect**
(Ding §5.3.1, from Theorem 4.1 applied inside the stratum). -/
theorem stratumDiffInMeans_unbiased (S : ScienceTable n) {g : Fin n → Fin K} {mk : Fin K → ℕ}
    (h : ∀ k, mk k ≤ (stratum g k).card) (k : Fin K)
    -- USER-INPUT: both arms of the stratum are nonempty; Ding Definition 5.1
    (h1 : 0 < mk k) (h0 : mk k < (stratum g k).card) :
    (stratifiedDesign g mk h).expect (stratumDiffInMeans S g k) = stratumATE S g k := by
  sorry

/-- **Unbiasedness of the stratified estimator** (Ding §5.3.1, p. 66): stratification
preserves unbiasedness for any allocation. -/
theorem stratifiedEstimator_unbiased (S : ScienceTable n) {g : Fin n → Fin K} {mk : Fin K → ℕ}
    (h : ∀ k, mk k ≤ (stratum g k).card)
    -- USER-INPUT: every stratum has units in both arms; Ding Definition 5.1
    (h1 : ∀ k, 0 < mk k) (h0 : ∀ k, mk k < (stratum g k).card)
    -- LEAN-ONLY: a nonempty population, so that `n⁻¹` is not a junk value
    (hn : 0 < n) :
    (stratifiedDesign g mk h).expect (stratifiedEstimator S g) = S.finiteATE := by
  sorry

/-- The population effect is the stratum-size-weighted average of the stratum effects — the
identity that makes the stratified estimator target `τ` (Ding §5.3.1). -/
theorem finiteATE_eq_sum_stratumATE (S : ScienceTable n) (g : Fin n → Fin K)
    (hn : 0 < n) :
    S.finiteATE = ∑ k, (((stratum g k).card : ℝ) / (n : ℝ)) * stratumATE S g k := by
  sorry

end StatLean.CausalInference
