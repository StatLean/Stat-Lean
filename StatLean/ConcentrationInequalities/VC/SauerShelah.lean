import StatLean.ConcentrationInequalities.VC.Defs
import StatLean.ConcentrationInequalities.ForMathlib.BinomialSumBound
import Mathlib.Combinatorics.SetFamily.Shatter

/-!
# Pajor and Sauer–Shelah lemmas for set-encoded classes

For a class $\mathcal{C} \subseteq \mathcal{P}(\Omega)$ with VC dimension at
most $d$ and any finite $\Lambda \subseteq \Omega$ with $|\Lambda| \le n$,
$$ \bigl|\mathcal{C}|_\Lambda\bigr|
   \;\le\; \#\{T \subseteq \Lambda : \mathcal{C} \text{ shatters } T\}
   \;\le\; \sum_{k=0}^{d} \binom{|\Lambda|}{k}
   \;\le\; \Bigl(\frac{e\,n}{d}\Bigr)^{d}, $$
together with the growth-function bounds
$2^{d} \le \Pi_{\mathcal{C}}(n) \le \sum_{k \le d} \binom{n}{k}$ of
Eq. (8.30).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.2 Lemma 8.3.7 (Pajor), §8.3.3 Lemma 8.3.9
(Sauer–Shelah), §8.3.4 Eq. (8.30) (growth-function bounds).

**Proof formalization notes.** Maximal Mathlib reuse: Pajor's lemma is
`Finset.card_le_card_shatterer` on the `traceFamily` bridge
(`shatters_traceFamily_iff` identifies Mathlib's `Finset.Shatters` of the
trace family with our set-level `Shatters` — beware, `Finset.Shatters` and
our `Shatters` coexist in scope, so Mathlib's must stay dot- or fully
qualified). Mathlib's `Finset.card_shatterer_le_sum_vcDim` requires
`[Fintype Ω]` and is unusable for `Ω = ℝⁿ`; instead we count Λ-relatively:
every trace-shattered `T` is `C`-shattered (hence `T.card ≤ d`) and `T ⊆ Λ`,
so `Finset.card_powersetCard` bounds the count by `∑_{k ≤ d} C(|Λ|, k)`.
The closed form is `sum_choose_le_exp_mul_pow`
(`ForMathlib/BinomialSumBound.lean`). Constants are the book's exactly.
Edge/degenerate behavior: `two_pow_le_growthFunction` needs `[Infinite Ω]`
and attainment of the `ℕ∞`-valued `vcDim` (`exists_shatters_card_eq`) —
nothing downstream consumes it, so it is this file's allowed named-sorry
fallback together with `pajor` decorations; the one lemma Theorem 8.3.13
needs is `card_traceFamily_le_sum_choose`.

**Bibliographic comments.** The counting lemma was found independently by
V. N. Vapnik and A. Ya. Chervonenkis (*Theory Probab. Appl.* 16 (1971),
264–280), N. Sauer (*J. Combin. Theory Ser. A* 13 (1972), 145–147), and
S. Shelah (*Pacific J. Math.* 41 (1972), 247–261). The sharper
"count shattered sets" form is due to A. Pajor, *Sous-espaces $\ell_1^n$ des
espaces de Banach*, Hermann, Paris, 1985; see HDP §8.3 Notes.
-/

open Finset

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*}

/-- Bridge between Mathlib's `Finset.Shatters` of the trace family and our
set-level `Shatters` (LEAN-ONLY: encoding bridge, no book content). -/
lemma shatters_traceFamily_iff [DecidableEq Ω] {C : Set (Set Ω)}
    {Λ Λ' : Finset Ω}
    -- LEAN-ONLY: the trace is only faithful on subsets of Λ; encoding-side
    -- condition, no scope change.
    (h : Λ' ⊆ Λ) :
    (traceFamily C Λ).Shatters Λ' ↔ Shatters C Λ' := by
  sorry

open Classical in
/-- **Pajor's lemma** (HDP §8.3.2, Lemma 8.3.7): the trace family has at most
as many members as there are subsets of `Λ` shattered by `C`. Via
`Finset.card_le_card_shatterer` and the `shatters_traceFamily_iff` bridge. -/
theorem pajor [DecidableEq Ω] (C : Set (Set Ω)) (Λ : Finset Ω) :
    (traceFamily C Λ).card ≤ (Λ.powerset.filter fun T => Shatters C T).card := by
  sorry

/-- **Sauer–Shelah, binomial form** (HDP §8.3.3, Lemma 8.3.9, first
inequality): `|C|_Λ| ≤ ∑_{k ≤ d} C(|Λ|, k)` when `vc(C) ≤ d`. Pajor + (every
shattered set has card ≤ d) + `Finset.card_powersetCard`. -/
theorem card_traceFamily_le_sum_choose {C : Set (Set Ω)} {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.3, Lemma 8.3.9.
    (hd : vcDim C ≤ (d : ℕ∞)) (Λ : Finset Ω) :
    (traceFamily C Λ).card ≤ ∑ k ∈ Finset.Iic d, Λ.card.choose k := by
  sorry

/-- **Sauer–Shelah, closed form** (HDP §8.3.3, Lemma 8.3.9, second
inequality): `|C|_Λ| ≤ (e·n/d)^d` for `|Λ| ≤ n`, via
`sum_choose_le_exp_mul_pow` and monotonicity of `Nat.choose` in `n`. -/
theorem card_traceFamily_le_pow {C : Set (Set Ω)} {d n : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.3, Lemma 8.3.9.
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d (nondegenerate dimension); HDP Exercise 0.6 regime.
    (hd1 : 1 ≤ d) {Λ : Finset Ω}
    -- USER-INPUT: sample-size bound |Λ| ≤ n; HDP §8.3.3, Lemma 8.3.9.
    (hΛ : Λ.card ≤ n)
    -- USER-INPUT: d ≤ n (the closed form's regime); HDP Exercise 0.6.
    (hdn : d ≤ n) :
    ((traceFamily C Λ).card : ℝ) ≤ (Real.exp 1 * n / d) ^ d := by
  sorry

/-- Growth-function upper bound (HDP §8.3.4, Eq. (8.30), right inequality,
`ℕ∞` form): `Π_C(n) ≤ ∑_{k ≤ d} C(n, k)` when `vc(C) ≤ d`. -/
theorem growthFunction_le_sum_choose {C : Set (Set Ω)} {d n : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.4, Eq. (8.30).
    (hd : vcDim C ≤ (d : ℕ∞)) :
    growthFunction C n ≤ ((∑ k ∈ Finset.Iic d, n.choose k : ℕ) : ℕ∞) := by
  sorry

/-- Attainment of the `ℕ∞`-valued `vcDim` supremum at a finite value
(LEAN-ONLY: `iSup` attainment in `ℕ∞`, no book content). -/
theorem exists_shatters_card_eq {C : Set (Set Ω)} {d : ℕ}
    -- LEAN-ONLY: a nonempty class shatters ∅, so the iSup ranges over a
    -- nonempty family; no scope change.
    (hC : C.Nonempty)
    -- USER-INPUT: exact finite VC dimension; HDP §8.3.4, Eq. (8.30).
    (hd : vcDim C = (d : ℕ∞)) :
    ∃ Λ : Finset Ω, Shatters C Λ ∧ Λ.card = d := by
  sorry

/-- Growth-function lower bound (HDP §8.3.4, Eq. (8.30), left inequality):
`2^d ≤ Π_C(n)` for `n ≥ d = vc(C)`. Decorative for downstream (nothing
consumes it); allowed to degrade to a named sorry. -/
theorem two_pow_le_growthFunction [Infinite Ω] {C : Set (Set Ω)} {d n : ℕ}
    -- LEAN-ONLY: nonempty class so a shattered d-set exists; no scope change.
    (hC : C.Nonempty)
    -- USER-INPUT: exact finite VC dimension; HDP §8.3.4, Eq. (8.30).
    (hd : vcDim C = (d : ℕ∞))
    -- USER-INPUT: n ≥ d so a shattered d-set extends to an n-point set;
    -- HDP §8.3.4, Eq. (8.30). ([Infinite Ω] is LEAN-ONLY: an n-point
    -- superset must exist inside Ω.)
    (hn : d ≤ n) :
    (2 ^ d : ℕ∞) ≤ growthFunction C n := by
  sorry

end StatLean.ConcentrationInequalities
