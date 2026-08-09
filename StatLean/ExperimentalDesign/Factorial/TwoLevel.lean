import Mathlib.Order.SymmDiff
import StatLean.ExperimentalDesign.Core.Contrast

/-!
# Two-level factorial structure: the ±1 character algebra

A `2^k` factorial experiment indexes its treatment combinations by the level vectors
`x ∈ {−1,+1}^k` (encoded here as `x : ι → Bool` with sign map `true ↦ +1`,
`false ↦ −1`, over an arbitrary finite factor index `ι`).  Every factorial effect —
main effect or interaction — is carried by a **character**
$$\chi_S(x) = \prod_{j \in S} \operatorname{sign}(x_j), \qquad S \subseteq \iota,$$
and the whole `2^k` effect calculus is the orthogonality relation
$$\sum_{x} \chi_S(x)\, \chi_{S'}(x) = \begin{cases} 2^k, & S = S' \\ 0, & S \ne S'
\end{cases}$$
together with its consequences: the **factorial expansion** of any response function
`y` on the treatment combinations,
$$y(x) = \sum_{S} \widehat y(S)\, \chi_S(x), \qquad
  \widehat y(S) = 2^{-k} \sum_x y(x) \chi_S(x),$$
uniqueness of the coefficients, and the Parseval identity
`∑ₓ y(x)² = 2^k ∑_S ŷ(S)²`.  Nonempty-set characters are treatment contrasts,
linking the factorial calculus to the contrast algebra of `Core/Contrast`.

## Main results

* `levelSign`, `character` — the sign map and the characters.
* `character_mul` — multiplicativity: `χ_S χ_T = χ_{S Δ T}` (Mead's product rule for
  effect rows).
* `sum_character_eq_zero`, `sum_character_mul` — character orthogonality.
* `factorialCoeff`, `factorialExpansion`, `factorialCoeff_eq_of_expansion` — the
  expansion and its uniqueness.
* `factorialParseval` — the sum-of-squares decomposition.
* `characterContrast` — nonempty characters as treatment contrasts.

**Reference.** R. Mead, *The Design of Experiments*, CUP, 1988, §13.1–§13.3: the
`±1` effect matrix `U` whose "elements are all ±1 and the rows are orthogonal", the
product rule "the elements of the PQ row are obtained by multiplying the
corresponding elements in the rows for P and Q", and the general `m`-factor effect
formula `effect = (1/2^{m−1})(p ± 1)(q ± 1)⋯`; the confounding calculus built on the
same characters is §16.2.  (`Mead §13.1`, `Mead §16.2`.)

**Scaling deviation from the book.** Mead normalises effects by `1/2^{m−1}` (and the
overall mean by `1/2^m`); our `factorialCoeff` uniformly uses `2^{−k}`, so a Mead
effect equals `2 · factorialCoeff` for nonempty `S` and the mean is
`factorialCoeff ∅`.  The uniform normalisation is what makes the expansion,
uniqueness and Parseval statements clean; the docstrings of consumers should convert.

**Proof formalization notes.**
* `character_mul` is the `∏` computation over `S ∆ T` (squares of signs cancel on
  `S ∩ T`); stated with `symmDiff` to avoid notation ambiguity.
* `sum_character_eq_zero` factors out one coordinate `j₀ ∈ S` and pairs `x` with its
  `j₀`-flip; equivalently, induct via `Fintype.sum_prod_type`-style splitting of the
  Boolean cube.  `sum_character_mul` is then `character_mul` plus the vanishing sum,
  with `symmDiff S T = ∅ ↔ S = T`.
* The expansion/uniqueness/Parseval block is finite Fourier inversion on
  `(ZMod 2)^ι` in elementary clothing; everything is a double-sum swap plus
  orthogonality.  `Fintype.card_fun` gives `|ι → Bool| = 2^k`.
-/

namespace StatLean.ExperimentalDesign

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **sign encoding** of a two-level factor: `true ↦ +1`, `false ↦ −1`
(`Mead §13.1`, the ±1 coding of upper/lower levels). -/
def levelSign (b : Bool) : ℝ := if b then 1 else -1

/-- The **character** of a set `S` of factors: `χ_S(x) = ∏_{j ∈ S} sign(x j)` — the
±1 row of the effect matrix indexed by the effect `S` (`Mead §13.1`). -/
noncomputable def character (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ j ∈ S, levelSign (x j)

@[simp]
theorem character_empty (x : ι → Bool) : character (∅ : Finset ι) x = 1 := by
  sorry

/-- Characters square to one pointwise. -/
theorem character_mul_self (S : Finset ι) (x : ι → Bool) :
    character S x * character S x = 1 := by
  sorry

/-- **Multiplicativity**: `χ_S · χ_T = χ_{S Δ T}` — Mead's product rule for effect
rows (`Mead §13.1`; the group law behind confounding, `Mead §16.2`). -/
theorem character_mul (S T : Finset ι) (x : ι → Bool) :
    character S x * character T x = character (symmDiff S T) x := by
  sorry

/-- A nonempty-set character sums to zero over the treatment combinations. -/
theorem sum_character_eq_zero {S : Finset ι}
    -- LEAN-ONLY: nonempty effect set; the empty character sums to `2^k`
    (hS : S.Nonempty) :
    ∑ x : ι → Bool, character S x = 0 := by
  sorry

/-- **Character orthogonality** (`Mead §13.1`, orthogonality of the rows of the
effect matrix): `∑ₓ χ_S(x) χ_T(x)` is `2^k` for `S = T` and `0` otherwise. -/
theorem sum_character_mul (S T : Finset ι) :
    ∑ x : ι → Bool, character S x * character T x
      = if S = T then (2 : ℝ) ^ Fintype.card ι else 0 := by
  sorry

/-- The **factorial coefficient** of a response function at the effect `S`:
`ŷ(S) = 2^{−k} ∑ₓ y(x) χ_S(x)`.  Equals half the Mead effect for nonempty `S` and
the overall mean for `S = ∅` (see the module docstring for the scaling). -/
noncomputable def factorialCoeff (y : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ x, y x * character S x

/-- **The factorial expansion** (`Mead §13.1`, the effect representation `y = Ux` in
matrix form): every response function is the character sum of its factorial
coefficients. -/
theorem factorialExpansion (y : (ι → Bool) → ℝ) (x : ι → Bool) :
    y x = ∑ S : Finset ι, factorialCoeff y S * character S x := by
  sorry

/-- **Uniqueness of the factorial coefficients**: any coefficient family reproducing
`y` through the character expansion is the family of factorial coefficients. -/
theorem factorialCoeff_eq_of_expansion (y : (ι → Bool) → ℝ) (c : Finset ι → ℝ)
    -- USER-INPUT: a character representation of the response; Mead §13.1
    (h : ∀ x, y x = ∑ S : Finset ι, c S * character S x) (S : Finset ι) :
    c S = factorialCoeff y S := by
  sorry

/-- **Parseval for the factorial expansion**: `∑ₓ y(x)² = 2^k ∑_S ŷ(S)²` — the exact
sum-of-squares decomposition of a `2^k` response into effect components
(`Mead §13.1`, the component SS of the effects). -/
theorem factorialParseval (y : (ι → Bool) → ℝ) :
    ∑ x, y x ^ 2
      = (2 : ℝ) ^ Fintype.card ι * ∑ S : Finset ι, factorialCoeff y S ^ 2 := by
  sorry

/-- A nonempty-set character, viewed as a **treatment contrast** on the treatment
combinations (`Mead §13.3`: factorial effects are contrasts). -/
noncomputable def characterContrast {S : Finset ι} (hS : S.Nonempty) :
    Contrast (ι → Bool) :=
  ⟨character S, by sorry⟩

end StatLean.ExperimentalDesign
