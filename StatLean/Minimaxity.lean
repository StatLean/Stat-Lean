import StatLean.Minimaxity.Defs

/-!
# Minimaxity — area umbrella

Minimax lower bounds, formalized from Wainwright, *High-Dimensional Statistics:
A Non-Asymptotic Viewpoint* (Cambridge University Press, 2019), Chapter 15.

The area develops, on top of Mathlib's decision-theoretic risk framework
(`ProbabilityTheory.minimaxRisk` / `bayesRisk`):

* **Core (`Defs`)**: Wainwright's minimax risk `M(θ(𝒫); Φ∘ρ)`, the M-ary testing
  error, the mixture distribution, and `2δ`-separated families.
* **Divergences (`ForMathlib/`)**: total variation, Kullback–Leibler (bridged to
  Mathlib `klDiv`), squared Hellinger (bridged to the StatLean Hellinger-product
  tensorization), Shannon/conditional entropy, Fano's inequality, with the
  Pinsker (Lemma 15.2) and Le Cam (Lemma 15.3) comparison inequalities; plus the
  Chapter-5 metric-entropy bricks (Hamming / sphere / sparse packing, Sobolev entropy).
* **Estimation → testing (`EstimationToTesting`)**: Proposition 15.1.
* **Le Cam's method (`LeCam/`)**: the two-point bound (Eq. (15.14)), the functional
  modulus form (Corollary 15.6), and the convex-hull bound (Lemma 15.9).
* **Fano's method (`Fano/`)**: mutual information, the Fano lower bound (Prop. 15.12),
  the local-packing proposition (§15.3.3), and the Yang–Barron bound (Lemma 15.21).
* **Examples (`Examples/`)**: the worked minimax-rate calculations of §15.2–15.3.

Modules are imported below as each lands.
-/

