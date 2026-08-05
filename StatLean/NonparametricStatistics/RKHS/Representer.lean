import StatLean.NonparametricStatistics.RKHS.Basic

/-!
# The representer theorem

Regularized empirical risk minimization over an RKHS:
`J(f) = W(‖f‖²) + L(f(x₁), …, f(xₙ))`, with `W` increasing and `L` depending only on
the values at the data points.

* **Representer theorem**: if `W` is *strictly* increasing, every minimizer of `J` lies
  in `span {k_{x₁}, …, k_{xₙ}}` — the problem is intrinsically finite-dimensional.
  (For merely monotone `W`, the orthogonal projection of a minimizer onto the span is
  again a minimizer with the same data values.)
* **Existence and uniqueness** for the ridge form `J(f) = ‖f‖² + L(...)` with `L`
  convex and continuous: the parallelogram law gives uniqueness, and coercivity via an
  affine minorant of `L` gives existence.

**Bibliographic comments.** G. Kimeldorf and G. Wahba, *Some results on Tchebycheffian
spline functions*, J. Math. Anal. Appl. **33** (1971), 82–95; the general form with an
arbitrary increasing regularizer is due to B. Schölkopf, R. Herbrich and A. J. Smola,
*A generalized representer theorem*, COLT (2001).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]
variable {n : ℕ}

/-- The span of the kernel functions at the data points — the finite-dimensional
subspace in which representer solutions live. -/
def dataSpan (x : Fin n → X) : Submodule 𝕜 H :=
  Submodule.span 𝕜 (Set.range fun i => kernelFun H (x i))

instance (x : Fin n → X) : FiniteDimensional 𝕜 (dataSpan (H := H) x) := by
  unfold dataSpan
  exact FiniteDimensional.span_of_finite 𝕜 (Set.finite_range fun i => kernelFun H (x i))

instance (x : Fin n → X) : CompleteSpace (dataSpan (H := H) x) :=
  FiniteDimensional.complete 𝕜 _

instance (x : Fin n → X) : (dataSpan (H := H) x).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- Functions orthogonal to the data span vanish at the data points. -/
theorem apply_eq_zero_of_mem_dataSpan_orthogonal {x : Fin n → X} {h : H}
    (hh : h ∈ (dataSpan x)ᗮ) (i : Fin n) : h (x i) = 0 := by
  sorry

/-- Projecting onto the data span preserves the data values. -/
theorem starProjection_dataSpan_apply {x : Fin n → X} (f : H) (i : Fin n) :
    ((dataSpan x).starProjection f) (x i) = f (x i) := by
  sorry

/-- **The representer theorem**: for `W` strictly increasing and any data-dependent loss
`L`, every minimizer of `f ↦ W(‖f‖²) + L(f ∘ x)` lies in the span of the kernel
functions of the data points. -/
theorem representer_mem_dataSpan (x : Fin n → X) (W : ℝ → ℝ)
    -- USER-INPUT: strictly increasing regularizer
    (hW : StrictMono W)
    (L : (Fin n → 𝕜) → ℝ) (f₀ : H)
    -- USER-INPUT: `f₀` minimizes the regularized empirical risk
    (hmin : ∀ f : H, W (‖f₀‖ ^ 2) + L (fun i => f₀ (x i))
      ≤ W (‖f‖ ^ 2) + L (fun i => f (x i))) :
    f₀ ∈ dataSpan x := by
  sorry

/-- Representer theorem, weak (monotone) form: the projection of a minimizer onto the
data span is again a minimizer. -/
theorem representer_starProjection_isMin (x : Fin n → X) (W : ℝ → ℝ)
    -- USER-INPUT: monotone regularizer
    (hW : Monotone W)
    (L : (Fin n → 𝕜) → ℝ) (f₀ : H)
    -- USER-INPUT: `f₀` minimizes the regularized empirical risk
    (hmin : ∀ f : H, W (‖f₀‖ ^ 2) + L (fun i => f₀ (x i))
      ≤ W (‖f‖ ^ 2) + L (fun i => f (x i))) :
    ∀ f : H, W (‖(dataSpan x).starProjection f₀‖ ^ 2)
        + L (fun i => ((dataSpan x).starProjection f₀) (x i))
      ≤ W (‖f‖ ^ 2) + L (fun i => f (x i)) := by
  sorry

/-- **Existence and uniqueness for convex ridge losses**: with the regularizer `‖f‖²`
and `L` convex, the regularized empirical risk has a unique minimizer.  (Continuity of
`L` on the finite-dimensional value space is automatic from convexity.) -/
theorem representer_existsUnique_of_convex (x : Fin n → X) (L : (Fin n → 𝕜) → ℝ)
    -- USER-INPUT: convex loss (in the data values, over the real structure)
    (hL : ConvexOn ℝ Set.univ L) :
    ∃! f₀ : H, ∀ f : H, ‖f₀‖ ^ 2 + L (fun i => f₀ (x i))
      ≤ ‖f‖ ^ 2 + L (fun i => f (x i)) := by
  sorry

/-- The hinge loss `v ↦ ∑ᵢ max(0, 1 − λᵢ·vᵢ)` of the soft-margin classifier is convex,
so the soft-margin problem has a unique solution in the data span. -/
theorem convexOn_hinge (lab : Fin n → ℝ) :
    ConvexOn ℝ Set.univ fun v : Fin n → ℝ => ∑ i, max 0 (1 - lab i * v i) := by
  sorry

end StatLean.NonparametricStatistics
