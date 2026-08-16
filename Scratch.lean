import StatLean.RobustStatistics

/-!
Tier-0 axiom audit for the RobustStatistics area (Round 1 headliners).
Every line below must report exactly
`[propext, Classical.choice, Quot.sound]` — anything else (in particular
`sorryAx`) means the result rests on unproven content.
-/

open StatLean.RobustStatistics

-- Breakdown: median vs mean, and the MMY (3.26) maximality bound.
#print axioms sampleMedian_breakdownCount
#print axioms sampleMedian_breakdownCount_eq_max
#print axioms sampleMedian_breakdownPoint
#print axioms sampleMedian_resists
#print axioms sampleMedian_breaksUnder
#print axioms locEquivariant_breakdownCount_le
#print axioms sampleMean_breakdownCount
#print axioms sampleMean_breaksUnder_one
#print axioms trimmedMean_breakdownCount
#print axioms trimmedMean_resists
#print axioms trimmedMean_breaksUnder

-- The mean's fragility trilogy.
#print axioms meanFunctional_hasInfluenceAt
#print axioms meanFunctional_influence_unbounded
#print axioms meanFunctional_bias_unbounded
#print axioms meanFunctional_locationEquivariantOn

-- Influence functions: the engine and the Huber instance.
#print axioms mLocationRoot_influence_of_lipschitz
#print axioms mLocationRoot_influence
#print axioms mLocationFunctional_hasInfluenceAt
#print axioms mLocation_influence_bounded
#print axioms huberLocation_influence
#print axioms huberLocation_influence_bounded

-- Population M-functionals: existence, uniqueness, MMY (3.21)/(3.22).
#print axioms exists_isMLocationRoot
#print axioms isMLocationRoot_unique_of_strictMono
#print axioms mLocationRoot_bounded_of_contamination
#print axioms mLocationRoot_contamination_unbounded
#print axioms mLocationRoot_bounded_of_odd
#print axioms huberLocationRoot_bounded

-- Huber loss/score API and the objective ↔ estimating-equation bridge.
#print axioms hasDerivAt_huberRho
#print axioms huberRho_convex
#print axioms abs_huberPsi_le
#print axioms huberPsi_tendsto_atTop
#print axioms isMLocationEstimate_of_score_eq_zero
#print axioms isMLocationEstimate_abs_sampleMedian
#print axioms exists_isMLocationEstimate_huber

-- Scale: MAD.
#print axioms sampleMAD_isDispersionEstimator
#print axioms sampleMAD_add_const
#print axioms sampleMAD_const_mul

-- Contamination algebra.
#print axioms integral_contaminate
#print axioms integral_contaminate_dirac
#print axioms map_contaminate
#print axioms grossErrorNbhd_mono

-- Regression + multivariate.
#print axioms IsMRegressionEstimate.normalEquation
#print axioms quadraticMRegression_normalEquation
#print axioms huberRegression_convex
#print axioms isMRegressionEstimate_regressionEquivariant
#print axioms huberRegression_score_leverage_unbounded
#print axioms meanVecFunctional_affineEquivariant
#print axioms covMatrixFunctional_affineEquivariant

-- Asymptotics (the one place a debt may still live).
#print axioms hasDerivAt_mLocationScore_huber
#print axioms mLocation_consistent
#print axioms huberLocation_consistent
#print axioms huberLocation_asymptoticNormal
