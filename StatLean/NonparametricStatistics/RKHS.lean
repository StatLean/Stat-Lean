import StatLean.NonparametricStatistics.RKHS.Basic
import StatLean.NonparametricStatistics.RKHS.KernelFunction
import StatLean.NonparametricStatistics.RKHS.OrthonormalExpansion
import StatLean.NonparametricStatistics.RKHS.Subspace
import StatLean.NonparametricStatistics.RKHS.Continuity
import StatLean.NonparametricStatistics.RKHS.ParsevalFrame
import StatLean.NonparametricStatistics.RKHS.Papadakis
import StatLean.NonparametricStatistics.RKHS.Moore
import StatLean.NonparametricStatistics.RKHS.Uniqueness
import StatLean.NonparametricStatistics.RKHS.RankOne
import StatLean.NonparametricStatistics.RKHS.InnerKernel
import StatLean.NonparametricStatistics.RKHS.MinKernel
import StatLean.NonparametricStatistics.RKHS.Sobolev
import StatLean.NonparametricStatistics.RKHS.FeatureMap
import StatLean.NonparametricStatistics.RKHS.Separation
import StatLean.NonparametricStatistics.RKHS.MaxMargin
import StatLean.NonparametricStatistics.RKHS.Representer
import StatLean.NonparametricStatistics.RKHS.IntegralOperator
import StatLean.NonparametricStatistics.RKHS.RangeSpace
import StatLean.NonparametricStatistics.RKHS.Mercer.Defs
import StatLean.NonparametricStatistics.RKHS.Mercer.OperatorLemmas
import StatLean.NonparametricStatistics.RKHS.Mercer.Basic
import StatLean.NonparametricStatistics.RKHS.Mercer.Compact
import StatLean.NonparametricStatistics.RKHS.Mercer.Theorem
import StatLean.NonparametricStatistics.RKHS.Mercer.SquareRoot

/-!
# Reproducing kernel Hilbert spaces

Umbrella module for the RKHS cluster of the nonparametric-statistics area: scalar RKHS
theory over Mathlib's `RKHS` class, kernel functions and Moore's theorem, Parseval
frames, the Sobolev and min-kernel examples, feature maps / maximal margin / representer
theorems, integral operators and range spaces, and Mercer theory.
-/
