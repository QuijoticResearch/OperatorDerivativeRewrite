import Foundation.BrownianWeightedPredictableIntegral
import Foundation.BrownianVolatilitySquareDefect
import Foundation.GaussianHermiteMartingale

/-! The actual weighted integral adjoint and the corrected stochastic-volatility square. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianWeightedSquareAdjoint
open InfiniteGaussian GaussianPredictableFull GaussianPredictableCutoff
open GaussianTimeSpaceHermite GaussianHermiteRepresentation GaussianHermiteMartingale
open BrownianClockWeightedEnergy BrownianWeightedPredictableIntegral BrownianVolatilitySquare

local instance (T : ℝ≥0) : CompleteSpace (domain T) := (domain_isClosed T).completeSpace_coe

def adjoint (T : ℝ≥0) : GaussianL2 →L[ℝ] domain T := (integral T).toContinuousLinearMap.adjoint

theorem adjoint_integral (T : ℝ≥0) (u : domain T) : adjoint T (integral T u) = u :=
  congrArg (fun L : domain T →L[ℝ] domain T => L u) (integral T).adjoint_comp_self

theorem adjoint_one (T : ℝ≥0) : adjoint T gaussianOne = 0 := by
  apply ext_inner_right ℝ
  intro u
  change inner ℝ ((integral T).toContinuousLinearMap.adjoint gaussianOne) u = inner ℝ 0 u
  rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left,
    gaussianOne_inner_eq_integral]
  exact integral_centered T u

def driverCoefficient (T : ℝ≥0) : domain T := pullback T (hermiteIntegrand 1 T)

theorem driver_representation (T : ℝ≥0) : integral T (driverCoefficient T) = driver T := by
  rw [driverCoefficient, integral_pullback, cut_hermiteIntegrand, min_self, driver_integral]

theorem adjoint_driver (T : ℝ≥0) : adjoint T (driver T) = driverCoefficient T := by
  rw [← driver_representation, adjoint_integral]

def squareCoefficient (T : ℝ≥0) : domain T := pullback T (correct T)

theorem cut_correct (T : ℝ≥0) : predictableCut T (correct T) = correct T := by
  rw [correct, map_add, map_smul, cut_hermiteIntegrand, cut_hermiteIntegrand, min_self]

theorem square_representation (T : ℝ≥0) :
    integral T (squareCoefficient T) = terminalSquare T - ((T : ℝ)^2/2) • gaussianOne := by
  rw [squareCoefficient, integral_pullback, cut_correct, corrected_representation]

theorem adjoint_square (T : ℝ≥0) : adjoint T (terminalSquare T) = squareCoefficient T := by
  have h := congrArg (adjoint T) (square_representation T)
  rw [adjoint_integral, map_sub, map_smul, adjoint_one, smul_zero, sub_zero] at h
  exact h.symm

end OperatorDerivativeRewrite.Foundation.BrownianWeightedSquareAdjoint
