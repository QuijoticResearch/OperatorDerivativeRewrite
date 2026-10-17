import Foundation.GaussianWeightedTimeHermite
import Foundation.GaussianCubicDiagnostic

/-! Exact representation of the square of the actual martingale integral of W against W. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianVolatilitySquare
open InfiniteGaussian GaussianTimeSpaceHermite GaussianHermiteRepresentation
open GaussianHermiteIntegrand GaussianHermiteTimeIntegral GaussianWeightedTimeHermite
open GaussianPredictableFull GaussianPredictableAdjoint GaussianTimeProductL2
open GaussianProductDerivative
open GaussianCubicDiagnostic
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

def driver (T : ℝ≥0) : GaussianL2 := (1/2 : ℝ) • (brownianCore T 2 : GaussianL2)

theorem driver_integral (T : ℝ≥0) : itoIntegral (hermiteIntegrand 1 T) = driver T := by
  rw [integral_hermiteIntegrand]
  norm_num [driver]

def terminalSquare (T : ℝ≥0) : GaussianL2 :=
  (1/4 : ℝ) • (brownianCore T 4 : GaussianL2) +
    (T : ℝ) • (brownianCore T 2 : GaussianL2) + ((T : ℝ)^2/2) • gaussianOne

theorem value_four (x t : ℝ) : value 4 x t = x^4 - 6*t*x^2 + 3*t^2 := by
  rw [value_recursion 2, value_three, value_two]
  norm_num
  ring

theorem terminalSquare_coeFn (T : ℝ≥0) :
    terminalSquare T =ᵐ[gaussianProduct] fun ω => (driver T ω)^2 := by
  have hd : driver T =ᵐ[gaussianProduct] fun ω =>
      (1/2 : ℝ) * value 2 (GaussianTimeProcess.process T ω) T := by
    filter_upwards [Lp.coeFn_smul (1/2 : ℝ) (brownianCore T 2 : GaussianL2),
      brownianCore_coeFn T 2] with ω hs h2
    exact hs.trans (by rw [Pi.smul_apply, h2, smul_eq_mul])
  filter_upwards [hd, brownianCore_coeFn T 4, brownianCore_coeFn T 2, gaussianOne_coeFn,
    Lp.coeFn_add ((1/4 : ℝ) • (brownianCore T 4 : GaussianL2))
      ((T : ℝ) • (brownianCore T 2 : GaussianL2)),
    Lp.coeFn_add ((1/4 : ℝ) • (brownianCore T 4 : GaussianL2) +
      (T : ℝ) • (brownianCore T 2 : GaussianL2)) (((T : ℝ)^2/2) • gaussianOne),
    Lp.coeFn_smul (1/4 : ℝ) (brownianCore T 4 : GaussianL2),
    Lp.coeFn_smul (T : ℝ) (brownianCore T 2 : GaussianL2),
    Lp.coeFn_smul ((T : ℝ)^2/2) gaussianOne] with ω hd h4 h2 h1 ha hb hc he hf
  change (((1/4 : ℝ) • (brownianCore T 4 : GaussianL2) +
    (T : ℝ) • (brownianCore T 2 : GaussianL2)) + ((T : ℝ)^2/2) • gaussianOne) ω = _
  rw [hb, Pi.add_apply, ha, Pi.add_apply, hc, he, hf, hd]
  simp only [Pi.smul_apply, h4, h2, h1, value_four, value_two, smul_eq_mul]
  ring

def correct (T : ℝ≥0) : fullPredictable :=
  hermiteIntegrand 3 T + (2*(T : ℝ)) • hermiteIntegrand 1 T

def candidate (T : ℝ≥0) : fullPredictable :=
  hermiteIntegrand 3 T + (2 : ℝ) • weightedIntegrand (fun t => t) (fun _ => 1) 1 T

def correction (T : ℝ≥0) : fullPredictable :=
  (2 : ℝ) • integratedHermite (fun _ => 1) 1 T

theorem corrected_representation (T : ℝ≥0) :
    itoIntegral (correct T) = terminalSquare T - ((T : ℝ)^2/2) • gaussianOne := by
  rw [correct, map_add, map_smul, integral_hermiteIntegrand, integral_hermiteIntegrand,
    terminalSquare]
  norm_num
  module

theorem correction_identity (T : ℝ≥0) : correct T - candidate T = correction T := by
  unfold correct candidate correction weightedIntegrand
  module

theorem polynomial_candidate (x t : ℝ) :
    value 3 x t + 2*t*value 1 x t = 2*((1/2 : ℝ)*value 2 x t)*x := by
  rw [value_three, value_one, value_two]
  ring

theorem polynomial_correct (x t T : ℝ) :
    value 3 x t + 2*T*value 1 x t =
      (2*((1/2 : ℝ)*value 2 x t)+2*(T-t))*x := by
  rw [value_three, value_one, value_two]
  ring

end OperatorDerivativeRewrite.Foundation.BrownianVolatilitySquare
