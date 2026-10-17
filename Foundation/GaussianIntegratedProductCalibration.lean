import Foundation.GaussianPolynomialPredictableProduct
import Foundation.PredictableLeibnizIntegratedCorrection

/-! The actual Bochner Brownian integral equals the ramp isonormal observable,
and calibrates the corrected polynomial product identity. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianIntegratedProductCalibration
open InfiniteGaussian GaussianTimeSpaceHermite GaussianPredictableFull GaussianPredictableAdjoint
open GaussianTimeProductL2 GaussianProductDerivative GaussianHermiteTimeIntegral GaussianHermiteTimeKernel
open PredictableLeibnizIntegratedCorrection IntegratedBrownianStatePrediction
open GaussianPolynomialHeat GaussianPolynomialProcess GaussianPolynomialPredictableProduct
open GaussianPolynomialIto GaussianScalarPolynomialIto PredictableLeibnizCounterexample
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

theorem integratedHermite_one_eq_adjoint (T : ℝ≥0) :
    integratedHermite (fun _ => (1 : ℝ)) 0 T = predictableAdjoint (integratedTerminal T) := by
  apply Subtype.ext
  apply scalarCurry.injective
  rw [integratedHermite_slices (fun x : ℝ => x) (fun _ => (1 : ℝ))
    continuous_id continuous_const (fun _ => hasDerivAt_id _) 0 T]
  apply Lp.ext
  filter_upwards [tailField_coeFn (fun x : ℝ => x) continuous_id 0 T,
    integratedTerminal_adjoint_slices T] with x ht hi
  rw [ht, hi]
  by_cases hx : x ∈ Ioc 0 (T : ℝ)
  · simp only [indicator_of_mem hx, brownianCore_zero_degree]
  · simp [hx]

theorem integratedTerminal_reconstructed (T : ℝ≥0) :
    itoIntegral (predictableAdjoint (integratedTerminal T)) = integratedTerminal T := by
  rw [integratedTerminal_adjoint, GaussianDeterministicIntegral.itoIntegral_deterministic]
  rfl

theorem integrated_core_eq_ramp (T : ℝ≥0) :
    (∫ t in 0..(T : ℝ), (brownianCore t.toNNReal 1 : GaussianL2)) = integratedTerminal T := by
  have he := integral_integratedHermite (fun _ => (1 : ℝ)) continuous_const 0 T
  rw [integratedHermite_one_eq_adjoint, integratedTerminal_reconstructed] at he
  simpa only [Nat.zero_add, Nat.cast_zero, zero_add, Nat.cast_one, inv_one, one_smul] using he.symm

theorem brownianCore_one (t : ℝ≥0) : (brownianCore t 1 : GaussianL2) = GaussianTimeProcess.wienerL2 t := by
  apply Lp.ext
  simpa only [value_one, GaussianTimeProcess.process] using brownianCore_coeFn t 1

theorem bochner_brownian_eq_ramp (T : ℝ≥0) :
    (∫ t in 0..(T : ℝ), GaussianTimeProcess.wienerL2 t.toNNReal) = integratedTerminal T := by
  simpa only [brownianCore_one] using integrated_core_eq_ramp T

theorem linear_value_eq_brownian (t : ℝ≥0) : valueL2 t (X 1) = GaussianTimeProcess.wienerL2 t := by
  apply Lp.ext
  simpa only [eval_X, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.succ_eq_add_one,
    Fin.isValue, GaussianTimeProcess.process] using valueL2_coeFn t (X 1)

theorem timeIntegral_linear_eq_ramp (T : ℝ≥0) : timeIntegral T (X 1) = integratedTerminal T := by
  change (∫ t in 0..(T : ℝ), valueL2 t.toNNReal (X 1)) = _
  simpa only [linear_value_eq_brownian] using bochner_brownian_eq_ramp T

def quadraticHeat (T : ℝ≥0) : SpaceTimePolynomial := hermite 2 + C (T : ℝ)

theorem quadraticHeat_heat (T : ℝ≥0) : heat (quadraticHeat T) = 0 := by
  rw [quadraticHeat, map_add, hermite_heat]
  simp [heat_apply]

theorem quadraticHeat_terminal (T : ℝ≥0) :
    valueL2 T (quadraticHeat T) =ᵐ[gaussianProduct] fun ω => (GaussianTimeProcess.process T ω)^2 := by
  have hh : hermite 2 = X 1^2 - X 0 := by simp [hermite_succ, GaussianPolynomialHeat.raise, pow_two]
  filter_upwards [valueL2_coeFn T (quadraticHeat T)] with ω hω
  rw [hω]
  simp [quadraticHeat, hh]

theorem cubic_crossGradientIntegral (T : ℝ≥0) :
    crossGradientIntegral T (quadraticHeat T) (hermite 1) = (2 : ℝ) • integratedTerminal T := by
  have hd : pderiv 1 (hermite 2) = (2 : ℝ) • hermite 1 := by
    convert hermite_spatial 1 using 1 <;> norm_num
  unfold crossGradientIntegral
  simp only [quadraticHeat, map_add, pderiv_C, add_zero, hd]
  have hq : pderiv 1 (hermite 1) = 1 := by simp
  rw [hq, mul_one, map_smul, hermite_one, timeIntegral_linear_eq_ramp]

theorem cubic_defect_eq_actual_crossGradient (T : ℝ≥0) :
    PredictableLeibnizCounterexample.cubicAdjoint T -
      PredictableLeibnizCounterexample.conditionalLeibnizCandidate T =
      scalarCurry (predictableAdjoint (crossGradientIntegral T (quadraticHeat T) (hermite 1)) :
        TimeProbabilityL2) := by
  rw [cubic_crossGradientIntegral, map_smul]
  change _ = scalarCurry ((2 : ℝ) • (predictableAdjoint (integratedTerminal T) : TimeProbabilityL2))
  rw [map_smul]
  exact cubic_defect_eq_integrated_adjoint T

theorem terminal_product_eq_cubic (T : ℝ≥0) :
    valueL2 T (quadraticHeat T * hermite 1) = polynomialValue T (Polynomial.X^3) := by
  apply Lp.ext
  filter_upwards [terminal_product_coeFn T (quadraticHeat T) (hermite 1), quadraticHeat_terminal T,
    valueL2_coeFn T (hermite 1), polynomialValue_coeFn T (Polynomial.X^3)] with ω hp hq hx hc
  rw [hp, hq, hx, hc]
  simp only [hermite_one, eval_X, Matrix.cons_val_one, Matrix.cons_val_zero,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem product_spatial_eq_original_candidate (T : ℝ≥0) :
    spatialField T (quadraticHeat T * hermite 1) = conditionalLeibnizCandidate T := by
  have he := corrected_heat_product T (quadraticHeat T) (hermite 1)
    (quadraticHeat_heat T) (hermite_heat 1)
  rw [terminal_product_eq_cubic, cubic_crossGradientIntegral, map_smul] at he
  change cubicAdjoint T = spatialField T (quadraticHeat T * hermite 1) +
    scalarCurry ((2 : ℝ) • (predictableAdjoint (integratedTerminal T) : TimeProbabilityL2)) at he
  rw [map_smul] at he
  have hc := cubic_defect_eq_integrated_adjoint T
  linear_combination (norm := module) hc - he

theorem calibrated_cubic_product_representer (T : ℝ≥0) :
    ∃! U : fullPredictable, scalarCurry (U : TimeProbabilityL2) = conditionalLeibnizCandidate T ∧
      predictableAdjoint (polynomialValue T (Polynomial.X^3)) =
        U + (2 : ℝ) • predictableAdjoint (integratedTerminal T) := by
  have he := corrected_heat_product_representer T (quadraticHeat T) (hermite 1)
    (quadraticHeat_heat T) (hermite_heat 1)
  simpa only [terminal_product_eq_cubic, product_spatial_eq_original_candidate,
    cubic_crossGradientIntegral, map_smul] using he
end OperatorDerivativeRewrite.Foundation.GaussianIntegratedProductCalibration
