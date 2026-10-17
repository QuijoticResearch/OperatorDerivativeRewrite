import Foundation.GaussianCubicDiagnostic
import Foundation.GaussianHermiteMartingale

/-! A Brownian cubic diagnostic for the conditional Leibniz formula proposed
in the risk-neutral-memory manuscript. The predictable adjoint is bounded. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PredictableLeibnizCounterexample
open InfiniteGaussian GaussianPredictableFull GaussianPredictableAdjoint GaussianTimeProductL2
open GaussianProductDerivative GaussianPolynomialIto
open GaussianConditionalIto GaussianHermiteMartingale GaussianTimeSpaceHermite
open GaussianHermiteRepresentation GaussianHermiteIntegrand
open GaussianCubicDiagnostic GaussianScalarPolynomialIto GaussianPolynomialProcess GaussianPolynomialDifferentiation
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

theorem predictableAdjoint_norm_le_one : ‖predictableAdjoint‖ ≤ 1 := by
  rw [predictableAdjoint, ContinuousLinearMap.adjoint.norm_map]
  exact itoIntegral.norm_toContinuousLinearMap_le

theorem square_expansion (T : ℝ≥0) : polynomialValue T (Polynomial.X^2) =
    (brownianCore T 2 : GaussianL2) + (T : ℝ) • gaussianOne := by
  apply Lp.ext
  filter_upwards [polynomialValue_coeFn T (Polynomial.X^2), brownianCore_coeFn T 2,
    gaussianOne_coeFn, Lp.coeFn_add (brownianCore T 2 : GaussianL2) ((T : ℝ) • gaussianOne),
    Lp.coeFn_smul (T : ℝ) gaussianOne] with ω hp h2 h1 ha hs
  rw [hp, ha, Pi.add_apply, hs, Pi.smul_apply, h2, h1]
  simp only [value_two, Polynomial.eval_pow, Polynomial.eval_X, smul_eq_mul]
  ring

theorem conditional_square (S T : ℝ≥0) (hST : S ≤ T) :
    pastProjection S (polynomialValue T (Polynomial.X^2)) =
      polynomialValue S (Polynomial.X^2) + ((T : ℝ)-S) • gaussianOne := by
  have h1 : pastProjection S gaussianOne = gaussianOne := by
    have h := pastProjection_brownianCore 0 S T
    simpa only [brownianCore_zero_degree] using h
  rw [square_expansion, map_add, map_smul, pastProjection_brownianCore, min_eq_left hST,
    h1, square_expansion]
  module

theorem predictableAdjoint_square (T : ℝ≥0) :
    predictableAdjoint (polynomialValue T (Polynomial.X^2)) = (2 : ℝ) • hermiteIntegrand 1 T := by
  rw [square_expansion, map_add, GaussianQuadraticCylinders.predictableAdjoint_constant, add_zero]
  simp only [hermiteIntegrand, map_smul, smul_smul]
  norm_num

theorem linear_expansion (T : ℝ≥0) : polynomialValue T Polynomial.X = (brownianCore T 1 : GaussianL2) := by
  apply Lp.ext
  filter_upwards [polynomialValue_coeFn T Polynomial.X, brownianCore_coeFn T 1] with ω hp h1
  rw [hp, h1]
  simp only [Polynomial.eval_X, value_one]

theorem conditional_linear (S T : ℝ≥0) (hST : S ≤ T) :
    pastProjection S (polynomialValue T Polynomial.X) = polynomialValue S Polynomial.X := by
  rw [linear_expansion, pastProjection_brownianCore, min_eq_left hST, linear_expansion]

theorem predictableAdjoint_linear (T : ℝ≥0) :
    predictableAdjoint (polynomialValue T Polynomial.X) = hermiteIntegrand 0 T := by
  rw [linear_expansion]
  simp only [hermiteIntegrand]
  norm_num

def cubicAdjoint (T : ℝ≥0) : Lp GaussianL2 2 (volume : Measure ℝ) :=
  scalarCurry (predictableAdjoint (polynomialValue T (Polynomial.X^3)) : TimeProbabilityL2)

def cubicSpatial (T : ℝ≥0) : Lp GaussianL2 2 (volume : Measure ℝ) := spatialField T (spatialPolynomial (Polynomial.X^3))

/-- This class has the explicit slices of the manuscript's conditional product rule
for F=B_T² and G=B_T; the slice identity below identifies that candidate. -/
def conditionalLeibnizCandidate (T : ℝ≥0) : Lp GaussianL2 2 (volume : Measure ℝ) :=
  (1/3 : ℝ) • cubicAdjoint T + (2/3 : ℝ) • cubicSpatial T

theorem candidate_slices (T : ℝ≥0) :
    conditionalLeibnizCandidate T =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator (fun x =>
      (3 : ℝ) • (GaussianTimeSpaceHermite.brownianCore x.toNNReal 2 : GaussianL2) +
        ((T : ℝ) + 2*x) • gaussianOne) := by
  have hC := cubicIntegrand_slices T
  rw [← cubic_predictableAdjoint] at hC
  filter_upwards [hC, spatialField_coeFn T (spatialPolynomial (Polynomial.X^3)),
    Lp.coeFn_add ((1/3 : ℝ) • cubicAdjoint T) ((2/3 : ℝ) • cubicSpatial T),
    Lp.coeFn_smul (1/3 : ℝ) (cubicAdjoint T),
    Lp.coeFn_smul (2/3 : ℝ) (cubicSpatial T)] with x hC hS ha hb hc
  change ((1/3 : ℝ) • cubicAdjoint T + (2/3 : ℝ) • cubicSpatial T) x = _
  rw [ha, Pi.add_apply, hb, hc, Pi.smul_apply, Pi.smul_apply]
  change (1/3 : ℝ) • scalarCurry (predictableAdjoint (polynomialValue T (Polynomial.X^3)) : TimeProbabilityL2) x +
    (2/3 : ℝ) • spatialField T (spatialPolynomial (Polynomial.X^3)) x = _
  rw [hC, hS]
  by_cases hx : x ∈ Ioc 0 (T : ℝ)
  · simp only [indicator_of_mem hx, cubic_spatial_value, Real.coe_toNNReal _ hx.1.le]
    module
  · simp [hx]

/-- The candidate slices use the actual conditional terminal-square value and
the product B_t*(2 B_t), not a substitution of a running derivative for an adjoint. -/
theorem candidate_conditional_slices (T : ℝ≥0) :
    conditionalLeibnizCandidate T =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator (fun x =>
      pastProjection x.toNNReal (polynomialValue T (Polynomial.X^2)) +
        (2 : ℝ) • polynomialValue x.toNNReal (Polynomial.X^2)) := by
  filter_upwards [candidate_slices T] with x hx
  rw [hx]
  by_cases hxt : x ∈ Ioc 0 (T : ℝ)
  · simp only [indicator_of_mem hxt]
    have hST : x.toNNReal ≤ T := by
      apply NNReal.coe_le_coe.mp
      simpa only [Real.coe_toNNReal _ hxt.1.le] using hxt.2
    rw [conditional_square _ _ hST]
    simp only [square_expansion, Real.coe_toNNReal _ hxt.1.le]
    module
  · simp [hxt]

theorem conditional_leibniz_defect_norm_sq (T : ℝ≥0) :
    ‖cubicAdjoint T - conditionalLeibnizCandidate T‖^2 = (4/3 : ℝ) * (T : ℝ)^3 := by
  have he : cubicAdjoint T - conditionalLeibnizCandidate T =
      (2/3 : ℝ) • (cubicAdjoint T - cubicSpatial T) := by
    rw [conditionalLeibnizCandidate]
    module
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  change (2/3 : ℝ)^2 * ‖cubicAdjoint T - cubicSpatial T‖^2 = _
  rw [cubicAdjoint, cubicSpatial, cubic_projection_difference_norm_sq]
  ring

theorem conditional_leibniz_fails_at_one : cubicAdjoint 1 ≠ conditionalLeibnizCandidate 1 := by
  intro h
  have he := conditional_leibniz_defect_norm_sq 1
  rw [h, sub_self, norm_zero] at he
  norm_num at he

end OperatorDerivativeRewrite.Foundation.PredictableLeibnizCounterexample
