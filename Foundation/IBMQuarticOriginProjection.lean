import Foundation.IBMQuarticClockTerminal
import Foundation.ProductL2Equivalence

/-! The actual quartic origin term has the source projection prescribed by
the primitive slope. Its independent clock mass factor is retained. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticOriginProjection
open InfiniteGaussian IBMQuarticSecondPrimitive IBMQuarticSecondChaos
open IBMQuarticSecondGeometry IBMEvenCorrectionProjection IBMGaussianSteinMoments
open GaussianNumberSectors GaussianTimeSpaceHermite

def originClass (n : ℕ) : GaussianL2 :=
  (1/6 : ℝ) • cubeProduct (tripleCoefficient n 0 0) (tripleCoefficient n 0 1)

theorem originClass_coeFn (n : ℕ) : originClass n =ᵐ[gaussianProduct] fun ω =>
    (1/6 : ℝ)*(IBMDyadicExtension.field n 0 ω 0)^3*IBMDyadicExtension.field n 1 ω 0 := by
  filter_upwards [Lp.coeFn_smul (1/6 : ℝ)
    (cubeProduct (tripleCoefficient n 0 0) (tripleCoefficient n 0 1)),
    cubeProduct_coeFn (tripleCoefficient n 0 0) (tripleCoefficient n 0 1),
    IBMDyadicExtension.field_coordinate_ae n 0 0,
    IBMDyadicExtension.field_coordinate_ae n 1 0] with ω hs hc h0 h1
  rw [originClass, hs, Pi.smul_apply, hc, h0, h1,
    gaussianTriple_eq_firstChaos, gaussianTriple_eq_firstChaos]
  simp only [smul_eq_mul]
  ring

theorem origin_projection (n : ℕ) : projection 2 (originClass n) = IBMQuarticSecondPrimitive.slope n 0 := by
  rw [originClass, map_smul, cubeProduct_projection_two, IBMQuarticSecondPrimitive.slope,
    ← coefficient_variance, ← coefficient_slope]
  module

theorem origin_projection_zero_slope (n : ℕ) : projection 2 (originClass n) =
    (IBMVarianceClockGeometry.variance n 0 / 2) •
      cross (tripleCoefficient n 0 0) (tripleCoefficient n 0 1) := by
  rw [origin_projection, IBMQuarticSecondPrimitive.slope, IBMVarianceClockGeometry.slope_zero]
  module

def projectedOriginJoint (n : ℕ) (T : ℝ≥0) : Lp ℝ 2 IBMSourceLaws.jointMeasure :=
  ProductL2Curry.productTensor gaussianProduct gaussianProduct
    (projection 2 (originClass n)) (BrownianMassLimitIdentification.coordinateClass T)

theorem projectedOriginJoint_coeFn (n : ℕ) (T : ℝ≥0) :
    projectedOriginJoint n T =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => IBMQuarticSecondPrimitive.slope n 0 ω.1 * BrownianMassLimitIdentification.coordinateClass T ω.2 := by
  unfold projectedOriginJoint IBMSourceLaws.jointMeasure
  simpa only [origin_projection, smul_eq_mul] using
    ProductL2Curry.productTensor_coeFn gaussianProduct gaussianProduct
      (projection 2 (originClass n)) (BrownianMassLimitIdentification.coordinateClass T)

/-- The actual independent-clock average of the projected origin term. -/
theorem projectedOrigin_clock_mean (n : ℕ) (T : ℝ≥0) :
    (fun ωX => ∫ ωY, projectedOriginJoint n T (ωX,ωY) ∂gaussianProduct) =ᵐ[gaussianProduct]
      (fun ωX => (∫ ωY, BrownianMassLimitIdentification.coordinateClass T ωY ∂gaussianProduct) *
        IBMQuarticSecondPrimitive.slope n 0 ωX) := by
  filter_upwards [ae_ae_of_ae_prod (projectedOriginJoint_coeFn n T)] with ωX hx
  rw [integral_congr_ae hx, integral_const_mul, mul_comm]

end OperatorDerivativeRewrite.Foundation.IBMQuarticOriginProjection
