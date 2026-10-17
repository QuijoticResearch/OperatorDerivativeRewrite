import Foundation.GaussianProjectedDerivativeClosure
import Foundation.GaussianPolynomialMartingale

/-! Corrected predictable product identities on actual heat-polynomial martingales. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianPolynomialPredictableProduct
open InfiniteGaussian GaussianPolynomialHeat GaussianPolynomialProcess GaussianPolynomialIto
open GaussianPolynomialMartingale GaussianPredictableFull GaussianPredictableAdjoint
open GaussianProductDerivative GaussianTimeProductL2 GaussianBochnerDerivative
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

theorem heat_product (p q : SpaceTimePolynomial) :
    heat (p*q) = heat p * q + p * heat q + pderiv 1 p * pderiv 1 q := by
  have hd : pderiv 1 (pderiv 1 (p*q)) =
      pderiv 1 (pderiv 1 p) * q +
      (pderiv 1 p * pderiv 1 q + pderiv 1 p * pderiv 1 q) + p * pderiv 1 (pderiv 1 q) := by
    simp only [pderiv_mul, map_add]
    ring
  rw [heat_apply, hd, heat_apply, heat_apply]
  simp only [pderiv_mul, smul_add, add_mul, mul_add, mul_smul_comm, smul_mul_assoc]
  module

theorem terminal_adjoint (T : ℝ≥0) (p : SpaceTimePolynomial) :
    scalarCurry (predictableAdjoint (valueL2 T p) : TimeProbabilityL2) =
      spatialField T p +
        scalarCurry (predictableAdjoint (timeIntegral T (heat p)) : TimeProbabilityL2) := by
  obtain ⟨U,hsp,hIto⟩ := (polynomial_ito T p).exists
  have he := congrArg predictableAdjoint hIto
  rw [map_sub, map_add, predictableAdjoint_integral, valueL2_zero,
    GaussianQuadraticCylinders.predictableAdjoint_constant, sub_zero] at he
  change predictableAdjoint (valueL2 T p) = U + predictableAdjoint (timeIntegral T (heat p)) at he
  have hc := congrArg (fun V : fullPredictable => scalarCurry (V : TimeProbabilityL2)) he
  simpa only [Submodule.coe_add, map_add, hsp] using hc

def crossGradientIntegral (T : ℝ≥0) (p q : SpaceTimePolynomial) : GaussianL2 :=
  timeIntegral T (pderiv 1 p * pderiv 1 q)

theorem corrected_heat_product (T : ℝ≥0) (p q : SpaceTimePolynomial)
    (hp : heat p = 0) (hq : heat q = 0) :
    scalarCurry (predictableAdjoint (valueL2 T (p*q)) : TimeProbabilityL2) =
      spatialField T (p*q) +
        scalarCurry (predictableAdjoint (crossGradientIntegral T p q) : TimeProbabilityL2) := by
  simpa only [heat_product, hp, hq, zero_mul, mul_zero, zero_add, crossGradientIntegral]
    using terminal_adjoint T (p*q)

theorem heat_terminal_adjoint (T : ℝ≥0) (p : SpaceTimePolynomial) (hp : heat p = 0) :
    scalarCurry (predictableAdjoint (valueL2 T p) : TimeProbabilityL2) = spatialField T p := by
  rw [terminal_adjoint, hp, map_zero, map_zero]
  change spatialField T p + scalarCurry (0 : TimeProbabilityL2) = _
  rw [map_zero, add_zero]

theorem terminal_product_coeFn (T : ℝ≥0) (p q : SpaceTimePolynomial) :
    valueL2 T (p*q) =ᵐ[gaussianProduct] fun ω => valueL2 T p ω * valueL2 T q ω := by
  filter_upwards [valueL2_coeFn T (p*q), valueL2_coeFn T p, valueL2_coeFn T q] with ω hp hq hr
  rw [hp, hq, hr, map_mul]

theorem product_spatial_slices (T : ℝ≥0) (p q : SpaceTimePolynomial) :
    spatialField T (p*q) =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator (fun t =>
      valueL2 t.toNNReal (p * pderiv 1 q + q * pderiv 1 p)) := by
  have he : pderiv 1 (p*q) = p * pderiv 1 q + q * pderiv 1 p := by
    rw [pderiv_mul]
    ring
  simpa only [he] using spatialField_coeFn T (p*q)

theorem heat_conditional_terminal (p : SpaceTimePolynomial) (hp : heat p = 0)
    (S T : ℝ≥0) (hST : S ≤ T) :
    GaussianConditionalIto.pastProjection S (valueL2 T p) = valueL2 S p := by
  rw [pastProjection_heatPolynomial p hp, min_eq_left hST]

theorem correction_vanishes_iff (T : ℝ≥0) (p q : SpaceTimePolynomial)
    (hp : heat p = 0) (hq : heat q = 0) :
    scalarCurry (predictableAdjoint (valueL2 T (p*q)) : TimeProbabilityL2) = spatialField T (p*q) ↔
      predictableAdjoint (crossGradientIntegral T p q) = 0 := by
  rw [corrected_heat_product T p q hp hq]
  constructor
  · intro he
    have hc : scalarCurry (predictableAdjoint (crossGradientIntegral T p q) : TimeProbabilityL2) = 0 := by
      linear_combination (norm := module) he
    apply Subtype.ext
    apply scalarCurry.injective
    simpa only [Submodule.coe_zero, map_zero] using hc
  · intro he
    simp only [he, Submodule.coe_zero, map_zero, add_zero]

theorem heat_product_ito_decomposition (T : ℝ≥0) (p q : SpaceTimePolynomial)
    (hp : heat p = 0) (hq : heat q = 0) :
    ∃! U : fullPredictable, scalarCurry (U : TimeProbabilityL2) = spatialField T (p*q) ∧
      valueL2 T (p*q) - valueL2 0 (p*q) = itoIntegral U + crossGradientIntegral T p q := by
  simpa only [heat_product, hp, hq, zero_mul, mul_zero, zero_add, crossGradientIntegral,
    timeIntegral, LinearMap.coe_mk, AddHom.coe_mk] using polynomial_ito T (p*q)

theorem corrected_heat_product_representer (T : ℝ≥0) (p q : SpaceTimePolynomial)
    (hp : heat p = 0) (hq : heat q = 0) :
    ∃! U : fullPredictable, scalarCurry (U : TimeProbabilityL2) = spatialField T (p*q) ∧
      predictableAdjoint (valueL2 T (p*q)) = U + predictableAdjoint (crossGradientIntegral T p q) := by
  obtain ⟨U,hsp,_⟩ := polynomial_representation T (p*q)
  refine ⟨U, ⟨hsp, ?_⟩, ?_⟩
  · apply Subtype.ext
    apply scalarCurry.injective
    change scalarCurry (predictableAdjoint (valueL2 T (p*q)) : TimeProbabilityL2) =
      scalarCurry ((U : TimeProbabilityL2) + (predictableAdjoint (crossGradientIntegral T p q) : TimeProbabilityL2))
    rw [map_add, hsp]
    exact corrected_heat_product T p q hp hq
  · intro V hV
    apply Subtype.ext
    exact scalarCurry.injective (hV.1.trans hsp.symm)
end OperatorDerivativeRewrite.Foundation.GaussianPolynomialPredictableProduct
