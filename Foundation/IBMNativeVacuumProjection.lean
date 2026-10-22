import Foundation.IBMNativeGaussianRecovery
import Foundation.IBMPredictableIntegralObservable
import Foundation.GaussianClockValueOperators

/-! The two native Gaussian vacuum remainders retain only the global mean. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMNativeVacuumProjection
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMNativeGaussianRecovery
open IBMPredictableIntegralObservable GaussianNumberSectors
set_option backward.isDefEq.respectTransparency false
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def fiberMean : ScalarFieldSpace →L[ℝ] GaussianL2 :=
  (innerSL ℝ gaussianOne).compLpL 2 gaussianProduct

def vacuumField : ScalarFieldSpace := BochnerClosedOperator.tensor gaussianProduct gaussianOne gaussianOne

theorem zeroSector_tensor (a v : GaussianL2) :
    zeroSector (BochnerClosedOperator.tensor gaussianProduct a v) =
      BochnerClosedOperator.tensor gaussianProduct a (projection 0 v) :=
  GaussianClockValueOperators.map_tensor (projection 0) a v

theorem zeroSector_eq_tensor (u : ScalarFieldSpace) :
    zeroSector u = BochnerClosedOperator.tensor gaussianProduct (fiberMean u) gaussianOne := by
  apply Lp.ext
  filter_upwards [(projection 0).coeFn_compLpL u,
    (innerSL ℝ gaussianOne).coeFn_compLpL u,
    BochnerClosedOperator.tensor_coeFn gaussianProduct (fiberMean u) gaussianOne] with ω hp hm ht
  change zeroSector u ω = projection 0 (u ω) at hp
  change fiberMean u ω = inner ℝ gaussianOne (u ω) at hm
  rw [hp, ht, projection_zero, hm]

theorem sourceUnitary_eq_flip (f : JointL2) :
    sourceUnitary f = ProductL2Curry.flip gaussianProduct gaussianProduct (clockUnitary f) := by
  change clockUnitary (swapEquiv f) =
    clockUnitary (ProductL2Curry.swap gaussianProduct gaussianProduct
      (clockUnitary.symm (clockUnitary f)))
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem vacuum_pairing (u : ScalarFieldSpace) :
    inner ℝ vacuumField u = inner ℝ gaussianOne (fiberMean u) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne gaussianOne,
    gaussianOne_coeFn, (innerSL ℝ gaussianOne).coeFn_compLpL u] with ω hv ho hm
  change vacuumField ω = gaussianOne ω • gaussianOne at hv
  change fiberMean u ω = inner ℝ gaussianOne (u ω) at hm
  rw [hv, ho, one_smul, Real.inner_apply, hm, one_mul]

theorem clockUnitary_jointOne : clockUnitary jointOne = vacuumField := by
  have hc : ∀ᵐ x ∂gaussianProduct,
      clockUnitary jointOne x =ᵐ[gaussianProduct] fun y => jointOne (x,y) :=
    ProductL2Curry.curryEquiv_coeFn gaussianProduct gaussianProduct jointOne
  have h1 := ae_ae_of_ae_prod jointOne_ae
  apply Lp.ext
  filter_upwards [hc, h1, BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne gaussianOne,
    gaussianOne_coeFn] with x hx h1 ht ho
  change vacuumField x = gaussianOne x • gaussianOne at ht
  rw [ht, ho, one_smul]
  apply Lp.ext
  filter_upwards [hx, h1, gaussianOne_coeFn] with y hy hxy ho
  rw [hy, hxy, ho]

theorem fiberMean_centered (f : JointL2) (hf : inner ℝ jointOne f = 0) :
    inner ℝ gaussianOne (fiberMean (clockUnitary f)) = 0 := by
  have hi := clockUnitary.inner_map_map jointOne f
  rw [clockUnitary_jointOne, vacuum_pairing] at hi
  exact hi.trans hf

theorem tensor_zero (a : GaussianL2) :
    BochnerClosedOperator.tensor gaussianProduct a (0 : GaussianL2) = 0 := by
  apply Lp.ext
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct a (0 : GaussianL2),
    Lp.coeFn_zero GaussianL2 2 gaussianProduct] with ω ht hz
  rw [ht, hz, smul_zero]
  rfl

theorem double_vacuum_zero (f : JointL2) (hf : inner ℝ jointOne f = 0) :
    sourceVacuum (clockVacuum f) = 0 := by
  have hs : zeroSector (sourceUnitary (clockVacuum f)) = 0 := by
    rw [sourceUnitary_eq_flip]
    change zeroSector (ProductL2Curry.flip gaussianProduct gaussianProduct
      (clockUnitary (clockUnitary.symm (zeroSector (clockUnitary f))))) = 0
    rw [LinearIsometryEquiv.apply_symm_apply, zeroSector_eq_tensor (clockUnitary f), ProductL2Curry.flip_tensor,
      zeroSector_tensor, projection_zero, fiberMean_centered f hf, zero_smul, tensor_zero]
  change sourceUnitary.symm (zeroSector (sourceUnitary (clockVacuum f))) = 0
  rw [hs, map_zero]

end OperatorDerivativeRewrite.Foundation.IBMNativeVacuumProjection
