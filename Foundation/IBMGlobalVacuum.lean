import Foundation.IBMNativeSourceRecovery
import Foundation.GaussianClockValueOperators
import Foundation.GaussianDeterministicGraphCore

/-! Identification of the actual composed native factor-zero projection with
global expectation. Source and clock order are verified through the unitaries. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMGlobalVacuum
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMNativeSourceRecovery
open GaussianNumberSectors
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

def one : JointL2 :=
  ProductL2Curry.productTensor gaussianProduct gaussianProduct gaussianOne gaussianOne

theorem clock_one : clockUnitary one =
    BochnerClosedOperator.tensor gaussianProduct gaussianOne gaussianOne :=
  ProductL2Curry.curry_productTensor _ _ _ _

theorem source_one : sourceUnitary one =
    BochnerClosedOperator.tensor gaussianProduct gaussianOne gaussianOne := by
  change clockUnitary (ProductL2Curry.swap gaussianProduct gaussianProduct one) = _
  rw [show ProductL2Curry.swap gaussianProduct gaussianProduct one = one from
    ProductL2Curry.swap_productTensor _ _ _ _]
  exact clock_one

theorem one_coeFn : one =ᵐ[IBMSourceLaws.jointMeasure] (fun _ => (1 : ℝ)) := by
  have hfst := measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)
  have hsnd := measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)
  have hx := hfst.quasiMeasurePreserving.ae_eq_comp gaussianOne_coeFn
  have hy := hsnd.quasiMeasurePreserving.ae_eq_comp gaussianOne_coeFn
  filter_upwards [ProductL2Curry.productTensor_coeFn gaussianProduct gaussianProduct
    gaussianOne gaussianOne, hx, hy] with z ht hx hy
  change gaussianOne z.1 = 1 at hx
  change gaussianOne z.2 = 1 at hy
  change one z = gaussianOne z.1 • gaussianOne z.2 at ht
  simpa only [hx, hy, smul_eq_mul, one_mul] using ht

theorem one_inner_mean (f : JointL2) :
    inner ℝ one f = ∫ ω, f ω ∂IBMSourceLaws.jointMeasure := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [one_coeFn] with ω hω
  simp [hω]

theorem one_intrinsic : one ∈ IntrinsicSpace := by
  change AEStronglyMeasurable[IBMConditionalObservable.observableSigma
    IBMConstructedSources.sceneryPath IBMConstructedSources.clockPath]
      one IBMSourceLaws.jointMeasure
  exact aestronglyMeasurable_const.congr one_coeFn.symm

theorem source_clock_flip (f : JointL2) :
    ProductL2Curry.flip gaussianProduct gaussianProduct (clockUnitary f) = sourceUnitary f := by
  change clockUnitary (ProductL2Curry.swap gaussianProduct gaussianProduct
    (clockUnitary.symm (clockUnitary f))) = sourceUnitary f
  rw [clockUnitary.symm_apply_apply]
  rfl

theorem clock_source_flip (f : JointL2) :
    clockUnitary f = ProductL2Curry.flip gaussianProduct gaussianProduct (sourceUnitary f) := by
  have h := congrArg (ProductL2Curry.flip gaussianProduct gaussianProduct) (source_clock_flip f)
  exact (GaussianClockValueOperators.flip_involutive (clockUnitary f)).symm.trans h

def factorMean (g : ScalarFieldSpace) : GaussianL2 :=
  (innerSL ℝ gaussianOne).compLpL 2 gaussianProduct g

theorem factor_vacuum_tensor (g : ScalarFieldSpace) :
    (projection 0).compLpL 2 gaussianProduct g =
      BochnerClosedOperator.tensor gaussianProduct (factorMean g) gaussianOne := by
  apply Lp.ext
  filter_upwards [(projection 0).coeFn_compLpL g,
    (innerSL ℝ gaussianOne).coeFn_compLpL g,
    BochnerClosedOperator.tensor_coeFn gaussianProduct (factorMean g) gaussianOne] with x hp hm ht
  rw [hp, ht, projection_zero]
  change factorMean g x = _ at hm
  rw [hm]
  rfl

theorem tensor_pairing (a v : GaussianL2) (g : ScalarFieldSpace) :
    inner ℝ (BochnerClosedOperator.tensor gaussianProduct a v) g =
      inner ℝ a ((innerSL ℝ v).compLpL 2 gaussianProduct g) := by
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct a v,
    (innerSL ℝ v).coeFn_compLpL g] with x ht hm
  rw [ht, real_inner_smul_left]
  rw [hm]
  simp only [Real.inner_apply, innerSL_apply_apply]

theorem composed_vacuum (f : JointL2) :
    clockVacuum (sourceVacuum f) = inner ℝ one f • one := by
  let g := sourceUnitary f
  let a := factorMean g
  have hs : sourceUnitary (sourceVacuum f) =
      BochnerClosedOperator.tensor gaussianProduct a gaussianOne := by
    change sourceUnitary (sourceUnitary.symm _) = _
    rw [sourceUnitary.apply_symm_apply]
    exact factor_vacuum_tensor g
  have hc : clockUnitary (sourceVacuum f) =
      BochnerClosedOperator.tensor gaussianProduct gaussianOne a := by
    have h := clock_source_flip (sourceVacuum f)
    rw [hs, ProductL2Curry.flip_tensor] at h
    exact h
  have hi : inner ℝ gaussianOne a = inner ℝ one f := by
    have h := sourceUnitary.inner_map_map one f
    rw [source_one, tensor_pairing] at h
    exact h
  apply clockUnitary.injective
  change clockUnitary (clockUnitary.symm
    ((projection 0).compLpL 2 gaussianProduct (clockUnitary (sourceVacuum f)))) = _
  rw [clockUnitary.apply_symm_apply]
  rw [hc, GaussianClockValueOperators.map_tensor, projection_zero, hi, map_smul, clock_one]
  apply Lp.ext
  filter_upwards [BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne
    (inner ℝ one f • gaussianOne),
    BochnerClosedOperator.tensor_coeFn gaussianProduct gaussianOne gaussianOne,
    Lp.coeFn_smul (inner ℝ one f)
      (BochnerClosedOperator.tensor gaussianProduct gaussianOne gaussianOne)] with x hl ht hr
  rw [hl, hr, Pi.smul_apply, ht]
  simp only [smul_smul]
  congr 1
  exact mul_comm _ _

theorem composed_vacuum_expectation (f : JointL2) :
    clockVacuum (sourceVacuum f) = (∫ ω, f ω ∂IBMSourceLaws.jointMeasure) • one := by
  rw [composed_vacuum, one_inner_mean]

end OperatorDerivativeRewrite.Foundation.IBMGlobalVacuum
