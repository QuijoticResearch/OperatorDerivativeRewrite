import Foundation.IBMActualQuadraticL2Reconstruction
import Foundation.IBMQuarticSourceGrowth

/-! Source sections of the ACTUAL fourth-power IBM observation, and its
exact second-chaos native testing law. No intrinsic projection commutation. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMActualQuarticSourceTesting
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMRawStepSources GaussianQuarticWick GaussianNumberSectors
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

theorem fourth_sections (R : ℝ≥0) :
    sourceUnitary (IBMActualQuarticMoment.fourthClass R) =ᵐ[gaussianProduct]
      fun Y => quartic (clockDirection R Y) := by
  have hu := ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct
    (ProductL2Curry.swap gaussianProduct gaussianProduct (IBMActualQuarticMoment.fourthClass R))
  have hs := ae_ae_of_ae_prod (ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct
    (IBMActualQuarticMoment.fourthClass R))
  have hq := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp
    (IBMActualQuarticMoment.fourthClass_ae R))
  change ∀ᵐ Y ∂gaussianProduct, sourceUnitary (IBMActualQuarticMoment.fourthClass R) Y = _
  filter_upwards [hu,hs,hq,IBMConstructedSources.clockPath_coordinate_ae R] with Y hu hs hq hc
  apply Lp.ext
  filter_upwards [hu,hs,hq,IBMActualQuarticMoment.scenery_firstChaos_ae
    |GaussianTimeProcess.process R Y|,quartic_coeFn (clockDirection R Y)] with X hu hs hq hf hp
  have hu' : sourceUnitary (IBMActualQuarticMoment.fourthClass R) Y X =
      IBMActualQuarticMoment.fourthClass R (X,Y) := hu.trans hs
  have hq' : IBMActualQuarticMoment.fourthClass R (X,Y) =
      (IBMConstructedSources.ibmValue R (X,Y))^4 := hq
  rw [hu',hq',IBMConstructedSources.ibmValue_eq,hc,hf,hp]
  rfl

theorem second_pairing (f : GaussianL2) (hf : f ∈ sector 2) (u : CoefficientSpace) :
    inner ℝ f (quartic u) = (6*‖u‖^2)*inner ℝ f (IBMSchwartzSourceContinuity.rawProduct u u) := by
  have hp := (sector 2).starProjection_inner_eq_zero (quartic u) f hf
  change inner ℝ (quartic u-projection 2 (quartic u)) f = 0 at hp
  rw [inner_sub_left,IBMQuarticSecondChaos.quartic_projection_two,real_inner_smul_left] at hp
  have hp' : inner ℝ f (quartic u) =
      (6*‖u‖^2)*inner ℝ f (GaussianTimeSpaceHermite.wick u 2 : GaussianL2) := by
    simpa only [real_inner_comm] using sub_eq_zero.mp hp
  have h0 : inner ℝ f gaussianOne = 0 := by
    have hg : gaussianOne ∈ sector 0 := by
      simpa only [GaussianTimeSpaceHermite.wick,GaussianTimeSpaceHermite.core_zero] using
        IBMCubicFirstChaos.wick_mem_sector u 0
    exact sectors_orthogonal (show (2:ℕ) ≠ 0 by decide) ⟨f,hf⟩ ⟨gaussianOne,hg⟩
  rw [IBMSourceProductBounds.rawProduct_eq_cross,inner_add_right,inner_smul_right,
    h0,mul_zero,add_zero,IBMQuarticSecondChaos.cross_self]
  linarith

theorem native_actual (H R : ℝ≥0) (N : ℕ) :
    IBMJointRandomGraphIdentity.nativeOperator H N (IBMActualQuarticMoment.fourthClass R)
      =ᵐ[gaussianProduct] fun Y => 6*|GaussianTimeProcess.process R Y| *
        IBMRawGridMixedObservable.mixedEnergy (H/(N+1)) (N+1) R R Y := by
  filter_upwards [IBMJointRandomContraction.joint_actual
      (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)) (IBMActualQuarticMoment.fourthClass R),
    fourth_sections R,IBMRawGridSecondChaos.sourceGrid_ae (H/(N+1)) (N+1),
    IBMRawGridMixedObservable.mixedSource_actual R R,
    IBMRawGridMixedObservable.source_mixed_pairing_ae (H/(N+1)) (N+1) R R] with Y ha hq hs hm he
  change IBMJointRandomContraction.jointOperator
    (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1))
      (IBMActualQuarticMoment.fourthClass R) Y = _
  rw [ha,hq]
  have hf : IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1) Y ∈ sector 2 := by
    rw [hs]
    exact IBMRawGridSecondChaos.source_mem_sector _ _
  rw [second_pairing _ hf,direction_norm_sq]
  rw [hm] at he
  rw [he]

end OperatorDerivativeRewrite.Foundation.IBMActualQuarticSourceTesting
