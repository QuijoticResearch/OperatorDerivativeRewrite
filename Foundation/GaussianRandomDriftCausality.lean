import Foundation.GaussianRandomStepDrift
import Foundation.GaussianConditionalClarkOcone

/-! Past/future orthogonality of the random drift and its original delayed stochastic step. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianRandomDriftCausality
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeProductL2
  GaussianPredictableFull GaussianPredictableAdjoint GaussianPredictableCutoff
  GaussianConditionalIto GaussianConditionalClarkOcone GaussianBrownianPRP
  GaussianRandomStepDrift
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

theorem actualDrift_past : actualDrift∈pastL2 1 := by
  exact A_past.neg.congr (Lp.coeFn_neg A).symm

theorem drift_projection : pastProjection 1 actualDrift=actualDrift :=
  Submodule.starProjection_eq_self_iff.mpr actualDrift_past

theorem drift_representer_cut :
    predictableCut 1 (predictableAdjoint actualDrift)=predictableAdjoint actualDrift :=
  past_representer_supported 1 actualDrift actualDrift_past

theorem theta_cut_zero : predictableCut 1 thetaField=0 := by
  apply Subtype.ext
  change cut 1 (productTensor (intervalVector 1 2) A)=0
  have ht := cut_tensor (1 : ℝ≥0) 1 2 A
  have hz := tensor_eq_zero_of_le (1 : ℝ≥0) 1 le_rfl A
  norm_num at ht hz
  exact ht.trans hz

theorem stochastic_projection_zero : pastProjection 1 (itoIntegral thetaField)=0 := by
  rw [pastProjection_integral,theta_cut_zero,map_zero]

theorem drift_stochastic_orthogonal : inner ℝ actualDrift (itoIntegral thetaField)=0 := by
  have ht := (pastL2 1).starProjection_inner_eq_zero
    (itoIntegral thetaField) actualDrift actualDrift_past
  change inner ℝ (itoIntegral thetaField-pastProjection 1 (itoIntegral thetaField)) actualDrift=0 at ht
  rw [stochastic_projection_zero,sub_zero] at ht
  rw [real_inner_comm]
  exact ht

theorem representers_orthogonal : inner ℝ (predictableAdjoint actualDrift) thetaField=0 := by
  have hd : cut 1 (predictableAdjoint actualDrift : TimeProbabilityL2)=
      (predictableAdjoint actualDrift : TimeProbabilityL2) :=
    congrArg (fun U : fullPredictable => (U : TimeProbabilityL2)) drift_representer_cut
  have hf : cut 1 (thetaField : TimeProbabilityL2)=0 :=
    congrArg (fun U : fullPredictable => (U : TimeProbabilityL2)) theta_cut_zero
  have ht := cut_inner 1 (predictableAdjoint actualDrift : TimeProbabilityL2)
    (thetaField : TimeProbabilityL2)
  rw [hd,hf,inner_zero_right] at ht
  exact ht

theorem drift_representer_nonzero : predictableAdjoint actualDrift≠0 := by
  intro h
  apply actualDrift_not_deterministic
  refine ⟨∫ ω, actualDrift ω ∂gaussianProduct,?_⟩
  have ht := brownian_representation actualDrift actualDrift_brownian
  rw [h,map_zero] at ht
  exact sub_eq_zero.mp ht.symm

theorem drift_representer_ne_theta : predictableAdjoint actualDrift≠thetaField := by
  intro h
  apply drift_representer_nonzero
  calc
    _ = predictableCut 1 (predictableAdjoint actualDrift) := drift_representer_cut.symm
    _ = 0 := by rw [h,theta_cut_zero]

theorem past_forecast :
    pastProjection 1 (actualDrift+itoIntegral thetaField)=actualDrift := by
  rw [map_add,drift_projection,stochastic_projection_zero,add_zero]

theorem future_error :
    actualDrift+itoIntegral thetaField-
      pastProjection 1 (actualDrift+itoIntegral thetaField)=itoIntegral thetaField := by
  rw [past_forecast]
  abel

end OperatorDerivativeRewrite.Foundation.GaussianRandomDriftCausality
