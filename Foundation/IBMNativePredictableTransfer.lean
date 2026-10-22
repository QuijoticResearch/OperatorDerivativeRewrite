import Foundation.IBMStochasticNativeDivergence
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! A constructed bounded transfer and an exact native-gradient/Itô-adjoint identity. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMNativePredictableTransfer
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMNativeGaussianRecovery IBMStochasticNativeDivergence IBMPredictableLpDictionary
open IBMFullPredictableIntegral
set_option backward.isDefEq.respectTransparency false
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable

theorem recoveryPair_add (f g : JointL2) : recoveryPair (f+g) = recoveryPair f + recoveryPair g := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [recoveryPair, pairField, sourceRecovery, clockRecovery, clockVacuum, map_add]

theorem recoveryPair_smul (c : ℝ) (f : JointL2) : recoveryPair (c • f) = c • recoveryPair f := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [recoveryPair, pairField, sourceRecovery, clockRecovery, clockVacuum, map_smul]

def recoveryOperator : JointL2 →L[ℝ] JointFieldSpace :=
  ({ toFun := recoveryPair
     map_add' := recoveryPair_add
     map_smul' := recoveryPair_smul } : JointL2 →ₗ[ℝ] JointFieldSpace).mkContinuous
    (Real.sqrt 2) (fun f => by
      change ‖recoveryPair f‖ ≤ Real.sqrt 2 * ‖f‖
      have h := recovery_bound f
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg f))).mp
      rwa [mul_pow, hs])

def transfer (F : JointL2) : PredictableL2 F →L[ℝ] JointFieldSpace :=
  recoveryOperator.comp (integral F).toContinuousLinearMap

theorem transfer_eq (F : JointL2) (H : PredictableL2 F) : transfer F H = nativeField F H := rfl

theorem transfer_divergence (F : JointL2) (H : PredictableL2 F) :
    jointDivergence ⟨transfer F H, nativeField_mem F H⟩ = stochasticOutput F H :=
  native_divergence F H

theorem transfer_duality (F : JointL2) (H : PredictableL2 F) (f : jointDerivative.domain) :
    inner ℝ H ((transfer F).adjoint (jointDerivative f)) =
      inner ℝ (stochasticOutput F H) (f : IntrinsicSpace) := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (stochastic_integration_by_parts F H f).symm

theorem native_gradient_adjoint_identity (F : JointL2) (f : jointDerivative.domain) :
    (transfer F).adjoint (jointDerivative f) =
      (integral F).toContinuousLinearMap.adjoint ((f : IntrinsicSpace) : JointL2) := by
  apply ext_inner_left ℝ
  intro H
  rw [transfer_duality, ContinuousLinearMap.adjoint_inner_right]
  rfl

end OperatorDerivativeRewrite.Foundation.IBMNativePredictableTransfer
