import Foundation.IBMNativeVacuumProjection
import Foundation.GaussianClockSourceSpectral

/-! Actual predictable stochastic integration has a constructed native divergence field. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMStochasticNativeDivergence
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMNativeGaussianRecovery IBMNativeVacuumProjection IBMPredictableIntegralObservable
open IBMPredictableLpDictionary IBMFullPredictableIntegral GaussianNumberSectors
set_option backward.isDefEq.respectTransparency false
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem centered_observable_recovery (f : IntrinsicSpace) (hf : inner ℝ jointOne (f : JointL2) = 0) :
    ∃ h : recoveryPair (f : JointL2) ∈ jointDivergence.domain,
      jointDivergence ⟨recoveryPair (f : JointL2), h⟩ = f := by
  obtain ⟨h, hv⟩ := recovery_pair_graph (f : JointL2)
  refine ⟨h, ?_⟩
  rw [double_vacuum_zero _ hf, sub_zero] at hv
  have hp : IntrinsicSpace.orthogonalProjectionOnto (f : JointL2) = f := by
    apply Subtype.ext
    change IntrinsicSpace.starProjection (f : JointL2) = (f : JointL2)
    exact Submodule.starProjection_eq_self_iff.mpr f.property
  exact hv.trans hp

theorem clockVacuum_norm_le (f : JointL2) : ‖clockVacuum f‖ ≤ ‖f‖ := by
  change ‖clockUnitary.symm (zeroSector (clockUnitary f))‖ ≤ ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  exact (GaussianClockSourceSpectral.sourceLift_contraction (projection 0)
    (projection_norm_le 0) (clockUnitary f)).trans_eq (clockUnitary.norm_map f)

theorem pair_norm_sq (a b : FieldSpace) :
    ‖pairField a b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [pairField, PiLp.inner_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, real_inner_self_eq_norm_sq]

theorem recovery_bound (f : JointL2) : ‖recoveryPair f‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 := by
  have hs : ‖sourceRecovery (clockVacuum f)‖ ≤ ‖f‖ :=
    (GaussianBochnerDivergenceRecovery.fiberRecovery_norm_le _ (sourceUnitary (clockVacuum f))).trans
      ((sourceUnitary.norm_map _).le.trans (clockVacuum_norm_le f))
  have hc : ‖clockRecovery f‖ ≤ ‖f‖ :=
    (GaussianBochnerDivergenceRecovery.fiberRecovery_norm_le _ (clockUnitary f)).trans_eq
      (clockUnitary.norm_map f)
  rw [recoveryPair, pair_norm_sq]
  nlinarith [norm_nonneg f, norm_nonneg (sourceRecovery (clockVacuum f)), norm_nonneg (clockRecovery f)]

def stochasticOutput (F : JointL2) (H : PredictableL2 F) : IntrinsicSpace :=
  ⟨integral F H, integral_mem_intrinsic F H⟩

def nativeField (F : JointL2) (H : PredictableL2 F) : JointFieldSpace :=
  recoveryPair (integral F H)

theorem nativeField_mem (F : JointL2) (H : PredictableL2 F) :
    nativeField F H ∈ jointDivergence.domain :=
  (centered_observable_recovery (stochasticOutput F H) (integral_centered F H)).choose

theorem native_divergence (F : JointL2) (H : PredictableL2 F) :
    jointDivergence ⟨nativeField F H, nativeField_mem F H⟩ = stochasticOutput F H :=
  (centered_observable_recovery (stochasticOutput F H) (integral_centered F H)).choose_spec

theorem nativeField_bound (F : JointL2) (H : PredictableL2 F) :
    ‖nativeField F H‖ ^ 2 ≤ 2 * ‖H‖ ^ 2 := by
  exact (recovery_bound (integral F H)).trans_eq (by rw [integral_norm])

theorem stochastic_integration_by_parts (F : JointL2) (H : PredictableL2 F)
    (f : jointDerivative.domain) :
    inner ℝ (stochasticOutput F H) (f : IntrinsicSpace) =
      inner ℝ (nativeField F H) (jointDerivative f) := by
  rw [← native_divergence F H]
  exact jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense _ f

end OperatorDerivativeRewrite.Foundation.IBMStochasticNativeDivergence
