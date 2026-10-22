import Foundation.IBMNativePredictableTransfer

/-! Orthogonal factor energy sharpens the existing ordered recovery to a contraction. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.IBMNativeRecoveryContraction
open InfiniteGaussian GaussianNumberSectors GaussianDivergenceRecovery GaussianBochnerDivergenceRecovery
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMNativeGaussianRecovery
open IBMStochasticNativeDivergence IBMPredictableLpDictionary IBMFullPredictableIntegral
set_option backward.isDefEq.respectTransparency false
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable

theorem gaussian_recovery_vacuum_zero (f : GaussianL2) : recovery (projection 0 f) = 0 := by
  have hg : ((0 : GaussianVectorL2), projection 0 f - projection 0 (projection 0 f)) ∈
      hilbertDivergence.graph := by
    rw [projection_idempotent, sub_self]
    exact hilbertDivergence.graph.zero_mem
  have hn := recovery_minimal_norm (projection 0 f) 0 hg
  rw [norm_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

theorem gaussian_recovery_center (f : GaussianL2) : recovery (f-projection 0 f) = recovery f := by
  change GaussianDivergenceRecovery.recoveryOperator (f-projection 0 f) = recovery f
  rw [map_sub]
  change recovery f - recovery (projection 0 f) = recovery f
  rw [gaussian_recovery_vacuum_zero, sub_zero]

theorem gaussian_centered_recovery_norm (f : GaussianL2) :
    ‖recovery f‖ ≤ ‖f-projection 0 f‖ := by
  rw [← gaussian_recovery_center]
  exact recovery_norm_le _

theorem fiber_centered_recovery_norm (u : ScalarFieldSpace) :
    ‖fiberRecovery gaussianProduct u‖ ≤ ‖fiberCenter gaussianProduct u‖ := by
  apply (Lp.norm_le_mul_norm_of_ae_le_mul (c := (1 : ℝ)) ?_).trans_eq (one_mul _)
  filter_upwards [fiberRecovery_coeFn gaussianProduct u, fiberCenter_coeFn gaussianProduct u]
    with ω hr hc
  rw [hr, hc, one_mul]
  exact gaussian_centered_recovery_norm _

theorem projection_self_pairing (f : GaussianL2) :
    inner ℝ f (projection 0 f) = inner ℝ (projection 0 f) (projection 0 f) := by
  exact ((sector 0).inner_orthogonalProjectionOnto_eq_of_mem_right
    ((sector 0).orthogonalProjectionOnto f) f).symm

theorem factor_energy_decomposition (u : ScalarFieldSpace) :
    ‖u‖ ^ 2 = ‖fiberCenter gaussianProduct u‖ ^ 2 + ‖zeroSector u‖ ^ 2 := by
  have hp : inner ℝ u (zeroSector u) = ‖zeroSector u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(projection 0).coeFn_compLpL u] with ω hω
    change zeroSector u ω = projection 0 (u ω) at hω
    rw [hω]
    exact projection_self_pairing _
  have hn := norm_sub_sq_real u (zeroSector u)
  rw [hp, ← fiberCenter_eq] at hn
  linarith

theorem clock_centered_recovery_norm (f : JointL2) :
    ‖clockRecovery f‖ ≤ ‖f-clockVacuum f‖ := by
  have h := fiber_centered_recovery_norm (clockUnitary f)
  rw [fiberCenter_eq] at h
  have he : clockUnitary (f-clockVacuum f) = clockUnitary f-zeroSector (clockUnitary f) := by
    rw [map_sub]
    change clockUnitary f - clockUnitary (clockUnitary.symm _) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  exact h.trans_eq (he.symm ▸ clockUnitary.norm_map _)

theorem clock_energy_decomposition (f : JointL2) :
    ‖f‖ ^ 2 = ‖f-clockVacuum f‖ ^ 2 + ‖clockVacuum f‖ ^ 2 := by
  have h := factor_energy_decomposition (clockUnitary f)
  have he : clockUnitary (f-clockVacuum f) = fiberCenter gaussianProduct (clockUnitary f) := by
    rw [fiberCenter_eq, map_sub]
    change clockUnitary f-clockUnitary (clockUnitary.symm _) = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  rw [← he, clockUnitary.norm_map, clockUnitary.norm_map] at h
  have hz : ‖clockVacuum f‖ = ‖zeroSector (clockUnitary f)‖ := clockUnitary.symm.norm_map _
  rwa [← hz] at h

theorem recovery_contraction (f : JointL2) : ‖recoveryPair f‖ ≤ ‖f‖ := by
  have hs : ‖sourceRecovery (clockVacuum f)‖ ≤ ‖clockVacuum f‖ :=
    (fiberRecovery_norm_le _ (sourceUnitary (clockVacuum f))).trans_eq (sourceUnitary.norm_map _)
  have hc := clock_centered_recovery_norm f
  have he := clock_energy_decomposition f
  have hp : ‖recoveryPair f‖ ^ 2 =
      ‖sourceRecovery (clockVacuum f)‖ ^ 2 + ‖clockRecovery f‖ ^ 2 := pair_norm_sq _ _
  nlinarith [norm_nonneg (recoveryPair f), norm_nonneg f,
    norm_nonneg (sourceRecovery (clockVacuum f)), norm_nonneg (clockVacuum f),
    norm_nonneg (clockRecovery f), norm_nonneg (f-clockVacuum f)]

theorem native_transfer_contraction (F : JointL2) (H : PredictableL2 F) :
    ‖IBMNativePredictableTransfer.transfer F H‖ ≤ ‖H‖ :=
  (recovery_contraction (integral F H)).trans_eq (integral_norm F H)

end OperatorDerivativeRewrite.Foundation.IBMNativeRecoveryContraction
