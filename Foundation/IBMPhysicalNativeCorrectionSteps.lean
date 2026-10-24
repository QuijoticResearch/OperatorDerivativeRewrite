import Foundation.IBMPhysicalPredictableSteps

/-! The ACTUAL correction-left sums are outputs of the ORIGINAL physical
Ito map, with all physical predictable-domain membership proved. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalNativeCorrectionSteps
open InfiniteGaussian IBMPhysicalWeakWiener GaussianTimeProcess
open IBMPhysicalPredictableSteps IBMPhysicalPastMeasurability
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

def partitionInput {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) : IBMPhysicalClockIto.Domain T :=
  ∑ i : Fin n, input (τ i.castSucc) (τ i.succ) T
    (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc)) (correction_past (τ i.castSucc))

theorem partitionInput_ae {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) :
    (partitionInput T τ).val =ᵐ[PredictableRealL2.horizonMeasure T gaussianProduct]
      fun z => ∑ i : Fin n, field (τ i.castSucc) (τ i.succ)
        (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc)) z := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n =>
    (input (τ i.castSucc) (τ i.succ) T (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc))
      (correction_past (τ i.castSucc))).val),
    ae_all_iff.mpr (fun i : Fin n => input_ae (τ i.castSucc) (τ i.succ) T
      (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc)) (correction_past (τ i.castSucc)))]
      with z hs hi
  simp only [partitionInput, Submodule.coe_sum]
  rw [hs, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _hi => hi i

theorem partition_integral {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (hend : τ (Fin.last n) ≤ T) : IBMPhysicalClockIto.integral T (partitionInput T τ) =
      IBMPhysicalCorrectionSteps.partitionClass τ hτ := by
  change IBMPhysicalClockIto.integralIsometry T (∑ i : Fin n,
    input (τ i.castSucc) (τ i.succ) T (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc))
      (correction_past (τ i.castSucc))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact integral_input (τ i.castSucc) (τ i.succ) T (hτ (Fin.castSucc_le_succ i))
    ((hτ (Fin.le_last i.succ)).trans hend) _ (correction_past (τ i.castSucc))

theorem partition_integral_actual {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (hend : τ (Fin.last n) ≤ T) : IBMPhysicalClockIto.integral T (partitionInput T τ)
      =ᵐ[gaussianProduct] IBMPhysicalClockProductRule.leftCorrectionSum τ := by
  rw [partition_integral T τ hτ hend]
  exact IBMPhysicalCorrectionSteps.partitionClass_ae τ hτ

theorem partition_isometry {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (hend : τ (Fin.last n) ≤ T) :
    ‖IBMPhysicalCorrectionSteps.partitionClass τ hτ‖ = ‖partitionInput T τ‖ := by
  rw [← partition_integral T τ hτ hend]
  exact IBMPhysicalClockIto.integral_norm T _

theorem partition_integral_mean_zero {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (hend : τ (Fin.last n) ≤ T) :
    (∫ Y, IBMPhysicalClockIto.integral T (partitionInput T τ) Y ∂gaussianProduct) = 0 := by
  rw [partition_integral T τ hτ hend]
  exact IBMPhysicalCorrectionSteps.partition_mean_zero τ hτ

end OperatorDerivativeRewrite.Foundation.IBMPhysicalNativeCorrectionSteps
