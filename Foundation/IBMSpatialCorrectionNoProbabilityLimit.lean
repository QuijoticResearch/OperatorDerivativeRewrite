import Foundation.IBMSpatialIntegralNoProbabilityLimit

/-! The WHOLE actual mollified correction fails convergence in probability,
although its sum with the integral still converges to actual IBM. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialCorrectionNoProbabilityLimit
open IBMSpatialPointClockObstruction IBMSpatialIntegralNoProbabilityLimit
open IBMSpatialIntegralTail

theorem compensated_identity (r : ℕ) (T : ℝ≥0) :
    value r T = realize (endpoint r T)-realize (correction r T) := by
  rw [correction, map_sub]
  abel

theorem compensated_identity_ae (r : ℕ) (T : ℝ≥0) :
    value r T =ᵐ[IBMSourceLaws.jointMeasure]
      fun w => realize (endpoint r T) w-realize (correction r T) w := by
  have h := Lp.coeFn_sub (realize (endpoint r T)) (realize (correction r T))
  rw [← compensated_identity r T] at h
  exact h

theorem not_tendstoInMeasure_reindexed (T : ℝ≥0) (hT : 0 < T) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) (F : IBMSourceLaws.JointSample → ℝ) :
    ¬ TendstoInMeasure IBMSourceLaws.jointMeasure
      (fun n => realize (correction (φ n) T)) atTop F := by
  intro hC
  obtain ⟨ns, hns, hc⟩ := hC.exists_seq_tendsto_ae
  have hE := (realize.continuous.tendsto _ |>.comp (endpoint_tendsto T)).comp
    (hφ.comp hns.tendsto_atTop)
  obtain ⟨ms, hms, he⟩ := (tendstoInMeasure_of_tendsto_Lp hE).exists_seq_tendsto_ae
  let ψ (n : ℕ) := φ (ns (ms n))
  have hψ : Tendsto ψ atTop atTop := hφ.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)
  have hi : ∀ᵐ w ∂IBMSourceLaws.jointMeasure, Tendsto (fun n => value (ψ n) T w) atTop
      (𝓝 (realize (IBMPhysicalNoiseClock.sourceKernel T) w-F w)) := by
    filter_upwards [he, hc, ae_all_iff.mpr (fun r => compensated_identity_ae r T)]
      with w he hc ha
    have hcs := hc.comp hms.tendsto_atTop
    have hs := he.sub hcs
    simpa only [ha, Function.comp_def, ψ] using hs
  have hp := tendstoInMeasure_of_tendsto_ae (fun n => Lp.aestronglyMeasurable (value (ψ n) T)) hi
  exact IBMSpatialIntegralNoProbabilityLimit.not_tendstoInMeasure_reindexed T hT ψ hψ _ hp

theorem not_tendstoInMeasure (T : ℝ≥0) (hT : 0 < T) (F : IBMSourceLaws.JointSample → ℝ) :
    ¬ TendstoInMeasure IBMSourceLaws.jointMeasure (fun r => realize (correction r T)) atTop F :=
  not_tendstoInMeasure_reindexed T hT id tendsto_id F

end OperatorDerivativeRewrite.Foundation.IBMSpatialCorrectionNoProbabilityLimit
