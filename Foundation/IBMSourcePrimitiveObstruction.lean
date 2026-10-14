import Foundation.GaussianFirstChaosRecovery
import Foundation.IBMClockCubicSourcePrimitive

/-! Necessary source-kernel norm and Cauchy conditions for the actual IBM
cubic primitive. This does not supply the missing kernel blow-up estimate. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.IBMSourcePrimitiveObstruction
open InfiniteGaussian GaussianNumberSectors GaussianTimeSpaceHermite IBMCubicFirstChaos
open GaussianDivergenceRecovery GaussianFirstChaosRecovery
open IBMClockCubicSourcePrimitive IBMClockCubicCorrection IBMSceneryCubicProjection
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

theorem firstProjection_norm_le_recovery (f : GaussianL2) :
    ‖GaussianPastFirstChaos.projection f‖ ≤ ‖recovery f‖ := by
  let h := firstChaosEmbedding.toContinuousLinearMap.adjoint f
  have hz : inner ℝ (firstChaosEmbedding h) gaussianOne=0 := by
    rw [real_inner_comm,← wick_one_eq_embedding]
    exact wick_centered h 0
  have hi : inner ℝ f (firstChaosEmbedding h)=‖h‖^2 := by
    have ha : inner ℝ (firstChaosEmbedding.toContinuousLinearMap.adjoint f) h =
        inner ℝ f (firstChaosEmbedding h) := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      rfl
    change inner ℝ h h=inner ℝ f (firstChaosEmbedding h) at ha
    simpa only [real_inner_self_eq_norm_sq] using ha.symm
  have hd := GaussianNumberSectors.graph_duality (firstChaos_derivative_graph h) (recovery_graph f)
  rw [inner_sub_right,projection_zero,inner_smul_right,hz,mul_zero,sub_zero,
    real_inner_comm f (firstChaosEmbedding h),hi] at hd
  have hn : ‖scalarTensor h gaussianOne‖=‖h‖ := by
    rw [← recovery_firstChaos,recovery_firstChaos_norm,firstChaosEmbedding.norm_map]
  have hb := real_inner_le_norm (scalarTensor h gaussianOne) (recovery f)
  rw [hd,hn] at hb
  change ‖firstChaosEmbedding h‖ ≤ ‖recovery f‖
  rw [firstChaosEmbedding.norm_map]
  by_cases hh : ‖h‖=0
  · simpa only [hh] using norm_nonneg (recovery f)
  · have hp : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg h) (Ne.symm hh)
    apply le_of_mul_le_mul_left _ hp
    nlinarith [hb]

def integratedSourceVector (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    FractionalSpectralKernel.SpectralSpace :=
  ∫ s in Set.Icc 0 T, sourceVector n |IBMConstructedSources.clockPath ωY (Real.toNNReal s)|

theorem integrated_source_projection (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    GaussianPastFirstChaos.projection (integratedCorrection n ωY T) =
      GaussianHilbertProcess.isonormalEmbedding FractionalSpectralKernel.SpectralSpace
        (integratedSourceVector n ωY T) :=
  IBMClockCubicTimeProjection.time_integrated_projection n ωY T

theorem integratedSourceVector_norm_le_primitive (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    ‖integratedSourceVector n ωY T‖ ≤ ‖sourcePrimitive n ωY T‖ := by
  have hb := firstProjection_norm_le_recovery (integratedCorrection n ωY T)
  rw [integrated_source_projection,LinearIsometry.norm_map] at hb
  exact hb

theorem integratedSourceVector_distance_le_primitive (n m : ℕ) (ωY : SampleSpace) (T : ℝ) :
    ‖integratedSourceVector n ωY T-integratedSourceVector m ωY T‖ ≤
      ‖sourcePrimitive n ωY T-sourcePrimitive m ωY T‖ := by
  have hb := firstProjection_norm_le_recovery
    (integratedCorrection n ωY T-integratedCorrection m ωY T)
  rw [map_sub,integrated_source_projection,integrated_source_projection,
    ← (GaussianHilbertProcess.isonormalEmbedding FractionalSpectralKernel.SpectralSpace).map_sub,
    LinearIsometry.norm_map] at hb
  change ‖integratedSourceVector n ωY T-integratedSourceVector m ωY T‖ ≤
    ‖recoveryOperator (integratedCorrection n ωY T-integratedCorrection m ωY T)‖ at hb
  rw [map_sub] at hb
  exact hb

theorem integratedSourceVector_cauchy_of_primitive_cauchy (ωY : SampleSpace) (T : ℝ)
    (hc : CauchySeq (fun n => sourcePrimitive n ωY T)) :
    CauchySeq (fun n => integratedSourceVector n ωY T) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc ε hε
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hb := integratedSourceVector_distance_le_primitive m n ωY T
  have hd : dist (integratedSourceVector m ωY T) (integratedSourceVector n ωY T) ≤
      dist (sourcePrimitive m ωY T) (sourcePrimitive n ωY T) := by
    simpa only [dist_eq_norm] using hb
  exact hd.trans_lt (hN m hm n hn)

end OperatorDerivativeRewrite.Foundation.IBMSourcePrimitiveObstruction
