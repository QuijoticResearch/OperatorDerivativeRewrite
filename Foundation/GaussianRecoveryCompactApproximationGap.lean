import Foundation.GaussianRecoveryCompactnessObstruction
import Mathlib.Analysis.SpecificLimits.Normed

/-! Full Gaussian recovery has distance exactly one from the compact operators. -/
noncomputable section
open MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianRecoveryCompactApproximationGap
open InfiniteGaussian GaussianDivergenceRecovery GaussianFirstChaosRecovery GaussianRecoveryCompactnessObstruction
private instance : Nontrivial CoefficientSpace := by
  refine ⟨⟨lp.single 2 0 (1 : ℝ),0,?_⟩⟩
  intro h
  have hn := coefficient_single_orthonormal.norm_eq_one 0
  rw [h,norm_zero] at hn
  norm_num at hn

def compression (K : GaussianL2 →L[ℝ] GaussianVectorL2) : CoefficientSpace →L[ℝ] CoefficientSpace :=
  vacuumEmbedding.toContinuousLinearMap.adjoint.comp (K.comp firstChaosEmbedding.toContinuousLinearMap)

theorem compression_recovery : compression recoveryOperator=ContinuousLinearMap.id ℝ CoefficientSpace := by
  apply firstChaos_graph_left_inverse
  intro h
  change (recovery (firstChaosEmbedding h),firstChaosEmbedding h)∈hilbertDivergence.graph
  rw [recovery_firstChaos]
  exact firstChaos_divergence_graph h

theorem compression_compact {K : GaussianL2 →L[ℝ] GaussianVectorL2} (hK : IsCompactOperator K) :
    IsCompactOperator (compression K) :=
  (hK.comp_clm firstChaosEmbedding.toContinuousLinearMap).clm_comp vacuumEmbedding.toContinuousLinearMap.adjoint

theorem compression_norm_bound (K : GaussianL2 →L[ℝ] GaussianVectorL2) : ‖compression K‖≤‖K‖ := by
  have h := ContinuousLinearMap.opNorm_comp_le vacuumEmbedding.toContinuousLinearMap.adjoint
    (K.comp firstChaosEmbedding.toContinuousLinearMap)
  have hh := ContinuousLinearMap.opNorm_comp_le K firstChaosEmbedding.toContinuousLinearMap
  have hV : ‖vacuumEmbedding.toContinuousLinearMap.adjoint‖=1 := by
    rw [ContinuousLinearMap.adjoint.norm_map,LinearIsometry.norm_toContinuousLinearMap]
  rw [hV,one_mul] at h
  rw [LinearIsometry.norm_toContinuousLinearMap,mul_one] at hh
  exact h.trans hh

theorem compact_endomorphism_distance {T : CoefficientSpace →L[ℝ] CoefficientSpace}
    (hT : IsCompactOperator T) : 1≤‖ContinuousLinearMap.id ℝ CoefficientSpace-T‖ := by
  by_contra h
  have hn : ‖(1 : CoefficientSpace →L[ℝ] CoefficientSpace)-T‖<1 := lt_of_not_ge h
  have hu : IsUnit T := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hn
  obtain ⟨u,hu⟩ := hu
  have hc := hT.comp_clm (↑(u⁻¹) : CoefficientSpace →L[ℝ] CoefficientSpace)
  rw [← hu] at hc
  change IsCompactOperator ((↑u : CoefficientSpace →L[ℝ] CoefficientSpace) * (↑(u⁻¹) : CoefficientSpace →L[ℝ] CoefficientSpace)) at hc
  rw [Units.mul_inv] at hc
  apply coefficient_space_not_finiteDimensional
  exact isCompactOperator_id_iff_finiteDimensional.mp hc

theorem compact_approximation_gap (K : GaussianL2 →L[ℝ] GaussianVectorL2)
    (hK : IsCompactOperator K) : 1≤‖recoveryOperator-K‖ := by
  have h := compact_endomorphism_distance (compression_compact hK)
  have he : compression (recoveryOperator-K)=ContinuousLinearMap.id ℝ CoefficientSpace-compression K := by
    apply ContinuousLinearMap.ext
    intro f
    change vacuumEmbedding.toContinuousLinearMap.adjoint
      ((recoveryOperator-K) (firstChaosEmbedding f))=f-compression K f
    rw [ContinuousLinearMap.sub_apply,map_sub]
    have hh := congrArg (fun T : CoefficientSpace →L[ℝ] CoefficientSpace => T f) compression_recovery
    change vacuumEmbedding.toContinuousLinearMap.adjoint (recoveryOperator (firstChaosEmbedding f))=f at hh
    rw [hh]
    rfl
  rw [← he] at h
  exact h.trans (compression_norm_bound _)

theorem recoveryOperator_norm_one : ‖recoveryOperator‖=1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖recovery f‖≤1*‖f‖
    simpa only [one_mul] using recovery_norm_le f
  · have h := recoveryOperator.le_opNorm (firstChaosEmbedding (lp.single 2 0 (1 : ℝ)))
    change ‖recovery (firstChaosEmbedding (lp.single 2 0 (1 : ℝ)))‖≤_
      at h
    rw [recovery_firstChaos,← vacuumEmbedding_apply,LinearIsometry.norm_map,LinearIsometry.norm_map] at h
    simpa only [coefficient_single_orthonormal.norm_eq_one 0,mul_one] using h

theorem optimal_compact_error :
    (∀ K : GaussianL2 →L[ℝ] GaussianVectorL2,IsCompactOperator K → 1≤‖recoveryOperator-K‖) ∧
      ∃ K : GaussianL2 →L[ℝ] GaussianVectorL2,IsCompactOperator K ∧ ‖recoveryOperator-K‖=1 := by
  refine ⟨compact_approximation_gap,0,isCompactOperator_zero,?_⟩
  rw [sub_zero,recoveryOperator_norm_one]

end OperatorDerivativeRewrite.Foundation.GaussianRecoveryCompactApproximationGap
