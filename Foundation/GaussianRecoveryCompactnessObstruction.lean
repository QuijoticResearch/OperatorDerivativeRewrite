import Foundation.GaussianFirstChaosRecovery
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! Infinite first-chaos source multiplicity prevents compact divergence recovery. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianRecoveryCompactnessObstruction
open InfiniteGaussian GaussianNumberSectors GaussianFirstChaosRecovery GaussianDivergenceRecovery

def vacuumEmbedding : CoefficientSpace →ₗᵢ[ℝ] GaussianVectorL2 where
  toLinearMap := recoveryOperator.toLinearMap.comp firstChaosEmbedding.toLinearMap
  norm_map' h := by
    change ‖recovery (firstChaosEmbedding h)‖=‖h‖
    rw [recovery_firstChaos_norm,LinearIsometry.norm_map]

theorem vacuumEmbedding_apply (h : CoefficientSpace) :
    vacuumEmbedding h=InfiniteGaussian.scalarTensor h gaussianOne := recovery_firstChaos h

theorem coefficient_single_orthonormal :
    Orthonormal ℝ (fun n : ℕ => (lp.single 2 n (1 : ℝ) : CoefficientSpace)) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [← firstChaosEmbedding.inner_map_map,firstChaos_single,firstChaos_single,one_smul,one_smul]
  have hc := coordinateL2_orthonormal
  rw [orthonormal_iff_ite] at hc
  exact hc n m

theorem coefficient_space_not_finiteDimensional : ¬ FiniteDimensional ℝ CoefficientSpace := by
  intro hf
  letI := hf
  have hi := coefficient_single_orthonormal.linearIndependent.lt_aleph0_of_finiteDimensional
  have hh : Cardinal.aleph0<Cardinal.aleph0 := by simpa only [Cardinal.mk_nat] using hi
  exact (lt_irrefl _) hh

theorem firstChaos_graph_left_inverse (K : GaussianL2 →L[ℝ] GaussianVectorL2)
    (hK : ∀ h : CoefficientSpace, (K (firstChaosEmbedding h),firstChaosEmbedding h)∈hilbertDivergence.graph) :
    vacuumEmbedding.toContinuousLinearMap.adjoint.comp (K.comp firstChaosEmbedding.toContinuousLinearMap)=
      ContinuousLinearMap.id ℝ CoefficientSpace := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.id_apply]
  have hi := GaussianNumberSectors.graph_duality (firstChaos_derivative_graph y) (hK x)
  rw [firstChaosEmbedding.inner_map_map] at hi
  change inner ℝ (K (firstChaosEmbedding x)) (vacuumEmbedding y)=inner ℝ x y
  rw [vacuumEmbedding_apply]
  calc
    _=inner ℝ (scalarTensor y gaussianOne) (K (firstChaosEmbedding x)) := real_inner_comm _ _
    _=inner ℝ y x := hi
    _=inner ℝ x y := real_inner_comm _ _

theorem no_compact_firstChaos_right_inverse (K : GaussianL2 →L[ℝ] GaussianVectorL2)
    (hK : ∀ h : CoefficientSpace, (K (firstChaosEmbedding h),firstChaosEmbedding h)∈hilbertDivergence.graph) :
    ¬ IsCompactOperator K := by
  intro hc
  have hi := (hc.comp_clm firstChaosEmbedding.toContinuousLinearMap).clm_comp
    vacuumEmbedding.toContinuousLinearMap.adjoint
  change IsCompactOperator (vacuumEmbedding.toContinuousLinearMap.adjoint.comp
    (K.comp firstChaosEmbedding.toContinuousLinearMap)) at hi
  rw [firstChaos_graph_left_inverse K hK] at hi
  apply coefficient_space_not_finiteDimensional
  exact isCompactOperator_id_iff_finiteDimensional.mp hi

theorem recovery_not_compact : ¬ IsCompactOperator recoveryOperator := by
  apply no_compact_firstChaos_right_inverse
  intro h
  change (recovery (firstChaosEmbedding h),firstChaosEmbedding h)∈hilbertDivergence.graph
  rw [recovery_firstChaos]
  exact firstChaos_divergence_graph h

end OperatorDerivativeRewrite.Foundation.GaussianRecoveryCompactnessObstruction



