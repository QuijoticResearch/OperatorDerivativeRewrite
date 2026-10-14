import Foundation.GaussianOneObservationRecoveryCompactness
import Foundation.SPDEWickBrownianPrediction

/-! Countably many actually observed Brownian modes retain noncompact recovery at every positive time. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.SPDEObservationRecoveryCompactness
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianDivergenceRecovery GaussianRecoveryCompactnessObstruction SPDEWickModes SPDEWickBrownianPrediction

theorem infinite_observed_source_noncompact {I : Type*} (h : I → CoefficientSpace)
    (J : CoefficientSpace →ₗᵢ[ℝ] CoefficientSpace) (hJ : ∀ c, J c∈sourceSpan h) :
    ¬ IsCompactOperator (recoveryOperator.comp (conditionalProjection h)) := by
  let U := (vacuumEmbedding.comp J).toContinuousLinearMap
  let V := (firstChaosEmbedding.comp J).toContinuousLinearMap
  have he : (recoveryOperator.comp (conditionalProjection h)).comp V=U := by
    apply ContinuousLinearMap.ext
    intro c
    change recovery (conditionalProjection h (firstChaosEmbedding (J c)))=vacuumEmbedding (J c)
    have hp : sourceProjection h (J c)=J c := Submodule.starProjection_eq_self_iff.mpr (hJ c)
    rw [conditional_firstChaos_projection,hp]
    rfl
  have hU : U.adjoint.comp U=1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U).mp (vacuumEmbedding.comp J).norm_map
  intro hc
  have hi := (hc.comp_clm V).clm_comp U.adjoint
  change IsCompactOperator (U.adjoint.comp ((recoveryOperator.comp (conditionalProjection h)).comp V)) at hi
  rw [he,hU] at hi
  exact coefficient_space_not_finiteDimensional (isCompactOperator_id_iff_finiteDimensional.mp hi)

def modeUnit (t : ℝ≥0) (i : ℕ) : CoefficientSpace := (Real.sqrt (t : ℝ))⁻¹ • brownianDirection i t

theorem modeUnit_orthonormal (t : ℝ≥0) (ht : 0<t) : Orthonormal ℝ (modeUnit t) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [modeUnit,real_inner_smul_left,real_inner_smul_right,brownianDirection_inner]
  by_cases hij : i=j
  · subst j
    simp only [if_pos rfl,min_self]
    have hp : Real.sqrt (t : ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr ht)
    have hs := Real.sq_sqrt t.coe_nonneg
    field_simp
    simp only [ite_true,mul_one]
    nlinarith [hs]
  · simp [hij]

def observedSourceEmbedding (t : ℝ≥0) (ht : 0<t) : CoefficientSpace →ₗᵢ[ℝ] CoefficientSpace :=
  (modeUnit_orthonormal t ht).orthogonalFamily.linearIsometry

theorem observedSourceEmbedding_hasSum (t : ℝ≥0) (ht : 0<t) (c : CoefficientSpace) :
    HasSum (fun i => c i • modeUnit t i) (observedSourceEmbedding t ht c) := by
  simpa only [observedSourceEmbedding,LinearIsometry.toSpanSingleton_apply] using
    (modeUnit_orthonormal t ht).orthogonalFamily.hasSum_linearIsometry c

theorem observedSourceEmbedding_mem (t : ℝ≥0) (ht : 0<t) (c : CoefficientSpace) :
    observedSourceEmbedding t ht c∈sourceSpan (pastDirections t) := by
  have hm (i : ℕ) : modeUnit t i∈sourceSpan (pastDirections t) :=
    (sourceSpan (pastDirections t)).smul_mem _
      ((Submodule.span ℝ (Set.range (pastDirections t))).le_topologicalClosure
        (Submodule.subset_span ⟨(i,⟨t,by simp⟩),rfl⟩))
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (observedSourceEmbedding_hasSum t ht c)
  exact Eventually.of_forall fun s => (sourceSpan (pastDirections t)).sum_mem (fun i hi =>
    (sourceSpan (pastDirections t)).smul_mem _ (hm i))

theorem positive_time_recovery_noncompact (t : ℝ≥0) (ht : 0<t) :
    ¬ IsCompactOperator (recoveryOperator.comp (conditionalProjection (pastDirections t))) :=
  infinite_observed_source_noncompact (pastDirections t) (observedSourceEmbedding t ht)
    (observedSourceEmbedding_mem t ht)

theorem zero_time_recovery_zero : recoveryOperator.comp (conditionalProjection (pastDirections 0))=0 := by
  have hz (p : ℕ × Set.Iic (0 : ℝ≥0)) : pastDirections 0 p=0 := by
    have hp : (p.2 : ℝ≥0)=0 := le_antisymm p.2.property (by positivity)
    rw [pastDirections,hp]
    apply norm_eq_zero.mp
    have hn := brownianDirection_energy p.1 0
    norm_num at hn
    rw [hn,norm_zero]
  apply ContinuousLinearMap.ext
  intro f
  change recovery (conditionalProjection (pastDirections 0) f)=0
  rw [GaussianConditionalCompactness.zero_family_projection _ hz,recovery_smul,
    GaussianOneObservationRecoveryCompactness.recovery_vacuum_zero,smul_zero]

theorem brownian_past_recovery_compact_iff (t : ℝ≥0) :
    IsCompactOperator (recoveryOperator.comp (conditionalProjection (pastDirections t))) ↔ t=0 := by
  constructor
  · intro hc
    by_contra ht
    exact positive_time_recovery_noncompact t (lt_of_le_of_ne (by positivity) (Ne.symm ht)) hc
  · intro ht
    subst t
    rw [zero_time_recovery_zero]
    change IsCompactOperator (0 : GaussianL2 → GaussianVectorL2)
    exact isCompactOperator_zero

end OperatorDerivativeRewrite.Foundation.SPDEObservationRecoveryCompactness

