import Foundation.GaussianQuadraticRecoverySurjectivity

/-! Full second-chaos conditioning is actual compression of both completed matrix coordinates. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticMatrixPrediction
open InfiniteGaussian GaussianNumberSectors GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianJointSourceProjection GaussianWickRecoveryPrediction GaussianJointRecoveryIntertwining
open GaussianConditionalFullGraphs GaussianLinearFieldDivergenceCompletion GaussianLinearFieldTranspose
open GaussianLinearFieldMatrixCoordinates GaussianQuadraticRecoverySurjectivity GaussianDivergenceRecovery GaussianSourceHodge

theorem joint_rank {I : Type*} (h : I → CoefficientSpace) (a b : CoefficientSpace) :
    jointConditional h (scalarTensor a (firstChaosEmbedding b))=
      scalarTensor (sourceProjection h a) (firstChaosEmbedding (sourceProjection h b)) := by
  rw [jointConditional,ContinuousLinearMap.comp_apply,fieldConditional_scalarTensor,
    conditional_firstChaos_projection,fieldSourceProjection_scalarTensor]

theorem joint_linear_mem {I : Type*} (h : I → CoefficientSpace)
    {v : GaussianVectorL2} (hv : v∈linearGaussianFields) : jointConditional h v∈linearGaussianFields := by
  have hs : linearFieldCore≤linearGaussianFields.comap (jointConditional h).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,b,rfl⟩
    change jointConditional h (scalarTensor a (firstChaosEmbedding b))∈linearGaussianFields
    rw [joint_rank]
    exact linear_rank_mem _ _
  exact (linearFieldCore.topologicalClosure_minimal hs
    ((Submodule.isClosed_topologicalClosure _).preimage (jointConditional h).continuous)) hv

theorem joint_transpose_commute {I : Type*} (h : I → CoefficientSpace) (v : GaussianVectorL2) :
    transpose (jointConditional h v)=jointConditional h (transpose v) := by
  rw [transpose_apply,transpose_apply,map_sub,map_nsmul,← joint_gradientProjection_commute]

theorem matrix_compression_pairing {I : Type*} (h : I → CoefficientSpace)
    (a b : CoefficientSpace) (v : GaussianVectorL2) :
    inner ℝ (scalarTensor a (firstChaosEmbedding b)) (jointConditional h v)=
      inner ℝ (scalarTensor (sourceProjection h a) (firstChaosEmbedding (sourceProjection h b))) v := by
  rw [← jointConditional_inner,joint_rank]

theorem coordinates_compression {I : Type*} (h : I → CoefficientSpace)
    (v : linearGaussianFields) (i j : ℕ) :
    coordinates ⟨jointConditional h v,joint_linear_mem h v.property⟩ (i,j)=
      inner ℝ (scalarTensor (sourceProjection h (unit i)) (firstChaosEmbedding (sourceProjection h (unit j)))) (v : GaussianVectorL2) := by
  rw [coordinates_apply]
  exact matrix_compression_pairing h (unit i) (unit j) v

theorem conditional_completed_divergence {I : Type*} (h : I → CoefficientSpace)
    {v : GaussianVectorL2} (hv : v∈linearGaussianFields) :
    completedDivergence (jointConditional h v)=conditionalProjection h (completedDivergence v) :=
  hilbertDivergence.mem_graph_snd_inj (full_divergence_graph (joint_linear_mem h hv))
    (conditional_divergence_graph h (full_divergence_graph hv)) rfl

theorem second_chaos_prediction {I : Type*} (h : I → CoefficientSpace)
    {f : GaussianL2} (hf : f∈sector 2) :
    conditionalProjection h f=completedDivergence (jointConditional h (recovery f)) := by
  rw [conditional_completed_divergence h (recovery_second_chaos_linear hf),completed_divergence_recovery hf]

theorem second_chaos_prediction_energy {I : Type*} (h : I → CoefficientSpace)
    {f : GaussianL2} (hf : f∈sector 2) :
    ‖conditionalProjection h f‖^2=2*‖jointConditional h (recovery f)‖^2 := by
  rw [second_chaos_prediction h hf,completed_energy (joint_linear_mem h (recovery_second_chaos_linear hf))]
  have hm := joint_preserves_gradientRange h (GaussianQuadraticSourceHodge.recovery_mem_gradientRange f)
  have hp : gradientProjection (jointConditional h (recovery f))=jointConditional h (recovery f) :=
    gradientRange.starProjection_eq_self_iff.mpr hm
  rw [hp]

theorem prediction_matrix_energy {I : Type*} (h : I → CoefficientSpace)
    {f : GaussianL2} (hf : f∈sector 2) :
    HasSum (fun p : ℕ × ℕ => 2*(inner ℝ
      (scalarTensor (sourceProjection h (unit p.1)) (firstChaosEmbedding (sourceProjection h (unit p.2)))) (recovery f))^2)
      (‖conditionalProjection h f‖^2) := by
  let v : linearGaussianFields := ⟨recovery f,recovery_second_chaos_linear hf⟩
  have hs := (coordinates_energy ⟨jointConditional h v,joint_linear_mem h v.property⟩).mul_left 2
  have he (p : ℕ × ℕ) := coordinates_compression h v p.1 p.2
  simpa only [Prod.mk.eta,he,second_chaos_prediction_energy h hf] using hs

end OperatorDerivativeRewrite.Foundation.GaussianQuadraticMatrixPrediction

