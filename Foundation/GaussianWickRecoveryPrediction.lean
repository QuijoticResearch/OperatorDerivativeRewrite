import Foundation.GaussianConditionalCompactness
import Foundation.GaussianPredictionDivergenceRecovery

/-! Exact actual Wick primitives and the source projection needed by prediction/recovery. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianWickRecoveryPrediction
open InfiniteGaussian GaussianNumberSectors GaussianTimeSpaceHermite GaussianTimeFieldNorm
open GaussianDivergenceRecovery GaussianConditionalGraph GaussianWickConditionalProjection

theorem wick_source_divergence_graph (u : CoefficientSpace) (n : ℕ) :
    (scalarTensor u (wick u n), (wick u (n+1) : GaussianL2))∈hilbertDivergence.graph := by
  have hg := LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (cylindricalDivergence_rank_graph (wick u n) u)
  rw [← wick_raising u n] at hg
  exact hg

theorem recovery_wick (u : CoefficientSpace) (n : ℕ) :
    recovery (wick u (n+1))=scalarTensor u (wick u n) := by
  let f : GaussianL2 := wick u (n+1)
  let z := scalarTensor u (wick u n)
  have hd := closedCylindricalDerivative_core_graph (wick u (n+1))
  have he : polynomialDerivative (wick u (n+1))=(n+1 : ℝ) • z := by
    simpa only [z,wick] using core_derivative u (‖u‖^2) n
  rw [he] at hd
  have hr := recovery_graph f
  have hc : inner ℝ gaussianOne f=0 := wick_centered u n
  rw [projection_zero,hc,zero_smul,sub_zero] at hr
  have hz : (recovery f-z,0)∈hilbertDivergence.graph := by
    simpa only [Prod.mk_sub_mk,f,z,sub_self] using
      hilbertDivergence.graph.sub_mem hr (wick_source_divergence_graph u n)
  have hR := recovery_orthogonal_kernel f (recovery f-z) hz
  have hU := GaussianNumberSectors.graph_duality hd hz
  rw [inner_zero_right,real_inner_smul_left] at hU
  have hUz : inner ℝ z (recovery f-z)=0 := (mul_eq_zero.mp hU).resolve_left (by positivity)
  have hU' : inner ℝ (recovery f-z) z=0 := by
    calc _=inner ℝ z (recovery f-z) := real_inner_comm _ _
         _=0 := hUz
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  change inner ℝ (recovery f-z) (recovery f-z)=0
  rw [inner_sub_right,hR,hU',sub_self]

theorem recovery_wick_energy (u : CoefficientSpace) (n : ℕ) :
    ‖recovery (wick u (n+1))‖^2=(n.factorial : ℝ)*(‖u‖^2)^(n+1) := by
  rw [recovery_wick,← real_inner_self_eq_norm_sq,scalarTensor_pair_inner,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,GaussianWickContinuity.wick_norm_sq,
    pow_succ (‖u‖^2) n]
  ring

def fieldConditional {I : Type*} (h : I → CoefficientSpace) : GaussianVectorL2 →L[ℝ] GaussianVectorL2 :=
  (lpMeas CoefficientSpace ℝ (MeasurableSpace.comap (firstChaosFamily h) inferInstance) 2 gaussianProduct).subtypeL.comp
    (condExpL2 CoefficientSpace ℝ (generatedSigma_le h))

theorem fieldConditional_scalarTensor {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (f : GaussianL2) :
    fieldConditional h (scalarTensor u f)=scalarTensor u (conditionalProjection h f) := by
  apply Lp.ext
  have he := condExpL2_comp_continuousLinearMap ℝ ℝ (generatedSigma_le h)
    ((ContinuousLinearMap.id ℝ ℝ).smulRight u) f
  change fieldConditional h (scalarTensor u f)=ᵐ[gaussianProduct]
    scalarTensor u (conditionalProjection h f) at he
  exact he

theorem predicted_wick_recovery {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) (n : ℕ) :
    recovery (conditionalProjection h (wick u (n+1)))=
      scalarTensor (sourceProjection h u) (wick (sourceProjection h u) n) := by
  rw [conditional_wick_projection,recovery_wick]

theorem scalarTensor_sub_direction (u v : CoefficientSpace) (f : GaussianL2) :
    scalarTensor u f-scalarTensor v f=scalarTensor (u-v) f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (scalarTensor u f) (scalarTensor v f),scalarTensor_coeFn u f,
    scalarTensor_coeFn v f,scalarTensor_coeFn (u-v) f] with ω hs hu hv huv
  rw [hs,Pi.sub_apply,hu,hv,huv,smul_sub]

theorem prediction_recovery_defect {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) (n : ℕ) :
    fieldConditional h (recovery (wick u (n+1)))-recovery (conditionalProjection h (wick u (n+1)))=
      scalarTensor (u-sourceProjection h u) (wick (sourceProjection h u) n) := by
  rw [recovery_wick,fieldConditional_scalarTensor,conditional_wick_projection,predicted_wick_recovery,
    scalarTensor_sub_direction]

theorem prediction_recovery_defect_energy {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) (n : ℕ) :
    ‖fieldConditional h (recovery (wick u (n+1)))-recovery (conditionalProjection h (wick u (n+1)))‖^2=
      (n.factorial : ℝ)*‖u-sourceProjection h u‖^2*(‖sourceProjection h u‖^2)^n := by
  rw [prediction_recovery_defect,← real_inner_self_eq_norm_sq,scalarTensor_pair_inner,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,GaussianWickContinuity.wick_norm_sq]
  ring

theorem firstChaos_noncommutation {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace)
    (hu : sourceProjection h u≠u) :
    fieldConditional h (recovery (firstChaosEmbedding u))≠
      recovery (conditionalProjection h (firstChaosEmbedding u)) := by
  intro he
  have hd := prediction_recovery_defect_energy h u 0
  rw [IBMCubicFirstChaos.wick_one_eq_embedding,he,sub_self,norm_zero] at hd
  norm_num at hd
  have hz : u-sourceProjection h u=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (u-sourceProjection h u)])
  exact hu (sub_eq_zero.mp hz).symm

end OperatorDerivativeRewrite.Foundation.GaussianWickRecoveryPrediction

