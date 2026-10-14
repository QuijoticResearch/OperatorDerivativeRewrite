import Foundation.GaussianObservedRecoveryRange

/-! Full joint source/sample intertwining for actual Gaussian divergence recovery. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianJointRecoveryIntertwining
open InfiniteGaussian GaussianNumberSectors GaussianConditionalGraph GaussianGeneratedGraphCore
open GaussianWickConditionalProjection GaussianWickRecoveryPrediction GaussianJointSourceProjection
open GaussianInverseNumberPotential GaussianDivergenceRecovery GaussianSourceHodge
open GaussianQuadraticSourceHodge GaussianObservedRecoveryRange GaussianTimeFieldNorm

theorem scalarTensor_add_source (u v : CoefficientSpace) (f : GaussianL2) :
    scalarTensor (u+v) f=scalarTensor u f+scalarTensor v f := by
  apply Lp.ext
  filter_upwards [scalarTensor_coeFn (u+v) f,scalarTensor_coeFn u f,scalarTensor_coeFn v f,
    Lp.coeFn_add (scalarTensor u f) (scalarTensor v f)] with ω huv hu hv ha
  rw [huv,ha,Pi.add_apply,hu,hv,smul_add]

theorem scalarTensor_smul_source (c : ℝ) (u : CoefficientSpace) (f : GaussianL2) :
    scalarTensor (c • u) f=c • scalarTensor u f := by
  apply Lp.ext
  filter_upwards [scalarTensor_coeFn (c • u) f,scalarTensor_coeFn u f,
    Lp.coeFn_smul c (scalarTensor u f)] with ω hc hu hs
  rw [hc,hs,Pi.smul_apply,hu,smul_comm]

def sourceTensor (f : GaussianL2) : CoefficientSpace →L[ℝ] GaussianVectorL2 :=
  ({ toFun := fun u => scalarTensor u f,
     map_add' := fun u v => scalarTensor_add_source u v f,
     map_smul' := fun c u => scalarTensor_smul_source c u f } :
    CoefficientSpace →ₗ[ℝ] GaussianVectorL2).mkContinuous ‖f‖ (fun u => by
      change ‖scalarTensor u f‖≤‖f‖*‖u‖
      have he : ‖scalarTensor u f‖^2=‖f‖^2*‖u‖^2 := by
        rw [← real_inner_self_eq_norm_sq,scalarTensor_pair_inner,real_inner_self_eq_norm_sq,
          real_inner_self_eq_norm_sq]
      nlinarith [norm_nonneg (scalarTensor u f),norm_nonneg f,norm_nonneg u,
        mul_nonneg (norm_nonneg f) (norm_nonneg u)])

theorem observed_rank_divergence_generated {I : Type*} (h : I → CoefficientSpace)
    (i : I) (p : MvPolynomial I ℝ) : rankDivergence (familyCore h p) (h i)∈generated h := by
  have hd := family_derivative_fixed h p
  have hfix := (jointConditional_fixed_iff h _).mp hd
  have hg : AEStronglyMeasurable[MeasurableSpace.comap (firstChaosFamily h) inferInstance]
      (polynomialDerivative (familyCore h p)) gaussianProduct := by
    have hc := hfix.2
    rw [fieldConditional_eq_starProjection] at hc
    exact Submodule.starProjection_eq_self_iff.mp hc
  have hi : firstChaosEmbedding (h i)∈generated h :=
    firstChaos_mem_generated_of_sourceSpan h (h i)
      ((Submodule.span ℝ (Set.range h)).le_topologicalClosure (Submodule.subset_span ⟨i,rfl⟩))
  have hp := familyPolynomial_aestronglyMeasurable h p
  have hm := (hp.mul hi).sub (hg.inner_const (c := h i) (𝕜 := ℝ))
  exact hm.congr (rankDivergence_coeFn (familyCore h p) (h i)).symm

theorem adjoint_divergence_potential {v : GaussianVectorL2} {f : GaussianL2}
    (hg : (v,f)∈hilbertDivergence.graph) : recoveryOperator.adjoint v=potentialOperator f := by
  have hs := recovery_adjoint_kernel_zero _ (residual_divergence_zero v)
  rw [map_sub] at hs
  have he := sub_eq_zero.mp hs
  change recoveryOperator.adjoint v=recoveryOperator.adjoint (recovery f)
  rw [recovery_divergence_gradientProjection _ _ hg]
  exact he

theorem adjoint_observed_polynomial_tensor {I : Type*} (h : I → CoefficientSpace)
    (i : I) (p : MvPolynomial I ℝ) :
    recoveryOperator.adjoint (scalarTensor (h i) (familyPolynomialEmbedding h p))∈generated h := by
  have hg := LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (cylindricalDivergence_rank_graph (familyCore h p) (h i))
  change recoveryOperator.adjoint (scalarTensor (h i) (familyCore h p))∈generated h
  rw [adjoint_divergence_potential hg]
  exact potential_preserves_generated h (observed_rank_divergence_generated h i p)

theorem adjoint_observed_tensor_generator {I : Type*} (h : I → CoefficientSpace)
    (i : I) {f : GaussianL2} (hf : f∈generated h) :
    recoveryOperator.adjoint (scalarTensor (h i) f)∈generated h := by
  let L := recoveryOperator.adjoint.comp (scalarTensor (h i))
  have hs : (familyPolynomialEmbedding h).range ≤ (generated h).comap L.toLinearMap := by
    rintro f ⟨p,rfl⟩
    exact adjoint_observed_polynomial_tensor h i p
  have hc := (familyPolynomialEmbedding h).range.topologicalClosure_minimal hs
    ((generated_isClosed h).preimage L.continuous)
  rw [familyPolynomial_closure] at hc
  exact hc hf

theorem adjoint_observed_tensor {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : u∈sourceSpan h) (f : GaussianL2) (hf : f∈generated h) :
    recoveryOperator.adjoint (scalarTensor u f)∈generated h := by
  let L := recoveryOperator.adjoint.comp (sourceTensor f)
  have hs : Submodule.span ℝ (Set.range h) ≤ (generated h).comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro u ⟨i,rfl⟩
    exact adjoint_observed_tensor_generator h i hf
  have hc := (Submodule.span ℝ (Set.range h)).topologicalClosure_minimal hs
    ((generated_isClosed h).preimage L.continuous)
  exact hc hu

theorem adjoint_joint_mem_generated {I : Type*} (h : I → CoefficientSpace) (v : GaussianVectorL2) :
    recoveryOperator.adjoint (jointConditional h v)∈generated h := by
  let L := recoveryOperator.adjoint.comp (jointConditional h)
  have hs : cylindricalVectorDomain ≤ (generated h).comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro v ⟨p,u,rfl⟩
    change recoveryOperator.adjoint (jointConditional h (scalarTensor u p))∈generated h
    rw [jointConditional,ContinuousLinearMap.comp_apply,fieldConditional_scalarTensor,
      fieldSourceProjection_scalarTensor]
    exact adjoint_observed_tensor h _ ((sourceSpan h).starProjection_apply_mem u) _
      ((generated h).starProjection_apply_mem p)
  have hc := cylindricalVectorDomain.topologicalClosure_minimal hs
    ((generated_isClosed h).preimage L.continuous)
  exact hc (show v∈cylindricalVectorDomain.topologicalClosure from
    cylindricalVectorDomain_dense v)

theorem adjoint_joint_conditional {I : Type*} (h : I → CoefficientSpace) (v : GaussianVectorL2) :
    recoveryOperator.adjoint (jointConditional h v)=conditionalProjection h (recoveryOperator.adjoint v) := by
  symm
  apply (generated h).eq_starProjection_of_mem_of_inner_eq_zero (adjoint_joint_mem_generated h v)
  intro w hw
  rw [inner_sub_left,ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left,
    jointConditional_inner]
  change inner ℝ v (recovery w)-inner ℝ v (jointConditional h (recovery w))=0
  rw [observed_recovery_fixed h hw,sub_self]

theorem joint_recovery_conditional {I : Type*} (h : I → CoefficientSpace) (f : GaussianL2) :
    jointConditional h (recovery f)=recovery (conditionalProjection h f) := by
  apply ext_inner_right ℝ
  intro v
  rw [jointConditional_inner]
  change inner ℝ (recoveryOperator f) (jointConditional h v)=inner ℝ (recoveryOperator (conditionalProjection h f)) v
  rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.adjoint_inner_right,
    adjoint_joint_conditional]
  exact ((generated h).inner_starProjection_left_eq_right f (recoveryOperator.adjoint v)).symm

theorem joint_recovery_operator {I : Type*} (h : I → CoefficientSpace) :
    (jointConditional h).comp recoveryOperator=recoveryOperator.comp (conditionalProjection h) := by
  apply ContinuousLinearMap.ext
  intro f
  exact joint_recovery_conditional h f

end OperatorDerivativeRewrite.Foundation.GaussianJointRecoveryIntertwining
