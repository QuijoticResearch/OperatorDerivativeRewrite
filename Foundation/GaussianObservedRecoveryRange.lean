import Foundation.GaussianInverseNumberPotential
import Foundation.GaussianJointSourceProjection
import Foundation.GaussianGeneratedGraphCore

/-! Every derivative of an observed Gaussian target is fixed by the actual joint projection. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianObservedRecoveryRange
open InfiniteGaussian GaussianNumberSectors GaussianConditionalGraph GaussianGeneratedGraphCore
open GaussianWickConditionalProjection GaussianWickRecoveryPrediction GaussianJointSourceProjection
open GaussianInverseNumberPotential GaussianDivergenceRecovery

theorem observed_tensor_fixed {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : u∈sourceSpan h) (f : GaussianL2) (hf : f∈generated h) :
    jointConditional h (scalarTensor u f)=scalarTensor u f := by
  have he : conditionalProjection h f=f := (generated h).starProjection_eq_self_iff.mpr hf
  have hs : sourceProjection h u=u := (sourceSpan h).starProjection_eq_self_iff.mpr hu
  rw [jointConditional,ContinuousLinearMap.comp_apply,fieldConditional_scalarTensor,
    fieldSourceProjection_scalarTensor,he,hs]

theorem finite_observed_derivative_fixed {I J : Type*} [Fintype J] (h : I → CoefficientSpace)
    (k : J → CoefficientSpace) (hk : ∀ j, k j∈sourceSpan h)
    (hp : ∀ q : MvPolynomial J ℝ, familyPolynomialEmbedding k q∈generated h)
    (p : MvPolynomial J ℝ) :
    jointConditional h (polynomialDerivative (cylinderCore k p))=
      polynomialDerivative (cylinderCore k p) := by
  rw [cylinder_gradient_expansion]
  change jointConditional h (∑ j, scalarTensor (k j) (cylinderCore k (MvPolynomial.pderiv j p)))=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact observed_tensor_fixed h (k j) (hk j) _ (hp _)

theorem family_derivative_fixed {I : Type*} (h : I → CoefficientSpace) (p : MvPolynomial I ℝ) :
    jointConditional h (polynomialDerivative (familyCore h p))=polynomialDerivative (familyCore h p) := by
  obtain ⟨s,p,rfl⟩ := MvPolynomial.exists_finset_rename p
  have he : familyCore h (MvPolynomial.rename Subtype.val p)=cylinderCore (fun i : s => h i) p := by
    apply Subtype.ext
    exact familyPolynomial_rename h s p
  rw [he]
  apply finite_observed_derivative_fixed
  · intro i
    exact (Submodule.span ℝ (Set.range h)).le_topologicalClosure (Submodule.subset_span ⟨i.val,rfl⟩)
  · intro q
    change isonormalCylinderL2 (fun i : s => h i) q∈generated h
    rw [← familyPolynomial_rename h s q]
    exact familyPolynomial_aestronglyMeasurable h _

theorem observed_derivative_fixed {I : Type*} (h : I → CoefficientSpace)
    {f : GaussianL2} {g : GaussianVectorL2} (hf : f∈generated h)
    (hd : (f,g)∈closedCylindricalDerivative.graph) : jointConditional h g=g := by
  let L := (jointConditional h-ContinuousLinearMap.id ℝ GaussianVectorL2).comp
    (ContinuousLinearMap.snd ℝ GaussianL2 GaussianVectorL2)
  have hs : (familyGraphMap h).range ≤ L.ker := by
    rintro z ⟨p,rfl⟩
    change jointConditional h (polynomialDerivative (familyCore h p))-
      polynomialDerivative (familyCore h p)=0
    rw [family_derivative_fixed,sub_self]
  have hc := (familyGraphMap h).range.topologicalClosure_minimal hs L.isClosed_ker
  have he := hc (independent_graph_mem_completedFamily h hf hd)
  change jointConditional h g-g=0 at he
  exact sub_eq_zero.mp he

theorem observed_recovery_fixed {I : Type*} (h : I → CoefficientSpace)
    {f : GaussianL2} (hf : f∈generated h) : jointConditional h (recovery f)=recovery f :=
  observed_derivative_fixed h (potential_preserves_generated h hf) (potential_derivative_graph f)

theorem conditional_recovery_joint_fixed {I : Type*} (h : I → CoefficientSpace) (f : GaussianL2) :
    jointConditional h (recovery (conditionalProjection h f))=recovery (conditionalProjection h f) :=
  observed_recovery_fixed h ((generated h).starProjection_apply_mem f)

theorem conditional_recovery_constraints {I : Type*} (h : I → CoefficientSpace) (f : GaussianL2) :
    fieldSourceProjection h (recovery (conditionalProjection h f))=recovery (conditionalProjection h f) ∧
      fieldConditional h (recovery (conditionalProjection h f))=recovery (conditionalProjection h f) :=
  (jointConditional_fixed_iff h _).mp (conditional_recovery_joint_fixed h f)

end OperatorDerivativeRewrite.Foundation.GaussianObservedRecoveryRange
