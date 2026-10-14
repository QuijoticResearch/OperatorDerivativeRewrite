import Foundation.GaussianWickRecoveryPrediction
import Foundation.SPDEWickModes

/-! The actual joint observed-source and observed-sample orthogonal projection. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianJointSourceProjection
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection GaussianWickRecoveryPrediction
open GaussianDivergenceRecovery SPDEWickModes

private instance observation_le {I : Type*} (h : I → CoefficientSpace) :
    Fact (MeasurableSpace.comap (firstChaosFamily h) inferInstance≤(inferInstance : MeasurableSpace SampleSpace)) :=
  ⟨generatedSigma_le h⟩

def fieldSourceProjection {I : Type*} (h : I → CoefficientSpace) : GaussianVectorL2 →L[ℝ] GaussianVectorL2 :=
  (sourceProjection h).compLpL 2 gaussianProduct

theorem fieldSourceProjection_scalarTensor {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (f : GaussianL2) :
    fieldSourceProjection h (scalarTensor u f)=scalarTensor (sourceProjection h u) f := by
  apply Lp.ext
  filter_upwards [(sourceProjection h).coeFn_compLpL (scalarTensor u f),scalarTensor_coeFn u f,
    scalarTensor_coeFn (sourceProjection h u) f] with ω hp hu hv
  change ((sourceProjection h).compLpL 2 gaussianProduct (scalarTensor u f)) ω=_
  rw [hp,hu,hv,map_smul]

theorem fieldConditional_source_commute {I : Type*} (h : I → CoefficientSpace) (f : GaussianVectorL2) :
    fieldConditional h (fieldSourceProjection h f)=fieldSourceProjection h (fieldConditional h f) := by
  apply Lp.ext
  have he := condExpL2_comp_continuousLinearMap ℝ ℝ (generatedSigma_le h) (sourceProjection h) f
  change fieldConditional h (fieldSourceProjection h f)=ᵐ[gaussianProduct]
    fieldSourceProjection h (fieldConditional h f) at he
  exact he

theorem fieldSourceProjection_idempotent {I : Type*} (h : I → CoefficientSpace) (f : GaussianVectorL2) :
    fieldSourceProjection h (fieldSourceProjection h f)=fieldSourceProjection h f := by
  have hP (u : CoefficientSpace) : sourceProjection h (sourceProjection h u)=sourceProjection h u :=
    Submodule.starProjection_eq_self_iff.mpr ((sourceSpan h).starProjection_apply_mem u)
  apply Lp.ext
  filter_upwards [(sourceProjection h).coeFn_compLpL (fieldSourceProjection h f),
    (sourceProjection h).coeFn_compLpL f] with ω h1 h2
  calc
    _=sourceProjection h ((fieldSourceProjection h f) ω) := h1
    _=sourceProjection h (sourceProjection h (f ω)) := congrArg (sourceProjection h) h2
    _=sourceProjection h (f ω) := hP _
    _=(fieldSourceProjection h f) ω := h2.symm

theorem fieldSourceProjection_inner {I : Type*} (h : I → CoefficientSpace) (f g : GaussianVectorL2) :
    inner ℝ (fieldSourceProjection h f) g=inner ℝ f (fieldSourceProjection h g) := by
  rw [L2_inner_eq_integral,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [(sourceProjection h).coeFn_compLpL f,(sourceProjection h).coeFn_compLpL g] with ω hf hg
  change inner ℝ (((sourceProjection h).compLpL 2 gaussianProduct f) ω) (g ω)=
    inner ℝ (f ω) (((sourceProjection h).compLpL 2 gaussianProduct g) ω)
  rw [hf,hg]
  exact (sourceSpan h).inner_starProjection_left_eq_right (f ω) (g ω)

theorem fieldConditional_eq_starProjection {I : Type*} (h : I → CoefficientSpace) :
    fieldConditional h=(lpMeas CoefficientSpace ℝ (MeasurableSpace.comap (firstChaosFamily h) inferInstance)
      2 gaussianProduct).starProjection := rfl

theorem fieldConditional_idempotent {I : Type*} (h : I → CoefficientSpace) (f : GaussianVectorL2) :
    fieldConditional h (fieldConditional h f)=fieldConditional h f := by
  rw [fieldConditional_eq_starProjection]
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ f)

theorem fieldConditional_inner {I : Type*} (h : I → CoefficientSpace) (f g : GaussianVectorL2) :
    inner ℝ (fieldConditional h f) g=inner ℝ f (fieldConditional h g) := by
  rw [fieldConditional_eq_starProjection]
  exact Submodule.inner_starProjection_left_eq_right _ f g

def jointConditional {I : Type*} (h : I → CoefficientSpace) : GaussianVectorL2 →L[ℝ] GaussianVectorL2 :=
  (fieldSourceProjection h).comp (fieldConditional h)

theorem jointConditional_idempotent {I : Type*} (h : I → CoefficientSpace) (f : GaussianVectorL2) :
    jointConditional h (jointConditional h f)=jointConditional h f := by
  simp only [jointConditional,ContinuousLinearMap.comp_apply]
  rw [fieldConditional_source_commute,fieldConditional_idempotent,fieldSourceProjection_idempotent]

theorem jointConditional_inner {I : Type*} (h : I → CoefficientSpace) (f g : GaussianVectorL2) :
    inner ℝ (jointConditional h f) g=inner ℝ f (jointConditional h g) := by
  simp only [jointConditional,ContinuousLinearMap.comp_apply]
  rw [fieldSourceProjection_inner,fieldConditional_inner,fieldConditional_source_commute]

theorem jointConditional_norm_le {I : Type*} (h : I → CoefficientSpace) (f : GaussianVectorL2) :
    ‖jointConditional h f‖≤‖f‖ := by
  have he := jointConditional_inner h f (jointConditional h f)
  rw [jointConditional_idempotent,real_inner_self_eq_norm_sq] at he
  have hi := real_inner_le_norm f (jointConditional h f)
  rw [← he] at hi
  by_cases hz : ‖jointConditional h f‖=0
  · rw [hz]; exact norm_nonneg _
  · have hp : 0<‖jointConditional h f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

theorem jointConditional_fixed_iff {I : Type*} (h : I → CoefficientSpace) (f : GaussianVectorL2) :
    jointConditional h f=f ↔ fieldSourceProjection h f=f ∧ fieldConditional h f=f := by
  have hm : fieldSourceProjection h (jointConditional h f)=jointConditional h f := by
    simp only [jointConditional,ContinuousLinearMap.comp_apply]
    exact fieldSourceProjection_idempotent h _
  have he : fieldConditional h (jointConditional h f)=jointConditional h f := by
    simp only [jointConditional,ContinuousLinearMap.comp_apply]
    rw [fieldConditional_source_commute,fieldConditional_idempotent]
  constructor
  · intro hf
    constructor
    · calc
        _=fieldSourceProjection h (jointConditional h f) := congrArg (fieldSourceProjection h) hf.symm
        _=jointConditional h f := hm
        _=f := hf
    · calc
        _=fieldConditional h (jointConditional h f) := congrArg (fieldConditional h) hf.symm
        _=jointConditional h f := he
        _=f := hf
  · rintro ⟨hm,he⟩
    rw [jointConditional,ContinuousLinearMap.comp_apply,he,hm]
theorem jointConditional_wick_recovery {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) (n : ℕ) :
    jointConditional h (recovery (GaussianTimeSpaceHermite.wick u (n+1)))=
      recovery (conditionalProjection h (GaussianTimeSpaceHermite.wick u (n+1))) := by
  rw [jointConditional,ContinuousLinearMap.comp_apply,recovery_wick,fieldConditional_scalarTensor,
    conditional_wick_projection,fieldSourceProjection_scalarTensor,predicted_wick_recovery]

theorem jointConditional_countable_wick_recovery {I : Type*} (h : I → CoefficientSpace)
    (u : ℕ → CoefficientSpace) (hu : ∀ i j, i≠j → inner ℝ (u i) (u j)=0)
    (d : ℕ) (hd : 0<d) (c : ℕ → ℝ)
    (hs : Summable (fun i => (c i)^2*(d.factorial : ℝ)*(‖u i‖^2)^d)) :
    jointConditional h (recovery (wickResponse u d c))=recovery (conditionalProjection h (wickResponse u d c)) := by
  have ha := ((jointConditional h).comp recoveryOperator).hasSum (wickResponse_hasSum u hu d hd c hs)
  have hb := (recoveryOperator.comp (conditionalProjection h)).hasSum (wickResponse_hasSum u hu d hd c hs)
  have he (i : ℕ) : jointConditional h (recovery (GaussianTimeSpaceHermite.wick (u i) d))=
      recovery (conditionalProjection h (GaussianTimeSpaceHermite.wick (u i) d)) := by
    have hdn : d=(d-1)+1 := by omega
    rw [hdn]
    exact jointConditional_wick_recovery h (u i) (d-1)
  simp only [ContinuousLinearMap.comp_apply,map_smul] at ha hb
  change HasSum (fun i => c i • jointConditional h (recovery (GaussianTimeSpaceHermite.wick (u i) d)))
    (jointConditional h (recovery (wickResponse u d c))) at ha
  change HasSum (fun i => c i • recovery (conditionalProjection h (GaussianTimeSpaceHermite.wick (u i) d)))
    (recovery (conditionalProjection h (wickResponse u d c))) at hb
  simp only [he] at ha
  exact ha.unique hb

end OperatorDerivativeRewrite.Foundation.GaussianJointSourceProjection


