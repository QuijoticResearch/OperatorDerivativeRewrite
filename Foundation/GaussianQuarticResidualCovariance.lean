import Foundation.GaussianQuarticConditionalVariance

/-! Conditional quartic residuals can have negative cross covariance, even for
orthogonal total Gaussian directions. Block variance must retain these terms. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianQuarticResidualCovariance
open InfiniteGaussian GaussianTimeSpaceHermite GaussianConditionalGraph
open GaussianWickConditionalProjection GaussianQuarticConditionalVariance
open TriadGaussianHodge (direction direction_inner direction_norm_sq)
set_option backward.isDefEq.respectTransparency false

theorem quartic_covariance (u v : CoefficientSpace) :
    inner ℝ (centeredQuartic u) (centeredQuartic v)=
      72*‖u‖^2*‖v‖^2*(inner ℝ u v)^2+24*(inner ℝ u v)^4 := by
  simp only [centeredQuartic,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,wick_inner]
  norm_num
  ring

theorem prediction_covariance {I : Type*} (h : I → CoefficientSpace) (u v : CoefficientSpace) :
    inner ℝ (prediction h u) (prediction h v)=
      72*‖u‖^2*‖v‖^2*(inner ℝ (sourceProjection h u) (sourceProjection h v))^2+
        24*(inner ℝ (sourceProjection h u) (sourceProjection h v))^4 := by
  rw [prediction_wick,prediction_wick]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,wick_inner]
  norm_num
  ring

def residual {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) : GaussianL2 :=
  centeredQuartic u-prediction h u

theorem residual_mean {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    (∫ ω, residual h u ω ∂gaussianProduct)=0 := by
  rw [← gaussianOne_inner_eq_integral]
  simp only [residual,inner_sub_right,gaussianOne_inner_eq_integral,
    centeredQuartic_mean,prediction_mean,sub_self]

theorem residual_prediction_orthogonal {I : Type*} (h : I → CoefficientSpace)
    (u v : CoefficientSpace) : inner ℝ (residual h u) (prediction h v)=0 := by
  exact (generated h).starProjection_inner_eq_zero (centeredQuartic u) (prediction h v)
    ((generated h).starProjection_apply_mem _)

theorem residual_covariance {I : Type*} (h : I → CoefficientSpace) (u v : CoefficientSpace) :
    inner ℝ (residual h u) (residual h v)=
      inner ℝ (centeredQuartic u) (centeredQuartic v)-inner ℝ (prediction h u) (prediction h v) := by
  have h1 := residual_prediction_orthogonal h u v
  have h2 := residual_prediction_orthogonal h v u
  simp only [residual,inner_sub_left] at h1 h2
  have h2' : inner ℝ (prediction h u) (centeredQuartic v)-
      inner ℝ (prediction h u) (prediction h v)=0 := by
    simpa only [real_inner_comm] using h2
  simp only [residual,inner_sub_left,inner_sub_right]
  linarith

theorem quartic_covariance_integral (u v : CoefficientSpace) :
    (∫ ω, ((firstChaosEmbedding u ω)^4-3*(‖u‖^2)^2)*
      ((firstChaosEmbedding v ω)^4-3*(‖v‖^2)^2) ∂gaussianProduct)=
        72*‖u‖^2*‖v‖^2*(inner ℝ u v)^2+24*(inner ℝ u v)^4 := by
  rw [← quartic_covariance,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [centeredQuartic_coeFn u,centeredQuartic_coeFn v] with ω hu hv
  simp [hu,hv,RCLike.inner_apply] <;> ring

def reflected : CoefficientSpace := direction 0-direction 1

theorem reflected_norm_sq : ‖reflected‖^2=2 := by
  norm_num [reflected,norm_sub_sq_real,direction_norm_sq,direction_inner]

theorem total_reflected_inner : inner ℝ total reflected=0 := by
  norm_num [total,reflected,inner_add_left,inner_sub_right,direction_inner,direction_norm_sq]

theorem reflected_projection : sourceProjection observed reflected=direction 0 := by
  apply (sourceSpan observed).eq_starProjection_of_mem_of_inner_eq_zero
  · exact (Submodule.span ℝ (Set.range observed)).le_topologicalClosure
      (Submodule.subset_span ⟨(),rfl⟩)
  · intro z hz
    rw [SchurGaussianInnovation.sourceSpan_eq_span] at hz
    change z ∈ Submodule.span ℝ (Set.range (fun _ : Unit => direction 0)) at hz
    have hz' : z ∈ Submodule.span ℝ {direction 0} := by simpa only [Set.range_const] using hz
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz'
    simp [reflected,real_inner_smul_right,inner_sub_left,direction_inner]

theorem example_full_covariance : inner ℝ (centeredQuartic total) (centeredQuartic reflected)=0 := by
  rw [quartic_covariance,total_reflected_inner]
  norm_num

theorem example_prediction_covariance : inner ℝ (prediction observed total) (prediction observed reflected)=312 := by
  rw [prediction_covariance,total_norm_sq,reflected_norm_sq,total_projection,reflected_projection,direction_inner]
  norm_num

theorem example_residual_covariance : inner ℝ (residual observed total) (residual observed reflected)= -312 := by
  rw [residual_covariance,example_full_covariance,example_prediction_covariance]
  norm_num

theorem example_reflected_variance : ‖centeredQuartic reflected‖^2=1536 := by
  rw [centeredQuartic_norm_sq,reflected_norm_sq]
  norm_num

theorem example_reflected_prediction_variance : ‖prediction observed reflected‖^2=312 := by
  rw [prediction_norm_sq,reflected_norm_sq,reflected_projection,direction_norm_sq]
  norm_num

theorem example_residual_variances :
    ‖residual observed total‖^2=1224 ∧ ‖residual observed reflected‖^2=1224 := by
  constructor
  · rw [residual,residual_energy,total_projection,total_norm_sq,direction_norm_sq]
    norm_num
  · rw [residual,residual_energy,reflected_projection,reflected_norm_sq,direction_norm_sq]
    norm_num

theorem example_sum_full_variance : ‖centeredQuartic total+centeredQuartic reflected‖^2=3072 := by
  rw [norm_add_sq_real,example_full_variance,example_reflected_variance,example_full_covariance]
  norm_num

theorem example_sum_prediction_variance : ‖prediction observed total+prediction observed reflected‖^2=1248 := by
  rw [norm_add_sq_real,example_retained_variance,example_reflected_prediction_variance,
    example_prediction_covariance]
  norm_num

theorem example_sum_residual_variance : ‖residual observed total+residual observed reflected‖^2=1824 := by
  rw [norm_add_sq_real,example_residual_variances.1,example_residual_variances.2,example_residual_covariance]
  norm_num

theorem residual_sum_below_diagonal :
    ‖residual observed total+residual observed reflected‖^2 <
      ‖residual observed total‖^2+‖residual observed reflected‖^2 := by
  rw [example_sum_residual_variance,example_residual_variances.1,example_residual_variances.2]
  norm_num

theorem sum_prediction_is_conditional :
    prediction observed total+prediction observed reflected=
      conditionalProjection observed (centeredQuartic total+centeredQuartic reflected) := by
  simp only [map_add,prediction]

theorem example_sum_fraction :
    1-‖conditionalProjection observed (centeredQuartic total+centeredQuartic reflected)‖^2/
      ‖centeredQuartic total+centeredQuartic reflected‖^2=(19/32 : ℝ) := by
  rw [← sum_prediction_is_conditional,example_sum_prediction_variance,example_sum_full_variance]
  norm_num

theorem sum_fraction_below_individual :
    1-‖conditionalProjection observed (centeredQuartic total+centeredQuartic reflected)‖^2/
      ‖centeredQuartic total+centeredQuartic reflected‖^2 <
    1-‖prediction observed total‖^2/‖centeredQuartic total‖^2 := by
  rw [example_sum_fraction,example_fraction]
  norm_num

theorem reflected_coordinate_coeFn : firstChaosEmbedding reflected =ᵐ[gaussianProduct]
    fun ω : SampleSpace => ω 0-ω 1 := by
  have he : firstChaosEmbedding reflected=firstChaosEmbedding (direction 0)-firstChaosEmbedding (direction 1) :=
    firstChaosEmbedding.map_sub _ _
  rw [he]
  filter_upwards [Lp.coeFn_sub (firstChaosEmbedding (direction 0)) (firstChaosEmbedding (direction 1)),
    TriadGaussianHodge.coordinate_coeFn 0,TriadGaussianHodge.coordinate_coeFn 1] with ω ha h0 h1
  change firstChaosEmbedding (direction 0) ω=ω 0 at h0
  change firstChaosEmbedding (direction 1) ω=ω 1 at h1
  rw [ha]
  exact congrArg₂ (·-·) h0 h1

theorem reflected_prediction_eq : prediction observed reflected=prediction observed total := by
  rw [prediction_wick,prediction_wick,total_projection,reflected_projection,total_norm_sq,reflected_norm_sq]

theorem residual_plus_coeFn : residual observed total =ᵐ[gaussianProduct]
    fun ω : SampleSpace => (ω 0+ω 1)^4-(ω 0)^4-6*(ω 0)^2-3 := by
  filter_upwards [Lp.coeFn_sub (centeredQuartic total) (prediction observed total),
    example_centered_coeFn,example_prediction_coeFn] with ω hs hc hp
  change (centeredQuartic total-prediction observed total) ω=_
  rw [hs]
  change centeredQuartic total ω-prediction observed total ω=_
  rw [hc,hp]
  ring

theorem residual_minus_coeFn : residual observed reflected =ᵐ[gaussianProduct]
    fun ω : SampleSpace => (ω 0-ω 1)^4-(ω 0)^4-6*(ω 0)^2-3 := by
  filter_upwards [Lp.coeFn_sub (centeredQuartic reflected) (prediction observed reflected),
    centeredQuartic_coeFn reflected,reflected_coordinate_coeFn,example_prediction_coeFn] with ω hs hc hx hp
  change (centeredQuartic reflected-prediction observed reflected) ω=_
  rw [hs]
  change centeredQuartic reflected ω-prediction observed reflected ω=_
  rw [hc,hx,reflected_norm_sq,reflected_prediction_eq,hp]
  ring

theorem example_residual_integral :
    (∫ ω : SampleSpace,
      ((ω 0+ω 1)^4-(ω 0)^4-6*(ω 0)^2-3)*
      ((ω 0-ω 1)^4-(ω 0)^4-6*(ω 0)^2-3) ∂gaussianProduct)= -312 := by
  rw [← example_residual_covariance,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [residual_plus_coeFn,residual_minus_coeFn] with ω hp hm
  simp [hp,hm,RCLike.inner_apply] <;> ring

end OperatorDerivativeRewrite.Foundation.GaussianQuarticResidualCovariance
