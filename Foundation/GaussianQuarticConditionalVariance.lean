import Foundation.GaussianQuarticWick
import Foundation.SchurGaussianInnovation
import Foundation.TriadGaussianHodge

/-! Actual Gaussian quartic conditional variances. The raw fourth power contains
both second and fourth chaos, so its retained energy is not a pure fourth-chaos factor. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianQuarticConditionalVariance
open InfiniteGaussian GaussianTimeSpaceHermite GaussianQuarticWick
open GaussianConditionalGraph GaussianWickConditionalProjection
open TriadGaussianHodge (direction direction_inner direction_norm_sq)
set_option backward.isDefEq.respectTransparency false

def centeredQuartic (u : CoefficientSpace) : GaussianL2 :=
  (wick u 4 : GaussianL2)+(6*‖u‖^2 : ℝ) • (wick u 2 : GaussianL2)

theorem centeredQuartic_coeFn (u : CoefficientSpace) :
    centeredQuartic u =ᵐ[gaussianProduct]
      fun ω => (firstChaosEmbedding u ω)^4-3*(‖u‖^2)^2 := by
  filter_upwards [Lp.coeFn_add (wick u 4 : GaussianL2)
    ((6*‖u‖^2 : ℝ) • (wick u 2 : GaussianL2)),
    Lp.coeFn_smul (6*‖u‖^2 : ℝ) (wick u 2 : GaussianL2),
    core_coeFn u (‖u‖^2) 4,core_coeFn u (‖u‖^2) 2] with ω ha hs h4 h2
  change centeredQuartic u ω=_
  rw [centeredQuartic,ha]
  simp only [Pi.add_apply]
  rw [hs]
  change (wick u 4 : GaussianL2) ω+(6*‖u‖^2)*(wick u 2 : GaussianL2) ω=_
  rw [show (wick u 4 : GaussianL2) ω=value 4 (firstChaosEmbedding u ω) (‖u‖^2) from h4,
    show (wick u 2 : GaussianL2) ω=value 2 (firstChaosEmbedding u ω) (‖u‖^2) from h2,
    value_four,value_two]
  ring

theorem centeredQuartic_mean (u : CoefficientSpace) :
    (∫ ω, centeredQuartic u ω ∂gaussianProduct)=0 := by
  rw [← gaussianOne_inner_eq_integral]
  simp only [centeredQuartic,inner_add_right,real_inner_smul_right]
  rw [wick_centered u 3,wick_centered u 1]
  ring

theorem centeredQuartic_norm_sq (u : CoefficientSpace) :
    ‖centeredQuartic u‖^2=96*(‖u‖^2)^4 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [centeredQuartic,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,wick_inner]
  norm_num
  ring

def prediction {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) : GaussianL2 :=
  conditionalProjection h (centeredQuartic u)

theorem prediction_wick {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    prediction h u=(wick (sourceProjection h u) 4 : GaussianL2)+
      (6*‖u‖^2 : ℝ) • (wick (sourceProjection h u) 2 : GaussianL2) := by
  simp only [prediction,centeredQuartic,map_add,map_smul,conditional_wick_projection]

theorem prediction_condExp {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    prediction h u =ᵐ[gaussianProduct]
      gaussianProduct[centeredQuartic u | MeasurableSpace.comap (firstChaosFamily h) inferInstance] :=
  conditionalProjection_ae_condExp h (centeredQuartic u)

theorem prediction_coeFn {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    prediction h u =ᵐ[gaussianProduct] fun ω =>
      (firstChaosEmbedding (sourceProjection h u) ω)^4+
        6*(‖u‖^2-‖sourceProjection h u‖^2)*(firstChaosEmbedding (sourceProjection h u) ω)^2+
        3*(‖sourceProjection h u‖^2)^2-6*‖u‖^2*‖sourceProjection h u‖^2 := by
  rw [prediction_wick]
  filter_upwards [Lp.coeFn_add (wick (sourceProjection h u) 4 : GaussianL2)
    ((6*‖u‖^2 : ℝ) • (wick (sourceProjection h u) 2 : GaussianL2)),
    Lp.coeFn_smul (6*‖u‖^2 : ℝ) (wick (sourceProjection h u) 2 : GaussianL2),
    core_coeFn (sourceProjection h u) (‖sourceProjection h u‖^2) 4,
    core_coeFn (sourceProjection h u) (‖sourceProjection h u‖^2) 2] with ω ha hs h4 h2
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs]
  change (wick (sourceProjection h u) 4 : GaussianL2) ω+
    (6*‖u‖^2)*(wick (sourceProjection h u) 2 : GaussianL2) ω=_
  rw [show (wick (sourceProjection h u) 4 : GaussianL2) ω=
      value 4 (firstChaosEmbedding (sourceProjection h u) ω) (‖sourceProjection h u‖^2) from h4,
    show (wick (sourceProjection h u) 2 : GaussianL2) ω=
      value 2 (firstChaosEmbedding (sourceProjection h u) ω) (‖sourceProjection h u‖^2) from h2,
    value_four,value_two]
  ring

theorem prediction_mean {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    (∫ ω, prediction h u ω ∂gaussianProduct)=0 := by
  rw [prediction_wick,← gaussianOne_inner_eq_integral]
  simp only [inner_add_right,real_inner_smul_right]
  rw [wick_centered _ 3,wick_centered _ 1]
  ring

theorem prediction_norm_sq {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    ‖prediction h u‖^2=24*(‖sourceProjection h u‖^2)^4+
      72*(‖u‖^2)^2*(‖sourceProjection h u‖^2)^2 := by
  rw [← real_inner_self_eq_norm_sq,prediction_wick]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,wick_inner]
  norm_num
  ring

def manuscriptFraction (r : ℝ) : ℝ := (240*r-225*r^2+114*r^3-33*r^4)/96
def correctedFraction (r : ℝ) : ℝ := (240*r-216*r^2+96*r^3-24*r^4)/96

theorem variance_fraction {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace)
    (hu : u ≠ 0) :
    1-‖prediction h u‖^2/‖centeredQuartic u‖^2=
      correctedFraction (1-‖sourceProjection h u‖^2/‖u‖^2) := by
  have hv : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  rw [prediction_norm_sq,centeredQuartic_norm_sq]
  unfold correctedFraction
  field_simp
  <;> ring

theorem fraction_discrepancy (r : ℝ) :
    correctedFraction r-manuscriptFraction r=(3/32 : ℝ)*r^2*(1-r)^2 := by
  unfold correctedFraction manuscriptFraction
  ring

theorem printed_underestimates (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    manuscriptFraction r < correctedFraction r := by
  have he := fraction_discrepancy r
  have hp : 0 < (3/32 : ℝ)*r^2*(1-r)^2 :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hr0)) (sq_pos_of_pos (by linarith))
  linarith

theorem residual_energy {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    ‖centeredQuartic u-prediction h u‖^2=
      96*(‖u‖^2)^4-24*(‖sourceProjection h u‖^2)^4-
        72*(‖u‖^2)^2*(‖sourceProjection h u‖^2)^2 := by
  have hm : prediction h u ∈ generated h := (generated h).starProjection_apply_mem _
  have ho := (generated h).starProjection_inner_eq_zero (centeredQuartic u) (prediction h u) hm
  change inner ℝ (centeredQuartic u-prediction h u) (prediction h u)=0 at ho
  rw [inner_sub_left,real_inner_self_eq_norm_sq] at ho
  rw [prediction_norm_sq] at ho
  rw [norm_sub_sq_real,centeredQuartic_norm_sq,prediction_norm_sq]
  linarith

theorem retained_fraction_zero {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace)
    (hu : u ≠ 0) (hp : sourceProjection h u=u) :
    1-‖prediction h u‖^2/‖centeredQuartic u‖^2=0 := by
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hd : ‖centeredQuartic u‖^2 ≠ 0 := by
    rw [centeredQuartic_norm_sq]
    positivity
  rw [prediction_wick,hp]
  change 1-‖centeredQuartic u‖^2/‖centeredQuartic u‖^2=0
  rw [div_self hd]
  ring

def observed : Unit → CoefficientSpace := fun _ => direction 0
def total : CoefficientSpace := direction 0+direction 1

theorem total_norm_sq : ‖total‖^2=2 := by
  norm_num [total,norm_add_sq_real,direction_norm_sq,direction_inner]

theorem total_projection : sourceProjection observed total=direction 0 := by
  apply (sourceSpan observed).eq_starProjection_of_mem_of_inner_eq_zero
  · exact (Submodule.span ℝ (Set.range observed)).le_topologicalClosure
      (Submodule.subset_span ⟨(),rfl⟩)
  · intro z hz
    rw [SchurGaussianInnovation.sourceSpan_eq_span] at hz
    change z ∈ Submodule.span ℝ (Set.range (fun _ : Unit => direction 0)) at hz
    have hz' : z ∈ Submodule.span ℝ {direction 0} := by
      simpa only [Set.range_const] using hz
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz'
    simp [total,real_inner_smul_right,inner_add_left,inner_sub_left,direction_inner]

theorem example_full_variance : ‖centeredQuartic total‖^2=1536 := by
  rw [centeredQuartic_norm_sq,total_norm_sq]
  norm_num

theorem example_retained_variance : ‖prediction observed total‖^2=312 := by
  rw [prediction_norm_sq,total_projection,direction_norm_sq,total_norm_sq]
  norm_num

theorem example_fraction : 1-‖prediction observed total‖^2/‖centeredQuartic total‖^2=(51/64 : ℝ) := by
  rw [example_full_variance,example_retained_variance]
  norm_num

theorem example_printed_fraction : manuscriptFraction (1/2)=(405/512 : ℝ) := by
  norm_num [manuscriptFraction]

theorem example_printed_fraction_fails :
    1-‖prediction observed total‖^2/‖centeredQuartic total‖^2 ≠ manuscriptFraction (1/2) := by
  rw [example_fraction,example_printed_fraction]
  norm_num

theorem example_interior_fraction : 1-‖sourceProjection observed total‖^2/‖total‖^2=(1/2 : ℝ) := by
  rw [total_projection,direction_norm_sq,total_norm_sq]
  norm_num

theorem total_coordinate_coeFn : firstChaosEmbedding total =ᵐ[gaussianProduct]
    fun ω : SampleSpace => ω 0+ω 1 := by
  have he : firstChaosEmbedding total=firstChaosEmbedding (direction 0)+firstChaosEmbedding (direction 1) :=
    firstChaosEmbedding.map_add _ _
  rw [he]
  filter_upwards [Lp.coeFn_add (firstChaosEmbedding (direction 0)) (firstChaosEmbedding (direction 1)),
    TriadGaussianHodge.coordinate_coeFn 0,TriadGaussianHodge.coordinate_coeFn 1] with ω ha h0 h1
  change firstChaosEmbedding (direction 0) ω=ω 0 at h0
  change firstChaosEmbedding (direction 1) ω=ω 1 at h1
  rw [ha]
  exact congrArg₂ (·+·) h0 h1

theorem example_centered_coeFn : centeredQuartic total =ᵐ[gaussianProduct]
    fun ω : SampleSpace => (ω 0+ω 1)^4-12 := by
  filter_upwards [centeredQuartic_coeFn total,total_coordinate_coeFn] with ω hc hx
  rw [hc,hx,total_norm_sq]
  norm_num

theorem example_prediction_coeFn : prediction observed total =ᵐ[gaussianProduct]
    fun ω : SampleSpace => (ω 0)^4+6*(ω 0)^2-9 := by
  have hp := prediction_coeFn observed total
  simp only [total_projection,direction_norm_sq,total_norm_sq] at hp
  filter_upwards [hp,TriadGaussianHodge.coordinate_coeFn 0] with ω hp h0
  change firstChaosEmbedding (direction 0) ω=ω 0 at h0
  rw [hp,h0]
  ring

theorem example_conditional_expectation :
    gaussianProduct[(fun ω : SampleSpace => (ω 0+ω 1)^4-12) |
      MeasurableSpace.comap (firstChaosFamily observed) inferInstance] =ᵐ[gaussianProduct]
        fun ω : SampleSpace => (ω 0)^4+6*(ω 0)^2-9 := by
  have hc := (prediction_condExp observed total).trans (condExp_congr_ae example_centered_coeFn)
  exact hc.symm.trans example_prediction_coeFn

theorem example_raw_mean : (∫ ω : SampleSpace, (ω 0+ω 1)^4 ∂gaussianProduct)=12 := by
  have hi : Integrable (centeredQuartic total) gaussianProduct :=
    (Lp.memLp (centeredQuartic total)).integrable (by norm_num)
  have he : (fun ω : SampleSpace => (ω 0+ω 1)^4) =ᵐ[gaussianProduct]
      fun ω => centeredQuartic total ω+12 := by
    filter_upwards [example_centered_coeFn] with ω hx
    rw [hx]
    ring
  rw [integral_congr_ae he,integral_add hi (integrable_const _),centeredQuartic_mean]
  simp

theorem example_full_integral_variance :
    (∫ ω : SampleSpace, ((ω 0+ω 1)^4-12)^2 ∂gaussianProduct)=1536 := by
  rw [← example_full_variance,← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [example_centered_coeFn] with ω hx
  simp [hx,RCLike.inner_apply,pow_two]

theorem example_retained_integral_variance :
    (∫ ω : SampleSpace, ((ω 0)^4+6*(ω 0)^2-9)^2 ∂gaussianProduct)=312 := by
  rw [← example_retained_variance,← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [example_prediction_coeFn] with ω hx
  simp [hx,RCLike.inner_apply,pow_two]

end OperatorDerivativeRewrite.Foundation.GaussianQuarticConditionalVariance
