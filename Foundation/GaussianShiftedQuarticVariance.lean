import Foundation.GaussianQuarticConditionalVariance

/-! The shifted Gaussian fourth power has a genuine conditional-variance
minimum at zero shift. This validates a local part of the entropy manuscript. -/
noncomputable section
open MeasureTheory Polynomial
namespace OperatorDerivativeRewrite.Foundation.GaussianShiftedQuarticVariance
open InfiniteGaussian GaussianTimeSpaceHermite GaussianQuarticWick
open TriadGaussianHodge (direction direction_norm_sq)
set_option backward.isDefEq.respectTransparency false

theorem value_three (x v : ℝ) : value 3 x v=x^3-3*v*x := by
  have h := value_recursion 1 x v
  rw [value_two,value_one] at h
  convert h using 1 <;> ring

def shiftedCentered (b : ℝ) (u : CoefficientSpace) : GaussianL2 :=
  (wick u 4 : GaussianL2)+(4*b : ℝ) • (wick u 3 : GaussianL2)+
    (6*(b^2+‖u‖^2) : ℝ) • (wick u 2 : GaussianL2)+
    (4*b*(b^2+3*‖u‖^2) : ℝ) • (wick u 1 : GaussianL2)

theorem shiftedCentered_coeFn (b : ℝ) (u : CoefficientSpace) :
    shiftedCentered b u =ᵐ[gaussianProduct] fun ω =>
      (b+firstChaosEmbedding u ω)^4-(b^4+6*b^2*‖u‖^2+3*(‖u‖^2)^2) := by
  filter_upwards [Lp.coeFn_add
    ((wick u 4 : GaussianL2)+(4*b : ℝ) • (wick u 3 : GaussianL2)+
      (6*(b^2+‖u‖^2) : ℝ) • (wick u 2 : GaussianL2))
    ((4*b*(b^2+3*‖u‖^2) : ℝ) • (wick u 1 : GaussianL2)),
    Lp.coeFn_add ((wick u 4 : GaussianL2)+(4*b : ℝ) • (wick u 3 : GaussianL2))
      ((6*(b^2+‖u‖^2) : ℝ) • (wick u 2 : GaussianL2)),
    Lp.coeFn_add (wick u 4 : GaussianL2) ((4*b : ℝ) • (wick u 3 : GaussianL2)),
    Lp.coeFn_smul (4*b : ℝ) (wick u 3 : GaussianL2),
    Lp.coeFn_smul (6*(b^2+‖u‖^2) : ℝ) (wick u 2 : GaussianL2),
    Lp.coeFn_smul (4*b*(b^2+3*‖u‖^2) : ℝ) (wick u 1 : GaussianL2),
    core_coeFn u (‖u‖^2) 4,core_coeFn u (‖u‖^2) 3,
    core_coeFn u (‖u‖^2) 2,core_coeFn u (‖u‖^2) 1] with ω ha hb hc hs3 hs2 hs1 h4 h3 h2 h1
  rw [shiftedCentered,ha]
  simp only [Pi.add_apply]
  rw [hb]
  simp only [Pi.add_apply]
  rw [hc]
  simp only [Pi.add_apply]
  rw [hs3,hs2,hs1]
  simp only [Pi.smul_apply,smul_eq_mul]
  change (wick u 4 : GaussianL2) ω+4*b*(wick u 3 : GaussianL2) ω+
    (6*(b^2+‖u‖^2))*(wick u 2 : GaussianL2) ω+
    (4*b*(b^2+3*‖u‖^2))*(wick u 1 : GaussianL2) ω=_
  rw [show (wick u 4 : GaussianL2) ω=value 4 (firstChaosEmbedding u ω) (‖u‖^2) from h4,
    show (wick u 3 : GaussianL2) ω=value 3 (firstChaosEmbedding u ω) (‖u‖^2) from h3,
    show (wick u 2 : GaussianL2) ω=value 2 (firstChaosEmbedding u ω) (‖u‖^2) from h2,
    show (wick u 1 : GaussianL2) ω=value 1 (firstChaosEmbedding u ω) (‖u‖^2) from h1,
    value_four,value_three,value_two,value_one]
  ring

theorem shiftedCentered_mean (b : ℝ) (u : CoefficientSpace) :
    (∫ ω, shiftedCentered b u ω ∂gaussianProduct)=0 := by
  rw [← gaussianOne_inner_eq_integral]
  simp only [shiftedCentered,inner_add_right,real_inner_smul_right]
  rw [wick_centered u 3,wick_centered u 2,wick_centered u 1,wick_centered u 0]
  ring

theorem shiftedCentered_norm_sq (b : ℝ) (u : CoefficientSpace) :
    ‖shiftedCentered b u‖^2=16*b^6*‖u‖^2+168*b^4*(‖u‖^2)^2+
      384*b^2*(‖u‖^2)^3+96*(‖u‖^2)^4 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [shiftedCentered,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,wick_inner]
  norm_num
  ring

theorem variance_minimum (b : ℝ) (u : CoefficientSpace) :
    96*(‖u‖^2)^4 ≤ ‖shiftedCentered b u‖^2 := by
  rw [shiftedCentered_norm_sq]
  have h1 : 0 ≤ 16*b^6*‖u‖^2 := by positivity
  have h2 : 0 ≤ 168*b^4*(‖u‖^2)^2 := by positivity
  have h3 : 0 ≤ 384*b^2*(‖u‖^2)^3 := by positivity
  linarith

theorem variance_at_zero (u : CoefficientSpace) :
    ‖shiftedCentered 0 u‖^2=96*(‖u‖^2)^4 := by
  simp [shiftedCentered_norm_sq]

theorem variance_strict (b : ℝ) (u : CoefficientSpace) (hb : b ≠ 0) (hu : u ≠ 0) :
    96*(‖u‖^2)^4 < ‖shiftedCentered b u‖^2 := by
  rw [shiftedCentered_norm_sq]
  have h1 : 0 ≤ 16*b^6*‖u‖^2 := by positivity
  have h2 : 0 ≤ 168*b^4*(‖u‖^2)^2 := by positivity
  have h3 : 0 < 384*b^2*(‖u‖^2)^3 :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hb))
      (pow_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)) 3)
  linarith

def fiberCentered (b z : ℝ) : ℝ := (b+z)^4-(b^4+6*b^2+3)

theorem fiber_lift (b : ℝ) : shiftedCentered b (direction 0) =ᵐ[gaussianProduct]
    fun ω : SampleSpace => fiberCentered b (ω 0) := by
  filter_upwards [shiftedCentered_coeFn b (direction 0),
    TriadGaussianHodge.coordinate_coeFn 0] with ω hc h0
  change firstChaosEmbedding (direction 0) ω=ω 0 at h0
  rw [hc,h0,direction_norm_sq]
  unfold fiberCentered
  ring

theorem fiber_centered_mean (b : ℝ) : (∫ z : ℝ, fiberCentered b z ∂GaussianCore.γ)=0 := by
  have hm := integral_map (μ := gaussianProduct)
    (coordinate_measurePreserving 0).measurable.aemeasurable
    (f := fiberCentered b) (by fun_prop [fiberCentered])
  rw [(coordinate_measurePreserving 0).map_eq] at hm
  rw [hm]
  exact (integral_congr_ae (fiber_lift b).symm).trans (shiftedCentered_mean b (direction 0))

theorem fiber_integrable (b : ℝ) : Integrable (fiberCentered b) GaussianCore.γ := by
  have h := (GaussianCore.polynomial_memLp
    ((C b+X)^4-C (b^4+6*b^2+3) : Polynomial ℝ) 1 (by norm_num)).integrable (by norm_num)
  change Integrable (fun z : ℝ => (b+z)^4-(b^4+6*b^2+3)) GaussianCore.γ
  simpa using h

theorem fiber_raw_mean (b : ℝ) :
    (∫ z : ℝ, (b+z)^4 ∂GaussianCore.γ)=b^4+6*b^2+3 := by
  have he : (fun z : ℝ => (b+z)^4)=fun z => fiberCentered b z+(b^4+6*b^2+3) := by
    funext z
    unfold fiberCentered
    ring
  rw [he,integral_add (fiber_integrable b) (integrable_const _),fiber_centered_mean]
  simp

theorem fiber_variance (b : ℝ) :
    (∫ z : ℝ, (fiberCentered b z)^2 ∂GaussianCore.γ)=16*b^6+168*b^4+384*b^2+96 := by
  have hm := integral_map (μ := gaussianProduct)
    (coordinate_measurePreserving 0).measurable.aemeasurable
    (f := fun z : ℝ => (fiberCentered b z)^2) (by fun_prop [fiberCentered])
  rw [(coordinate_measurePreserving 0).map_eq] at hm
  rw [hm]
  have he : (∫ ω : SampleSpace, (fiberCentered b (ω 0))^2 ∂gaussianProduct)=
      ‖shiftedCentered b (direction 0)‖^2 := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [fiber_lift b] with ω hx
    simp [hx,pow_two]
  change (∫ ω : SampleSpace, (fiberCentered b (ω 0))^2 ∂gaussianProduct)=_
  rw [he,shiftedCentered_norm_sq,direction_norm_sq]
  ring

theorem fiber_variance_minimum (b : ℝ) :
    96 ≤ ∫ z : ℝ, (fiberCentered b z)^2 ∂GaussianCore.γ := by
  rw [fiber_variance]
  have h1 : 0 ≤ 16*b^6 := by positivity
  have h2 : 0 ≤ 168*b^4 := by positivity
  have h3 : 0 ≤ 384*b^2 := by positivity
  linarith

end OperatorDerivativeRewrite.Foundation.GaussianShiftedQuarticVariance
