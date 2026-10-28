import Foundation.SU2ForestCycleReduction
/-!
Actual SU2 shared-edge Haar projection, residual moments and an algebraic
conditional spectral bracket. No physical transfer derivative is identified
by the bracket alone.
-/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2SharedPlaquetteProjection
open QuaternionSU2Representation SU2WilsonConvolution BoundedExponentialTiltResponse

theorem translated_trace_covariance (C : SU2) :
    (∫ U, halfTrace (C*U)*halfTrace U ∂law)=halfTrace C/4 := by
  have hm := (SU2TiltEnergyResponse.moment_values law).1
  have hsecond : (∫ U, halfTrace U*halfTrace U ∂law)=(1/4:ℝ) := by
    simpa only [pow_two] using (SU2TiltEnergyResponse.moment_values law).2.1
  have hc := expectation_hasDerivAt_zero law halfTrace halfTrace halfTrace_measurable
    halfTrace_measurable halfTrace_bound 1 (by norm_num) halfTrace_bound
  rw [hsecond,hm] at hc
  norm_num at hc
  have hd := expectation_hasDerivAt_zero law halfTrace (fun U => halfTrace (C*U))
    halfTrace_measurable (halfTrace_measurable.comp (measurable_const_mul C))
    halfTrace_bound 1 (by norm_num) (fun U => halfTrace_bound (C*U))
  rw [hm,mul_zero,sub_zero] at hd
  have he : (fun β => expectation law halfTrace (fun U => halfTrace (C*U)) β) =
      fun β => expectation law halfTrace halfTrace β*halfTrace C := by
    funext β
    rw [← tilted_integral law halfTrace (fun U => halfTrace (C*U)) halfTrace_measurable halfTrace_bound]
    rw [← tilted_integral law halfTrace halfTrace halfTrace_measurable halfTrace_bound]
    exact halfTrace_eigen β C
  change HasDerivAt (fun β => expectation law halfTrace (fun U => halfTrace (C*U)) β) _ 0 at hd
  rw [he] at hd
  have hu := hd.unique (hc.mul_const (halfTrace C))
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using hu

def sharedProduct (L R U : SU2) : ℝ := halfTrace (L*U)*halfTrace (U⁻¹*R)
def sharedMean (L R : SU2) : ℝ := halfTrace (L*R)/4
def sharedResidual (L R U : SU2) : ℝ := sharedProduct L R U-sharedMean L R

theorem sharedProduct_measurable (L R : SU2) : Measurable (sharedProduct L R) :=
  (halfTrace_measurable.comp (measurable_const_mul L)).mul
    (halfTrace_measurable.comp ((measurable_mul_const R).comp measurable_inv))

theorem sharedProduct_bound (L R U : SU2) : |sharedProduct L R U| ≤ 1 := by
  rw [sharedProduct,abs_mul]
  simpa only [one_mul] using mul_le_mul (halfTrace_bound (L*U)) (halfTrace_bound (U⁻¹*R))
    (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

theorem sharedProduct_integrable (L R : SU2) : Integrable (sharedProduct L R) law := by
  apply Integrable.of_bound (sharedProduct_measurable L R).aestronglyMeasurable 1
  filter_upwards with U
  simpa only [Real.norm_eq_abs] using sharedProduct_bound L R U

theorem sharedProduct_mean (L R : SU2) : (∫ U, sharedProduct L R U ∂law)=sharedMean L R := by
  let F : SU2 → ℝ := fun V => halfTrace V*halfTrace (V⁻¹*(L*R))
  have he : (fun U => F (L*U))=sharedProduct L R := by
    funext U
    have hg : (L*U)⁻¹*(L*R)=U⁻¹*R := by group
    simp only [F,sharedProduct,hg]
  have ht := integral_mul_left_eq_self (μ := law) F L
  rw [he] at ht
  rw [ht]
  have hF : F = fun V => halfTrace ((L*R)⁻¹*V)*halfTrace V := by
    funext V
    have hv : halfTrace (V⁻¹*(L*R))=halfTrace ((L*R)⁻¹*V) := by
      simpa only [mul_inv_rev,inv_inv] using (halfTrace_inv (V⁻¹*(L*R))).symm
    simp only [F,hv,mul_comm]
  rw [hF,translated_trace_covariance,halfTrace_inv]
  rfl

theorem sharedResidual_integrable (L R : SU2) : Integrable (sharedResidual L R) law :=
  (sharedProduct_integrable L R).sub (integrable_const _)

theorem sharedResidual_mean_zero (L R : SU2) : (∫ U, sharedResidual L R U ∂law)=0 := by
  unfold sharedResidual
  rw [integral_sub (sharedProduct_integrable L R) (integrable_const _),sharedProduct_mean]
  simp

theorem sharedMean_gauge (g h L R : SU2) :
    sharedMean (g*L*h⁻¹) (h*R*g⁻¹)=sharedMean L R := by
  have he : (g*L*h⁻¹)*(h*R*g⁻¹)=g*(L*R)*g⁻¹ := by group
  rw [sharedMean,he,halfTrace_conjugate]
  rfl

theorem sharedProduct_gauge (g h L R U : SU2) :
    sharedProduct (g*L*h⁻¹) (h*R*g⁻¹) (h*U*g⁻¹)=sharedProduct L R U := by
  have he : (g*L*h⁻¹)*(h*U*g⁻¹)=g*(L*U)*g⁻¹ := by group
  have he' : (h*U*g⁻¹)⁻¹*(h*R*g⁻¹)=g*(U⁻¹*R)*g⁻¹ := by group
  rw [sharedProduct,he,he',halfTrace_conjugate,halfTrace_conjugate]
  rfl
end OperatorDerivativeRewrite.Foundation.SU2SharedPlaquetteProjection

namespace OperatorDerivativeRewrite.Foundation.SU2SharedPlaquetteProjection
open QuaternionSU2Representation SU2WilsonConvolution

private theorem unit_product_integrable (f g : SU2 → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hb : ∀ U, |f U| ≤ 1) (hc : ∀ U, |g U| ≤ 1) : Integrable (fun U => f U*g U) law := by
  apply Integrable.of_bound (hf.mul hg).aestronglyMeasurable 1
  filter_upwards with U
  change ‖f U*g U‖ ≤ 1
  rw [Real.norm_eq_abs,abs_mul]
  simpa using mul_le_mul (hb U) (hc U) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

theorem trace_square_mean (C : SU2) : (∫ U, halfTrace (C*U)^2 ∂law)=(1/4:ℝ) := by
  rw [integral_mul_left_eq_self (μ := law) (fun U => halfTrace U^2) C]
  exact (SU2TiltEnergyResponse.moment_values law).2.1

theorem trace_square_right_mean (C : SU2) : (∫ U, halfTrace (U*C)^2 ∂law)=(1/4:ℝ) := by
  have he : (fun U => halfTrace (U*C)^2) = fun U => halfTrace (C*U)^2 :=
    funext (fun U => congrArg (fun x : ℝ => x^2) (halfTrace_mul_comm U C))
  rw [he,trace_square_mean]

theorem translated_pair_covariance (C D : SU2) :
    (∫ U, halfTrace (C*U)*halfTrace (D*U) ∂law)=halfTrace (C*D⁻¹)/4 := by
  let F := fun V : SU2 => halfTrace ((C*D⁻¹)*V)*halfTrace V
  have he : (fun U => F (D*U))=fun U => halfTrace (C*U)*halfTrace (D*U) := by
    funext U
    have hg : (C*D⁻¹)*(D*U)=C*U := by group
    simp only [F,hg]
  have ht := integral_mul_left_eq_self (μ := law) F D
  rw [he] at ht
  rw [ht]
  exact translated_trace_covariance (C*D⁻¹)

theorem sharedMean_bound (L R : SU2) : |sharedMean L R| ≤ 1 := by
  unfold sharedMean
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
  exact (div_le_div_of_nonneg_right (halfTrace_bound (L*R)) (by norm_num)).trans (by norm_num)

theorem shared_projection_second_moments (U : SU2) :
    (∫ L, ∫ R, sharedProduct L R U^2 ∂law ∂law)=(1/16:ℝ) ∧
    (∫ L, ∫ R, sharedMean L R^2 ∂law ∂law)=(1/64:ℝ) ∧
    (∫ L, ∫ R, sharedResidual L R U^2 ∂law ∂law)=(3/64:ℝ) := by
  have hP2 (L : SU2) : (∫ R, sharedProduct L R U^2 ∂law)=halfTrace (L*U)^2/4 := by
    simp only [sharedProduct,mul_pow]
    rw [integral_const_mul,trace_square_mean]
    ring
  have hM2 (L : SU2) : (∫ R, sharedMean L R^2 ∂law)=(1/64:ℝ) := by
    simp only [sharedMean,div_pow]
    rw [integral_div,trace_square_mean]
    norm_num
  have hPM (L : SU2) : (∫ R, sharedProduct L R U*sharedMean L R ∂law)=halfTrace (L*U)^2/16 := by
    have he : (fun R => sharedProduct L R U*sharedMean L R) =
        fun R => (halfTrace (L*U)/4)*(halfTrace (U⁻¹*R)*halfTrace (L*R)) := by
      funext R; unfold sharedProduct sharedMean; ring
    rw [he,integral_const_mul,translated_pair_covariance]
    have ht : halfTrace (U⁻¹*L⁻¹)=halfTrace (L*U) := by rw [← mul_inv_rev,halfTrace_inv]
    rw [ht]
    ring
  have hR2 (L : SU2) : (∫ R, sharedResidual L R U^2 ∂law)=halfTrace (L*U)^2/8+1/64 := by
    have hp : Measurable (fun R => sharedProduct L R U) :=
      measurable_const.mul (halfTrace_measurable.comp (measurable_const_mul U⁻¹))
    have hm : Measurable (sharedMean L) := (halfTrace_measurable.comp (measurable_const_mul L)).div_const 4
    have hip : Integrable (fun R => sharedProduct L R U^2) law := by
      simpa only [pow_two] using unit_product_integrable _ _ hp hp
        (fun R => sharedProduct_bound L R U) (fun R => sharedProduct_bound L R U)
    have him : Integrable (fun R => sharedMean L R^2) law := by
      simpa only [pow_two] using unit_product_integrable _ _ hm hm (sharedMean_bound L) (sharedMean_bound L)
    have hipm := unit_product_integrable _ _ hp hm (fun R => sharedProduct_bound L R U) (sharedMean_bound L)
    have he : (fun R => sharedResidual L R U^2) =
        fun R => (sharedProduct L R U^2-2*(sharedProduct L R U*sharedMean L R))+sharedMean L R^2 := by
      funext R; unfold sharedResidual; ring
    have hadd := integral_add (hip.sub (hipm.const_mul 2)) him
    have hsub := integral_sub hip (hipm.const_mul 2)
    simp only [Pi.sub_apply] at hadd hsub
    rw [he,hadd,hsub,integral_const_mul,hP2,hPM,hM2]
    ring
  have his : Integrable (fun L => halfTrace (L*U)^2) law := by
    simpa only [pow_two,Function.comp_apply] using unit_product_integrable (fun L => halfTrace (L*U)) (fun L => halfTrace (L*U))
      (halfTrace_measurable.comp (measurable_mul_const U)) (halfTrace_measurable.comp (measurable_mul_const U))
      (fun L => halfTrace_bound (L*U)) (fun L => halfTrace_bound (L*U))
  refine ⟨?_,?_,?_⟩
  · simp_rw [hP2]
    rw [integral_div,trace_square_right_mean]
    norm_num
  · simp_rw [hM2]
    simp
  · simp_rw [hR2]
    rw [integral_add (his.div_const 8) (integrable_const _),integral_div,trace_square_right_mean]
    norm_num
end OperatorDerivativeRewrite.Foundation.SU2SharedPlaquetteProjection

namespace OperatorDerivativeRewrite.Foundation.SU2SharedPlaquetteProjection
/-- Algebraic bracket in the proposed two-channel perturbative reduction.
This definition alone identifies no derivative of a physical transfer. -/
def overlapBracket (x m : ℝ) : ℝ :=
  (1+x)/(4*(1-x))+3*(1+x*((4*m-1)/3))/(4*(1-x*((4*m-1)/3)))-(1+x^2)/(1-x^2)

theorem overlapBracket_positive (x m : ℝ) (hx : 0 < x) (hxm : x ≤ m) (hm : m < 1) :
    0 < overlapBracket x m := by
  have hm0 : 0 < m := hx.trans_le hxm
  have hx1 : x < 1 := hxm.trans_lt hm
  have hd : (4*m-1)/3 < 1 := by linarith
  have hd' : 0 < 3+(4*m-1)/3 := by linarith
  have hcross := mul_lt_mul_of_pos_left hd hx
  have hden : 0 < 1-x*((4*m-1)/3) := by linarith
  have hsquare : 0 < 1-x^2 := by nlinarith [mul_pos (sub_pos.mpr hx1) (by linarith : 0 < 1+x)]
  have hcomp := mul_le_mul_of_nonneg_right hxm hd'.le
  have hnum : 0 < 1+3*((4*m-1)/3)-x*(3+(4*m-1)/3) := by
    nlinarith [mul_pos hm0 (sub_pos.mpr hm)]
  have he : overlapBracket x m =
      x*(1+3*((4*m-1)/3)-x*(3+(4*m-1)/3))/(2*(1-x^2)*(1-x*((4*m-1)/3))) := by
    have halg (d : ℝ) (hxd : 1-x*d ≠ 0) :
        (1+x)/(4*(1-x))+3*(1+x*d)/(4*(1-x*d))-(1+x^2)/(1-x^2) =
          x*(1+3*d-x*(3+d))/(2*(1-x^2)*(1-x*d)) := by
      field_simp [(sub_pos.mpr hx1).ne',hxd,hsquare.ne']
      <;> ring
    exact halg ((4*m-1)/3) hden.ne' 
  rw [he]
  exact div_pos (mul_pos hx hnum) (mul_pos (mul_pos (by norm_num) hsquare) hden)
end OperatorDerivativeRewrite.Foundation.SU2SharedPlaquetteProjection
