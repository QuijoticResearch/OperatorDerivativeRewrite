import Foundation.RiemannQuarticContour
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
/-! Actual saddle contour geometry and quadratic Gaussian normalization.
The complex slope derivative at a real center equals its real derivative.
For Re(z)>=0 a nearby actual saddle has nonnegative height, so its horizontal
line admits the proved signed half-line contour shift. The local curvature
has negative real part, and mathlib's principal complex Gaussian integral
provides a nonzero normalization at that ACTUAL curvature. This does not
identify the full shifted integrand with its quadratic model or bound the
integrated local and tail remainder. -/
noncomputable section
open Set Metric Complex MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleGeometry
open RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes RiemannQuarticCurvature
open RiemannQuarticSaddleNeighborhood RiemannQuarticQuantitativeSaddle RiemannQuarticFrequencyBranch

theorem slope_deriv_real (t u : ℝ) (hu : 0 < u) :
    deriv (complexSlope t) (u : ℂ)=((deriv (phaseSlope t) u : ℝ) : ℂ) := by
  have ha := (complexSlope_analyticAt t u hu).differentiableAt.hasDerivAt
  have hr : HasDerivAt (phaseSlope t) (deriv (complexSlope t) (u : ℂ)).re u := by
    convert ha.real_of_complex using 1
    funext x
    rw [complexSlope_real]
    rfl
  have hi : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (deriv (complexSlope t) (u : ℂ)).im u := by
    have h := (ha.const_mul (-Complex.I)).real_of_complex
    convert h using 1
    · funext x
      rw [complexSlope_real]
      simp [Complex.mul_re]
    · simp [Complex.mul_re,Complex.mul_im]
  have him : (deriv (complexSlope t) (u : ℂ)).im=0 := hi.unique (hasDerivAt_const u 0)
  apply Complex.ext
  · simpa using hr.deriv.symm
  · simpa using him

theorem scalar_linearization_bound (f : ℂ → ℂ) (b a : ℂ) (r C : ℝ)
    (hd : ∀ w ∈ closedBall b r, DifferentiableAt ℂ f w)
    (hb : ∀ w ∈ closedBall b r, ‖deriv f w-a‖ ≤ C)
    (x y : ℂ) (hx : x ∈ closedBall b r) (hy : y ∈ closedBall b r) :
    ‖f x-f y-a*(x-y)‖ ≤ C*‖x-y‖ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hd w hw).sub ((hasDerivAt_id w).const_mul a).differentiableAt)
    (fun w hw => by
      rw [deriv_sub (hd w hw) ((hasDerivAt_id w).const_mul a).differentiableAt,
        ((hasDerivAt_id w).const_mul a).deriv]
      simpa using hb w hw)
    (convex_closedBall b r) hy hx
  simp only [Pi.sub_apply,id_eq] at h
  convert h using 1 <;> congr 1 <;> ring

theorem real_projection_mem (u : ℝ) (w : ℂ) (r : ℝ) (hw : w ∈ closedBall (u : ℂ) r) :
    (w.re : ℂ) ∈ closedBall (u : ℂ) r := by
  have h := Complex.abs_re_le_norm (w-(u : ℂ))
  have hd : ‖w-(u : ℂ)‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hw
  rw [mem_closedBall,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  simpa using h.trans hd

theorem stationary_saddle_height_nonneg (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (z w : ℂ) (hz : 0 ≤ z.re)
    (hw : w ∈ closedBall (u : ℂ) (1/102400)) (he : complexSlope t w= -(Complex.I*z)) :
    0 ≤ w.im := by
  have hd : ∀ v ∈ closedBall (u : ℂ) (1/102400), DifferentiableAt ℂ (complexSlope t) v := by
    intro v hv
    exact (slope_analytic_on_neighborhood t u hu v
      (closedBall_subset_closedBall (by norm_num) hv)).differentiableAt
  have hb := stationary_slope_deriv_near_center t u ht hu hs
  have h := scalar_linearization_bound (complexSlope t) (u : ℂ)
    (deriv (complexSlope t) (u : ℂ)) (1/102400)
    (‖deriv (complexSlope t) (u : ℂ)‖/2) hd hb w (w.re : ℂ) hw (real_projection_mem u w _ hw)
  have hneg := stationary_phaseSlope_deriv_neg t u ht hu hs
  rw [slope_deriv_real t u (by linarith),he,complexSlope_real] at h
  have hnorm : ‖w-(w.re : ℂ)‖=|w.im| := by
    have hh : w-(w.re : ℂ)=(w.im : ℂ)*Complex.I := by apply Complex.ext <;> simp
    rw [hh,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  rw [hnorm,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hneg] at h
  have him := Complex.abs_im_le_norm
    (-(Complex.I*z)-(phaseSlope t w.re : ℂ)-((deriv (phaseSlope t) u : ℝ) : ℂ)*(w-(w.re : ℂ)))
  have hle := him.trans h
  simp only [Complex.sub_im,Complex.neg_im,Complex.mul_re,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,zero_add,one_mul,
    add_zero,sub_zero] at hle
  by_contra hn
  have hwneg : w.im < 0 := lt_of_not_ge hn
  rw [abs_of_neg hwneg] at hle
  have hleft := neg_le_abs (-z.re-deriv (phaseSlope t) u*w.im)
  nlinarith


theorem slope_deriv_re_half_bound (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    (deriv (complexSlope t) w).re ≤ deriv (phaseSlope t) u/2 := by
  have hv := stationary_slope_deriv_near_center t u ht hu hs w hw
  have hn := stationary_phaseSlope_deriv_neg t u ht hu hs
  rw [slope_deriv_real t u (by linarith),Complex.norm_real,Real.norm_eq_abs,abs_of_neg hn] at hv
  have hr := Complex.re_le_norm (deriv (complexSlope t) w-deriv (complexSlope t) (u : ℂ))
  rw [slope_deriv_real t u (by linarith),Complex.sub_re,Complex.ofReal_re] at hr
  linarith

theorem branch_geometry (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ ≤ (t*u^3+1)/51200) (hre : 0 ≤ z.re) :
    0 < (branch t u ht hu hs z).re ∧ 0 ≤ (branch t u ht hu hs z).im ∧
      (branch t u ht hu hs z).im ≤ 1/102400 := by
  have hspec := branch_spec t u ht hu hs z hz
  have hheight := stationary_saddle_height_nonneg t u ht hu hs z _ hre hspec.1 hspec.2
  have hd : ‖branch t u ht hu hs z-(u : ℂ)‖ ≤ (1/102400 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hspec.1
  have hr := (Complex.abs_re_le_norm (branch t u ht hu hs z-(u : ℂ))).trans hd
  have hi := (Complex.abs_im_le_norm (branch t u ht hu hs z-(u : ℂ))).trans hd
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hr hi
  constructor
  · rcases abs_le.mp hr with ⟨hlo,hhi⟩
    linarith
  · exact ⟨hheight,(le_abs_self _).trans hi⟩

theorem halfline_shift_through_saddle (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ ≤ (t*u^3+1)/51200) (hre : 0 ≤ z.re) :
    (∫ x : ℝ in Ioi 0, saddleWeight t z (x : ℂ))=
      (∫ x : ℝ in Ioi 0, saddleWeight t z ((x : ℂ)+
        (((branch t u ht hu hs z).im : ℝ) : ℂ)*Complex.I))+
      Complex.I*(∫ y : ℝ in 0..(branch t u ht hu hs z).im,
        saddleWeight t z ((y : ℂ)*Complex.I)) := by
  have hg := branch_geometry t u ht hu hs z hz hre
  exact RiemannQuarticContour.halfline_contour_shift t z (branch t u ht hu hs z).im
    hg.2.1 (by linarith [hg.2.2])


theorem gaussian_coefficient_re_pos (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    0 < (-(deriv (complexSlope t) w)/2).re := by
  have hh := slope_deriv_re_half_bound t u ht hu hs w hw
  have hn := stationary_phaseSlope_deriv_neg t u ht hu hs
  simp only [Complex.div_ofNat_re,Complex.neg_re]
  linarith

theorem quadratic_gaussian_integrable (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    Integrable (fun s : ℝ => Complex.exp ((deriv (complexSlope t) w/2)*(s : ℂ)^2)) := by
  have h := integrable_cexp_neg_mul_sq (gaussian_coefficient_re_pos t u ht hu hs w hw)
  convert h using 1
  funext s
  congr 1
  ring

theorem quadratic_gaussian_integral (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    (∫ s : ℝ, Complex.exp ((deriv (complexSlope t) w/2)*(s : ℂ)^2))=
      ((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ) := by
  have h := integral_gaussian_complex (gaussian_coefficient_re_pos t u ht hu hs w hw)
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  ring

theorem quadratic_gaussian_integral_ne_zero (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    (∫ s : ℝ, Complex.exp ((deriv (complexSlope t) w/2)*(s : ℂ)^2)) ≠ 0 := by
  rw [quadratic_gaussian_integral t u ht hu hs w hw]
  apply Complex.cpow_ne_zero_iff.mpr
  left
  apply div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  intro he
  have hp := gaussian_coefficient_re_pos t u ht hu hs w hw
  rw [he] at hp
  simpa using hp

end OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleGeometry
