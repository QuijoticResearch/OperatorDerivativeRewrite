import Foundation.RiemannQuarticSpatialPhase
/-! Gaussian MODEL tails and local actual-integral/full Gaussian comparison.
For Re(b)>0 the one-sided tail is bounded by exp(-Re(b)*r^2)/(2*Re(b)*r).
The two-sided truncation error and actual curvature lower bound combine
with the signed local integral estimate. Actual nonlocal shifted-integrand
tails and a complete two-saddle approximation are not supplied by this module. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticGaussianTail

theorem first_moment_tail (c a : ℝ) (hc : 0 < c) :
    (∫ x : ℝ in Ioi a, x*Real.exp (-c*x^2))=Real.exp (-c*a^2)/(2*c) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => -(2*c)⁻¹*Real.exp (-c*y^2))
      (x*Real.exp (-c*x^2)) x := by
    convert! (((hasDerivAt_id x).pow 2).const_mul (-c)).exp.const_mul (-(2*c)⁻¹) using 1
    dsimp only [id_eq,Pi.pow_apply]
    field_simp [hc.ne']
    ring
  have he : Tendsto (fun x : ℝ => Real.exp (-c*x^2)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.mpr hc))
  have hf : Tendsto (fun x : ℝ => -(2*c)⁻¹*Real.exp (-c*x^2)) atTop (nhds 0) := by
    simpa using he.const_mul (-(2*c)⁻¹)
  have h : (∫ x : ℝ in Ioi a, x*Real.exp (-c*x^2))=
      (0 : ℝ)-(-(2*c)⁻¹*Real.exp (-c*a^2)) :=
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x)
      (integrable_mul_exp_neg_mul_sq hc).integrableOn hf
  convert h using 1 <;> ring

theorem real_tail_bound (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    (∫ x : ℝ in Ioi r, Real.exp (-c*x^2)) ≤ Real.exp (-c*r^2)/(2*c*r) := by
  have hf : IntegrableOn (fun x : ℝ => Real.exp (-c*x^2)) (Ioi r) :=
    (integrable_exp_neg_mul_sq hc).integrableOn
  have hg : IntegrableOn (fun x : ℝ => (x*Real.exp (-c*x^2))/r) (Ioi r) :=
    (integrable_mul_exp_neg_mul_sq hc).integrableOn.div_const r
  have h := setIntegral_mono_on hf hg measurableSet_Ioi (fun x hx => by
    apply (le_div_iff₀ hr).mpr
    have hx' : r < x := hx
    have hm := mul_le_mul_of_nonneg_right hx'.le (Real.exp_pos (-c*x^2)).le
    nlinarith)
  rw [integral_div,first_moment_tail c r hc] at h
  convert h using 1 <;> simp only [div_eq_mul_inv,mul_inv_rev] <;> ring

theorem complex_tail_norm_bound (b : ℂ) (hb : 0 < b.re) (r : ℝ) (hr : 0 < r) :
    ‖∫ x : ℝ in Ioi r, Complex.exp (-b*(x : ℂ)^2)‖ ≤
      Real.exp (-b.re*r^2)/(2*b.re*r) := by
  calc
    _ ≤ ∫ x : ℝ in Ioi r, ‖Complex.exp (-b*(x : ℂ)^2)‖ := norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in Ioi r, Real.exp (-b.re*x^2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact norm_cexp_neg_mul_sq b x
    _ ≤ _ := real_tail_bound b.re r hb hr


theorem full_minus_truncated_bound (b : ℂ) (hb : 0 < b.re) (r : ℝ) (hr : 0 < r) :
    ‖(∫ x : ℝ, Complex.exp (-b*(x : ℂ)^2))-
      (∫ x : ℝ in -r..r, Complex.exp (-b*(x : ℂ)^2))‖ ≤
      Real.exp (-b.re*r^2)/(b.re*r) := by
  let f := fun x : ℝ => Complex.exp (-b*(x : ℂ)^2)
  have hi := integrable_cexp_neg_mul_sq hb
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := -r) (f := f) hi.integrableOn hi.integrableOn
  have hmiddle := intervalIntegral.integral_interval_add_Ioi
    (a := -r) (b := r) (f := f) hi.integrableOn hi.integrableOn
  have hleft : (∫ x : ℝ in Iic (-r), f x)=(∫ x : ℝ in Ioi r, f x) := by
    simpa only [f,Complex.ofReal_neg,neg_sq] using (integral_comp_neg_Ioi r f).symm
  have he : (∫ x : ℝ, f x)-(∫ x : ℝ in -r..r, f x)=
      (∫ x : ℝ in Ioi r, f x)+(∫ x : ℝ in Ioi r, f x) := by
    linear_combination -hsplit -hmiddle +hleft
  change ‖(∫ x : ℝ, f x)-(∫ x : ℝ in -r..r, f x)‖ ≤ _
  rw [he]
  have ht := complex_tail_norm_bound b hb r hr
  change ‖∫ x : ℝ in Ioi r, f x‖ ≤ _ at ht
  calc
    _ ≤ ‖∫ x : ℝ in Ioi r, f x‖+‖∫ x : ℝ in Ioi r, f x‖ := norm_add_le _ _
    _ ≤ 2*(Real.exp (-b.re*r^2)/(2*b.re*r)) := by linarith
    _ = _ := by field_simp <;> ring

open RiemannQuarticSaddleGeometry RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes
open RiemannQuarticQuantitativeSaddle RiemannQuarticSpatialPhase RiemannQuarticFrequencyBranch

theorem gaussian_coefficient_lower (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    t*u^3+1 ≤ (-(deriv (complexSlope t) w)/2).re := by
  have hhalf := slope_deriv_re_half_bound t u ht hu hs w hw
  have hl := stationary_slope_deriv_norm_lower t u ht hu hs
  have hn := RiemannQuarticCurvature.stationary_phaseSlope_deriv_neg t u ht hu hs
  rw [slope_deriv_real t u (by linarith),Complex.norm_real,Real.norm_eq_abs,abs_of_neg hn] at hl
  simp only [Complex.div_ofNat_re,Complex.neg_re]
  linarith

theorem actual_gaussian_truncation_error (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (r : ℝ) (hr : 0 < r) :
    ‖(∫ s : ℝ, Complex.exp ((deriv (complexSlope t) w/2)*(s : ℂ)^2))-
      (∫ s : ℝ in -r..r, Complex.exp ((deriv (complexSlope t) w/2)*(s : ℂ)^2))‖ ≤
      Real.exp (-(t*u^3+1)*r^2)/((t*u^3+1)*r) := by
  let b := -(deriv (complexSlope t) w)/2
  have hb : 0 < b.re := gaussian_coefficient_re_pos t u ht hu hs w hw
  have h := full_minus_truncated_bound b hb r hr
  have he : (fun s : ℝ => Complex.exp (-b*(s : ℂ)^2))=
      (fun s : ℝ => Complex.exp ((deriv (complexSlope t) w/2)*(s : ℂ)^2)) := by
    funext s
    dsimp [b]
    congr 1
    ring
  rw [he] at h
  apply h.trans
  have hQ : 0 < t*u^3+1 := by positivity
  have hl : t*u^3+1 ≤ b.re := gaussian_coefficient_lower t u ht hu hs w hw
  calc
    _ ≤ Real.exp (-(t*u^3+1)*r^2)/(b.re*r) :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg r])) (mul_pos hb hr).le
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le (mul_pos hQ hr)
      (mul_le_mul_of_nonneg_right hl hr.le)

theorem local_integral_full_gaussian_error (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) (hstat : complexSlope t w= -(Complex.I*z))
    (r : ℝ) (hr : 0 < r) (hrr : r < 1/102400) (hsmall : (204800*(t*u^3+1))*r^3 ≤ 1) :
    ‖(∫ s : ℝ in -r..r, saddleWeight t z (w+(s : ℂ)))-
      saddleWeight t z w*((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)‖ ≤
      ‖saddleWeight t z w‖*((819200*(t*u^3+1))*r^4+
        Real.exp (-(t*u^3+1)*r^2)/((t*u^3+1)*r)) := by
  rw [← quadratic_gaussian_integral t u ht hu hs w hw]
  have hl := local_signed_integral_error t u ht hu hs z w hw hstat r hr.le hrr hsmall
  have hfun : (fun s : ℝ => Complex.exp (deriv (complexSlope t) w*(s : ℂ)^2/2))=
      (fun s : ℝ => Complex.exp ((deriv (complexSlope t) w/2)*(s : ℂ)^2)) := by
    funext s
    congr 1
    ring
  rw [hfun] at hl
  have ht := actual_gaussian_truncation_error t u ht hu hs w hw r hr
  let A := saddleWeight t z w
  let L := ∫ s : ℝ in -r..r, saddleWeight t z (w+(s : ℂ))
  let G := ∫ s : ℝ, Complex.exp ((deriv (complexSlope t) w/2)*(s : ℂ)^2)
  let G0 := ∫ s : ℝ in -r..r, Complex.exp ((deriv (complexSlope t) w/2)*(s : ℂ)^2)
  have he : L-A*G=(L-A*G0)+A*(G0-G) := by ring
  change ‖L-A*G‖ ≤ _
  rw [he]
  have hn := norm_add_le (L-A*G0) (A*(G0-G))
  rw [norm_mul,norm_sub_rev G0 G] at hn
  have hp := mul_le_mul_of_nonneg_left ht (norm_nonneg A)
  change ‖L-A*G0‖ ≤ _ at hl
  change ‖A‖*‖G-G0‖ ≤ _ at hp
  nlinarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticGaussianTail
