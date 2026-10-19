import Foundation.RiemannQuarticGaussianTail
/-! Actual weighted slope monotonicity on a thin shifted half-line.
For t>0, y<=0 and abs(h)<=1/102400, exp(-4*x)*(Re G_t(x+i*h)-y)
is strictly decreasing on x>=1. The D-4 cancellation removes the leading
exponential term; actual error and derivative bounds close the strict sign.
A zero of the shifted slope is consequently its unique zero on this half-line,
with positive slope on the left and negative slope on the right. These are
actual logarithmic-slope statements, not a global Fourier zero theorem. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticWeightedSlope

theorem model_cancellation (t x h y : ℝ) :
    (12*t*(x^2-h^2)-16*Real.pi*Real.exp (4*x)*Real.cos (4*h))-
      4*(4*t*(x^3-3*x*h^2)+9-4*Real.pi*Real.exp (4*x)*Real.cos (4*h)-y)=
      4*t*(x^2*(3-4*x)+h^2*(12*x-3))-36+4*y := by ring

theorem polynomial_bracket_bound (x h : ℝ) (hx : 1 ≤ x) (hh : |h| ≤ 1/102400) :
    x^2*(3-4*x)+h^2*(12*x-3) ≤ -(x^3)/2 := by
  have hh2 : h^2 ≤ (1/102400 : ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg h) (by norm_num : (0 : ℝ) ≤ 1/102400)).mpr hh
  have hhsmall : h^2 ≤ (1/24 : ℝ) := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hx2 : 1 ≤ x^2 := by nlinarith
  have hx3 : x ≤ x^3 := by nlinarith [mul_le_mul_of_nonneg_right hx2 hx0]
  have hp := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)
  have hhp := mul_le_mul_of_nonneg_right hhsmall (by linarith : 0 ≤ 12*x)
  nlinarith [sq_nonneg h]

theorem scalar_normalized_slope_budget (t x h y E E' : ℝ) (ht : 0 < t) (hx : 1 ≤ x)
    (hh : |h| ≤ 1/102400) (hy : y ≤ 0) (hE : |E| ≤ 1) (hE' : E' ≤ 32) :
    4*t*(x^2*(3-4*x)+h^2*(12*x-3))-36+4*y+E'-4*E < 0 := by
  have hb := polynomial_bracket_bound x h hx hh
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4*t)
  have hElow := (abs_le.mp hE).1
  have hx3 : 0 < x^3 := by positivity
  have hp := mul_pos ht hx3
  nlinarith


open RiemannQuarticSaddleBranch RiemannQuarticSaddleTheta RiemannQuarticSaddleNeighborhood
open RiemannQuarticQuantitativeSaddle

theorem horizontal_point_mem (x h r : ℝ) (hh : |h| ≤ r) :
    (x : ℂ)+(h : ℂ)*Complex.I ∈ closedBall (x : ℂ) r := by
  rw [mem_closedBall,dist_eq_norm]
  have he : (x : ℂ)+(h : ℂ)*Complex.I-(x : ℂ)=(h : ℂ)*Complex.I := by ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  exact hh

theorem model_hasDerivAt (t : ℝ) (w : ℂ) :
    HasDerivAt (modelDerivative t) (12*(t : ℂ)*w^2-16*(Real.pi : ℂ)*Complex.exp (4*w)) w := by
  have hp := (((hasDerivAt_id w).pow 3).const_mul (4*(t : ℂ))).add_const 9
  have he := (((hasDerivAt_id w).const_mul (4 : ℂ)).cexp).const_mul (4*(Real.pi : ℂ))
  have h := hp.sub he
  convert h using 1
  · funext v
    rfl
  · simp only [id_eq]
    ring

theorem model_real_re (t x h : ℝ) :
    (modelDerivative t ((x : ℂ)+(h : ℂ)*Complex.I)).re=
      4*t*(x^3-3*x*h^2)+9-4*Real.pi*Real.exp (4*x)*Real.cos (4*h) := by
  simp [modelDerivative,Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.mul_im,
    cube_re,Complex.exp_re]
  ring

theorem model_deriv_real_re (t x h : ℝ) :
    (deriv (modelDerivative t) ((x : ℂ)+(h : ℂ)*Complex.I)).re=
      12*t*(x^2-h^2)-16*Real.pi*Real.exp (4*x)*Real.cos (4*h) := by
  rw [(model_hasDerivAt t _).deriv]
  simp [pow_two,Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.mul_im,
    Complex.exp_re]
  ring

theorem actual_operator_budget (t x h y : ℝ) (ht : 0 < t) (hx : 1 ≤ x)
    (hh : |h| ≤ 1/102400) (hy : y ≤ 0) :
    (deriv (complexSlope t) ((x : ℂ)+(h : ℂ)*Complex.I)).re-
      4*((complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re-y) < 0 := by
  let w := (x : ℂ)+(h : ℂ)*Complex.I
  have hw16 : w ∈ closedBall (x : ℂ) (1/16) := horizontal_point_mem x h _ (hh.trans (by norm_num))
  have hw32 : w ∈ closedBall (x : ℂ) (1/32) := horizontal_point_mem x h _ (hh.trans (by norm_num))
  have he := slope_model_error_on_neighborhood t x hx w hw16
  have hd := slope_error_inner_cauchy_bound t x hx w hw32 1
  simp only [iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,pow_one,one_mul] at hd
  have ha := slope_analytic_on_neighborhood t x hx w hw16
  have hm : AnalyticAt ℂ (modelDerivative t) w := by unfold modelDerivative; fun_prop
  change ‖deriv (complexSlope t - modelDerivative t) w‖ ≤ 32 at hd
  rw [deriv_sub ha.differentiableAt hm.differentiableAt] at hd
  let E := (complexSlope t w-modelDerivative t w).re
  let E' := (deriv (complexSlope t) w-deriv (modelDerivative t) w).re
  have hE : |E| ≤ 1 := (Complex.abs_re_le_norm _).trans he
  have hE' : E' ≤ 32 := (Complex.re_le_norm _).trans hd
  have hb := scalar_normalized_slope_budget t x h y E E' ht hx hh hy hE hE'
  have hid : (deriv (complexSlope t) w).re-4*((complexSlope t w).re-y)=
      4*t*(x^2*(3-4*x)+h^2*(12*x-3))-36+4*y+E'-4*E := by
    dsimp [E,E']
    try simp only [Complex.sub_re]
    dsimp [w]
    rw [model_real_re,model_deriv_real_re]
    ring
  change (deriv (complexSlope t) w).re-4*((complexSlope t w).re-y)<0
  rw [hid]
  exact hb

def normalizedSlope (t h y x : ℝ) : ℝ :=
  Real.exp (-4*x)*((complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re-y)

theorem normalizedSlope_hasDerivAt (t h y x : ℝ) (hx : 1 ≤ x) (hh : |h| ≤ 1/102400) :
    HasDerivAt (normalizedSlope t h y)
      (Real.exp (-4*x)*((deriv (complexSlope t) ((x : ℂ)+(h : ℂ)*Complex.I)).re-
        4*((complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re-y))) x := by
  let w := (x : ℂ)+(h : ℂ)*Complex.I
  have hw : w ∈ closedBall (x : ℂ) (1/16) := horizontal_point_mem x h _ (hh.trans (by norm_num))
  have ha := slope_analytic_on_neighborhood t x hx w hw
  have hc := ha.differentiableAt.hasDerivAt.comp (x : ℂ)
    ((hasDerivAt_id (x : ℂ)).add_const ((h : ℂ)*Complex.I))
  have hc' : HasDerivAt (fun v : ℂ => complexSlope t (v+(h : ℂ)*Complex.I))
      (deriv (complexSlope t) w) (x : ℂ) := by
    convert hc using 1 <;> first | rfl | simp only [mul_one]
  have hr := hc'.real_of_complex.sub_const y
  have he := (((hasDerivAt_id x).const_mul (-4 : ℝ)).exp).mul hr
  convert he using 1
  · funext v
    rfl
  · dsimp [w]
    try simp only [id_eq]
    ring

theorem normalizedSlope_strictAntiOn (t h y : ℝ) (ht : 0 < t)
    (hh : |h| ≤ 1/102400) (hy : y ≤ 0) :
    StrictAntiOn (normalizedSlope t h y) (Ici 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  · intro x hx
    exact (normalizedSlope_hasDerivAt t h y x hx hh).continuousAt.continuousWithinAt
  · intro x hx
    have hx1 : 1 ≤ x := interior_subset hx
    rw [(normalizedSlope_hasDerivAt t h y x hx1 hh).deriv]
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) (actual_operator_budget t x h y ht hx1 hh hy)

theorem shifted_slope_signs (t h y a : ℝ) (ht : 0 < t)
    (hh : |h| ≤ 1/102400) (hy : y ≤ 0) (ha : 1 ≤ a)
    (hs : (complexSlope t ((a : ℂ)+(h : ℂ)*Complex.I)).re=y) :
    (∀ x : ℝ, 1 ≤ x → x < a → y < (complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re) ∧
    (∀ x : ℝ, a < x → (complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re < y) := by
  have hanti := normalizedSlope_strictAntiOn t h y ht hh hy
  have hzero : normalizedSlope t h y a=0 := by simp [normalizedSlope,hs]
  constructor
  · intro x hx hxa
    have hpos := hanti hx ha hxa
    rw [hzero] at hpos
    have hp : 0 < (complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re-y :=
      (mul_pos_iff_of_pos_left (Real.exp_pos (-4*x))).mp hpos
    linarith
  · intro x hax
    have hx : 1 ≤ x := le_trans ha hax.le
    have hneg := hanti ha hx hax
    rw [hzero] at hneg
    have hp : (complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re-y < 0 :=
      by
        change Real.exp (-4*x)*((complexSlope t ((x : ℂ)+(h : ℂ)*Complex.I)).re-y)<0 at hneg
        nlinarith [Real.exp_pos (-4*x)]
    linarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticWeightedSlope
