import Foundation.RiemannQuarticCurvature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Liouville
/-! Explicit complex neighborhoods for the actual arithmetic phase slope.
On closed balls of radius1/16 about every real u>=1 the kernel is analytic,
nonzero and has Re(exp4w)>=8. The actual/model slope error is uniformly<=1,
and its n-th derivative at the real center is bounded by n!*16^n via Cauchy.
These are integration-variable neighborhoods, not frequency inverse radii;
global continuation and integrated contour remainders remain separate. -/
noncomputable section
open Set Metric
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleNeighborhood
open RiemannThetaComplexKernel RiemannQuarticCurvature RiemannQuarticSaddleBranch

theorem coordinate_bounds (u : ℝ) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    |w.re-u| ≤ 1/16 ∧ |w.im| ≤ 1/16 := by
  have hn : ‖w-(u : ℂ)‖ ≤ (1/16 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hr := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hn
  have hi := (Complex.abs_im_le_norm (w-(u : ℂ))).trans hn
  simpa only [Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,sub_zero] using And.intro hr hi

theorem quarter_exp_bounds : (3/4 : ℝ) ≤ Real.exp (-1/4) ∧ Real.exp (1/4) ≤ 4/3 := by
  have hl : (3/4 : ℝ) ≤ Real.exp (-1/4) := by have h := Real.add_one_le_exp (-1/4 : ℝ); linarith
  have he : Real.exp (-1/4)*Real.exp (1/4)=1 := by rw [← Real.exp_add]; norm_num
  have hm := mul_le_mul_of_nonneg_right hl (Real.exp_pos (1/4)).le
  exact ⟨hl,by nlinarith⟩

theorem exp_real_bounds (u : ℝ) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    (3/4)*Real.exp (4*u) ≤ Real.exp (4*w.re) ∧
      Real.exp (4*w.re) ≤ (4/3)*Real.exp (4*u) := by
  have hc := (coordinate_bounds u w hw).1
  rcases abs_le.mp hc with ⟨hlo,hhi⟩
  have hlow : Real.exp (4*u-1/4) ≤ Real.exp (4*w.re) := Real.exp_le_exp.mpr (by linarith)
  have hhigh : Real.exp (4*w.re) ≤ Real.exp (4*u+1/4) := Real.exp_le_exp.mpr (by linarith)
  have hp := quarter_exp_bounds
  constructor
  · calc
      _ ≤ Real.exp (-1/4)*Real.exp (4*u) := mul_le_mul_of_nonneg_right hp.1 (Real.exp_pos _).le
      _ = Real.exp (4*u-1/4) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hlow
  · calc
      _ ≤ Real.exp (4*u+1/4) := hhigh
      _ = Real.exp (1/4)*Real.exp (4*u) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hp.2 (Real.exp_pos _).le

theorem cos_lower (u : ℝ) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    (31/32 : ℝ) ≤ Real.cos (4*w.im) := by
  have hb := (coordinate_bounds u w hw).2
  rcases abs_le.mp hb with ⟨hlo,hhi⟩
  have hsq : w.im^2 ≤ 1/256 := by nlinarith [sq_nonneg w.im]
  have h := Real.one_sub_sq_div_two_le_cos (x := 4*w.im)
  nlinarith

theorem exp_complex_real_lower (u : ℝ) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    (1/2)*Real.exp (4*u) ≤ (Complex.exp (4*w)).re := by
  have he := (exp_real_bounds u w hw).1
  have hc := cos_lower u w hw
  have hm := mul_le_mul he hc (by norm_num : (0 : ℝ) ≤ 31/32) (Real.exp_pos _).le
  have hp := Real.exp_pos (4*u)
  have hr : (Complex.exp (4*w)).re=Real.exp (4*w.re)*Real.cos (4*w.im) := by
    rw [Complex.exp_re]
    norm_num [Complex.mul_re,Complex.mul_im]
  rw [hr]
  nlinarith

theorem exp_complex_norm_upper (u : ℝ) (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    ‖Complex.exp (4*w)‖ ≤ (4/3)*Real.exp (4*u) := by
  rw [Complex.norm_exp]
  norm_num [Complex.mul_re]
  exact (exp_real_bounds u w hw).2

theorem neighborhood_domain (u : ℝ) (hu : 1 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/16)) : 0 ≤ w.re ∧ 8 ≤ (Complex.exp (4*w)).re := by
  have hc := (abs_le.mp (coordinate_bounds u w hw).1).1
  have he := exp_complex_real_lower u w hw
  have hv := exp_four_ge_sixteen u hu
  constructor <;> linarith

theorem kernel_analytic_on_neighborhood (u : ℝ) (hu : 1 ≤ u) :
    AnalyticOnNhd ℂ kernelComplex (closedBall (u : ℂ) (1/16)) := by
  intro w hw
  exact kernelComplex_analyticAt w (by have h := (neighborhood_domain u hu w hw).2; linarith)

theorem kernel_nonzero_on_neighborhood (u : ℝ) (hu : 1 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/16)) : kernelComplex w ≠ 0 := by
  have h := neighborhood_domain u hu w hw
  exact kernel_ne_zero w h.1 (by linarith [h.2])

theorem slope_analytic_on_neighborhood (t u : ℝ) (hu : 1 ≤ u) :
    AnalyticOnNhd ℂ (complexSlope t) (closedBall (u : ℂ) (1/16)) := by
  intro w hw
  have ha := kernel_analytic_on_neighborhood u hu w hw
  have hn := kernel_nonzero_on_neighborhood u hu w hw
  exact (analyticAt_const.mul (analyticAt_id.pow 3)).add (ha.deriv.div ha hn)

open RiemannThetaDerivativeBounds

theorem leading_norm_upper (w : ℂ) (ha : 0 ≤ w.re) :
    ‖leading w‖ ≤ 44*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re) := by
  have h9 : ‖Complex.exp (9*w)‖=Real.exp (9*w.re) := by simpa using norm_exp_scaled 9 w
  have h5 : ‖Complex.exp (5*w)‖=Real.exp (5*w.re) := by simpa using norm_exp_scaled 5 w
  have hE : ‖Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*w))‖=
      Real.exp (-Real.pi*(Complex.exp (4*w)).re) := by
    simpa only [Complex.ofReal_neg] using norm_exp_scaled (-Real.pi) (Complex.exp (4*w))
  have hA : ‖2*(Real.pi : ℂ)^2*Complex.exp (9*w)‖=2*Real.pi^2*Real.exp (9*w.re) := by
    simp only [norm_mul,norm_pow,norm_pi,h9]
    norm_num
  have hB : ‖3*(Real.pi : ℂ)*Complex.exp (5*w)‖=3*Real.pi*Real.exp (5*w.re) := by
    simp only [norm_mul,norm_pi,h5]
    norm_num
  have h59 : Real.exp (5*w.re) ≤ Real.exp (9*w.re) := Real.exp_le_exp.mpr (by linarith)
  have hp2 : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
  have hp : 2*Real.pi^2+3*Real.pi ≤ 44 := by nlinarith [Real.pi_lt_four]
  have hc : 2*Real.pi^2*Real.exp (9*w.re)+3*Real.pi*Real.exp (5*w.re) ≤44*Real.exp (9*w.re) := by
    calc
      _ ≤ (2*Real.pi^2+3*Real.pi)*Real.exp (9*w.re) := by
        nlinarith [mul_le_mul_of_nonneg_left h59 (by positivity : 0 ≤ 3*Real.pi)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
  rw [leading,norm_mul,hE]
  calc
    _ ≤ (‖2*(Real.pi : ℂ)^2*Complex.exp (9*w)‖+‖3*(Real.pi : ℂ)*Complex.exp (5*w)‖)*
        Real.exp (-Real.pi*(Complex.exp (4*w)).re) :=
      mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le
    _ ≤ _ := by rw [hA,hB]; exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le

theorem derivativeEnvelope_upper (w : ℂ) (ha : 0 ≤ w.re) :
    derivativeEnvelope w ≤ 82816*Real.exp (13*w.re)*Real.exp (-4*Real.pi*(Complex.exp (4*w)).re) := by
  have h9 : Real.exp (9*w.re) ≤ Real.exp (13*w.re) := Real.exp_le_exp.mpr (by linarith)
  have h5 : Real.exp (5*w.re) ≤ Real.exp (13*w.re) := Real.exp_le_exp.mpr (by linarith)
  have hp2 : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
  have hp3 : Real.pi^3 ≤ 64 := by
    have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 3
    norm_num at h
    exact h
  have hp : 960*Real.pi^2+1024*Real.pi^3+480*Real.pi ≤ 82816 := by nlinarith [Real.pi_lt_four]
  unfold derivativeEnvelope
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    _ ≤ (960*Real.pi^2+1024*Real.pi^3+480*Real.pi)*Real.exp (13*w.re) := by
      nlinarith [mul_le_mul_of_nonneg_left h9 (by positivity : 0 ≤ 960*Real.pi^2),
        mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 480*Real.pi)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le

theorem residualEnvelope_upper (w : ℂ) (ha : 0 ≤ w.re) :
    residualEnvelope w ≤
      12*Real.pi*Real.exp (5*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)+
        223616*Real.exp (13*w.re)*Real.exp (-4*Real.pi*(Complex.exp (4*w)).re) := by
  have hl := leading_norm_upper w ha
  have hd := derivativeEnvelope_upper w ha
  have he4 : 1 ≤ Real.exp (4*w.re) := Real.one_le_exp (by positivity)
  have hc : 9+4*Real.pi*Real.exp (4*w.re) ≤ 25*Real.exp (4*w.re) := by
    have h := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (Real.exp_pos (4*w.re)).le
    nlinarith
  have h13 : Real.exp (4*w.re)*Real.exp (9*w.re)=Real.exp (13*w.re) := by
    rw [← Real.exp_add]; congr 1; ring
  have hR : Real.exp (-3*Real.pi*(Complex.exp (4*w)).re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)=
      Real.exp (-4*Real.pi*(Complex.exp (4*w)).re) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold residualEnvelope
  calc
    _ ≤ 12*Real.pi*Real.exp (5*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)+
        (82816*Real.exp (13*w.re)*Real.exp (-4*Real.pi*(Complex.exp (4*w)).re))+
        (25*Real.exp (4*w.re))*(128*Real.exp (-3*Real.pi*(Complex.exp (4*w)).re)*
          (44*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re))) := by gcongr
    _ = _ := by
      have hp : (25*Real.exp (4*w.re))*(128*Real.exp (-3*Real.pi*(Complex.exp (4*w)).re)*
          (44*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)))=
          140800*Real.exp (13*w.re)*Real.exp (-4*Real.pi*(Complex.exp (4*w)).re) := by
        calc
          _ = 140800*(Real.exp (4*w.re)*Real.exp (9*w.re))*
              (Real.exp (-3*Real.pi*(Complex.exp (4*w)).re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)) := by ring
          _ = _ := by rw [h13,hR]
      rw [hp]
      ring

theorem logDerivative_coarse_bound (w : ℂ) (ha : 0 ≤ w.re) (hR : 1 ≤ (Complex.exp (4*w)).re) :
    ‖kernelDerivative w/kernelComplex w-(9-4*(Real.pi : ℂ)*Complex.exp (4*w))‖ ≤
      5*Real.exp (-4*w.re)+30000*Real.exp (4*w.re)*Real.exp (-3*Real.pi*(Complex.exp (4*w)).re) := by
  apply (logDerivative_model_bound w ha hR).trans
  apply (div_le_iff₀ (by positivity : 0 <
    (21/8 : ℝ)*Real.pi*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re))).mpr
  apply (residualEnvelope_upper w ha).trans
  have h5 : Real.exp (5*w.re)=Real.exp (-4*w.re)*Real.exp (9*w.re) := by
    rw [← Real.exp_add]; congr 1; ring
  have h13 : Real.exp (13*w.re)=Real.exp (4*w.re)*Real.exp (9*w.re) := by
    rw [← Real.exp_add]; congr 1; ring
  have hR4 : Real.exp (-4*Real.pi*(Complex.exp (4*w)).re)=
      Real.exp (-3*Real.pi*(Complex.exp (4*w)).re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re) := by
    rw [← Real.exp_add]; congr 1; ring
  have hp1 : 12*Real.pi ≤ 5*((21/8 : ℝ)*Real.pi) := by nlinarith [Real.pi_pos]
  have hp2 : (223616 : ℝ) ≤ 30000*((21/8 : ℝ)*Real.pi) := by nlinarith [Real.pi_gt_three]
  rw [h5,h13,hR4]
  calc
    _ = (12*Real.pi)*Real.exp (-4*w.re)*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)+
        (223616 : ℝ)*(Real.exp (4*w.re)*Real.exp (9*w.re))*
          (Real.exp (-3*Real.pi*(Complex.exp (4*w)).re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)) := by ring
    _ ≤ (5*((21/8 : ℝ)*Real.pi))*Real.exp (-4*w.re)*Real.exp (9*w.re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)+
        (30000*((21/8 : ℝ)*Real.pi))*(Real.exp (4*w.re)*Real.exp (9*w.re))*
          (Real.exp (-3*Real.pi*(Complex.exp (4*w)).re)*Real.exp (-Real.pi*(Complex.exp (4*w)).re)) := by gcongr
    _ = _ := by ring

theorem slope_model_error_on_neighborhood (t u : ℝ) (hu : 1 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    ‖complexSlope t w-RiemannQuarticSaddleTheta.modelDerivative t w‖ ≤ 1 := by
  have hdom := neighborhood_domain u hu w hw
  have hv := exp_four_ge_sixteen u hu
  have he := exp_real_bounds u w hw
  have he_upper := he.2
  have hR := exp_complex_real_lower u w hw
  have hbound := logDerivative_coarse_bound w hdom.1 (by linarith [hdom.2])
  have hfirst : 5*Real.exp (-4*w.re) ≤ (5/12 : ℝ) := by
    rw [show -4*w.re=-(4*w.re) by ring,Real.exp_neg,← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith [he.1]
  have hr : Real.exp (-3*Real.pi*(Complex.exp (4*w)).re) ≤ Real.exp (-Real.pi*Real.exp (4*u)) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 3*Real.pi)
    nlinarith [mul_pos Real.pi_pos (Real.exp_pos (4*u))]
  have htail : 30000*Real.exp (4*w.re)*Real.exp (-3*Real.pi*(Complex.exp (4*w)).re) ≤ (1/2 : ℝ) := by
    have hcomp : 30000*Real.exp (4*w.re)*Real.exp (-3*Real.pi*(Complex.exp (4*w)).re) ≤
        40000*Real.exp (4*u)*Real.exp (-Real.pi*Real.exp (4*u)) := by
      calc
        _ ≤ 30000*((4/3)*Real.exp (4*u))*Real.exp (-Real.pi*Real.exp (4*u)) := by gcongr
        _ = _ := by ring
    have hc := curvature_error_small (Real.exp (4*u)) hv
    have hp : 80000*Real.exp (4*u) ≤ 6000000*(Real.exp (4*u))^2 := by
      have h := mul_le_mul_of_nonneg_right
        (by linarith : (80000 : ℝ) ≤ 6000000*Real.exp (4*u)) (Real.exp_pos (4*u)).le
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-Real.pi*Real.exp (4*u))).le
    nlinarith
  have heq : complexSlope t w-RiemannQuarticSaddleTheta.modelDerivative t w=
      kernelDerivative w/kernelComplex w-(9-4*(Real.pi : ℂ)*Complex.exp (4*w)) := by
    unfold complexSlope RiemannQuarticSaddleTheta.modelDerivative
    rw [(kernelComplex_hasDerivAt w (by linarith [hdom.2])).deriv]
    ring
  rw [heq]
  linarith

theorem slope_error_analytic_on_neighborhood (t u : ℝ) (hu : 1 ≤ u) :
    AnalyticOnNhd ℂ (fun w => complexSlope t w-RiemannQuarticSaddleTheta.modelDerivative t w)
      (closedBall (u : ℂ) (1/16)) := by
  intro w hw
  have hm : AnalyticAt ℂ (RiemannQuarticSaddleTheta.modelDerivative t) w := by
    unfold RiemannQuarticSaddleTheta.modelDerivative
    fun_prop
  exact (slope_analytic_on_neighborhood t u hu w hw).sub hm

theorem slope_error_cauchy_bound (t u : ℝ) (hu : 1 ≤ u) (n : ℕ) :
    ‖iteratedDeriv n (fun w => complexSlope t w-RiemannQuarticSaddleTheta.modelDerivative t w) (u : ℂ)‖ ≤
      (n.factorial : ℝ)*(16 : ℝ)^n := by
  have ha := slope_error_analytic_on_neighborhood t u hu
  have hd := ha.differentiableOn.diffContOnCl_ball (Set.Subset.refl _)
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1/16) hd
    (fun w hw => slope_model_error_on_neighborhood t u hu w (sphere_subset_closedBall hw))
  calc
    _ ≤ (n.factorial : ℝ)*1/((1/16 : ℝ)^n) := h
    _ = _ := by simp only [one_div,inv_pow,mul_one,div_inv_eq_mul]
end OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleNeighborhood
