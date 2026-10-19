import Foundation.RiemannThetaHolomorphic
/-! Quantitative comparison of the actual theta-kernel logarithmic derivative
with the leading quartic saddle model. The sixth moment is needed by the
exact kernel derivative. All tail and denominator bounds have explicit domains.
No actual saddle existence or global contour/re-entry theorem is asserted. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RiemannThetaDerivativeBounds
open RiemannQuarticKernel RiemannQuarticSaddleTheta

def ratioSix (v : ℝ) : ℝ := 64*Real.exp (-3*Real.pi*v)

theorem ratioSix_nonneg (v : ℝ) : 0 ≤ ratioSix v := by unfold ratioSix; positivity

theorem ratioSix_le_sixteenth (v : ℝ) (hv : 1 ≤ v) : ratioSix v ≤ 1/16 := by
  have h32 := RiemannThetaEffective.exp_nine_halves_ge
  have h9 : (1024 : ℝ) ≤ Real.exp 9 := by
    calc
      (1024 : ℝ)=32*32 := by norm_num
      _ ≤ Real.exp (9/2)*Real.exp (9/2) := mul_le_mul h32 h32 (by norm_num) (Real.exp_pos _).le
      _ = Real.exp 9 := by rw [← Real.exp_add]; congr 1; ring
  have hx : 9 ≤ 3*Real.pi*v := by
    have h := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 3*Real.pi)
    nlinarith [Real.pi_gt_three]
  have he := h9.trans (Real.exp_le_exp.mpr hx)
  unfold ratioSix
  rw [show -3*Real.pi*v=-(3*Real.pi*v) by ring, Real.exp_neg]
  have hi : (Real.exp (3*Real.pi*v))⁻¹ ≤ (1024 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr he
  nlinarith

theorem thetaTerm_six_step (v : ℝ) (hv : 0 ≤ v) (n : ℕ) :
    thetaTerm 6 v (n+1) ≤ ratioSix v*thetaTerm 6 v n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp : ((n : ℝ)+2)^6 ≤ 64*((n : ℝ)+1)^6 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ)+2)
      (by linarith : (n : ℝ)+2 ≤ 2*((n : ℝ)+1)) 6
    nlinarith
  have he : Real.exp (-Real.pi*((n : ℝ)+2)^2*v)=
      Real.exp (-Real.pi*((n : ℝ)+1)^2*v)*Real.exp (-Real.pi*(2*(n : ℝ)+3)*v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hg : Real.exp (-Real.pi*(2*(n : ℝ)+3)*v) ≤ Real.exp (-3*Real.pi*v) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hn) hv]
  simp only [thetaTerm, Nat.cast_add, Nat.cast_one]
  rw [show (n : ℝ)+1+1=(n : ℝ)+2 by ring, he]
  calc
    _ ≤ (64*((n : ℝ)+1)^6)*
        (Real.exp (-Real.pi*((n : ℝ)+1)^2*v)*Real.exp (-3*Real.pi*v)) := by gcongr
    _ = _ := by unfold ratioSix; ring

theorem thetaTerm_six_shift (v : ℝ) (hv : 0 ≤ v) (N n : ℕ) :
    thetaTerm 6 v (N+n) ≤ thetaTerm 6 v N*(ratioSix v)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ ≤ ratioSix v*thetaTerm 6 v (N+n) := by
        simpa only [Nat.add_succ] using thetaTerm_six_step v hv (N+n)
      _ ≤ ratioSix v*(thetaTerm 6 v N*(ratioSix v)^n) :=
        mul_le_mul_of_nonneg_left ih (ratioSix_nonneg v)
      _ = _ := by rw [pow_succ]; ring

theorem tail_six_bound (N : ℕ) (v : ℝ) (hv : 1 ≤ v) :
    RiemannThetaEffective.tail 6 N v ≤ 2*thetaTerm 6 v N := by
  have hr0 := ratioSix_nonneg v
  have hr : ratioSix v ≤ 1/2 := (ratioSix_le_sixteenth v hv).trans (by norm_num)
  have hr1 : ratioSix v < 1 := by linarith
  have hs := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (thetaTerm 6 v N)
  have hh : RiemannThetaEffective.tail 6 N v ≤ thetaTerm 6 v N*(1-ratioSix v)⁻¹ := by
    exact ((RiemannThetaEffective.tail_summable 6 N v (by linarith)).tsum_le_tsum
      (thetaTerm_six_shift v (by linarith) N) hs.summable).trans_eq hs.tsum_eq
  apply hh.trans
  rw [← div_eq_mul_inv, div_le_iff₀ (by linarith : 0 < 1-ratioSix v)]
  nlinarith [thetaTerm_nonneg 6 v N]

theorem complex_tail_six_bound (v : ℂ) (hv : 1 ≤ v.re) :
    ‖complexThetaTail 6 1 v‖ ≤ 128*Real.exp (-4*Real.pi*v.re) := by
  have hs : Summable (fun n => ‖complexThetaTerm 6 v (1+n)‖) := by
    simp_rw [norm_complexThetaTerm]
    exact RiemannThetaEffective.tail_summable 6 1 v.re (by linarith)
  calc
    _ ≤ ∑' n, ‖complexThetaTerm 6 v (1+n)‖ := norm_tsum_le_tsum_norm hs
    _ = RiemannThetaEffective.tail 6 1 v.re := by simp only [norm_complexThetaTerm, RiemannThetaEffective.tail]
    _ ≤ 2*thetaTerm 6 v.re 1 := tail_six_bound 1 v.re hv
    _ = _ := by norm_num [thetaTerm]; ring_nf
open RiemannThetaComplexKernel

def leadingDerivative (u : ℂ) : ℂ :=
  (30*(Real.pi : ℂ)^2*Complex.exp (9*u)-
    8*(Real.pi : ℂ)^3*Complex.exp (13*u)-15*(Real.pi : ℂ)*Complex.exp (5*u))*
    Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*u))

theorem derivative_remainder (u : ℂ) (hu : 0 < (Complex.exp (4*u)).re) :
    kernelDerivative u-leadingDerivative u=
      30*(Real.pi : ℂ)^2*Complex.exp (9*u)*complexThetaTail 4 1 (Complex.exp (4*u))-
        8*(Real.pi : ℂ)^3*Complex.exp (13*u)*complexThetaTail 6 1 (Complex.exp (4*u))-
        15*(Real.pi : ℂ)*Complex.exp (5*u)*complexThetaTail 2 1 (Complex.exp (4*u)) := by
  unfold kernelDerivative leadingDerivative
  rw [moment_split 4 _ hu, moment_split 6 _ hu, moment_split 2 _ hu]
  simp only [complexThetaTerm, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add,
    one_pow, one_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_mul]
  ring

theorem complex_tail_four_bound (k : ℕ) (hk : k ≤ 4) (v : ℂ) (hv : 1/2 ≤ v.re) :
    ‖complexThetaTail k 1 v‖ ≤ 32*Real.exp (-4*Real.pi*v.re) := by
  have h := complexThetaTail_relative k hk v hv
  rw [leading_theta_norm] at h
  convert h using 1
  have he : Real.exp (-4*Real.pi*v.re)=
      Real.exp (-3*Real.pi*v.re)*Real.exp (-Real.pi*v.re) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

theorem derivative_error_bound (u : ℂ) (hu : 1 ≤ (Complex.exp (4*u)).re) :
    ‖kernelDerivative u-leadingDerivative u‖ ≤
      (960*Real.pi^2*Real.exp (9*u.re)+1024*Real.pi^3*Real.exp (13*u.re)+
        480*Real.pi*Real.exp (5*u.re))*Real.exp (-4*Real.pi*(Complex.exp (4*u)).re) := by
  have h4 := complex_tail_four_bound 4 le_rfl (Complex.exp (4*u)) (by linarith)
  have h2 := complex_tail_four_bound 2 (by norm_num) (Complex.exp (4*u)) (by linarith)
  have h6 := complex_tail_six_bound (Complex.exp (4*u)) hu
  have h9 : ‖30*(Real.pi : ℂ)^2*Complex.exp (9*u)‖=30*Real.pi^2*Real.exp (9*u.re) := by
    simp only [norm_mul, norm_pow, norm_pi]
    rw [show (9 : ℂ)=(9 : ℝ) by norm_num, norm_exp_scaled]
    norm_num
  have h13 : ‖8*(Real.pi : ℂ)^3*Complex.exp (13*u)‖=8*Real.pi^3*Real.exp (13*u.re) := by
    simp only [norm_mul, norm_pow, norm_pi]
    rw [show (13 : ℂ)=(13 : ℝ) by norm_num, norm_exp_scaled]
    norm_num
  have h5 : ‖15*(Real.pi : ℂ)*Complex.exp (5*u)‖=15*Real.pi*Real.exp (5*u.re) := by
    simp only [norm_mul, norm_pi]
    rw [show (5 : ℂ)=(5 : ℝ) by norm_num, norm_exp_scaled]
    norm_num
  rw [derivative_remainder u (by linarith)]
  calc
    _ ≤ ‖30*(Real.pi : ℂ)^2*Complex.exp (9*u)*complexThetaTail 4 1 (Complex.exp (4*u))-
        8*(Real.pi : ℂ)^3*Complex.exp (13*u)*complexThetaTail 6 1 (Complex.exp (4*u))‖+
        ‖15*(Real.pi : ℂ)*Complex.exp (5*u)*complexThetaTail 2 1 (Complex.exp (4*u))‖ := norm_sub_le _ _
    _ ≤ (‖30*(Real.pi : ℂ)^2*Complex.exp (9*u)*complexThetaTail 4 1 (Complex.exp (4*u))‖+
        ‖8*(Real.pi : ℂ)^3*Complex.exp (13*u)*complexThetaTail 6 1 (Complex.exp (4*u))‖)+
        ‖15*(Real.pi : ℂ)*Complex.exp (5*u)*complexThetaTail 2 1 (Complex.exp (4*u))‖ := by gcongr; exact norm_sub_le _ _
    _ = 30*Real.pi^2*Real.exp (9*u.re)*‖complexThetaTail 4 1 (Complex.exp (4*u))‖+
        8*Real.pi^3*Real.exp (13*u.re)*‖complexThetaTail 6 1 (Complex.exp (4*u))‖+
        15*Real.pi*Real.exp (5*u.re)*‖complexThetaTail 2 1 (Complex.exp (4*u))‖ := by
      rw [norm_mul, h9, norm_mul, h13, norm_mul, h5]
    _ ≤ 30*Real.pi^2*Real.exp (9*u.re)*(32*Real.exp (-4*Real.pi*(Complex.exp (4*u)).re))+
        8*Real.pi^3*Real.exp (13*u.re)*(128*Real.exp (-4*Real.pi*(Complex.exp (4*u)).re))+
        15*Real.pi*Real.exp (5*u.re)*(32*Real.exp (-4*Real.pi*(Complex.exp (4*u)).re)) := by gcongr
    _ = _ := by ring

theorem leading_model_correction (u : ℂ) :
    leadingDerivative u-(9-4*(Real.pi : ℂ)*Complex.exp (4*u))*leading u=
      12*(Real.pi : ℂ)*Complex.exp (5*u)*
        Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*u)) := by
  have h13 : Complex.exp (13*u)=Complex.exp (9*u)*Complex.exp (4*u) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h9 : Complex.exp (9*u)=Complex.exp (5*u)*Complex.exp (4*u) := by
    rw [← Complex.exp_add]; congr 1; ring
  unfold leadingDerivative leading
  rw [h13,h9]
  ring

theorem kernel_relative_eighth (u : ℂ) (ha : 0 ≤ u.re)
    (hu : 1 ≤ (Complex.exp (4*u)).re) :
    ‖kernelComplex u-leading u‖ ≤ (1/8 : ℝ)*‖leading u‖ := by
  have hr := ratioSix_le_sixteenth (Complex.exp (4*u)).re hu
  unfold ratioSix at hr
  have hc : 128*Real.exp (-3*Real.pi*(Complex.exp (4*u)).re) ≤ (1/8 : ℝ) := by linarith
  exact (relative_bound u ha (by linarith)).trans
    (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

theorem kernel_norm_lower (u : ℂ) (ha : 0 ≤ u.re)
    (hu : 1 ≤ (Complex.exp (4*u)).re) :
    (21/8 : ℝ)*Real.pi*Real.exp (9*u.re)*Real.exp (-Real.pi*(Complex.exp (4*u)).re) ≤
      ‖kernelComplex u‖ := by
  have hr := kernel_relative_eighth u ha hu
  have hn := norm_sub_norm_le (leading u) (kernelComplex u)
  rw [norm_sub_rev] at hr
  have hl := leading_norm_lower u ha
  nlinarith

theorem actual_model_residual (u : ℂ) :
    kernelDerivative u-(9-4*(Real.pi : ℂ)*Complex.exp (4*u))*kernelComplex u=
      12*(Real.pi : ℂ)*Complex.exp (5*u)*Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*u))+
      (kernelDerivative u-leadingDerivative u)-
      (9-4*(Real.pi : ℂ)*Complex.exp (4*u))*(kernelComplex u-leading u) := by
  have h := leading_model_correction u
  linear_combination h

def derivativeEnvelope (u : ℂ) : ℝ :=
  (960*Real.pi^2*Real.exp (9*u.re)+1024*Real.pi^3*Real.exp (13*u.re)+
    480*Real.pi*Real.exp (5*u.re))*Real.exp (-4*Real.pi*(Complex.exp (4*u)).re)

def residualEnvelope (u : ℂ) : ℝ :=
  12*Real.pi*Real.exp (5*u.re)*Real.exp (-Real.pi*(Complex.exp (4*u)).re)+
    derivativeEnvelope u+
    (9+4*Real.pi*Real.exp (4*u.re))*
      (128*Real.exp (-3*Real.pi*(Complex.exp (4*u)).re)*‖leading u‖)

theorem actual_model_residual_bound (u : ℂ) (ha : 0 ≤ u.re)
    (hu : 1 ≤ (Complex.exp (4*u)).re) :
    ‖kernelDerivative u-(9-4*(Real.pi : ℂ)*Complex.exp (4*u))*kernelComplex u‖ ≤
      residualEnvelope u := by
  have he := relative_bound u ha (by linarith)
  have hd := derivative_error_bound u hu
  have hm : ‖9-4*(Real.pi : ℂ)*Complex.exp (4*u)‖ ≤ 9+4*Real.pi*Real.exp (4*u.re) := by
    calc
      _ ≤ ‖(9 : ℂ)‖+‖4*(Real.pi : ℂ)*Complex.exp (4*u)‖ := norm_sub_le _ _
      _ = _ := by
        simp only [norm_mul, norm_pi]
        rw [show (4 : ℂ)=(4 : ℝ) by norm_num, norm_exp_scaled]
        norm_num
  have hc : ‖12*(Real.pi : ℂ)*Complex.exp (5*u)*Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*u))‖=
      12*Real.pi*Real.exp (5*u.re)*Real.exp (-Real.pi*(Complex.exp (4*u)).re) := by
    simp only [norm_mul, norm_pi]
    rw [show (5 : ℂ)=(5 : ℝ) by norm_num, norm_exp_scaled]
    rw [show -(Real.pi : ℂ)=((-Real.pi : ℝ) : ℂ) by simp, norm_exp_scaled]
    norm_num
  rw [actual_model_residual]
  calc
    _ ≤ ‖12*(Real.pi : ℂ)*Complex.exp (5*u)*Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*u))+
        (kernelDerivative u-leadingDerivative u)‖+
        ‖(9-4*(Real.pi : ℂ)*Complex.exp (4*u))*(kernelComplex u-leading u)‖ := norm_sub_le _ _
    _ ≤ ‖12*(Real.pi : ℂ)*Complex.exp (5*u)*Complex.exp (-(Real.pi : ℂ)*Complex.exp (4*u))‖+
        ‖kernelDerivative u-leadingDerivative u‖+
        ‖(9-4*(Real.pi : ℂ)*Complex.exp (4*u))*(kernelComplex u-leading u)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ _ := by
      rw [hc, norm_mul]
      unfold residualEnvelope derivativeEnvelope
      gcongr

theorem logDerivative_model_bound (u : ℂ) (ha : 0 ≤ u.re)
    (hu : 1 ≤ (Complex.exp (4*u)).re) :
    ‖kernelDerivative u/kernelComplex u-(9-4*(Real.pi : ℂ)*Complex.exp (4*u))‖ ≤
      residualEnvelope u/
        ((21/8 : ℝ)*Real.pi*Real.exp (9*u.re)*Real.exp (-Real.pi*(Complex.exp (4*u)).re)) := by
  have hne := kernel_ne_zero u ha hu
  have heq : kernelDerivative u/kernelComplex u-(9-4*(Real.pi : ℂ)*Complex.exp (4*u))=
      (kernelDerivative u-(9-4*(Real.pi : ℂ)*Complex.exp (4*u))*kernelComplex u)/kernelComplex u := by
    field_simp
  rw [heq, norm_div]
  calc
    _ ≤ residualEnvelope u/‖kernelComplex u‖ :=
      div_le_div_of_nonneg_right (actual_model_residual_bound u ha hu) (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by unfold residualEnvelope derivativeEnvelope; positivity)
      (by positivity) (kernel_norm_lower u ha hu)

theorem phase_model_bound (t : ℝ) (u : ℂ) (ha : 0 ≤ u.re)
    (hu : 1 ≤ (Complex.exp (4*u)).re) :
    ‖(4*(t : ℂ)*u^3+kernelDerivative u/kernelComplex u)-modelDerivative t u‖ ≤
      residualEnvelope u/
        ((21/8 : ℝ)*Real.pi*Real.exp (9*u.re)*Real.exp (-Real.pi*(Complex.exp (4*u)).re)) := by
  convert logDerivative_model_bound u ha hu using 1
  congr 1
  unfold modelDerivative
  ring
end OperatorDerivativeRewrite.Foundation.RiemannThetaDerivativeBounds
