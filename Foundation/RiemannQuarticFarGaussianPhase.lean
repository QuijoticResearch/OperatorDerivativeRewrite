import Foundation.RiemannQuarticFarAnalyticBranch
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
/-! Differentiating the genuine model-curvature Gaussian along actual far saddles.
The positive-real coefficient fixes the principal square-root branch. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarGaussianPhase
open RiemannQuarticFarAnalyticBranch RiemannQuarticFarCorrection RiemannQuarticFarModelSaddle
open RiemannQuarticFrequencyBranch RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch
open RiemannQuarticFarGaussianLimit RiemannQuarticFarGaussianLocal RiemannQuarticFarPairing

theorem gaussian_integral_hasDerivAt (b : ℂ) (hb : 0 < b.re) :
    HasDerivAt (fun c : ℂ => ∫ s : ℝ, Complex.exp (-c*(s : ℂ)^2))
      (-(∫ s : ℝ, Complex.exp (-b*(s : ℂ)^2))/(2*b)) b := by
  let G := fun c : ℂ => ∫ s : ℝ, Complex.exp (-c*(s : ℂ)^2)
  have hbne : b ≠ 0 := by intro h; simp [h] at hb
  have hn : ∀ᶠ c : ℂ in nhds b, 0 < c.re :=
    continuous_re.continuousAt.eventually (lt_mem_nhds hb)
  have heq : G =ᶠ[nhds b] (fun c : ℂ => ((Real.pi : ℂ)/c)^(1/2 : ℂ)) := by
    filter_upwards [hn] with c hc
    exact integral_gaussian_complex hc
  have hreal : 0 < ((Real.pi : ℂ)/b).re := by
    rw [Complex.div_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero]
    exact div_pos (mul_pos Real.pi_pos hb) (Complex.normSq_pos.mpr hbne)
  have hpow := ((hasDerivAt_const b (Real.pi : ℂ)).div (hasDerivAt_id b) hbne).cpow_const
    (c := (1/2 : ℂ)) (Or.inl hreal)
  have hd : DifferentiableAt ℂ G b := hpow.differentiableAt.congr_of_eventuallyEq heq
  have hsq : (fun c : ℂ => G c^2*c) =ᶠ[nhds b] (fun _ => (Real.pi : ℂ)) := by
    filter_upwards [hn] with c hc
    have hcne : c ≠ 0 := by intro h; simp [h] at hc
    change (∫ s : ℝ, Complex.exp (-c*(s : ℂ)^2))^2*c= _
    rw [integral_gaussian_sq_complex hc,div_mul_cancel₀ _ hcne]
  have hder := (((hd.hasDerivAt.pow 2).mul (hasDerivAt_id b)).congr_of_eventuallyEq hsq.symm).unique
    (hasDerivAt_const b (Real.pi : ℂ))
  norm_num only [Nat.reduceSub,pow_one,mul_one,id_eq,Pi.pow_apply] at hder
  have hsval : G b^2=(Real.pi : ℂ)/b := integral_gaussian_sq_complex hb
  have hG : G b ≠ 0 := by
    intro h
    rw [h,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsval
    exact (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hbne) hsval.symm
  have hprod : G b*(2*b*deriv G b+G b)=0 := by linear_combination hder
  have hrel : 2*b*deriv G b+G b=0 := (mul_eq_zero.mp hprod).resolve_left hG
  have hvalue : deriv G b= -G b/(2*b) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hbne)).mpr
    linear_combination hrel
  rw [← hvalue]
  exact hd.hasDerivAt

theorem model_curvature_hasDerivAt (t : ℝ) (v : ℂ) :
    HasDerivAt (deriv (modelDerivative t))
      (24*(t : ℂ)*v-64*(Real.pi : ℂ)*Complex.exp (4*v)) v := by
  have he : deriv (modelDerivative t)=(fun q : ℂ => 12*(t : ℂ)*q^2-16*(Real.pi : ℂ)*Complex.exp (4*q)) :=
    funext (fun q => (modelDerivative_hasDerivAt t q).deriv)
  rw [he]
  have h := (((hasDerivAt_id v).pow 2).const_mul (12*(t : ℂ))).sub
    ((((hasDerivAt_id v).const_mul (4 : ℂ)).cexp).const_mul (16*(Real.pi : ℂ)))
  convert h using 1
  · funext q; rfl
  · simp only [id_eq,Nat.reduceSub,pow_one,mul_one]
    ring

private theorem polynomial_bound (t x : ℝ) (ht : 1 ≤ t) (w : ℂ)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) : 4*t*‖w‖^3+9 ≤ x := by
  have hpow := pow_le_pow_left₀ (norm_nonneg w) (by linarith : ‖w‖ ≤ ‖w‖+1) 3
  have hm := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ t)
  nlinarith [pow_nonneg (norm_nonneg w) 3]

variable (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
  (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
  (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
include ht hx hr hi hp hs
local notation "B" => RiemannQuarticFarAnalyticBranch.branch t x ht hx w hr hi hp hs

theorem model_curvature_norm_bound (v : ℂ) (hv : ‖v-w‖ ≤ 1/x) :
    ‖24*(t : ℂ)*v-64*(Real.pi : ℂ)*Complex.exp (4*v)‖ ≤ 4096*x := by
  have ht0 : 0 ≤ t := by linarith
  have hx0 : 0 < x := by linarith
  have hv1 : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hv4 : 4*‖v-w‖ ≤ 1 := by
    have h := (le_div_iff₀ hx0).mp hv
    nlinarith
  have he0 := model_exp_norm_le_frequency t x ht0 hx0 w (polynomial_bound t x ht w hp) hs
  have hed := exp4_difference_bound w v hv4
  have het := norm_add_le (Complex.exp (4*v)-Complex.exp (4*w)) (Complex.exp (4*w))
  rw [sub_add_cancel] at het
  have hmul := mul_le_mul_of_nonneg_left hv1 (by positivity : 0 ≤ 8*‖Complex.exp (4*w)‖)
  have he : ‖Complex.exp (4*v)‖ ≤ 9*x := by nlinarith
  let M := ‖w‖+1
  have hM : 1 ≤ M := by dsimp [M]; linarith [norm_nonneg w]
  have hM0 : 0 ≤ M := by linarith
  have hM2 : 1 ≤ M^2 := by nlinarith
  have hM3 : M ≤ M^3 := by nlinarith [mul_nonneg hM0 (by linarith : 0 ≤ M^2-1)]
  have hvM : ‖v‖ ≤ M := by
    have h := norm_add_le (v-w) w
    rw [sub_add_cancel] at h
    dsimp [M]
    linarith
  have hvt := mul_le_mul_of_nonneg_left hvM ht0
  have hMt := mul_le_mul_of_nonneg_left hM3 ht0
  have hpoly : 24*t*‖v‖ ≤ x := by
    change 100*(t*M^3+1) ≤ x at hp
    nlinarith [mul_nonneg ht0 (pow_nonneg hM0 3)]
  have h := norm_sub_le (24*(t : ℂ)*v) (64*(Real.pi : ℂ)*Complex.exp (4*v))
  simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ht0,abs_of_pos Real.pi_pos] at h
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (norm_nonneg (Complex.exp (4*v)))
  nlinarith

def gaussian (z : ℂ) : ℂ :=
  ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) (B z)*(s : ℂ)^2/2)

private theorem coefficient_pos (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    0 < (-(deriv (modelDerivative t) (B z))/2).re := by
  exact model_gaussian_coefficient_pos t x ht (by linarith) w (B z) (by linarith) hi hs
    (polynomial_bound t x ht w hp)
    (by simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t x ht hx w hr hi hp hs z hz).1)

theorem gaussian_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    HasDerivAt (gaussian t x ht hx w hr hi hp hs)
      (-((24*(t : ℂ)*(B z)-64*(Real.pi : ℂ)*Complex.exp (4*(B z)))/
        (2*deriv (modelDerivative t) (B z)))*deriv B z*gaussian t x ht hx w hr hi hp hs z) z := by
  let v := B z
  let b := -(deriv (modelDerivative t) v)/2
  have hb : HasDerivAt B (deriv B z) z :=
    (branch_analyticAt t x ht hx w hr hi hp hs z hz).differentiableAt.hasDerivAt
  have hc := (((model_curvature_hasDerivAt t v).comp z hb).neg).div_const (2 : ℂ)
  have hpos := coefficient_pos t x ht hx w hr hi hp hs z hz.le
  have hdne : deriv (modelDerivative t) v ≠ 0 := by
    intro h
    norm_num [v,h] at hpos
  have h := (gaussian_integral_hasDerivAt b hpos).comp z hc
  have hG : (∫ s : ℝ, Complex.exp (-b*(s : ℂ)^2))=gaussian t x ht hx w hr hi hp hs z := by
    apply integral_congr_ae
    filter_upwards [] with s
    congr 1
    dsimp [b,v]
    ring
  convert h using 1
  · funext y
    apply integral_congr_ae
    filter_upwards [] with s
    congr 1
    simp only [Function.comp_apply,Pi.neg_apply]
    ring
  · rw [hG]
    dsimp only [b,v]
    field_simp [show deriv (modelDerivative t) (B z) ≠ 0 from hdne]

theorem gaussian_ne_zero (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    gaussian t x ht hx w hr hi hp hs z ≠ 0 := by
  have h := modelGaussianAmplitude_ne_zero t x ht hx w (B z) hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t x ht hx w hr hi hp hs z hz).1) z
  exact (mul_ne_zero_iff.mp h).2

theorem gaussian_logDerivative (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    deriv (gaussian t x ht hx w hr hi hp hs) z/gaussian t x ht hx w hr hi hp hs z=
      -((24*(t : ℂ)*(B z)-64*(Real.pi : ℂ)*Complex.exp (4*(B z)))/
        (2*deriv (modelDerivative t) (B z)))*deriv B z := by
  rw [(gaussian_hasDerivAt t x ht hx w hr hi hp hs z hz).deriv]
  exact mul_div_cancel_right₀ _ (gaussian_ne_zero t x ht hx w hr hi hp hs z hz.le)

theorem gaussian_logDerivative_norm_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    ‖deriv (gaussian t x ht hx w hr hi hp hs) z/gaussian t x ht hx w hr hi hp hs z‖ ≤ 512/x := by
  have hv : ‖B z-w‖ ≤ 1/x := by
    simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t x ht hx w hr hi hp hs z hz.le).1
  have hC := model_curvature_norm_bound t x ht hx w hr hi hp hs (B z) hv
  have hDn := (gaussian_coefficient_norm_bounds t x ht hx w (B z) hp hs hv).1
  rw [norm_div,norm_neg,Complex.norm_ofNat] at hDn
  have hD : 2*x ≤ ‖deriv (modelDerivative t) (B z)‖ := by linarith
  have hB := branch_deriv_norm_bound t x ht hx w hr hi hp hs z hz
  have hx0 : 0 < x := by linarith
  rw [gaussian_logDerivative t x ht hx w hr hi hp hs z hz,norm_mul,norm_neg,norm_div,norm_mul,Complex.norm_ofNat]
  calc
    _ ≤ (4096*x/(2*(2*x)))*(1/(2*x)) := by
      apply mul_le_mul _ hB (norm_nonneg _) (by positivity)
      exact div_le_div₀ (by positivity) hC (by positivity) (by nlinarith)
    _ = 512/x := by field_simp; ring

theorem gaussian_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    AnalyticAt ℂ (gaussian t x ht hx w hr hi hp hs) z := by
  have hd : DifferentiableOn ℂ (gaussian t x ht hx w hr hi hp hs) (ball (x : ℂ) 1) := by
    intro y hy
    have hy' : ‖y-(x : ℂ)‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hy
    exact (gaussian_hasDerivAt t x ht hx w hr hi hp hs y hy').differentiableAt.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_eq_norm] using hz))

def phaseSlope (z : ℂ) : ℂ := Complex.I*(B z)+
  deriv (gaussian t x ht hx w hr hi hp hs) z/gaussian t x ht hx w hr hi hp hs z

theorem phaseSlope_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    AnalyticAt ℂ (phaseSlope t x ht hx w hr hi hp hs) z := by
  have hb := branch_analyticAt t x ht hx w hr hi hp hs z hz
  have hg := gaussian_analyticAt t x ht hx w hr hi hp hs z hz
  exact (analyticAt_const.mul hb).add (hg.deriv.div hg (gaussian_ne_zero t x ht hx w hr hi hp hs z hz.le))

theorem phaseSlope_error_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    ‖phaseSlope t x ht hx w hr hi hp hs z-Complex.I*(B z)‖ ≤ 512/x := by
  simpa only [phaseSlope,add_sub_cancel_left] using
    gaussian_logDerivative_norm_bound t x ht hx w hr hi hp hs z hz

theorem amplitude_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    HasDerivAt (fun y => modelGaussianAmplitude t y (B y))
      (phaseSlope t x ht hx w hr hi hp hs z*modelGaussianAmplitude t z (B z)) z := by
  have hW := actual_weight_hasDerivAt t x ht hx w hr hi hp hs z hz
  have hG := gaussian_hasDerivAt t x ht hx w hr hi hp hs z hz
  have h := hW.mul hG
  convert h using 1
  · funext y
    rfl
  · unfold phaseSlope
    rw [gaussian_logDerivative t x ht hx w hr hi hp hs z hz]
    change (Complex.I*(B z)+_)*(saddleWeight t z (B z)*gaussian t x ht hx w hr hi hp hs z)= _
    ring

theorem amplitude_logDerivative (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    deriv (fun y => modelGaussianAmplitude t y (B y)) z/modelGaussianAmplitude t z (B z)=
      phaseSlope t x ht hx w hr hi hp hs z := by
  rw [(amplitude_hasDerivAt t x ht hx w hr hi hp hs z hz).deriv]
  apply mul_div_cancel_right₀
  exact modelGaussianAmplitude_ne_zero t x ht hx w (B z) hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t x ht hx w hr hi hp hs z hz.le).1) z

theorem exists_normalized_amplitude_phase : ∃ P : ℂ → ℂ, P (x : ℂ)=0 ∧
    ∀ z ∈ ball (x : ℂ) 1, HasDerivAt P (phaseSlope t x ht hx w hr hi hp hs z) z := by
  have hd : DifferentiableOn ℂ (phaseSlope t x ht hx w hr hi hp hs) (ball (x : ℂ) 1) := by
    intro z hz
    have hz' : ‖z-(x : ℂ)‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hz
    exact (phaseSlope_analyticAt t x ht hx w hr hi hp hs z hz').differentiableAt.differentiableWithinAt
  exact hd.isExactOn_ball.with_val_at (x : ℂ) 0

theorem amplitude_eq_exp_phase (P : ℂ → ℂ) (hP0 : P (x : ℂ)=0)
    (hP : ∀ z ∈ ball (x : ℂ) 1, HasDerivAt P (phaseSlope t x ht hx w hr hi hp hs z) z)
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    modelGaussianAmplitude t z (B z)=modelGaussianAmplitude t (x : ℂ) (B (x : ℂ))*Complex.exp (P z) := by
  let F := fun y => modelGaussianAmplitude t y (B y)*Complex.exp (-P y)
  have hd : ∀ y ∈ ball (x : ℂ) 1, HasDerivAt F 0 y := by
    intro y hy
    have hy' : ‖y-(x : ℂ)‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hy
    have h := (amplitude_hasDerivAt t x ht hx w hr hi hp hs y hy').mul (hP y hy).neg.cexp
    convert h using 1 <;> ring
  have hz' : z ∈ ball (x : ℂ) 1 := by simpa only [mem_ball,dist_eq_norm] using hz
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (x : ℂ) 1).isPreconnected
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) hz' (mem_ball_self (by norm_num : (0 : ℝ)<1))
  change modelGaussianAmplitude t z (B z)*Complex.exp (-P z)=
    modelGaussianAmplitude t (x : ℂ) (B (x : ℂ))*Complex.exp (-P (x : ℂ)) at he
  rw [hP0,neg_zero,Complex.exp_zero,mul_one] at he
  have hm := congrArg (fun c => c*Complex.exp (P z)) he
  rw [mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one] at hm
  exact hm

theorem amplitude_phase_real_derivative (P : ℂ → ℂ)
    (hP : ∀ z ∈ ball (x : ℂ) 1, HasDerivAt P (phaseSlope t x ht hx w hr hi hp hs z) z)
    (y : ℝ) (hy : |y-x| < 1) :
    HasDerivAt (fun a : ℝ => (P (a : ℂ)).im) (phaseSlope t x ht hx w hr hi hp hs (y : ℂ)).im y ∧
      120018 ≤ (phaseSlope t x ht hx w hr hi hp hs (y : ℂ)).im := by
  have hy' : ‖(y : ℂ)-(x : ℂ)‖ < 1 := by
    simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hy
  have hyball : (y : ℂ) ∈ ball (x : ℂ) 1 := by simpa only [mem_ball,dist_eq_norm] using hy'
  have hd := ((hP (y : ℂ) hyball).const_mul (-Complex.I)).real_of_complex
  refine ⟨?_,?_⟩
  · simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
      neg_zero,zero_mul,neg_neg,one_mul,neg_one_mul,sub_neg_eq_add,zero_add] using hd
  · obtain ⟨Q,hQ0,hQ⟩ := exists_normalized_weight_phase t x ht hx w hr hi hp hs
    have hRe := (weight_phase_real_derivative t x ht hx w hr hi hp hs Q hQ y hy).2
    have he := gaussian_logDerivative_norm_bound t x ht hx w hr hi hp hs (y : ℂ) hy'
    have him := (Complex.abs_im_le_norm (deriv (gaussian t x ht hx w hr hi hp hs) (y : ℂ)/
      gaussian t x ht hx w hr hi hp hs (y : ℂ))).trans he
    have hsmall : 512/x ≤ 1 := (div_le_iff₀ (by linarith : 0 < x)).mpr (by linarith)
    have hid : (phaseSlope t x ht hx w hr hi hp hs (y : ℂ)).im=(B (y : ℂ)).re+
        (deriv (gaussian t x ht hx w hr hi hp hs) (y : ℂ)/gaussian t x ht hx w hr hi hp hs (y : ℂ)).im := by
      simp [phaseSlope,Complex.mul_im]
    rw [hid]
    linarith [(abs_le.mp him).1]

theorem amplitude_phase_real_growth (P : ℂ → ℂ)
    (hP : ∀ z ∈ ball (x : ℂ) 1, HasDerivAt P (phaseSlope t x ht hx w hr hi hp hs z) z)
    (a b : ℝ) (ha : a ∈ Ioo (x-1) (x+1)) (hb : b ∈ Ioo (x-1) (x+1)) (hab : a ≤ b) :
    120018*(b-a) ≤ (P (b : ℂ)).im-(P (a : ℂ)).im := by
  have hd (y : ℝ) (hy : y ∈ Ioo (x-1) (x+1)) :=
    amplitude_phase_real_derivative t x ht hx w hr hi hp hs P hP y (by
      rw [abs_lt]
      constructor <;> linarith [hy.1,hy.2])
  exact (convex_Ioo (x-1) (x+1)).mul_sub_le_image_sub_of_le_deriv
    (fun y hy => (hd y hy).1.continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).1.differentiableAt.differentiableWithinAt)
    (fun y hy => by rw [(hd y (interior_subset hy)).1.deriv]; exact (hd y (interior_subset hy)).2)
    a ha b hb hab

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarGaussianPhase
