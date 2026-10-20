import Foundation.RiemannSixthTransitionAnalyticBranch
import Foundation.RiemannSixthFarGaussianPhase
/-! Analytic Gaussian amplitudes on actual transition saddle branches.
The coefficient lies in the positive real half-plane; its branch is fixed
by the genuine complex Gaussian integral. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionGaussianPhase
open RiemannSixthTransitionAnalyticBranch RiemannSixthTransitionCorrection
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannEvenComplexWeight
open RiemannSixthFarPairing (modelGaussianAmplitude)

open RiemannQuarticFarGaussianPhase (gaussian_integral_hasDerivAt)
open RiemannSixthFarGaussianPhase (model_curvature_hasDerivAt)

variable (t K x r : ℝ) (w : ℂ)
  (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re)
  (hmargin : t*w.re^5+8 ≤ 4*Real.pi*(Complex.exp (4*w)).re) (hi : |w.im| ≤ 1/2)
  (hnorm : ‖w‖ ≤ 2*w.re) (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
  (hE : ‖Complex.exp (4*w)‖ ≤ K)
  (hsmall : (30005*Real.exp (-w.re))*K ≤ t*w.re^5/4)
  (hrpos : 0 < r) (hradius : r ≤ t*w.re^5/K)
include ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius
local notation "B" => RiemannSixthTransitionAnalyticBranch.branch t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius

theorem model_curvature_norm_bound (v : ℂ) (hv : ‖v-w‖ ≤ 1/K) :
    ‖120*(t : ℂ)*v^3-64*(Real.pi : ℂ)*Complex.exp (4*v)‖ ≤ 3240*(t*w.re^5)+512*K := by
  have hK0 : 0 < K := by linarith
  have hv1 : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ hK0).mpr (by linarith))
  have hv4 : 4*‖v-w‖ ≤ 1 := by nlinarith [(le_div_iff₀ hK0).mp hv]
  have hvn : ‖v‖ ≤ 3*w.re := by
    have h := norm_add_le (v-w) w
    rw [sub_add_cancel] at h
    linarith
  have hed := RiemannQuarticFarCorrection.exp4_difference_bound w v hv4
  have hmul := mul_le_mul hE hv (norm_nonneg _) hK0.le
  have hcan : K*(1/K)=1 := by field_simp
  rw [hcan] at hmul
  have hetri := norm_add_le (Complex.exp (4*v)-Complex.exp (4*w)) (Complex.exp (4*w))
  rw [sub_add_cancel] at hetri
  have he : ‖Complex.exp (4*v)‖ ≤ 2*K := by nlinarith
  have hp : w.re^3 ≤ w.re^5 := pow_le_pow_right₀ (by linarith : 1 ≤ w.re) (by norm_num)
  have hvt := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hvn 3)
    (show 0 ≤ 120*t by positivity)
  have hpt := mul_le_mul_of_nonneg_left hp (show 0 ≤ 3240*t by positivity)
  have h := norm_sub_le (120*(t : ℂ)*v^3) (64*(Real.pi : ℂ)*Complex.exp (4*v))
  simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ t),abs_of_pos Real.pi_pos] at h
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (norm_nonneg (Complex.exp (4*v)))
  nlinarith

theorem model_real_curvature (v : ℂ) (hv : ‖v-w‖ ≤ 1/K) :
    (deriv (modelDerivative 3 t) v).re ≤ -3*t*w.re^5 := by
  have hb := scaled_model_deriv_bound t K w v ht hK (by linarith) hnorm hE hv
  let A : ℂ := -(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)
  have he : A.re= -16*Real.pi*(Complex.exp (4*w)).re := by simp [A,Complex.mul_re]
  have hre := Complex.re_le_norm (deriv (modelDerivative 3 t) v-A)
  rw [Complex.sub_re,he] at hre
  nlinarith

theorem gaussian_coefficient_norm_bounds (v : ℂ) (hv : ‖v-w‖ ≤ 1/K) :
    t*w.re^5 ≤ ‖-(deriv (modelDerivative 3 t) v)/2‖ ∧
      ‖-(deriv (modelDerivative 3 t) v)/2‖ ≤ 64*K := by
  have hreal := model_real_curvature t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius v hv
  have hQ0 : 0 ≤ t*w.re^5 := by positivity
  have hR0 : 0 ≤ (Complex.exp (4*w)).re := by nlinarith [Real.pi_pos]
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hR0
  have hnormexp := (Complex.re_le_norm (Complex.exp (4*w))).trans hE
  have hQ : t*w.re^5 ≤ 16*K := by nlinarith
  have hb := scaled_model_deriv_bound t K w v ht hK (by linarith) hnorm hE hv
  have hnA : ‖-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)‖ ≤ 64*K := by
    simp only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    have hmul := mul_le_mul Real.pi_lt_four.le hE (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith
  have htri := norm_add_le (deriv (modelDerivative 3 t) v-(-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w)))
    (-(16 : ℂ)*(Real.pi : ℂ)*Complex.exp (4*w))
  rw [sub_add_cancel] at htri
  have hre := Complex.re_le_norm (-(deriv (modelDerivative 3 t) v)/2)
  simp only [Complex.div_ofNat_re,Complex.neg_re] at hre
  rw [norm_div,norm_neg,Complex.norm_ofNat] at hre
  rw [norm_div,norm_neg,Complex.norm_ofNat]
  constructor <;> nlinarith

def gaussian (z : ℂ) : ℂ :=
  ∫ s : ℝ, Complex.exp (deriv (modelDerivative 3 t) (B z)*(s : ℂ)^2/2)

private theorem coefficient_pos (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    0 < (-(deriv (modelDerivative 3 t) (B z))/2).re := by
  have hv : ‖B z-w‖ ≤ 1/K := by
    simpa only [mem_closedBall,dist_eq_norm] using
      (branch_spec t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).1
  have hc := model_real_curvature t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius (B z) hv
  simp only [Complex.div_ofNat_re,Complex.neg_re]
  have hQ : 0 < t*w.re^5 := by positivity
  nlinarith

theorem gaussian_formula (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z=
      ((Real.pi : ℂ)/(-(deriv (modelDerivative 3 t) (B z))/2))^(1/2 : ℂ) := by
  have h := integral_gaussian_complex
    (coefficient_pos t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz)
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with s
  congr 1
  ring

theorem gaussian_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    HasDerivAt (gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius)
      (-((120*(t : ℂ)*(B z)^3-64*(Real.pi : ℂ)*Complex.exp (4*(B z)))/
        (2*deriv (modelDerivative 3 t) (B z)))*deriv B z*gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z) z := by
  let v := B z
  let b := -(deriv (modelDerivative 3 t) v)/2
  have hb : HasDerivAt B (deriv B z) z :=
    (branch_analyticAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).differentiableAt.hasDerivAt
  have hc := (((model_curvature_hasDerivAt t v).comp z hb).neg).div_const (2 : ℂ)
  have hpos := coefficient_pos t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz.le
  have hdne : deriv (modelDerivative 3 t) v ≠ 0 := by
    intro h
    norm_num [v,h] at hpos
  have h := (gaussian_integral_hasDerivAt b hpos).comp z hc
  have hG : (∫ s : ℝ, Complex.exp (-b*(s : ℂ)^2))=gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z := by
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
    field_simp [show deriv (modelDerivative 3 t) (B z) ≠ 0 from hdne]

theorem gaussian_ne_zero (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z ≠ 0 := by
  let b := -(deriv (modelDerivative 3 t) (B z))/2
  have hpos := coefficient_pos t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz
  have hsq := integral_gaussian_sq_complex hpos
  have he : (∫ s : ℝ, Complex.exp (-b*(s : ℂ)^2))=
      gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z := by
    apply integral_congr_ae
    filter_upwards [] with s
    congr 1
    dsimp [b]
    ring
  rw [he] at hsq
  intro hzero
  rw [hzero,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hsq
  exact (div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (show b ≠ 0 by intro h; simp [b,h] at hpos)) hsq.symm

theorem gaussian_normalization_bounds (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    1 ≤ 8*Real.sqrt K*‖gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z‖ ∧
      ‖gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z‖^2*(t*w.re^5) ≤ Real.pi := by
  let b := -(deriv (modelDerivative 3 t) (B z))/2
  let g := ‖gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z‖
  have hb := coefficient_pos t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz
  have hbne : b ≠ 0 := by intro h; simp [b,h] at hb
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hbne
  have hv : ‖B z-w‖ ≤ 1/K := by
    simpa only [mem_closedBall,dist_eq_norm] using
      (branch_spec t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).1
  have hn := gaussian_coefficient_norm_bounds t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius (B z) hv
  have hg := integral_gaussian_sq_complex hb
  have he : (∫ s : ℝ, Complex.exp (-b*(s : ℂ)^2))=
      gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z := by
    apply integral_congr_ae
    filter_upwards [] with s
    congr 1
    dsimp [b]
    ring
  rw [he] at hg
  have hnorm := congrArg norm hg
  simp only [norm_pow,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] at hnorm
  have hid : g^2*‖b‖=Real.pi := (eq_div_iff hbn.ne').mp (by
    simpa only [b,norm_div] using hnorm)
  have hm := mul_le_mul_of_nonneg_left hn.2 (sq_nonneg g)
  have hroot := Real.sq_sqrt (show 0 ≤ K by linarith)
  have hprod : 0 ≤ 8*Real.sqrt K*g := by positivity
  have hsquare : 1 ≤ (8*Real.sqrt K*g)^2 := by
    calc
      _ ≤ Real.pi := by linarith [Real.pi_gt_three]
      _ ≤ g^2*(64*K) := by nlinarith
      _ = _ := by rw [mul_pow,mul_pow,hroot]; ring
  constructor
  · change 1 ≤ 8*Real.sqrt K*g
    nlinarith
  · exact (mul_le_mul_of_nonneg_left hn.1 (sq_nonneg g)).trans hid.le

theorem gaussian_logDerivative (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    deriv (gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius) z/gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z=
      -((120*(t : ℂ)*(B z)^3-64*(Real.pi : ℂ)*Complex.exp (4*(B z)))/
        (2*deriv (modelDerivative 3 t) (B z)))*deriv B z := by
  rw [(gaussian_hasDerivAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).deriv]
  exact mul_div_cancel_right₀ _ (gaussian_ne_zero t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz.le)

theorem gaussian_logDerivative_norm_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖deriv (gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius) z/gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z‖ ≤ (3240*(t*w.re^5)+512*K)/(8*(t*w.re^5)^2) := by
  have hv : ‖B z-w‖ ≤ 1/K := by
    simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz.le).1
  have hC := model_curvature_norm_bound t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius (B z) hv
  have hDn := (gaussian_coefficient_norm_bounds t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius (B z) hv).1
  rw [norm_div,norm_neg,Complex.norm_ofNat] at hDn
  have hD : 2*(t*w.re^5) ≤ ‖deriv (modelDerivative 3 t) (B z)‖ := by linarith
  have hB := branch_deriv_norm_bound t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz
  have hQ : 0 < t*w.re^5 := by positivity
  rw [gaussian_logDerivative t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz,norm_mul,norm_neg,norm_div,norm_mul,Complex.norm_ofNat]
  calc
    _ ≤ ((3240*(t*w.re^5)+512*K)/(2*(2*(t*w.re^5))))*(1/(2*(t*w.re^5))) := by
      apply mul_le_mul _ hB (norm_nonneg _) (by positivity)
      exact div_le_div₀ (by positivity) hC (by positivity) (by nlinarith)
    _ = _ := by field_simp; ring

theorem gaussian_logDerivative_scaled_bound (C : ℝ) (hC : 0 ≤ C)
    (hscale : K ≤ C*(t*w.re^5)) (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖deriv (gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius) z/gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z‖ ≤ (405+64*C)/(t*w.re^5) := by
  apply (gaussian_logDerivative_norm_bound t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).trans
  have hQ : 0 < t*w.re^5 := by positivity
  apply (div_le_iff₀ (by positivity : 0 < 8*(t*w.re^5)^2)).mpr
  field_simp
  nlinarith

theorem gaussian_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    AnalyticAt ℂ (gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius) z := by
  have hd : DifferentiableOn ℂ (gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius) (ball (x : ℂ) r) := by
    intro y hy
    have hy' : ‖y-(x : ℂ)‖ < r := by simpa only [mem_ball,dist_eq_norm] using hy
    exact (gaussian_hasDerivAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius y hy').differentiableAt.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_eq_norm] using hz))

def phaseSlope (z : ℂ) : ℂ := Complex.I*(B z)+
  deriv (gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius) z/gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z

theorem phaseSlope_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    AnalyticAt ℂ (phaseSlope t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius) z := by
  have hb := branch_analyticAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz
  have hg := gaussian_analyticAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz
  exact (analyticAt_const.mul hb).add (hg.deriv.div hg (gaussian_ne_zero t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz.le))

theorem phaseSlope_model_bound (C : ℝ) (hC : 0 ≤ C) (hscale : K ≤ C*(t*w.re^5))
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖phaseSlope t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z-Complex.I*w‖ ≤
      1/K+(405+64*C)/(t*w.re^5) := by
  have hg := gaussian_logDerivative_scaled_bound t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius C hC hscale z hz
  have hb : ‖B z-w‖ ≤ 1/K := by
    simpa only [mem_closedBall,dist_eq_norm] using
      (branch_spec t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz.le).1
  have he : phaseSlope t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z-Complex.I*w=
      Complex.I*(B z-w)+deriv (gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius) z/
        gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z := by unfold phaseSlope; ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,Complex.norm_I,one_mul]
  exact add_le_add hb hg

theorem phaseSlope_error_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖phaseSlope t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z-Complex.I*(B z)‖ ≤ (3240*(t*w.re^5)+512*K)/(8*(t*w.re^5)^2) := by
  simpa only [phaseSlope,add_sub_cancel_left] using
    gaussian_logDerivative_norm_bound t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz

theorem amplitude_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    HasDerivAt (fun y => modelGaussianAmplitude t y (B y))
      (phaseSlope t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z*modelGaussianAmplitude t z (B z)) z := by
  have hW := actual_weight_hasDerivAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz
  have hG := gaussian_hasDerivAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz
  have h := hW.mul hG
  convert h using 1
  · funext y
    rfl
  · unfold phaseSlope
    rw [gaussian_logDerivative t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz]
    change (Complex.I*(B z)+_)*(weight 3 t z (B z)*gaussian t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z)= _
    ring

theorem amplitude_logDerivative (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    deriv (fun y => modelGaussianAmplitude t y (B y)) z/modelGaussianAmplitude t z (B z)=
      phaseSlope t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z := by
  rw [(amplitude_hasDerivAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz).deriv]
  apply mul_div_cancel_right₀
  exact mul_ne_zero (actual_weight_ne_zero t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz.le) (gaussian_ne_zero t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz.le)

theorem exists_normalized_amplitude_phase : ∃ P : ℂ → ℂ, P (x : ℂ)=0 ∧
    ∀ z ∈ ball (x : ℂ) r, HasDerivAt P (phaseSlope t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z) z := by
  have hd : DifferentiableOn ℂ (phaseSlope t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius) (ball (x : ℂ) r) := by
    intro z hz
    have hz' : ‖z-(x : ℂ)‖ < r := by simpa only [mem_ball,dist_eq_norm] using hz
    exact (phaseSlope_analyticAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius z hz').differentiableAt.differentiableWithinAt
  exact hd.isExactOn_ball.with_val_at (x : ℂ) 0

theorem amplitude_eq_exp_phase (P : ℂ → ℂ) (hP0 : P (x : ℂ)=0)
    (hP : ∀ z ∈ ball (x : ℂ) r, HasDerivAt P (phaseSlope t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hradius z) z)
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    modelGaussianAmplitude t z (B z)=modelGaussianAmplitude t (x : ℂ) (B (x : ℂ))*Complex.exp (P z) := by
  let F := fun y => modelGaussianAmplitude t y (B y)*Complex.exp (-P y)
  have hd : ∀ y ∈ ball (x : ℂ) r, HasDerivAt F 0 y := by
    intro y hy
    have hy' : ‖y-(x : ℂ)‖ < r := by simpa only [mem_ball,dist_eq_norm] using hy
    have h := (amplitude_hasDerivAt t K x r w ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius y hy').mul (hP y hy).neg.cexp
    convert h using 1 <;> ring
  have hz' : z ∈ ball (x : ℂ) r := by simpa only [mem_ball,dist_eq_norm] using hz
  have he := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (x : ℂ) r).isPreconnected
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hd y hy).deriv) hz' (mem_ball_self hrpos)
  change modelGaussianAmplitude t z (B z)*Complex.exp (-P z)=
    modelGaussianAmplitude t (x : ℂ) (B (x : ℂ))*Complex.exp (-P (x : ℂ)) at he
  rw [hP0,neg_zero,Complex.exp_zero,mul_one] at he
  have hm := congrArg (fun c => c*Complex.exp (P z)) he
  rw [mul_assoc,← Complex.exp_add,neg_add_cancel,Complex.exp_zero,mul_one] at hm
  exact hm


omit ht hK hr hmargin hi hnorm hs hE hsmall hrpos hradius in
theorem exists_actual_transition_amplitude (t u M x : ℝ)
    (ht : 1 ≤ t) (hM : 0 ≤ M) (hu : 65536*(M+7) ≤ u)
    (hstationary : RiemannEvenRealSaddle.phaseSlope 3 t u=0)
    (hx : |x| ≤ M*RiemannQuarticTransitionSaddle.realScale u) :
    ∃ (w : ℂ) (b P : ℂ → ℂ), ‖w-(u : ℂ)‖ ≤ M+7 ∧ P (x : ℂ)=0 ∧
      (∀ z : ℂ, ‖z-(x : ℂ)‖ ≤ 1/(1024*(M+8)) →
        complexSlope 3 t (b z)= -(Complex.I*z) ∧
        modelGaussianAmplitude t z (b z) ≠ 0) ∧
      (∀ z : ℂ, ‖z-(x : ℂ)‖ < 1/(1024*(M+8)) →
        AnalyticAt ℂ b z ∧ HasDerivAt P
          (deriv (fun y => modelGaussianAmplitude t y (b y)) z/modelGaussianAmplitude t z (b z)) z ∧
        ‖deriv P z-Complex.I*w‖ ≤
          1/((M+8)*RiemannQuarticTransitionSaddle.realScale u)+
            (405+65536*(M+8))/(t*w.re^5) ∧
        modelGaussianAmplitude t z (b z)=
          modelGaussianAmplitude t (x : ℂ) (b (x : ℂ))*Complex.exp (P z)) := by
  let K := (M+8)*RiemannQuarticTransitionSaddle.realScale u
  let C := 1024*(M+8)
  let r := 1/C
  have hC : 0 < C := by dsimp [C]; positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hxnorm : ‖(x : ℂ)‖ ≤ M*RiemannQuarticTransitionSaddle.realScale u := by simpa using hx
  obtain ⟨w,hw,_⟩ := RiemannSixthTransitionSaddle.existsUnique_transition_model_saddle
    t u M (x : ℂ) ht hM hu hstationary (by simp) hxnorm
  have hg := RiemannSixthTransitionSaddle.transition_model_geometry t u M (x : ℂ) w
    ht hM hu hstationary (by simp) hxnorm hw.1 hw.2
  have hd := transition_scale_data t u M (x : ℂ) w ht hM hu hstationary (by simp) hxnorm hw.1 hw.2
  have hK : 8 ≤ K := hd.1
  have hnorm := hd.2.2.2.1
  have hE := hd.2.2.2.2.1
  have hsmall := hd.2.2.2.2.2.1
  have hmargin := hd.2.2.2.2.2.2
  have hcoord := (Complex.abs_re_le_norm (w-(u : ℂ))).trans hg.1
  simp only [Complex.sub_re,Complex.ofReal_re] at hcoord
  have hr : 120020 ≤ w.re := by linarith [(abs_le.mp hcoord).1]
  have hscale : K ≤ C*(t*w.re^5) :=
    RiemannSixthTransitionAnalyticBranch.moving_scale_ratio_bound t u M w ht hM hu hstationary hg.1
  have hradius : r ≤ t*w.re^5/K := by
    apply (le_div_iff₀ (by linarith : 0 < K)).mpr
    dsimp [r]
    have hh : K/C ≤ t*w.re^5 := (div_le_iff₀ hC).mpr (by nlinarith)
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hh
  let b := branch t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hradius
  obtain ⟨P,hP0,hP⟩ := exists_normalized_amplitude_phase t K x r w ht hK hr hmargin hd.2.2.1
    hnorm hw.2 hE hsmall hrpos hradius
  refine ⟨w,b,P,hg.1,hP0,?_,?_⟩
  · intro z hz
    have hspec := branch_spec t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hz
    exact ⟨hspec.2,mul_ne_zero
      (actual_weight_ne_zero t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hz)
      (gaussian_ne_zero t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hz)⟩
  · intro z hz
    have hzball : z ∈ ball (x : ℂ) r := by simpa only [mem_ball,dist_eq_norm] using hz
    have hp := hP z hzball
    have hbound := phaseSlope_model_bound t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius
      C hC.le hscale z hz
    have hlog := amplitude_logDerivative t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hz
    refine ⟨branch_analyticAt t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius z hz,
      ?_,?_,amplitude_eq_exp_phase t K x r w ht hK hr hmargin hd.2.2.1 hnorm hw.2 hE hsmall hrpos hradius P hP0 hP z hz⟩
    · rw [hlog]
      exact hp
    · rw [hp.deriv]
      convert hbound using 1 <;> dsimp [K,C] <;> ring

end OperatorDerivativeRewrite.Foundation.RiemannSixthTransitionGaussianPhase
