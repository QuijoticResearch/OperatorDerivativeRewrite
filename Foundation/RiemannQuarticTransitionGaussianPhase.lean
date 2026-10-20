import Foundation.RiemannQuarticTransitionAnalyticBranch
import Foundation.RiemannQuarticFarGaussianPhase
/-! Analytic Gaussian amplitudes on actual transition saddle branches.
The coefficient lies in the positive real half-plane; its branch is fixed
by the genuine complex Gaussian integral. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionGaussianPhase
open RiemannQuarticTransitionAnalyticBranch RiemannQuarticTransitionGaussian
open RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannQuarticFarModelSaddle RiemannQuarticFarPairing
open RiemannQuarticFarGaussianPhase (gaussian_integral_hasDerivAt model_curvature_hasDerivAt)

variable (t K x r : ℝ) (w : ℂ)
  (ht : 1 ≤ t) (hK : 8 ≤ K) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hnorm : ‖w‖ ≤ 2*w.re) (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
  (hE : ‖Complex.exp (4*w)‖ ≤ K)
  (hsmall : (30005*Real.exp (-w.re))*K ≤ t*w.re^3/4)
  (hrpos : 0 < r) (hradius : r ≤ t*w.re^3/K)
include ht hK hr hi hnorm hs hE hsmall hrpos hradius
local notation "B" => RiemannQuarticTransitionAnalyticBranch.branch t K x r w ht hK hr hi hnorm hs hE hsmall hradius

theorem model_curvature_norm_bound (v : ℂ) (hv : ‖v-w‖ ≤ 1/K) :
    ‖24*(t : ℂ)*v-64*(Real.pi : ℂ)*Complex.exp (4*v)‖ ≤ 72*(t*w.re^3)+512*K := by
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
  have hp : w.re ≤ w.re^3 := by
    have hh := one_le_pow₀ (by linarith : 1 ≤ w.re) (n := 2)
    nlinarith [mul_le_mul_of_nonneg_right hh (by linarith : 0 ≤ w.re)]
  have hvt := mul_le_mul_of_nonneg_left hvn (by linarith : 0 ≤ 24*t)
  have hpt := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ 72*t)
  have h := norm_sub_le (24*(t : ℂ)*v) (64*(Real.pi : ℂ)*Complex.exp (4*v))
  simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ t),abs_of_pos Real.pi_pos] at h
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (norm_nonneg (Complex.exp (4*v)))
  nlinarith

def gaussian (z : ℂ) : ℂ :=
  ∫ s : ℝ, Complex.exp (deriv (modelDerivative t) (B z)*(s : ℂ)^2/2)

private theorem coefficient_pos (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    0 < (-(deriv (modelDerivative t) (B z))/2).re := by
  exact RiemannQuarticTransitionGaussian.model_gaussian_coefficient_pos t K (x : ℂ) w (B z)
    ht hK (by linarith) hi hnorm (by simp) hs hE
    (by simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).1)

theorem gaussian_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    HasDerivAt (gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius)
      (-((24*(t : ℂ)*(B z)-64*(Real.pi : ℂ)*Complex.exp (4*(B z)))/
        (2*deriv (modelDerivative t) (B z)))*deriv B z*gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) z := by
  let v := B z
  let b := -(deriv (modelDerivative t) v)/2
  have hb : HasDerivAt B (deriv B z) z :=
    (branch_analyticAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).differentiableAt.hasDerivAt
  have hc := (((model_curvature_hasDerivAt t v).comp z hb).neg).div_const (2 : ℂ)
  have hpos := coefficient_pos t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le
  have hdne : deriv (modelDerivative t) v ≠ 0 := by
    intro h
    norm_num [v,h] at hpos
  have h := (gaussian_integral_hasDerivAt b hpos).comp z hc
  have hG : (∫ s : ℝ, Complex.exp (-b*(s : ℂ)^2))=gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius z := by
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

theorem gaussian_ne_zero (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius z ≠ 0 := by
  have h := gaussian_normalization_lower t K (x : ℂ) w (B z) ht hK (by linarith) hi hnorm
    (by simp) hs hE (by simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).1)
  change 1 ≤ 8*Real.sqrt K*‖gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius z‖ at h
  intro hz0
  norm_num [hz0] at h

theorem gaussian_logDerivative (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    deriv (gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z/gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius z=
      -((24*(t : ℂ)*(B z)-64*(Real.pi : ℂ)*Complex.exp (4*(B z)))/
        (2*deriv (modelDerivative t) (B z)))*deriv B z := by
  rw [(gaussian_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).deriv]
  exact mul_div_cancel_right₀ _ (gaussian_ne_zero t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le)

theorem gaussian_logDerivative_norm_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖deriv (gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z/gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius z‖ ≤ (72*(t*w.re^3)+512*K)/(8*(t*w.re^3)^2) := by
  have hv : ‖B z-w‖ ≤ 1/K := by
    simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le).1
  have hC := model_curvature_norm_bound t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius (B z) hv
  have hDn := (RiemannQuarticTransitionGaussian.gaussian_coefficient_norm_bounds t K (x : ℂ) w (B z)
    ht hK (by linarith) hi hnorm (by simp) hs hE hv).1
  rw [norm_div,norm_neg,Complex.norm_ofNat] at hDn
  have hD : 2*(t*w.re^3) ≤ ‖deriv (modelDerivative t) (B z)‖ := by linarith
  have hB := branch_deriv_norm_bound t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz
  have hQ : 0 < t*w.re^3 := by positivity
  rw [gaussian_logDerivative t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz,norm_mul,norm_neg,norm_div,norm_mul,Complex.norm_ofNat]
  calc
    _ ≤ ((72*(t*w.re^3)+512*K)/(2*(2*(t*w.re^3))))*(1/(2*(t*w.re^3))) := by
      apply mul_le_mul _ hB (norm_nonneg _) (by positivity)
      exact div_le_div₀ (by positivity) hC (by positivity) (by nlinarith)
    _ = _ := by field_simp; ring

theorem gaussian_logDerivative_scaled_bound (C : ℝ) (hC : 0 ≤ C)
    (hscale : K ≤ C*(t*w.re^3)) (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖deriv (gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z/gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius z‖ ≤ (9+64*C)/(t*w.re^3) := by
  apply (gaussian_logDerivative_norm_bound t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).trans
  have hQ : 0 < t*w.re^3 := by positivity
  apply (div_le_iff₀ (by positivity : 0 < 8*(t*w.re^3)^2)).mpr
  field_simp
  nlinarith

theorem gaussian_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    AnalyticAt ℂ (gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z := by
  have hd : DifferentiableOn ℂ (gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius) (ball (x : ℂ) r) := by
    intro y hy
    have hy' : ‖y-(x : ℂ)‖ < r := by simpa only [mem_ball,dist_eq_norm] using hy
    exact (gaussian_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius y hy').differentiableAt.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_eq_norm] using hz))

def phaseSlope (z : ℂ) : ℂ := Complex.I*(B z)+
  deriv (gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z/gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius z

theorem phaseSlope_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    AnalyticAt ℂ (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z := by
  have hb := branch_analyticAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz
  have hg := gaussian_analyticAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz
  exact (analyticAt_const.mul hb).add (hg.deriv.div hg (gaussian_ne_zero t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le))

theorem phaseSlope_model_bound (C : ℝ) (hC : 0 ≤ C) (hscale : K ≤ C*(t*w.re^3))
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z-Complex.I*w‖ ≤
      1/K+(9+64*C)/(t*w.re^3) := by
  have hg := gaussian_logDerivative_scaled_bound t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius C hC hscale z hz
  have hb : ‖B z-w‖ ≤ 1/K := by
    simpa only [mem_closedBall,dist_eq_norm] using
      (branch_spec t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le).1
  have he : phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z-Complex.I*w=
      Complex.I*(B z-w)+deriv (gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius) z/
        gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius z := by unfold phaseSlope; ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,Complex.norm_I,one_mul]
  exact add_le_add hb hg

theorem phaseSlope_error_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    ‖phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z-Complex.I*(B z)‖ ≤ (72*(t*w.re^3)+512*K)/(8*(t*w.re^3)^2) := by
  simpa only [phaseSlope,add_sub_cancel_left] using
    gaussian_logDerivative_norm_bound t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz

theorem amplitude_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    HasDerivAt (fun y => modelGaussianAmplitude t y (B y))
      (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z*modelGaussianAmplitude t z (B z)) z := by
  have hW := actual_weight_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz
  have hG := gaussian_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz
  have h := hW.mul hG
  convert h using 1
  · funext y
    rfl
  · unfold phaseSlope
    rw [gaussian_logDerivative t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz]
    change (Complex.I*(B z)+_)*(saddleWeight t z (B z)*gaussian t K x r w ht hK hr hi hnorm hs hE hsmall hradius z)= _
    ring

theorem amplitude_logDerivative (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    deriv (fun y => modelGaussianAmplitude t y (B y)) z/modelGaussianAmplitude t z (B z)=
      phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z := by
  rw [(amplitude_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz).deriv]
  apply mul_div_cancel_right₀
  exact mul_ne_zero (actual_weight_ne_zero t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le) (gaussian_ne_zero t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz.le)

theorem exists_normalized_amplitude_phase : ∃ P : ℂ → ℂ, P (x : ℂ)=0 ∧
    ∀ z ∈ ball (x : ℂ) r, HasDerivAt P (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) z := by
  have hd : DifferentiableOn ℂ (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius) (ball (x : ℂ) r) := by
    intro z hz
    have hz' : ‖z-(x : ℂ)‖ < r := by simpa only [mem_ball,dist_eq_norm] using hz
    exact (phaseSlope_analyticAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius z hz').differentiableAt.differentiableWithinAt
  exact hd.isExactOn_ball.with_val_at (x : ℂ) 0

theorem amplitude_eq_exp_phase (P : ℂ → ℂ) (hP0 : P (x : ℂ)=0)
    (hP : ∀ z ∈ ball (x : ℂ) r, HasDerivAt P (phaseSlope t K x r w ht hK hr hi hnorm hs hE hsmall hradius z) z)
    (z : ℂ) (hz : ‖z-(x : ℂ)‖ < r) :
    modelGaussianAmplitude t z (B z)=modelGaussianAmplitude t (x : ℂ) (B (x : ℂ))*Complex.exp (P z) := by
  let F := fun y => modelGaussianAmplitude t y (B y)*Complex.exp (-P y)
  have hd : ∀ y ∈ ball (x : ℂ) r, HasDerivAt F 0 y := by
    intro y hy
    have hy' : ‖y-(x : ℂ)‖ < r := by simpa only [mem_ball,dist_eq_norm] using hy
    have h := (amplitude_hasDerivAt t K x r w ht hK hr hi hnorm hs hE hsmall hrpos hradius y hy').mul (hP y hy).neg.cexp
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


end OperatorDerivativeRewrite.Foundation.RiemannQuarticTransitionGaussianPhase
