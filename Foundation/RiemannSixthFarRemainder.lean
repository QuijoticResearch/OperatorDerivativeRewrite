import Foundation.RiemannSixthFarCorrection
import Foundation.RiemannQuarticFarRemainder
/-! Sharp actual sixth-order arithmetic slope errors on corrected balls
and horizontal intervals. The exp(-4 Re(w)) scale is retained explicitly. -/
noncomputable section
open Set Metric Complex
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarRemainder
open RiemannSixthFarCorrection RiemannEvenModelPhase RiemannEvenSaddleBranch
open RiemannThetaComplexKernel
open RiemannQuarticFarRemainder (horizontal_exp_real_lower)

theorem neighbor_error_sharp_bound (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 2/x) :
    ‖complexSlope 3 t v-modelDerivative 3 t v‖ ≤ 30005*Real.exp (-4*w.re+4) := by
  have hdom := neighbor_domain t x ht hx w v hr hi hs hp hv
  have hd : ‖v-w‖ ≤ 1 := hv.trans ((div_le_iff₀ (by linarith : 0 < x)).mpr (by linarith))
  have hcoord := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hcoord
  have hlo := (abs_le.mp hcoord).1
  have hhi := (abs_le.mp hcoord).2
  have heq : complexSlope 3 t v-modelDerivative 3 t v=
      kernelDerivative v/kernelComplex v-(9-4*(Real.pi : ℂ)*Complex.exp (4*v)) := by
    unfold complexSlope modelDerivative
    rw [(kernelComplex_hasDerivAt v (by linarith [hdom.2.1])).deriv]
    ring
  rw [heq]
  apply (RiemannQuarticSaddleNeighborhood.logDerivative_coarse_bound v hdom.1 hdom.2.1).trans
  have hcub : 1024*w.re ≤ w.re^3 := by
    have hsq : 1024 ≤ w.re^2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)
    nlinarith
  have h35 : w.re^3 ≤ w.re^5 := pow_le_pow_right₀ (by linarith : 1 ≤ w.re) (by norm_num)
  have htcub : w.re^3 ≤ t*w.re^5 := h35.trans (by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5])
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith [hdom.2.1] : 0 ≤ (Complex.exp (4*v)).re)
  have h1 : Real.exp (-4*v.re) ≤ Real.exp (-4*w.re+4) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (4*v.re)*Real.exp (-3*Real.pi*(Complex.exp (4*v)).re) ≤ Real.exp (-4*w.re+4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hdom.2.2]
  have hh1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ)≤5)
  have hh2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ)≤30000)
  nlinarith




theorem horizontal_neighbor_domain (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (s : ℝ) (hsr : |s| ≤ 1/16) :
    0 ≤ (v+(s : ℂ)).re ∧ 1 ≤ (Complex.exp (4*(v+(s : ℂ)))).re ∧
      t*w.re^5/64 ≤ (Complex.exp (4*(v+(s : ℂ)))).re ∧
      |(v+(s : ℂ)).re-w.re| ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hd2 : ‖v-w‖ ≤ 2/x := hv.trans (by apply (div_le_div_iff_of_pos_right hx0).mpr; norm_num)
  have hdom := neighbor_domain t x ht hx w v hr hi hs hp hd2
  have hE := horizontal_exp_real_lower v (by linarith [hdom.2.1]) s hsr
  have hd : ‖v-w‖ ≤ 1/8 := hv.trans ((div_le_iff₀ hx0).mpr (by linarith))
  have hre := (Complex.abs_re_le_norm (v-w)).trans hd
  simp only [Complex.sub_re] at hre
  have hcub : 32768 ≤ w.re^5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤32) hr 5
    norm_num at h
    linarith
  have htcu : w.re^5 ≤ t*w.re^5 := by nlinarith
  simp only [Complex.add_re,Complex.ofReal_re] at *
  rcases abs_le.mp hre with ⟨hr1,hr2⟩
  rcases abs_le.mp hsr with ⟨hs1,hs2⟩
  refine ⟨by linarith,by nlinarith [hdom.2.2],by nlinarith [hdom.2.2],?_⟩
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem horizontal_neighbor_error (t x : ℝ) (ht : 1 ≤ t) (hx : 8 ≤ x) (w v : ℂ)
    (hr : 32 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
    (hp : 6*t*‖w‖^5+9 ≤ x) (hv : ‖v-w‖ ≤ 1/x) (s : ℝ) (hsr : |s| ≤ 1/16) :
    ‖complexSlope 3 t (v+(s : ℂ))-modelDerivative 3 t (v+(s : ℂ))‖ ≤
      30005*Real.exp (-4*w.re+4) := by
  let q := v+(s : ℂ)
  have hd := horizontal_neighbor_domain t x ht hx w v hr hi hs hp hv s hsr
  change 0 ≤ q.re ∧ 1 ≤ (Complex.exp (4*q)).re ∧ t*w.re^5/64 ≤ (Complex.exp (4*q)).re ∧
    |q.re-w.re| ≤ 1 at hd
  have heq : complexSlope 3 t q-modelDerivative 3 t q=
      kernelDerivative q/kernelComplex q-(9-4*(Real.pi : ℂ)*Complex.exp (4*q)) := by
    unfold complexSlope modelDerivative
    rw [(kernelComplex_hasDerivAt q (by linarith [hd.2.1])).deriv]
    ring
  change ‖complexSlope 3 t q-modelDerivative 3 t q‖ ≤ _
  rw [heq]
  apply (RiemannQuarticSaddleNeighborhood.logDerivative_coarse_bound q hd.1 hd.2.1).trans
  have hcub : 1024*w.re ≤ w.re^3 := by
    have hsq : 1024 ≤ w.re^2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ w.re)
    nlinarith
  have h35 : w.re^3 ≤ w.re^5 := pow_le_pow_right₀ (by linarith : 1 ≤ w.re) (by norm_num)
  have htcub : w.re^3 ≤ t*w.re^5 := h35.trans (by nlinarith [pow_nonneg (by linarith : 0 ≤ w.re) 5])
  have hpi := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (by linarith [hd.2.1] : 0 ≤ (Complex.exp (4*q)).re)
  have hlo := (abs_le.mp hd.2.2.2).1
  have hhi := (abs_le.mp hd.2.2.2).2
  have h1 : Real.exp (-4*q.re) ≤ Real.exp (-4*w.re+4) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (4*q.re)*Real.exp (-3*Real.pi*(Complex.exp (4*q)).re) ≤ Real.exp (-4*w.re+4) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hd.2.2.1]
  have hh1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ)≤5)
  have hh2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ)≤30000)
  nlinarith

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarRemainder
