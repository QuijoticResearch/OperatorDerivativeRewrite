import Foundation.RiemannSixthFarAnalyticBranch
import Foundation.RiemannSixthUniformFarSaddles

/-! The actual critical value along a holomorphic sixth-order saddle branch.
Its derivative is an exact actual-kernel identity, not a model Gaussian law. -/
noncomputable section
open Set Metric Complex
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthCriticalValue
open RiemannEvenModelPhase RiemannEvenSaddleBranch RiemannThetaComplexKernel
open RiemannSixthFarAnalyticBranch

variable (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
  (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
  (hs : modelDerivative 3 t w = -(Complex.I*(x : ℂ)))
include ht hx hr hi hp hs
local notation "B" => branch t x ht hx w hr hi hp hs

def criticalValue (z : ℂ) : ℂ :=
  Complex.exp ((t : ℂ)*(B z)^6+Complex.I*z*B z)*kernelComplex (B z)

theorem criticalValue_ne_zero (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    criticalValue t x ht hx w hr hi hp hs z ≠ 0 := by
  exact mul_ne_zero (Complex.exp_ne_zero _) (branch_domain t x ht hx w hr hi hp hs z hz).2.2

theorem branch_exp_real_pos (z : ℂ) (hz : ‖z-(x : ℂ)‖ ≤ 1) :
    0 < (Complex.exp (4*B z)).re := by
  have hd := branch_domain t x ht hx w hr hi hp hs z hz
  have hc := RiemannQuarticNaturalContour.cosine_margin_pos |(B z).im| (abs_nonneg _) hd.2.1
  have he := RiemannQuarticNaturalContour.exp_real_lower |(B z).im| (abs_nonneg _) hd.2.1 (B z) le_rfl
  exact lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) he

theorem criticalValue_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    HasDerivAt (criticalValue t x ht hx w hr hi hp hs)
      (Complex.I*B z*criticalValue t x ht hx w hr hi hp hs z) z := by
  let b := B z
  let d := -Complex.I/deriv (complexSlope 3 t) b
  have hb : HasDerivAt B d z := (branch_hasStrictDerivAt t x ht hx w hr hi hp hs z hz).hasDerivAt
  have hk := kernelComplex_hasDerivAt b (branch_exp_real_pos t x ht hx w hr hi hp hs z hz.le)
  have hnonzero := (branch_domain t x ht hx w hr hi hp hs z hz.le).2.2
  change kernelComplex b ≠ 0 at hnonzero
  have he : (6*(t : ℂ)*b^5+Complex.I*z)*kernelComplex b+kernelDerivative b = 0 := by
    have hroot := (branch_spec t x ht hx w hr hi hp hs z hz.le).2
    change complexSlope 3 t b = -(Complex.I*z) at hroot
    unfold complexSlope at hroot
    rw [hk.deriv] at hroot
    norm_num at hroot
    field_simp [hnonzero] at hroot
    linear_combination hroot
  have hP : HasDerivAt (fun y : ℂ => (t : ℂ)*(B y)^6+Complex.I*y*B y)
      (6*(t : ℂ)*b^5*d+Complex.I*b+Complex.I*z*d) z := by
    have h := ((hb.pow 6).const_mul (t : ℂ)).add (((hasDerivAt_id z).mul hb).const_mul Complex.I)
    convert h using 1
    · funext y
      simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
      ring
    · dsimp only [id_eq]
      ring
  have h := hP.cexp.mul (hk.comp z hb)
  convert h using 1
  · funext y; rfl
  · dsimp only [Function.comp_def]
    change Complex.I*b*(Complex.exp ((t : ℂ)*b^6+Complex.I*z*b)*kernelComplex b) = _
    linear_combination -(Complex.exp ((t : ℂ)*b^6+Complex.I*z*b)*d)*he

theorem criticalValue_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    AnalyticAt ℂ (criticalValue t x ht hx w hr hi hp hs) z := by
  have hb := branch_analyticAt t x ht hx w hr hi hp hs z hz
  have hk := kernelComplex_analyticAt (B z) (branch_exp_real_pos t x ht hx w hr hi hp hs z hz.le)
  exact (((analyticAt_const.mul (hb.pow 6)).add ((analyticAt_const.mul analyticAt_id).mul hb)).cexp).mul (hk.comp hb)

theorem criticalValue_log_derivative (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    deriv (criticalValue t x ht hx w hr hi hp hs) z/criticalValue t x ht hx w hr hi hp hs z = Complex.I*B z := by
  rw [(criticalValue_hasDerivAt t x ht hx w hr hi hp hs z hz).deriv]
  exact mul_div_cancel_right₀ _ (criticalValue_ne_zero t x ht hx w hr hi hp hs z hz.le)

end OperatorDerivativeRewrite.Foundation.RiemannSixthCriticalValue
