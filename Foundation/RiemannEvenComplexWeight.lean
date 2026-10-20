import Foundation.RiemannEvenFlow
import Foundation.RiemannQuarticNaturalContour

/-! Literal integer-even tilted complex theta weight, identified with the
actual real integrand. Reflection is used only inside the natural strip. -/
noncomputable section
open Set Complex MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenComplexWeight
open RiemannThetaComplexKernel RiemannQuarticKernelReflection

def weight (m : ℕ) (t : ℝ) (z w : ℂ) : ℂ :=
  Complex.exp ((t : ℂ)*w^(2*m)+Complex.I*z*w)*kernelComplex w

theorem weight_quartic (t : ℝ) (z w : ℂ) :
    weight 2 t z w = RiemannQuarticFrequencyBranch.saddleWeight t z w := rfl

theorem weight_real (m : ℕ) (t : ℝ) (z : ℂ) (u : ℝ) :
    weight m t z (u : ℂ) = RiemannEvenFlow.integrand m 0 t z u := by
  simp only [weight, RiemannEvenFlow.integrand, RiemannEvenDomain.weighted,
    pow_zero, one_mul, mul_one, zero_mul, add_zero, kernelComplex_real,
    Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_pow, Complex.exp_add]
  rw [show Complex.I*z*(u : ℂ) = Complex.I*(u : ℂ)*z by ring]
  ring

theorem jet_zero_eq_halfline (m : ℕ) (t : ℝ) (z : ℂ) :
    RiemannEvenFlow.jet m 0 t z = ∫ u : ℝ in Ioi 0, weight m t z (u : ℂ) := by
  unfold RiemannEvenFlow.jet RiemannQuarticFlow.halfLine
  rw [integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  exact (weight_real m t z u).symm

theorem weight_neg_neg (m : ℕ) (t : ℝ) (z w : ℂ) (hw : w ∈ strip) :
    weight m t (-z) (-w) = weight m t z w := by
  unfold weight
  rw [kernelComplex_even w hw]
  have hp : (-w)^(2*m) = w^(2*m) := by rw [pow_mul, neg_sq, ← pow_mul]
  rw [hp]
  congr 2 <;> ring

theorem weight_analyticAt (m : ℕ) (t : ℝ) (z w : ℂ) (hw : |w.im| < Real.pi/8) :
    AnalyticAt ℂ (weight m t z) w := by
  have ha : AnalyticAt ℂ (fun v : ℂ => Complex.exp ((t : ℂ)*v^(2*m)+Complex.I*z*v)) w := by
    fun_prop
  have hstrip : w ∈ strip := by
    change -Real.pi/8 < w.im ∧ w.im < Real.pi/8
    constructor <;> linarith [(abs_lt.mp hw).1,(abs_lt.mp hw).2]
  exact ha.mul (kernelComplex_analyticAt w (strip_domain w hstrip))

end OperatorDerivativeRewrite.Foundation.RiemannEvenComplexWeight
