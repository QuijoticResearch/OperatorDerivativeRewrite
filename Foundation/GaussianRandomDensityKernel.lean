import Foundation.GaussianCore
import Mathlib.MeasureTheory.Integral.Prod

/-! A positive normalized Gaussian exponential kernel with a bounded past-dependent coefficient. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianRandomDensityKernel
open GaussianCore
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def kernel (a y : ℝ) : ℝ := Real.exp (-a*y-a^2/2)

def pairDensity (p : ℝ × ℝ) : ℝ := kernel (Real.sin p.1) p.2

theorem kernel_positive (a y : ℝ) : 0<kernel a y := Real.exp_pos _

theorem kernel_continuous : Continuous (Function.uncurry kernel) := by
  unfold kernel
  fun_prop

theorem kernel_factor (a y : ℝ) :
    kernel a y=Real.exp (-a^2/2)*Real.exp ((-a)*y) := by
  rw [kernel,← Real.exp_add]
  congr 1
  ring

theorem kernel_integrable (a : ℝ) : Integrable (kernel a) γ := by
  have h : kernel a=fun y => Real.exp (-a^2/2)*Real.exp ((-a)*y) := funext (kernel_factor a)
  rw [h]
  exact (integrable_exp_mul_gaussianReal (-a)).const_mul _

theorem kernel_integral (a : ℝ) : (∫ y, kernel a y ∂γ)=1 := by
  have hm := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (-a)
  change (∫ y : ℝ, Real.exp ((-a)*y) ∂γ)=Real.exp (0*(-a)+(1 : ℝ)*(-a)^2/2) at hm
  have h : kernel a=fun y => Real.exp (-a^2/2)*Real.exp ((-a)*y) := funext (kernel_factor a)
  rw [h,integral_const_mul,hm,← Real.exp_add]
  convert Real.exp_zero using 1 <;> congr 1 <;> ring

theorem kernel_bound (a y : ℝ) (ha : |a|≤1) :
    kernel a y≤Real.exp y+Real.exp (-y) := by
  have hprod : -a*y≤|y| := by
    calc
      _ ≤ |-a*y| := le_abs_self _
      _ = |a| * |y| := by rw [abs_mul,abs_neg]
      _ ≤ 1*|y| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      _ = |y| := one_mul _
  have he : kernel a y≤Real.exp |y| := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg a]
  apply he.trans
  by_cases hy : 0≤y
  · rw [abs_of_nonneg hy]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_neg (lt_of_not_ge hy)]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

theorem pairDensity_continuous : Continuous pairDensity := by
  unfold pairDensity kernel
  fun_prop

theorem pairDensity_positive (p : ℝ × ℝ) : 0<pairDensity p := kernel_positive _ _

theorem pairDensity_integrable : Integrable pairDensity (γ.prod γ) := by
  have hp : Integrable (fun y : ℝ => Real.exp y) γ := by
    simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) 1)
  have hn : Integrable (fun y : ℝ => Real.exp (-y)) γ := by
    simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-1))
  apply Integrable.mono' ((hp.add hn).comp_snd γ) pairDensity_continuous.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs,abs_of_pos (pairDensity_positive p)]
    exact kernel_bound _ _ (Real.abs_sin_le_one _))

theorem pairDensity_integral : (∫ p, pairDensity p ∂γ.prod γ)=1 := by
  rw [integral_prod _ pairDensity_integrable]
  simp [pairDensity,kernel_integral,Measure.real]

end OperatorDerivativeRewrite.Foundation.GaussianRandomDensityKernel
