import Foundation.ComplexRootPoissonGrowth
import Foundation.ComplexRootOneStepCalculus

/-! Unbounded holomorphic exponential tests under genuine compound-root probability laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonTransform
open ComplexFourthRootNoise ComplexFourthRootWalk ComplexRootPoissonGrowth

theorem noise_norm_bound (a : ℝ) (k : Fin 4) : ‖noise a k‖ ≤ 2*|a| := by
  have hs := norm_square a k
  have hn := norm_nonneg (noise a k)
  have ha := abs_nonneg a
  nlinarith [sq_abs a]

theorem exponential_noise_bound (a ξ : ℝ) (k : Fin 4) :
    ‖Complex.exp (Complex.I * (ξ : ℂ) * noise a k)‖ ≤ Real.exp (2 * |a| * |ξ|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ‖Complex.I * (ξ : ℂ) * noise a k‖ := Complex.re_le_norm _
    _ = |ξ| * ‖noise a k‖ := by simp [norm_mul, Real.norm_eq_abs]
    _ ≤ |ξ| * (2*|a|) :=
      mul_le_mul_of_nonneg_left (noise_norm_bound a k) (abs_nonneg ξ)
    _ = _ := by ring

theorem exponential_walk_bound (n : ℕ) (a ξ : ℝ) (ω : Sample n) :
    ‖Complex.exp (Complex.I * (ξ : ℂ) * terminal n a ω)‖ ≤
      (Real.exp (2 * |a| * |ξ|))^n := by
  unfold terminal
  simp only [Finset.mul_sum, Complex.exp_sum, norm_prod]
  calc
    _ ≤ ∏ _i : Fin n, Real.exp (2 * |a| * |ξ|) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => exponential_noise_bound a ξ (ω i))
    _ = _ := by simp

theorem exponential_integrable (r : ℝ≥0) (a ξ : ℝ) :
    Integrable (fun z => Complex.exp (Complex.I * (ξ : ℂ) * z))
      (ComplexRootPoissonLaw.law r a) :=
  growth_integrable r a _ (by fun_prop) (Real.exp (2 * |a| * |ξ|))
    (fun n ω => exponential_walk_bound n a ξ ω)

theorem transform (r : ℝ≥0) (a ξ : ℝ) :
    (∫ z, Complex.exp (Complex.I * (ξ : ℂ) * z) ∂ComplexRootPoissonLaw.law r a) =
      Complex.exp ((r : ℂ)*(stepTransform a ξ-1)) := by
  rw [integral_growth r a _ (by fun_prop) (Real.exp (2 * |a| * |ξ|))
    (fun n ω => exponential_walk_bound n a ξ ω)]
  simp_rw [terminal_transform]
  exact PoissonEntireMoments.complex_powers_integral r (stepTransform a ξ)

theorem transform_formula (r : ℝ≥0) (a ξ : ℝ) :
    (∫ z, Complex.exp (Complex.I * (ξ : ℂ) * z) ∂ComplexRootPoissonLaw.law r a) =
      Complex.exp ((r : ℂ)*(((Real.cos (a*ξ)*Real.cosh (a*ξ) : ℝ) : ℂ)-1)) := by
  rw [transform, ComplexRootOneStepCalculus.stepTransform_formula]
  simp only [Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_cosh]

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonTransform
