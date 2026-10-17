import Foundation.ComplexRootTiltedLaw

/-! Actual norm-exponential moments of complex-root laws, controlling complex variation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootNormTransform

theorem step_norm_mean (a ξ : ℝ) :
    (∫ k, ‖Complex.exp (Complex.I*(ξ : ℂ)*ComplexFourthRootNoise.noise a k)‖
      ∂ComplexFourthRootNoise.probability) = Real.cosh (a*ξ) := by
  simp_rw [Complex.norm_exp]
  rw [ComplexRootOneStepCalculus.integral_real_formula]
  norm_num [ComplexFourthRootNoise.noise, ComplexFourthRootNoise.root,
    Complex.mul_re, Complex.mul_im, Real.cosh_eq, mul_comm]
  ring

theorem walk_norm_mean (a ξ : ℝ) (n : ℕ) :
    (∫ ω, ‖Complex.exp (Complex.I*(ξ : ℂ)*ComplexFourthRootWalk.terminal n a ω)‖
      ∂ComplexFourthRootWalk.probability n) = (Real.cosh (a*ξ))^n := by
  unfold ComplexFourthRootWalk.terminal
  simp only [Finset.mul_sum, Complex.exp_sum, norm_prod]
  rw [ComplexFourthRootWalk.probability]
  have he := integral_fintype_prod_eq_prod
    (μ := fun _ : Fin n => ComplexFourthRootNoise.probability)
    (fun _ k => ‖Complex.exp (Complex.I*(ξ : ℂ)*ComplexFourthRootNoise.noise a k)‖)
  simpa only [ComplexFourthRootWalk.increment, step_norm_mean, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using he

theorem compound_norm_mean (a ξ : ℝ) (r : ℝ≥0) :
    (∫ z, ‖Complex.exp (Complex.I*(ξ : ℂ)*z)‖ ∂ComplexRootPoissonLaw.law r a) =
      Real.exp ((r : ℝ)*(Real.cosh (a*ξ)-1)) := by
  let F : ℂ → ℂ := fun z => (‖Complex.exp (Complex.I*(ξ : ℂ)*z)‖ : ℂ)
  have hF : Continuous F := Complex.continuous_ofReal.comp
    ((continuous_const.mul continuous_id).cexp.norm)
  have hb (n : ℕ) (ω : ComplexFourthRootWalk.Sample n) :
      ‖F (ComplexFourthRootWalk.terminal n a ω)‖ ≤ (Real.exp (2 * |a| * |ξ|))^n := by
    simpa only [F, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] using
      ComplexRootPoissonTransform.exponential_walk_bound n a ξ ω
  have he := ComplexRootPoissonGrowth.integral_growth r a F hF
    (Real.exp (2 * |a| * |ξ|)) hb
  simp only [F] at he
  simp_rw [integral_complex_ofReal, walk_norm_mean] at he
  rw [PoissonEntireMoments.real_powers_integral] at he
  exact Complex.ofReal_injective he

theorem symbol_real (a ξ : ℝ) : MarkedHolomorphicExponential.symbol a ξ =
    ((Real.cos (a*ξ)*Real.cosh (a*ξ)-1 : ℝ) : ℂ) := by
  unfold MarkedHolomorphicExponential.symbol
  rw [ComplexRootOneStepCalculus.stepTransform_formula]
  push_cast
  rfl

theorem tilted_density_norm_mean (a ξ : ℝ) (r : ℝ≥0) :
    (∫ z, ‖ComplexRootTiltedLaw.density a ξ r z‖ ∂ComplexRootPoissonLaw.law r a) =
      Real.exp ((r : ℝ)*Real.cosh (a*ξ)*(1-Real.cos (a*ξ))) := by
  simp only [ComplexRootTiltedLaw.density, norm_mul]
  rw [integral_const_mul, compound_norm_mean, Complex.norm_exp, symbol_real]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [← Real.exp_add]
  congr 1
  ring

theorem tilted_variation_mass (a ξ : ℝ) (r : ℝ≥0) :
    (ComplexRootTiltedLaw.law a ξ r).variation Set.univ = ENNReal.ofReal
      (Real.exp ((r : ℝ)*Real.cosh (a*ξ)*(1-Real.cos (a*ξ)))) := by
  rw [ComplexRootTiltedLaw.law,
    Measure.variation_withDensityᵥ (ComplexRootTiltedLaw.density_integrable a ξ r),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_norm_eq_lintegral_enorm (ComplexRootTiltedLaw.density_integrable a ξ r),
    tilted_density_norm_mean]

end OperatorDerivativeRewrite.Foundation.ComplexRootNormTransform
