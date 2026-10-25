import Foundation.IBMUniformRidgeNativeBounds
import Foundation.GaussianMixedTrigCovariance

/-! Actual Gaussian characteristic coefficients for phased Fourier ridge tests.
The zero direction is included in the same formula. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFourierRidgeCoefficients
open InfiniteGaussian

def mode (β x : ℝ) : ℝ := Real.cos (β+x)

theorem mode_smooth (β : ℝ) : ContDiff ℝ 2 (mode β) := by
  exact Real.contDiff_cos.comp (contDiff_const.add contDiff_id)

theorem mode_bound (β x : ℝ) : ‖mode β x‖ ≤ (1:ℝ) := Real.abs_cos_le_one _

theorem mode_deriv (β : ℝ) : deriv (mode β) = fun x => -Real.sin (β+x) := by
  funext x
  change deriv (fun y => Real.cos (β+y)) x = _
  simpa only [Function.comp_def,mul_one] using ((Real.hasDerivAt_cos (β+x)).comp x ((hasDerivAt_id x).const_add β)).deriv

theorem mode_first_bound (β x : ℝ) : ‖deriv (mode β) x‖ ≤ (1:ℝ) := by
  rw [mode_deriv,norm_neg]
  exact Real.abs_sin_le_one _

theorem mode_second (β : ℝ) : deriv (deriv (mode β)) = -mode β := by
  rw [mode_deriv]
  funext x
  simpa [mode,Function.comp_def] using (((Real.hasDerivAt_sin (β+x)).comp x ((hasDerivAt_id x).const_add β)).neg).deriv

theorem mode_second_bound (β x : ℝ) : ‖deriv (deriv (mode β)) x‖ ≤ (1:ℝ) := by
  rw [mode_second,Pi.neg_apply,norm_neg]
  exact mode_bound β x

theorem firstChaos_characteristic (u : CoefficientSpace) :
    (∫ X, Complex.exp ((firstChaosEmbedding u X:ℂ)*Complex.I) ∂gaussianProduct) =
      (Real.exp (-‖u‖^2/2):ℂ) := by
  have hm := integral_map (μ := gaussianProduct)
    (Lp.stronglyMeasurable (firstChaosEmbedding u)).aemeasurable
    (f := fun x : ℝ => Complex.exp ((x:ℂ)*Complex.I)) (by fun_prop)
  have hc := firstChaos_charFun u 1
  rw [charFun_apply_real] at hc
  simp only [Complex.ofReal_one,one_mul,one_pow,mul_one] at hc
  rw [hm] at hc
  simpa only [Complex.ofReal_one,one_mul,one_pow,mul_one,Complex.ofReal_exp,
    Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_pow,Complex.ofReal_ofNat] using hc

theorem mode_mean (β : ℝ) (u : CoefficientSpace) :
    (∫ X, mode β (firstChaosEmbedding u X) ∂gaussianProduct) =
      Real.cos β*Real.exp (-‖u‖^2/2) := by
  have hi : Integrable (fun X => Complex.exp ((firstChaosEmbedding u X:ℂ)*Complex.I))
      gaussianProduct := by
    apply Integrable.mono' (integrable_const (1:ℝ)) (by fun_prop)
    exact Filter.Eventually.of_forall fun X => by simp [Complex.norm_exp,Complex.mul_re]
  have he := congrArg Complex.re (firstChaos_characteristic u)
  have hs := congrArg Complex.im (firstChaos_characteristic u)
  change RCLike.re (∫ X, Complex.exp ((firstChaosEmbedding u X:ℂ)*Complex.I)
    ∂gaussianProduct) = _ at he
  change RCLike.im (∫ X, Complex.exp ((firstChaosEmbedding u X:ℂ)*Complex.I)
    ∂gaussianProduct) = _ at hs
  rw [← integral_re hi] at he
  rw [← integral_im hi] at hs
  simp only [Complex.ofReal_re] at he
  simp only [Complex.ofReal_im] at hs
  simp [Complex.exp_re,Complex.exp_im,Complex.mul_re,Complex.mul_im,pow_two] at he hs
  have hcos := (IBMFirstChaosDiagonalStein.bounded_comp_memLp u
    Real.continuous_cos Real.abs_cos_le_one).integrable (by norm_num)
  have hsin := (IBMFirstChaosDiagonalStein.bounded_comp_memLp u
    Real.continuous_sin Real.abs_sin_le_one).integrable (by norm_num)
  simp only [mode,Real.cos_add]
  rw [integral_sub (hcos.const_mul _) (hsin.const_mul _),integral_const_mul,
    integral_const_mul]
  rw [he,hs]
  ring

theorem coefficient_formula (β : ℝ) (u : CoefficientSpace) :
    IBMBoundedC2SecondProjection.coefficient (mode β) u =
      -(1/2:ℝ)*Real.cos β*Real.exp (-‖u‖^2/2) := by
  rw [IBMBoundedC2SecondProjection.coefficient,mode_second]
  simp only [Pi.neg_apply,integral_neg,mode_mean]
  ring

end OperatorDerivativeRewrite.Foundation.IBMFourierRidgeCoefficients
