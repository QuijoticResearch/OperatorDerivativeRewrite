import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Complex.RealDeriv

/-! The complex fundamental theorem for actual absolutely continuous curves with an ae derivative. -/
noncomputable section
open MeasureTheory Filter Set
namespace OperatorDerivativeRewrite.Foundation.ComplexAbsoluteContinuousFTC

theorem integral_eq_sub (f d : ℝ → ℂ) (a b : ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (d t) t)
    (hi : IntervalIntegrable d volume a b) :
    (∫ t in a..b, d t) = f b - f a := by
  have hr := Complex.reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have him := Complex.imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hf
  have hRe : (∫ t in a..b, (d t).re) = (f b).re - (f a).re := by
    calc
      _ = ∫ t in a..b, deriv (fun s => (f s).re) t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hd] with t ht hmem
        exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (ht hmem)).deriv.symm
      _ = _ := hr.integral_deriv_eq_sub
  have hIm : (∫ t in a..b, (d t).im) = (f b).im - (f a).im := by
    calc
      _ = ∫ t in a..b, deriv (fun s => (f s).im) t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hd] with t ht hmem
        exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (ht hmem)).deriv.symm
      _ = _ := him.integral_deriv_eq_sub
  apply Complex.ext
  · rw [Complex.sub_re, ← hRe]
    exact (intervalIntegral.intervalIntegral_re hi).symm
  · rw [Complex.sub_im, ← hIm]
    exact (intervalIntegral.intervalIntegral_im hi).symm

end OperatorDerivativeRewrite.Foundation.ComplexAbsoluteContinuousFTC
