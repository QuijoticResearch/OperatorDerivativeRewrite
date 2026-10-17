import Foundation.BrownianCompensatedSampling
import Mathlib.Probability.Independence.Integration

/-! Actual two-time characteristic functions of the independent Brownian center source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianTwoTimeFourier
open InfiniteGaussian IBMConstructedSources StickyPairPaths StickyPairSampling
open StickyPairMarginals IBMOneTimeFourier
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

theorem source_fourier (u : ℝ) (t : ℝ≥0) :
    (∫ w, observable u (clockPath w t) ∂gaussianProduct)=
      (Real.exp (-(u^2*(t:ℝ)/2)) : ℂ) := by
  rw [← centered_fourier]
  apply integral_congr_ae
  filter_upwards [source_zero] with w hw
  simp [centeredPath,hw]

theorem increment_fourier (u : ℝ) (s t : ℝ≥0) :
    (∫ w, observable u (clockPath w t-clockPath w s) ∂gaussianProduct)=
      (Real.exp (-(u^2*(nndist (t:ℝ) (s:ℝ):ℝ)/2)) : ℂ) := by
  have hl := (clock_isBrownian.toIsPreBrownianReal.hasLaw_sub t s).integral_comp
    (observable_continuous u).aestronglyMeasurable
  change (∫ w, observable u (clockPath w t-clockPath w s) ∂gaussianProduct)=
    ∫ x, observable u x ∂gaussianReal 0 (nndist (t:ℝ) (s:ℝ)) at hl
  rw [hl,← charFun_eq_observable,charFun_gaussianReal,Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem two_time_fourier (p q : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ w, observable p (clockPath w s)*observable q (clockPath w t) ∂gaussianProduct)=
      (Real.exp (-((p+q)^2*(s:ℝ)+q^2*((t:ℝ)-s))/2) : ℂ) := by
  have hi := clock_isBrownian.toIsPreBrownianReal.hasIndepIncrements.indepFun_eval_sub
    (r := 0) (by positivity) hst source_zero
  have hc := hi.comp (observable_continuous (p+q)).measurable (observable_continuous q).measurable
  have hm1 : AEStronglyMeasurable (fun w => observable (p+q) (clockPath w s)) gaussianProduct :=
    ((observable_continuous (p+q)).measurable.comp
      ((ContinuousMap.measurable_eval s).comp clockPath_measurable)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun w => observable q (clockPath w t-clockPath w s))
      gaussianProduct := ((observable_continuous q).measurable.comp
        (((ContinuousMap.measurable_eval t).comp clockPath_measurable).sub
          ((ContinuousMap.measurable_eval s).comp clockPath_measurable))).aestronglyMeasurable
  have hf := hc.integral_mul_eq_mul_integral hm1 hm2
  change (∫ w, observable (p+q) (clockPath w s)*
    observable q (clockPath w t-clockPath w s) ∂gaussianProduct)=
    (∫ w, observable (p+q) (clockPath w s) ∂gaussianProduct)*
    ∫ w, observable q (clockPath w t-clockPath w s) ∂gaussianProduct at hf
  have he (x y : ℝ) : observable p x*observable q y=
      observable (p+q) x*observable q (y-x) := by
    unfold observable
    rw [← Complex.exp_add,← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [hf,source_fourier,increment_fourier,← Complex.ofReal_mul,← Real.exp_add]
  have hR : (s:ℝ) ≤ t := by exact_mod_cast hst
  simp only [coe_nndist,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hR)]
  congr 1
  ring

theorem centered_two_time_fourier (p q : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ w, observable p (centeredPath w s)*observable q (centeredPath w t) ∂gaussianProduct)=
      (Real.exp (-((p+q)^2*(s:ℝ)+q^2*((t:ℝ)-s))/2) : ℂ) := by
  rw [← two_time_fourier p q s t hst]
  apply integral_congr_ae
  filter_upwards [source_zero] with w hw
  simp [centeredPath,hw]

end OperatorDerivativeRewrite.Foundation.BrownianTwoTimeFourier
