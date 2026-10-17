import Foundation.GaussianLikelihoodRootInnovation
import Mathlib.Probability.CondVar

/-! The terminal likelihood root has explicit, almost surely positive conditional variance. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianLikelihoodRootConditionalVariance
open InfiniteGaussian GaussianTimeProcess GaussianCore GaussianCriticalExponential
open GaussianLinearTiltLaw GaussianLinearLikelihoodMoments GaussianTiltL2Domain
open GaussianLinearPastTransport GaussianConditionalLikelihoodRoot GaussianLikelihoodRootInnovation
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

theorem linearDensity_setIntegral {s : Set SampleSpace} (hs : MeasurableSet s) :
    (∫ ω in s, linearDensity ω ∂gaussianProduct) = Qlinear.real s := by
  have h : ENNReal.ofReal (∫ ω in s, linearDensity ω ∂gaussianProduct) = Qlinear s := by
    rw [Qlinear, withDensity_apply _ hs]
    exact ofReal_integral_eq_lintegral_ofReal linearDensity_integrable.integrableOn
      (Filter.Eventually.of_forall (fun ω => (linearDensity_positive ω).le))
  have hp : 0 ≤ ∫ ω in s, linearDensity ω ∂gaussianProduct :=
    integral_nonneg (fun ω => (linearDensity_positive ω).le)
  simpa only [ENNReal.toReal_ofReal hp, measureReal_def] using congrArg ENNReal.toReal h

theorem linearDensity_condExp_one :
    gaussianProduct[linearDensity | naturalFiltration 1] =ᵐ[gaussianProduct] fun _ => 1 := by
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (naturalFiltration.le 1) linearDensity_integrable
  · intro s _ _
    exact (integrable_const (1 : ℝ)).integrableOn
  · intro s hs _
    rw [linearDensity_setIntegral (naturalFiltration.le 1 s hs)]
    simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Qlinear_eq_P_on_past hs]
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem root_square_condExp_one :
    gaussianProduct[rootDensity ^ 2 | naturalFiltration 1] =ᵐ[gaussianProduct] fun _ => 1 := by
  have h : rootDensity ^ 2 = linearDensity := funext rootDensity_sq
  rw [h]
  exact linearDensity_condExp_one

theorem root_conditional_variance :
    Var[rootDensity; gaussianProduct | naturalFiltration 1] =ᵐ[gaussianProduct]
      fun ω => 1 - Real.exp (-(1/4 : ℝ)*(process 1 ω)^2) := by
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp
    (naturalFiltration.le 1) rootDensity_memLp_P, root_square_condExp_one,
    rootDensity_condExp] with ω hvar hsq hmean
  simpa only [Pi.sub_apply, Pi.pow_apply, hsq, hmean, meanPast_square] using hvar

theorem time_one_nonzero_ae : ∀ᵐ ω ∂gaussianProduct, process 1 ω ≠ 0 := by
  letI : NullSingletonClass γ := nullSingletonClass_gaussianReal (by norm_num)
  exact ((process_hasLaw 1).ae_iff (by fun_prop)).mpr (γ.ae_ne 0)

theorem root_conditional_variance_positive :
    ∀ᵐ ω ∂gaussianProduct, 0 < Var[rootDensity; gaussianProduct | naturalFiltration 1] ω := by
  filter_upwards [root_conditional_variance, time_one_nonzero_ae] with ω hvar hne
  rw [hvar]
  have hex : Real.exp (-(1/4 : ℝ)*(process 1 ω)^2) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [sq_pos_of_ne_zero hne]
  linarith

end OperatorDerivativeRewrite.Foundation.GaussianLikelihoodRootConditionalVariance
