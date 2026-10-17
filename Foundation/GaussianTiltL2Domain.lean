import Foundation.GaussianLinearTiltLaw

/-! An explicit change of L2 domain under two equivalent probability measures. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianTiltL2Domain
open InfiniteGaussian GaussianCriticalExponential GaussianLinearLikelihoodMoments
  GaussianLinearTiltLaw
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

def rootDensity (ω : SampleSpace) : ℝ := Real.sqrt (linearDensity ω)

theorem rootDensity_measurable : Measurable rootDensity := by
  unfold rootDensity
  exact Real.continuous_sqrt.measurable.comp linearDensity_measurable

theorem rootDensity_sq (ω : SampleSpace) : rootDensity ω ^ 2 = linearDensity ω :=
  Real.sq_sqrt (linearDensity_positive ω).le

theorem rootDensity_memLp_P : MemLp rootDensity 2 gaussianProduct := by
  apply (memLp_two_iff_integrable_sq rootDensity_measurable.aestronglyMeasurable).mpr
  have he : (fun ω => rootDensity ω ^ 2) = linearDensity := funext rootDensity_sq
  rw [he]
  exact linearDensity_integrable

theorem rootDensity_square_lintegral_P :
    (∫⁻ ω, ENNReal.ofReal (rootDensity ω ^ 2) ∂gaussianProduct) = 1 := by
  simp_rw [rootDensity_sq]
  exact linearDensity_normalized

theorem rootDensity_square_lintegral_Q :
    (∫⁻ ω, ENNReal.ofReal (rootDensity ω ^ 2) ∂Qlinear) = ∞ := by
  rw [Qlinear, lintegral_withDensity_eq_lintegral_mul gaussianProduct
    linearDensity_measurable.ennreal_ofReal (rootDensity_measurable.pow_const 2).ennreal_ofReal]
  change (∫⁻ ω, ENNReal.ofReal (linearDensity ω)*ENNReal.ofReal (rootDensity ω ^ 2)
    ∂gaussianProduct) = ∞
  simp_rw [rootDensity_sq, ← ENNReal.ofReal_mul (linearDensity_positive _).le, ← pow_two]
  exact linearDensity_square_lintegral

theorem rootDensity_not_memLp_Q : ¬ MemLp rootDensity 2 Qlinear := by
  intro h
  have he := ofReal_integral_eq_lintegral_ofReal h.integrable_sq
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (rootDensity ω)))
  rw [rootDensity_square_lintegral_Q] at he
  exact ENNReal.ofReal_ne_top he

theorem explicit_L2_domain_counterexample : ∃ f : SampleSpace → ℝ,
    Measurable f ∧ MemLp f 2 gaussianProduct ∧ ¬ MemLp f 2 Qlinear :=
  ⟨rootDensity, rootDensity_measurable, rootDensity_memLp_P, rootDensity_not_memLp_Q⟩

end OperatorDerivativeRewrite.Foundation.GaussianTiltL2Domain
