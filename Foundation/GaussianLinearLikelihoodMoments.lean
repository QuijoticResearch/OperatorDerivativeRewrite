import Foundation.GaussianUnboundedDelayedStep

/-! The normalized unbounded-step likelihood is L1 but not L2. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianLinearLikelihoodMoments
open InfiniteGaussian GaussianTimeProcess GaussianCore GaussianRandomDensityKernel
  GaussianDensityTranslation GaussianCriticalExponential GaussianRandomTerminalMeasure
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

theorem kernel_square_factor (a y : ℝ) :
    kernel a y ^ 2 = Real.exp (a^2) * kernel (2*a) y := by
  simp only [kernel]
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem kernel_square_lintegral (a : ℝ) :
    (∫⁻ y, ENNReal.ofReal (kernel a y ^ 2) ∂γ) = ENNReal.ofReal (Real.exp (a^2)) := by
  have hn := ofReal_integral_eq_lintegral_ofReal (kernel_integrable (2*a))
    (Filter.Eventually.of_forall (fun y => (kernel_positive (2*a) y).le))
  rw [kernel_integral] at hn
  simp_rw [kernel_square_factor, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ (kernel_measurable (2*a)).ennreal_ofReal, ← hn]
  simp

theorem exp_square_lintegral : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (x^2)) ∂γ) = ∞ := by
  have h : (∫⁻ x, ENNReal.ofReal (critical x) ∂γ) ≤
      ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (x^2)) ∂γ := by
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg x]
  rw [critical_lintegral] at h
  exact top_le_iff.mp h

theorem linearPair_square_lintegral :
    (∫⁻ p, ENNReal.ofReal (linearPair p ^ 2) ∂γ.prod γ) = ∞ := by
  rw [lintegral_prod _ (linearPair_measurable.pow_const 2).ennreal_ofReal.aemeasurable]
  change (∫⁻ x, ∫⁻ y, ENNReal.ofReal (kernel x y ^ 2) ∂γ ∂γ) = ∞
  simp_rw [kernel_square_lintegral]
  exact exp_square_lintegral

theorem linearDensity_integrable : Integrable linearDensity gaussianProduct := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    linearDensity_measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => (linearDensity_positive ω).le))).mp
  rw [linearDensity_normalized]
  exact ENNReal.one_ne_top

theorem linearDensity_square_lintegral :
    (∫⁻ ω, ENNReal.ofReal (linearDensity ω ^ 2) ∂gaussianProduct) = ∞ := by
  calc
    _ = ∫⁻ p, ENNReal.ofReal (linearPair p ^ 2) ∂γ.prod γ :=
      joint_law.lintegral_comp (linearPair_measurable.pow_const 2).ennreal_ofReal.aemeasurable
    _ = ∞ := linearPair_square_lintegral

theorem linearDensity_square_not_integrable :
    ¬ Integrable (fun ω => linearDensity ω ^ 2) gaussianProduct := by
  intro h
  have he := ofReal_integral_eq_lintegral_ofReal h
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (linearDensity ω)))
  rw [linearDensity_square_lintegral] at he
  exact ENNReal.ofReal_ne_top he

theorem linearDensity_not_memLp_two : ¬ MemLp linearDensity 2 gaussianProduct := by
  intro h
  exact linearDensity_square_not_integrable h.integrable_sq

end OperatorDerivativeRewrite.Foundation.GaussianLinearLikelihoodMoments
