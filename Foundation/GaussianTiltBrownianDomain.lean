import Foundation.GaussianTiltHalfDensity
import Foundation.GaussianBrownianPRP

/-! The domain counterexample is an actual Brownian-generated P-level PRP terminal value. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianTiltBrownianDomain
open InfiniteGaussian GaussianTimeProcess GaussianRandomDensityKernel GaussianCriticalExponential
  GaussianLinearTiltLaw GaussianTiltL2Domain GaussianBrownianGeneratedSpace GaussianBrownianPRP
  GaussianPredictableFull
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

theorem rootDensity_brownian_measurable : Measurable[brownianSigma] rootDensity :=
  Real.continuous_sqrt.measurable.comp
    (kernel_continuous.measurable.comp
      ((process_brownian_measurable 1).prodMk
        ((process_brownian_measurable 2).sub (process_brownian_measurable 1))))

def terminalValue : GaussianL2 := rootDensity_memLp_P.toLp rootDensity

theorem terminalValue_coeFn : terminalValue =ᵐ[gaussianProduct] rootDensity :=
  MemLp.coeFn_toLp _

theorem terminalValue_brownian : terminalValue ∈ brownianL2 :=
  rootDensity_brownian_measurable.stronglyMeasurable.aestronglyMeasurable.congr
    terminalValue_coeFn.symm

theorem terminalValue_representation : ∃! U : fullPredictable,
    itoIntegral U = terminalValue - (∫ ω, terminalValue ω ∂gaussianProduct) • gaussianOne :=
  brownian_representation_exists_unique terminalValue terminalValue_brownian

theorem terminalValue_not_memLp_Q : ¬ MemLp terminalValue 2 Qlinear := by
  intro h
  exact rootDensity_not_memLp_Q (h.ae_eq (Qlinear_ac_P.ae_le terminalValue_coeFn))

theorem no_Q_L2_representative_of_original_class : ¬ ∃ f : SampleSpace → ℝ,
    f =ᵐ[gaussianProduct] rootDensity ∧ MemLp f 2 Qlinear := by
  rintro ⟨f, hf, hmem⟩
  exact rootDensity_not_memLp_Q (hmem.ae_eq (Qlinear_ac_P.ae_le hf))

end OperatorDerivativeRewrite.Foundation.GaussianTiltBrownianDomain
