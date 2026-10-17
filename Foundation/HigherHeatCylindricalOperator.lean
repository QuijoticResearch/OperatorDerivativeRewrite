import Foundation.HigherHeatNegativeProbe

/-! The constructed higher-heat cylindrical expectation realizes actual Schwartz/L2 evolution. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped NNReal Topology SchwartzMap BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCylindricalOperator
open GaussianSchwartzKernel HigherHeatSignedLaws HigherHeatDyadicLaws
open HigherHeatCylindricalExpectation HigherHeatNegativeProbe

def shiftedTest (f : 𝓢(ℝ,ℝ)) (x : ℝ) : ℝ →ᵇ ℝ :=
  f.toBoundedContinuousFunction.compContinuous ⟨fun y : ℝ => x-y,by fun_prop⟩

theorem shiftedTest_apply (f : 𝓢(ℝ,ℝ)) (x y : ℝ) : shiftedTest f x y=f (x-y) := rfl

def observationCylinder (f : 𝓢(ℝ,ℝ)) (x : ℝ) : Cylinder :=
  cylinderOf 0 (terminalTest (shiftedTest f x))

def complexify (f : 𝓢(ℝ,ℝ)) : 𝓢(ℝ,ℂ) := f.postcompCLM Complex.ofRealCLM

theorem complexify_apply (f : 𝓢(ℝ,ℝ)) (x : ℝ) : complexify f x=(f x : ℂ) := rfl

def evolved (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (f : 𝓢(ℝ,ℝ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (evenKernel m hm T hT) (complexify f)

theorem expectation_evolved (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (f : 𝓢(ℝ,ℝ)) (x : ℝ) :
    (cylindricalExpectation m hm T hT (observationCylinder f x) : ℂ)=evolved m hm T hT f x := by
  rw [observationCylinder,cylindricalExpectation_apply,terminal_expectation]
  simp only [shiftedTest_apply]
  rw [evolved,SchwartzMap.convolution_apply,convolution_def,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with y
  simp only [Complex.ofReal_mul,realKernel_coe,complexify_apply,ContinuousLinearMap.mul_apply']

theorem evolution_realized (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (f : 𝓢(ℝ,ℝ)) :
    HigherHeatL2.evolution m T ((complexify f).toLp 2)=(evolved m hm T hT f).toLp 2 :=
  l2_kernel_evolution m hm T hT (complexify f)

theorem schwartz_operator_realization (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (f : 𝓢(ℝ,ℝ)) : ∃ g : 𝓢(ℝ,ℂ),
      HigherHeatL2.evolution m T ((complexify f).toLp 2)=g.toLp 2 ∧
      ∀ x : ℝ, (cylindricalExpectation m hm T hT (observationCylinder f x) : ℂ)=g x := by
  exact ⟨evolved m hm T hT f,evolution_realized m hm T hT f,expectation_evolved m hm T hT f⟩

end OperatorDerivativeRewrite.Foundation.HigherHeatCylindricalOperator
