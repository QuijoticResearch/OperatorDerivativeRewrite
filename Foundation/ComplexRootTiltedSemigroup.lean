import Foundation.ComplexRootTiltedWalk
import Foundation.ComplexPoissonCompensation
import Foundation.MarkedHolomorphicExponential

/-! A genuine weighted Poisson operator semigroup with its compensated jump generator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootTiltedSemigroup
open ComplexRootTransitionOperator (Test)
open ComplexRootTiltedStep ComplexRootTiltedWalk

local instance : NormedAlgebra ℝ (Test →L[ℂ] Test) :=
  NormedAlgebra.restrictScalars ℝ ℂ (Test →L[ℂ] Test)
local instance : Nontrivial Test := ⟨⟨BoundedContinuousFunction.const ℂ 0,
    BoundedContinuousFunction.const ℂ 1, by
      intro h
      have he := congrArg (fun f : Test => f 0) h
      norm_num at he⟩⟩
local instance : NormOneClass (Test →L[ℂ] Test) := ⟨ContinuousLinearMap.norm_id⟩
local instance : NormedAlgebra ℚ (Test →L[ℂ] Test) :=
  NormedAlgebra.restrictScalars ℚ ℝ (Test →L[ℂ] Test)
local instance : Module ℝ (Test →L[ℂ] Test) :=
  (NormedAlgebra.toNormedSpace (𝕜 := ℝ) (Test →L[ℂ] Test)).toModule
local instance : TopologicalSpace (Test →L[ℂ] Test) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance : AddCommGroup (Test →L[ℂ] Test) :=
  (inferInstance : NormedRing (Test →L[ℂ] Test)).toAddCommGroup

def transition (a ξ t : ℝ) : Test →L[ℂ] Test :=
  PoissonContractionAlgebra.evolution (generator a ξ + 1) t

theorem transition_zero (a ξ : ℝ) : transition a ξ 0 = ContinuousLinearMap.id ℂ Test :=
  PoissonContractionAlgebra.evolution_zero (generator a ξ + 1)

theorem transition_add (a ξ s t : ℝ) :
    transition a ξ (s+t) = (transition a ξ s).comp (transition a ξ t) :=
  PoissonContractionAlgebra.evolution_add (generator a ξ + 1) s t

theorem transition_continuous (a ξ : ℝ) : Continuous (transition a ξ) :=
  PoissonContractionAlgebra.evolution_continuous (generator a ξ + 1)

set_option backward.isDefEq.respectTransparency false in
theorem transition_hasDerivAt (a ξ t : ℝ) :
    HasDerivAt (transition a ξ) ((transition a ξ t).comp (generator a ξ)) t := by
  convert! PoissonContractionAlgebra.evolution_hasDerivAt (generator a ξ + 1) t using 1
  simp only [add_sub_cancel_right]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem transition_average (a ξ : ℝ) (r : ℝ≥0) :
    transition a ξ r = Complex.exp (-(r : ℂ)*MarkedHolomorphicExponential.symbol a ξ) •
      PoissonContractionAlgebra.average (weightedStep a ξ) r := by
  have he := ComplexPoissonCompensation.exp_compensated_average (weightedStep a ξ)
    (ComplexFourthRootWalk.stepTransform a ξ) r
  have hs : (r : ℂ)*(1-ComplexFourthRootWalk.stepTransform a ξ) =
      -(r : ℂ)*MarkedHolomorphicExponential.symbol a ξ := by
    unfold MarkedHolomorphicExponential.symbol
    ring
  simpa only [transition, PoissonContractionAlgebra.evolution, add_sub_cancel_right,
    generator, hs, ContinuousLinearMap.one_def] using he

set_option backward.isDefEq.respectTransparency false in
theorem transition_average_apply (a ξ : ℝ) (r : ℝ≥0) (f : Test) (z : ℂ) :
    transition a ξ r f z = Complex.exp (-(r : ℂ)*MarkedHolomorphicExponential.symbol a ξ) *
      (∫ n : ℕ, ((weightedStep a ξ)^n) f z ∂poissonMeasure r) := by
  rw [transition_average]
  change _ * ((∫ n : ℕ, (weightedStep a ξ)^n ∂poissonMeasure r) f) z = _
  congr 1
  have hi : Integrable (fun n : ℕ => (weightedStep a ξ)^n) (poissonMeasure r) :=
    PoissonEntireAlgebra.powers_integrable (weightedStep a ξ) r
  rw [ContinuousLinearMap.integral_apply hi f]
  exact ((BoundedContinuousFunction.evalCLM ℂ z).integral_comp_comm
    ((ContinuousLinearMap.apply ℂ Test f).integrable_comp hi)).symm

end OperatorDerivativeRewrite.Foundation.ComplexRootTiltedSemigroup
