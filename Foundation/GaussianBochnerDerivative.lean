import Foundation.BochnerClosedOperator
import Foundation.InfiniteGaussianKernel
import Foundation.GaussianTimeSensitivity

/-! The closed Gaussian derivative in Bochner time L2.
This is an independently specified fiberwise domain, not a core closure.
Product-space equivalence and predictable graph density are separate obligations. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianBochnerDerivative
open InfiniteGaussian BochnerClosedOperator

abbrev TimeScalarL2 := Lp GaussianL2 2 (volume : Measure ℝ)
abbrev TimeDerivativeL2 := Lp GaussianVectorL2 2 (volume : Measure ℝ)

def fieldDerivative : TimeScalarL2 →ₗ.[ℝ] TimeDerivativeL2 :=
  lift volume closedCylindricalDerivative

theorem fieldDerivative_graph_iff (u : TimeScalarL2) (v : TimeDerivativeL2) :
    (u, v) ∈ fieldDerivative.graph ↔
      ∀ᵐ t ∂(volume : Measure ℝ), (u t, v t) ∈ closedCylindricalDerivative.graph :=
  mem_lift_graph_iff _ _ _ _

theorem fieldDerivative_domain_iff (u : TimeScalarL2) :
    u ∈ fieldDerivative.domain ↔ ∃ v : TimeDerivativeL2,
      ∀ᵐ t ∂(volume : Measure ℝ), (u t, v t) ∈ closedCylindricalDerivative.graph :=
  mem_lift_domain_iff _ _ _

theorem fieldDerivative_isClosed : fieldDerivative.IsClosed :=
  lift_isClosed _ _ closedCylindricalDerivative_isClosed

theorem fieldDerivative_dense_domain : Dense (fieldDerivative.domain : Set TimeScalarL2) :=
  lift_dense_domain _ _ closedCylindricalDerivative_dense_domain

theorem polynomial_tensor_graph (a : Lp ℝ 2 (volume : Measure ℝ))
    (f : polynomialCylindricalDomain) :
    (tensor volume a (f : GaussianL2), tensor volume a (polynomialDerivative f)) ∈
      fieldDerivative.graph :=
  tensor_graph _ _ _ _ _ (LinearPMap.le_graph_of_le cylindricalDerivative.le_closure
    (cylindricalDerivative.mem_graph f))

/-- Constant-in-probability fields obtained from an actual scalar L2 time profile. -/
def deterministicField (a : Lp ℝ 2 (volume : Measure ℝ)) : TimeScalarL2 :=
  (ContinuousLinearMap.toSpanSingleton ℝ gaussianOne).compLp a

theorem deterministicField_coeFn (a : Lp ℝ 2 (volume : Measure ℝ)) :
    deterministicField a =ᵐ[volume] fun t => a t • gaussianOne :=
  (ContinuousLinearMap.toSpanSingleton ℝ gaussianOne).coeFn_compLp a

/-- Fiberwise vanishing gives a SINGLE measurable square-integrable deterministic profile. -/
theorem fieldDerivative_zero_iff_deterministic (u : TimeScalarL2) :
    (u, (0 : TimeDerivativeL2)) ∈ fieldDerivative.graph ↔
      ∃ a : Lp ℝ 2 (volume : Measure ℝ), u = deterministicField a := by
  rw [fieldDerivative_graph_iff]
  constructor
  · intro hu
    let a := (innerSL ℝ gaussianOne).compLp u
    refine ⟨a, ?_⟩
    apply Lp.ext
    filter_upwards [hu, Lp.coeFn_zero GaussianVectorL2 2 (volume : Measure ℝ),
      (innerSL ℝ gaussianOne).coeFn_compLp u, deterministicField_coeFn a]
      with t ht h0 ha hd
    rw [h0] at ht
    have he := (closedDerivative_zero_iff_vacuum (u t)).mp ht
    change a t = inner ℝ gaussianOne (u t) at ha
    rw [hd, ha]
    exact he
  · rintro ⟨a, rfl⟩
    filter_upwards [deterministicField_coeFn a,
      Lp.coeFn_zero GaussianVectorL2 2 (volume : Measure ℝ)] with t ht h0
    rw [ht, h0]
    exact closedDerivative_constant_graph (a t)

end OperatorDerivativeRewrite.Foundation.GaussianBochnerDerivative
