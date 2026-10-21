import Foundation.ComplexGaussianPolynomialTransport
import Foundation.RiemannQuadraticUniformHeat

/-! The actual Xi polynomial approximants evolve by the already verified
order-two polynomial operator. The whole-complex-plane local-uniform limit is
the actual forward Xi flow. Global finite-polynomial zero control remains a
separate obligation; no new threshold or RH implication is asserted. -/
noncomputable section
open Set Filter Complex Polynomial MeasureTheory
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticOperatorApproximation
open RiemannEvenFlow PureOrderPolynomialTransport

theorem exists_actual_uniform_operator_approximation :
    ∃ P : ℕ → ℝ[X],
      (∀ n : ℕ,((P n).map (algebraMap ℝ ℂ)).eval 0=flow 1 0 0) ∧
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval z=0 → |z.im| ≤ 1) ∧
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval (-z)=
        ((P n).map (algebraMap ℝ ℂ)).eval z) ∧
      TendstoLocallyUniformly (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z)
        (flow 1 0) atTop ∧
      (∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ z : ℂ,
        ‖((P n).map (algebraMap ℝ ℂ)).eval z‖ ≤ C*Real.exp (ε*‖z‖^2)) ∧
      ∀ s : ℝ≥0,TendstoLocallyUniformly
        (fun n z => ((transport 2 (-(s:ℝ)) (P n)).map (algebraMap ℝ ℂ)).eval z)
        (flow 1 (s:ℝ)) atTop := by
  obtain ⟨P,h0,hstrip,heven,hlim,hbudget,hint,hheat⟩ :=
    RiemannQuadraticUniformHeat.exists_actual_uniform_heat_approximation
  refine ⟨P,h0,hstrip,heven,hlim,hbudget,?_⟩
  intro s
  have hh := hheat s I (-1) (by simpa using Complex.I_sq)
  simpa only [mul_neg_one,neg_neg,
    ComplexGaussianPolynomialTransport.imaginary_gaussian_transport] using hh

theorem exists_actual_forward_operator_approximation :
    ∃ P : ℕ → ℝ[X],
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval z=0 → |z.im| ≤ 1) ∧
      ∀ s : ℝ≥0,TendstoLocallyUniformly
        (fun n z => ((transport 2 (-(s:ℝ)) (P n)).map (algebraMap ℝ ℂ)).eval z)
        (flow 1 (s:ℝ)) atTop := by
  obtain ⟨P,h0,hstrip,heven,hlim,hbudget,hheat⟩ := exists_actual_uniform_operator_approximation
  exact ⟨P,hstrip,hheat⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticOperatorApproximation
