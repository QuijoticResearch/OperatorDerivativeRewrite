import Foundation.EvenEntirePolynomialApproximation
import Foundation.RiemannQuadraticCanonical

/-! Genuine even real polynomial approximants to the actual quadratic Xi flow.
Their zeros are exactly the actual flow zeros in expanding disks. No assertion
of real-rootedness, Gaussian heat convergence or global strip contraction. -/
noncomputable section
open Set Metric Filter Complex Polynomial
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticPolynomial
open RiemannEvenFlow

theorem exists_actual_polynomial_approximation (t : ℝ) :
    ∃ r : ℝ → ℝ, ∃ P : ℕ → ℝ[X],
      Tendsto r atTop atTop ∧
      (∀ R : ℝ, 1≤R → 2*R<r R ∧ r R<2*R+1) ∧
      (∀ n : ℕ, ∀ z : ℂ, ((P n).map (algebraMap ℝ ℂ)).eval z=0 ↔
        z∈ball (0:ℂ) (r ((n:ℝ)+1)) ∧ flow 1 t z=0) ∧
      (∀ n : ℕ, ((P n).map (algebraMap ℝ ℂ)).eval 0=flow 1 t 0) ∧
      (∀ n : ℕ, ∀ z : ℂ, ((P n).map (algebraMap ℝ ℂ)).eval (-z)=
        ((P n).map (algebraMap ℝ ℂ)).eval z) ∧
      TendstoLocallyUniformly (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z)
        (flow 1 t) atTop := by
  exact EvenEntirePolynomialApproximation.exists_real_polynomial_approximation
    (flow 1 t) (RiemannQuadraticDivisor.flow_analytic t)
    (RiemannQuadraticDivisor.flow_origin_ne_zero t) (RiemannEvenEvolution.flow_even 1 t)
    (RiemannEvenEntireGrowth.exists_subquadratic_growth 1 t)
    (RiemannEvenWindowZeros.flow_conj 1 t)

theorem exists_actual_strip_polynomial_approximation (t b : ℝ)
    (hstrip : ∀ z : ℂ, flow 1 t z=0 → |z.im|≤b) :
    ∃ P : ℕ → ℝ[X],
      (∀ n : ℕ, ∀ z : ℂ, ((P n).map (algebraMap ℝ ℂ)).eval z=0 → |z.im|≤b) ∧
      (∀ n : ℕ, ((P n).map (algebraMap ℝ ℂ)).eval 0=flow 1 t 0) ∧
      TendstoLocallyUniformly (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z)
        (flow 1 t) atTop := by
  obtain ⟨r,P,hr,hrb,hzeros,hzero,heven,hlim⟩ := exists_actual_polynomial_approximation t
  exact ⟨P,fun n z hz => hstrip z ((hzeros n z).mp hz).2,hzero,hlim⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticPolynomial
