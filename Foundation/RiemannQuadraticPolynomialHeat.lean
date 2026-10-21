import Foundation.EvenEntireGaussianBudget
import Foundation.RiemannQuadraticZeroProductTails
import Foundation.RiemannQuadraticGaussian

/-! Actual Xi divisor polynomials with uniform Gaussian budgets and genuine heat
convergence. The same real polynomial sequence preserves exact initial disk zeros,
converges compact-uniformly, and converges in every fixed shifted Gaussian L1 law.
Heat averages converge pointwise in the complex spatial variable; no global zero
contraction or spatially uniform heat-limit theorem is asserted here. -/
noncomputable section
open Set Metric Filter Complex Polynomial MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticPolynomialHeat
open RiemannEvenFlow

theorem exists_actual_polynomials_with_gaussian_budget :
    ∃ r : ℝ → ℝ, ∃ P : ℕ → ℝ[X], Tendsto r atTop atTop ∧
      (∀ R : ℝ,1 ≤ R → 2*R<r R ∧ r R<2*R+1) ∧
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval z=0 ↔
        z∈ball (0:ℂ) (r ((n:ℝ)+1)) ∧ flow 1 0 z=0) ∧
      (∀ n : ℕ,((P n).map (algebraMap ℝ ℂ)).eval 0=flow 1 0 0) ∧
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval (-z)=
        ((P n).map (algebraMap ℝ ℂ)).eval z) ∧
      TendstoLocallyUniformly (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z)
        (flow 1 0) atTop ∧
      ∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ z : ℂ,
        ‖((P n).map (algebraMap ℝ ℂ)).eval z‖ ≤ C*Real.exp (ε*‖z‖^2) := by
  exact EvenEntireGaussianBudget.exists_real_polynomials_with_gaussian_budget
    (flow 1 0) (RiemannQuadraticDivisor.flow_analytic 0)
    (RiemannQuadraticDivisor.flow_origin_ne_zero 0) (RiemannEvenEvolution.flow_even 1 0)
    (RiemannEvenEntireGrowth.exists_subquadratic_growth 1 0)
    (RiemannEvenWindowZeros.flow_conj 1 0) 1 RiemannQuadraticZeroProductTails.zero_time_strip

theorem exists_actual_polynomial_heat_approximation :
    ∃ P : ℕ → ℝ[X],
      (∀ n : ℕ,((P n).map (algebraMap ℝ ℂ)).eval 0=flow 1 0 0) ∧
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval z=0 → |z.im| ≤ 1) ∧
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval (-z)=
        ((P n).map (algebraMap ℝ ℂ)).eval z) ∧
      TendstoLocallyUniformly (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z)
        (flow 1 0) atTop ∧
      (∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ z : ℂ,
        ‖((P n).map (algebraMap ℝ ℂ)).eval z‖ ≤ C*Real.exp (ε*‖z‖^2)) ∧
      ∀ s : ℝ≥0,∀ z c : ℂ,
        (∀ n : ℕ,Integrable (fun y : ℝ => ((P n).map (algebraMap ℝ ℂ)).eval
          (z+c*(y:ℂ))) (RiemannQuadraticGaussian.law s)) ∧
        Tendsto (fun n => ∫ y : ℝ,
          ‖((P n).map (algebraMap ℝ ℂ)).eval (z+c*(y:ℂ))-flow 1 0 (z+c*(y:ℂ))‖
            ∂RiemannQuadraticGaussian.law s) atTop (𝓝 0) ∧
        ∀ delta : ℝ,c^2=(delta:ℂ) →
          Tendsto (fun n => ∫ y : ℝ,((P n).map (algebraMap ℝ ℂ)).eval (z+c*(y:ℂ))
            ∂RiemannQuadraticGaussian.law s) atTop (𝓝 (flow 1 (-(s:ℝ)*delta) z)) := by
  obtain ⟨r,P,hr,hrb,hzeros,hzero,heven,hlim,hbudget⟩ :=
    exists_actual_polynomials_with_gaussian_budget
  refine ⟨P,hzero,?_,heven,hlim,hbudget,?_⟩
  · intro n z hz
    exact RiemannQuadraticZeroProductTails.zero_time_strip z ((hzeros n z).mp hz).2
  · intro s z c
    letI : IsGaussian (RiemannQuadraticGaussian.law s) := by
      change IsGaussian (gaussianReal 0 (2*s))
      infer_instance
    have hcont : Continuous (flow 1 0) := by
      have hd : Differentiable ℂ (flow 1 0) :=
        fun w => (RiemannQuadraticDivisor.flow_analytic 0 w (mem_univ _)).differentiableAt
      exact hd.continuous
    have hPcont (n : ℕ) : Continuous (fun w : ℂ => ((P n).map (algebraMap ℝ ℂ)).eval w) :=
      ((P n).map (algebraMap ℝ ℂ)).differentiable.continuous
    obtain ⟨hn,hf,ht⟩ := EvenEntireGaussianBudget.gaussian_integral_limit
      (RiemannQuadraticGaussian.law s)
      (fun n w => ((P n).map (algebraMap ℝ ℂ)).eval w) (flow 1 0)
      hPcont hcont hlim hbudget z c
    refine ⟨hn,EvenEntireGaussianBudget.gaussian_L1_limit
      (RiemannQuadraticGaussian.law s)
      (fun n w => ((P n).map (algebraMap ℝ ℂ)).eval w) (flow 1 0)
      hPcont hcont hlim hbudget z c,?_⟩
    intro delta hc
    have he : (∫ y : ℝ,flow 1 0 (z+c*(y:ℂ)) ∂RiemannQuadraticGaussian.law s)=
        flow 1 (-(s:ℝ)*delta) z := by
      simpa only [zero_sub,neg_mul] using RiemannQuadraticGaussian.shifted_flow_average s 0 delta z c hc
    rw [he] at ht
    exact ht

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticPolynomialHeat
