import Foundation.GaussianCompactHeat
import Foundation.RiemannQuadraticPolynomialHeat

/-! Actual Xi polynomial Gaussian heat averages converge locally uniformly in
space. A single real even polynomial sequence has the verified initial zero strip,
normalization and Gaussian domain. The result supplies the limit topology, but
does not assert global finite-polynomial zero contraction or a new threshold. -/
noncomputable section
open Set Metric Filter Complex Polynomial MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticUniformHeat
open RiemannEvenFlow

theorem exists_actual_uniform_heat_approximation :
    ∃ P : ℕ → ℝ[X],
      (∀ n : ℕ,((P n).map (algebraMap ℝ ℂ)).eval 0=flow 1 0 0) ∧
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval z=0 → |z.im| ≤ 1) ∧
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval (-z)=
        ((P n).map (algebraMap ℝ ℂ)).eval z) ∧
      TendstoLocallyUniformly (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z)
        (flow 1 0) atTop ∧
      (∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ z : ℂ,
        ‖((P n).map (algebraMap ℝ ℂ)).eval z‖ ≤ C*Real.exp (ε*‖z‖^2)) ∧
      (∀ s : ℝ≥0,∀ z c : ℂ,∀ n : ℕ,
        Integrable (fun y : ℝ => ((P n).map (algebraMap ℝ ℂ)).eval (z+c*(y:ℂ)))
          (RiemannQuadraticGaussian.law s)) ∧
      ∀ s : ℝ≥0,∀ c : ℂ,∀ delta : ℝ,c^2=(delta:ℂ) →
        TendstoLocallyUniformly
          (fun n z => ∫ y : ℝ,((P n).map (algebraMap ℝ ℂ)).eval (z+c*(y:ℂ))
            ∂RiemannQuadraticGaussian.law s)
          (flow 1 (-(s:ℝ)*delta)) atTop := by
  obtain ⟨P,hzero,hstrip,heven,hlim,hbudget,hheat⟩ :=
    RiemannQuadraticPolynomialHeat.exists_actual_polynomial_heat_approximation
  refine ⟨P,hzero,hstrip,heven,hlim,hbudget,?_,?_⟩
  · intro s z c n
    exact (hheat s z c).1 n
  · intro s c delta hc
    letI : IsGaussian (RiemannQuadraticGaussian.law s) := by
      change IsGaussian (gaussianReal 0 (2*s))
      infer_instance
    have hcont : Continuous (flow 1 0) := by
      have hd : Differentiable ℂ (flow 1 0) :=
        fun w => (RiemannQuadraticDivisor.flow_analytic 0 w (mem_univ _)).differentiableAt
      exact hd.continuous
    have hPcont (n : ℕ) : Continuous (fun w : ℂ => ((P n).map (algebraMap ℝ ℂ)).eval w) :=
      ((P n).map (algebraMap ℝ ℂ)).differentiable.continuous
    have hu := GaussianCompactHeat.gaussian_integral_locally_uniform
      (RiemannQuadraticGaussian.law s)
      (fun n w => ((P n).map (algebraMap ℝ ℂ)).eval w) (flow 1 0)
      hPcont hcont hlim hbudget c
    have he : (fun z => ∫ y : ℝ,flow 1 0 (z+c*(y:ℂ)) ∂RiemannQuadraticGaussian.law s)=
        flow 1 (-(s:ℝ)*delta) := by
      funext z
      simpa only [zero_sub,neg_mul] using RiemannQuadraticGaussian.shifted_flow_average s 0 delta z c hc
    rw [he] at hu
    exact hu

theorem exists_actual_forward_uniform_heat :
    ∃ P : ℕ → ℝ[X],
      (∀ n : ℕ,∀ z : ℂ,((P n).map (algebraMap ℝ ℂ)).eval z=0 → |z.im| ≤ 1) ∧
      ∀ s : ℝ≥0,TendstoLocallyUniformly
        (fun n z => ∫ y : ℝ,((P n).map (algebraMap ℝ ℂ)).eval (z+I*(y:ℂ))
          ∂RiemannQuadraticGaussian.law s) (flow 1 (s:ℝ)) atTop := by
  obtain ⟨P,h0,hstrip,heven,hlim,hbudget,hint,hheat⟩ := exists_actual_uniform_heat_approximation
  refine ⟨P,hstrip,?_⟩
  intro s
  simpa only [mul_neg_one,neg_neg] using hheat s I (-1) (by simpa using Complex.I_sq)

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticUniformHeat
