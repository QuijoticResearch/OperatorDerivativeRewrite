import Foundation.EvenEntireInverseSquareTails
import Foundation.RiemannQuadraticXiTransfer
import Foundation.RiemannQuadraticPolynomial
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! Actual quadratic Xi zero-product moments and time-zero annular Gaussian bounds.
The width-one time-zero strip follows from Mathlib zeta nonvanishing for Re(s)>1.
No external zero-free improvement, real-root premise or RH assumption is used. -/
noncomputable section
open Set Metric Filter Complex Polynomial
open scoped Topology ComplexConjugate
attribute [local instance] Classical.propDecidable
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticZeroProductTails
open RiemannEvenFlow

theorem zero_time_nonzero_below (z : ℂ) (hz : z.im < -1) : flow 1 0 z≠0 := by
  have hfree : ∀ s : ℂ, (1:ℝ)<s.re → riemannZeta s≠0 :=
    fun s hs => riemannZeta_ne_zero_of_one_lt_re hs
  have hn := RiemannQuadraticXiTransfer.nonzero_of_zeta_half_plane 1 hfree 1 z
    (by linarith : z.im<1-2*(1:ℝ))
  simpa only [RiemannRealOrderFlow.flow_zero_time] using hn

theorem zero_time_strip (z : ℂ) (hz : flow 1 0 z=0) : |z.im|≤1 := by
  rw [abs_le]
  constructor
  · by_contra h
    exact zero_time_nonzero_below z (lt_of_not_ge h) hz
  · by_contra h
    have hc : flow 1 0 (conj z)=0 := by rw [RiemannEvenWindowZeros.flow_conj,hz]; simp
    have hi : (conj z).im < -1 := by
      simp only [Complex.conj_im]
      linarith [lt_of_not_ge h]
    exact zero_time_nonzero_below (conj z) hi hc

open EvenEntirePolynomialApproximation EvenEntireInverseSquareTails

theorem exists_actual_inverse_square_limit (t : ℝ) :
    ∃ r : ℝ → ℝ, Tendsto r atTop atTop ∧
      (∀ R : ℝ,1≤R → 2*R<r R ∧ r R<2*R+1) ∧
      TendstoLocallyUniformly (fun R z => flow 1 t 0*
        (numeratorPoly (flow 1 t) (RiemannQuadraticDivisor.flow_analytic t) (r R)).eval z)
        (flow 1 t) atTop ∧
      Tendsto (fun R => inverseSquareSum (flow 1 t)
        (RiemannQuadraticDivisor.flow_analytic t) (r R)) atTop
        (𝓝 (-deriv (deriv (flow 1 t)) 0/(2*flow 1 t 0))) := by
  exact exists_inverseSquareSum_limit (flow 1 t) (RiemannQuadraticDivisor.flow_analytic t)
    (RiemannQuadraticDivisor.flow_origin_ne_zero t) (RiemannEvenEvolution.flow_even 1 t)
    (RiemannEvenEntireGrowth.exists_subquadratic_growth 1 t)

theorem exists_zero_time_gaussian_product_tails :
    ∃ r : ℝ → ℝ, Tendsto r atTop atTop ∧
      (∀ R : ℝ,1≤R → 2*R<r R ∧ r R<2*R+1) ∧
      TendstoLocallyUniformly (fun R z => flow 1 0 0*
        (numeratorPoly (flow 1 0) (RiemannQuadraticDivisor.flow_analytic 0) (r R)).eval z)
        (flow 1 0) atTop ∧
      Tendsto (fun R => inverseSquareSum (flow 1 0)
        (RiemannQuadraticDivisor.flow_analytic 0) (r R)) atTop
        (𝓝 (-deriv (deriv (flow 1 0)) 0/(2*flow 1 0 0))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℝ, ∀ i j : ℝ, N ≤ i → N ≤ j → r i ≤ r j →
        ∀ z : ℂ,
          ‖∏ a∈halfZeroSupport (flow 1 0) (RiemannQuadraticDivisor.flow_analytic 0) (r j)\
              halfZeroSupport (flow 1 0) (RiemannQuadraticDivisor.flow_analytic 0) (r i),
            (1-z^2/a^2)^(MeromorphicOn.divisor (flow 1 0) (ball 0 (r j)) a).toNat‖≤
            Real.exp (ε*‖z‖^2) := by
  exact exists_gaussian_product_tails (flow 1 0) (RiemannQuadraticDivisor.flow_analytic 0)
    (RiemannQuadraticDivisor.flow_origin_ne_zero 0) (RiemannEvenEvolution.flow_even 1 0)
    (RiemannEvenEntireGrowth.exists_subquadratic_growth 1 0) 1 zero_time_strip


end OperatorDerivativeRewrite.Foundation.RiemannQuadraticZeroProductTails
