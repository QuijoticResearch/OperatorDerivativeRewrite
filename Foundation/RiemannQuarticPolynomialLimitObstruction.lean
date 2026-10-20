import Foundation.RealRootedLaguerreLimit
import Foundation.RiemannQuarticLaguerreWitness
import Foundation.RiemannQuarticRealDerivatives

/-! The actual quartic transform at t = 8 cannot be a locally uniform
complex limit of real polynomials that split over the reals. This closes
the necessary Laguerre-inequality bridge for this precise approximation
property; it does not supply the converse entire-function classification. -/
noncomputable section
open Polynomial Filter Set Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticPolynomialLimitObstruction
open RiemannQuarticFlow RiemannQuarticReality RiemannQuarticRealDerivatives

theorem real_jet_laguerre_nonneg_of_polynomial_limit_on
    (t : ℝ) (P : ℕ → ℝ[X]) (U : Set ℂ) (hU : IsOpen U)
    (hP : ∀ n, (P n).Splits)
    (hlim : TendstoLocallyUniformlyOn
      (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow t) atTop U)
    (x : ℝ) (hx : (x : ℂ) ∈ U) :
    0 ≤ (deriv (realFlow t) x)^2 - realFlow t x * iteratedDeriv 2 (realFlow t) x := by
  have h := RealRootedLaguerreLimit.laguerre_nonneg_of_locally_uniform_split_polynomials_on
    P (flow t) U hU hP hlim x hx
  have h0 := realFlow_complex_derivative_re 0 t x
  have h1 := realFlow_complex_derivative_re 1 t x
  have h2 := realFlow_complex_derivative_re 2 t x
  simp only [iteratedDeriv_zero] at h0
  simp only [iteratedDeriv_one] at h1
  have h2' : iteratedDeriv 2 (realFlow t) x = (deriv (deriv (flow t)) (x : ℂ)).re := by
    simpa only [show 2 = 1 + 1 by rfl, iteratedDeriv_succ,
      iteratedDeriv_one, iteratedDeriv_zero] using h2
  rwa [← h0, ← h1, ← h2'] at h

theorem actual_time_eight_not_polynomial_limit_on
    (U : Set ℂ) (hU : IsOpen U) (hx : ((632083/10000 : ℝ) : ℂ) ∈ U) :
    ¬ ∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
      TendstoLocallyUniformlyOn
        (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow 8) atTop U := by
  rintro ⟨P,hP,hlim⟩
  have h := real_jet_laguerre_nonneg_of_polynomial_limit_on
    8 P U hU hP hlim (632083/10000) hx
  have hn := RiemannQuarticLaguerreWitness.actual_real_derivative_negative
  linarith

theorem actual_time_eight_not_polynomial_limit :
    ¬ ∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
      TendstoLocallyUniformlyOn
        (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow 8) atTop univ :=
  actual_time_eight_not_polynomial_limit_on univ isOpen_univ (mem_univ _)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticPolynomialLimitObstruction
