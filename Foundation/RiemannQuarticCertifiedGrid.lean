import Foundation.RiemannQuarticGridChecks
import Foundation.RiemannQuarticEvenQuadrature
import Foundation.RiemannQuarticCellWitnesses
import Foundation.RiemannQuarticRealDerivatives

/-! Unconditional error bounds for the full actual four-term integrals.
The three numerical polynomial-value bounds remain separate obligations. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCertifiedGrid
open RiemannQuarticNodeQuadrature RiemannQuarticGridAssembly
open RiemannQuarticRealCertificate RiemannQuarticTaylorJets

theorem uniform_sixteenth (j : ℕ) (hj : j < 160) (u : ℝ)
    (hu : u ∈ Set.Icc (center j-(1/200 : ℝ)) (center j+(1/200 : ℝ)))
    (k : ℕ) (hk : k ≤ 2) :
    |coefficient (realIntegrand 4 k (632083/10000)) 16 u| ≤ (10^22 : ℝ) :=
  cell_sixteenth j hj (RiemannQuarticGridChecks.all_cells j hj) u hu k hk

theorem quadrature_error (k : ℕ) (hk : k ≤ 2) :
    |realQuadrature 4 k (632083/10000)-totalPolynomial k| ≤ (16/10^15 : ℝ) :=
  quadrature_polynomial_error k hk RiemannQuarticGridChecks.all_cells

theorem actual_derivative_error (k : ℕ) (hk : k ≤ 2) :
    ‖iteratedDeriv k (RiemannQuarticFlow.flow 8) ((632083/10000 : ℝ) : ℂ)-
      (totalPolynomial k : ℂ)‖ ≤ (161/10^16 : ℝ) := by
  have he := derivative_four_error k hk (632083/10000)
  rw [finiteDerivative_real 4 k hk (632083/10000)] at he
  have ht := dist_triangle
    (iteratedDeriv k (RiemannQuarticFlow.flow 8) ((632083/10000 : ℝ) : ℂ))
    (realQuadrature 4 k (632083/10000) : ℂ) (totalPolynomial k : ℂ)
  simp only [dist_eq_norm] at ht
  have hr : ‖(realQuadrature 4 k (632083/10000) : ℂ)-(totalPolynomial k : ℂ)‖=
      |realQuadrature 4 k (632083/10000)-totalPolynomial k| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hr] at ht
  calc
    _ ≤ _+_ := ht
    _ ≤ (1/10^16 : ℝ)+(16/10^15 : ℝ) := add_le_add he (quadrature_error k hk)
    _ = _ := by norm_num

theorem negative_of_polynomial_bounds
    (h0 : totalPolynomial 0 ≤ -(164/10^12 : ℝ))
    (h1 : |totalPolynomial 1| ≤ (38/10^14 : ℝ))
    (h2 : totalPolynomial 2 ≤ -(1455/10^13 : ℝ)) :
    realLaguerre (632083/10000) < -(2/10^20 : ℝ) :=
  negative_Laguerre_of_polynomial_bounds RiemannQuarticGridChecks.all_cells h0 h1 h2

theorem negative_of_cell_checks
    (hc : ∀ j < 160, ∀ k ≤ 2, RiemannQuarticCellWitnesses.check j k=true) :
    realLaguerre (632083/10000) < -(2/10^20 : ℝ) := by
  have hp := RiemannQuarticCellWitnesses.polynomial_bounds hc
  exact negative_of_polynomial_bounds hp.1 hp.2.1 hp.2.2

theorem real_negative_of_cell_checks
    (hc : ∀ j < 160, ∀ k ≤ 2, RiemannQuarticCellWitnesses.check j k=true) :
    (deriv (RiemannQuarticReality.realFlow 8) (632083/10000))^2-
      RiemannQuarticReality.realFlow 8 (632083/10000)*
        iteratedDeriv 2 (RiemannQuarticReality.realFlow 8) (632083/10000) <
      -(2/10^20 : ℝ) := by
  rw [← RiemannQuarticRealDerivatives.realLaguerre_eq]
  exact negative_of_cell_checks hc

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCertifiedGrid
