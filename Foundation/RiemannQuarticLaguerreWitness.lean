import Foundation.RiemannQuarticCertifiedGrid
import Foundation.RiemannQuarticInitialValues
import Foundation.RiemannQuarticValueCells005To024
import Foundation.RiemannQuarticValueCells025To044
import Foundation.RiemannQuarticValueCells045To064
import Foundation.RiemannQuarticValueCells065To084
import Foundation.RiemannQuarticValueCells085To104
import Foundation.RiemannQuarticValueCells105To124
import Foundation.RiemannQuarticValueCells125To144
import Foundation.RiemannQuarticValueCells145To159
/-! Actual t=8 Laguerre inequality witness from all exact cell value checks.
This proves the explicit inequality for actual infinite-flow derivatives;
it does not encode Laguerre-Polya membership or infer an eventual threshold. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticLaguerreWitness
open RiemannQuarticCellWitnesses

theorem all_value_checks (j : ℕ) (hj : j < 160) (k : ℕ) (hk : k ≤ 2) : check j k=true := by
  by_cases h5 : j < 5
  · exact RiemannQuarticInitialValues.first_five j k h5 hk
  by_cases h25 : j < 25
  · exact RiemannQuarticValueCells005To024.verified_range j k (by omega) h25 hk
  by_cases h45 : j < 45
  · exact RiemannQuarticValueCells025To044.verified_range j k (by omega) h45 hk
  by_cases h65 : j < 65
  · exact RiemannQuarticValueCells045To064.verified_range j k (by omega) h65 hk
  by_cases h85 : j < 85
  · exact RiemannQuarticValueCells065To084.verified_range j k (by omega) h85 hk
  by_cases h105 : j < 105
  · exact RiemannQuarticValueCells085To104.verified_range j k (by omega) h105 hk
  by_cases h125 : j < 125
  · exact RiemannQuarticValueCells105To124.verified_range j k (by omega) h125 hk
  by_cases h145 : j < 145
  · exact RiemannQuarticValueCells125To144.verified_range j k (by omega) h145 hk
  exact RiemannQuarticValueCells145To159.verified_range j k (by omega) hj hk

theorem actual_laguerre_negative :
    RiemannQuarticRealCertificate.realLaguerre (632083/10000) < -(2/10^20 : ℝ) :=
  RiemannQuarticCertifiedGrid.negative_of_cell_checks all_value_checks

theorem actual_real_derivative_negative :
    (deriv (RiemannQuarticReality.realFlow 8) (632083/10000))^2-
      RiemannQuarticReality.realFlow 8 (632083/10000)*
        iteratedDeriv 2 (RiemannQuarticReality.realFlow 8) (632083/10000) < -(2/10^20 : ℝ) :=
  RiemannQuarticCertifiedGrid.real_negative_of_cell_checks all_value_checks

theorem laguerre_inequality_fails :
    ¬ ∀ x : ℝ, 0 ≤ (deriv (RiemannQuarticReality.realFlow 8) x)^2-
      RiemannQuarticReality.realFlow 8 x*iteratedDeriv 2 (RiemannQuarticReality.realFlow 8) x := by
  intro h
  have hn := actual_real_derivative_negative
  have hp := h (632083/10000)
  norm_num at hn
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticLaguerreWitness
