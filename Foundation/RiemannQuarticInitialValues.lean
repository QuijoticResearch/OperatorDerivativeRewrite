import Foundation.RiemannQuarticCellWitnesses

/-! Exact value certificates for the first five cells, all three channels.
The remaining155 cells are separate verification obligations. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticInitialValues
open RiemannQuarticCellWitnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cell_0_0 : check 0 0=true := by
  decide +kernel

theorem cell_0_1 : check 0 1=true := by
  decide +kernel

theorem cell_0_2 : check 0 2=true := by
  decide +kernel

theorem cell_1_0 : check 1 0=true := by
  decide +kernel

theorem cell_1_1 : check 1 1=true := by
  decide +kernel

theorem cell_1_2 : check 1 2=true := by
  decide +kernel

theorem cell_2_0 : check 2 0=true := by
  decide +kernel

theorem cell_2_1 : check 2 1=true := by
  decide +kernel

theorem cell_2_2 : check 2 2=true := by
  decide +kernel

theorem cell_3_0 : check 3 0=true := by
  decide +kernel

theorem cell_3_1 : check 3 1=true := by
  decide +kernel

theorem cell_3_2 : check 3 2=true := by
  decide +kernel

theorem cell_4_0 : check 4 0=true := by
  decide +kernel

theorem cell_4_1 : check 4 1=true := by
  decide +kernel

theorem cell_4_2 : check 4 2=true := by
  decide +kernel

theorem first_five (j k : ℕ) (hj : j < 5) (hk : k ≤ 2) : check j k=true := by
  interval_cases j <;> interval_cases k
  · exact cell_0_0
  · exact cell_0_1
  · exact cell_0_2
  · exact cell_1_0
  · exact cell_1_1
  · exact cell_1_2
  · exact cell_2_0
  · exact cell_2_1
  · exact cell_2_2
  · exact cell_3_0
  · exact cell_3_1
  · exact cell_3_2
  · exact cell_4_0
  · exact cell_4_1
  · exact cell_4_2

end OperatorDerivativeRewrite.Foundation.RiemannQuarticInitialValues
