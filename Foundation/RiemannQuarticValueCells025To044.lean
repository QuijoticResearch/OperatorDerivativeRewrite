import Foundation.RiemannQuarticCellWitnesses

/-! Exact rounded value certificates for cells25,...,44, all three channels. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells025To044
open RiemannQuarticCellWitnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cell_25_0 : check 25 0=true := by
  decide +kernel

theorem cell_25_1 : check 25 1=true := by
  decide +kernel

theorem cell_25_2 : check 25 2=true := by
  decide +kernel

theorem cell_26_0 : check 26 0=true := by
  decide +kernel

theorem cell_26_1 : check 26 1=true := by
  decide +kernel

theorem cell_26_2 : check 26 2=true := by
  decide +kernel

theorem cell_27_0 : check 27 0=true := by
  decide +kernel

theorem cell_27_1 : check 27 1=true := by
  decide +kernel

theorem cell_27_2 : check 27 2=true := by
  decide +kernel

theorem cell_28_0 : check 28 0=true := by
  decide +kernel

theorem cell_28_1 : check 28 1=true := by
  decide +kernel

theorem cell_28_2 : check 28 2=true := by
  decide +kernel

theorem cell_29_0 : check 29 0=true := by
  decide +kernel

theorem cell_29_1 : check 29 1=true := by
  decide +kernel

theorem cell_29_2 : check 29 2=true := by
  decide +kernel

theorem cell_30_0 : check 30 0=true := by
  decide +kernel

theorem cell_30_1 : check 30 1=true := by
  decide +kernel

theorem cell_30_2 : check 30 2=true := by
  decide +kernel

theorem cell_31_0 : check 31 0=true := by
  decide +kernel

theorem cell_31_1 : check 31 1=true := by
  decide +kernel

theorem cell_31_2 : check 31 2=true := by
  decide +kernel

theorem cell_32_0 : check 32 0=true := by
  decide +kernel

theorem cell_32_1 : check 32 1=true := by
  decide +kernel

theorem cell_32_2 : check 32 2=true := by
  decide +kernel

theorem cell_33_0 : check 33 0=true := by
  decide +kernel

theorem cell_33_1 : check 33 1=true := by
  decide +kernel

theorem cell_33_2 : check 33 2=true := by
  decide +kernel

theorem cell_34_0 : check 34 0=true := by
  decide +kernel

theorem cell_34_1 : check 34 1=true := by
  decide +kernel

theorem cell_34_2 : check 34 2=true := by
  decide +kernel

theorem cell_35_0 : check 35 0=true := by
  decide +kernel

theorem cell_35_1 : check 35 1=true := by
  decide +kernel

theorem cell_35_2 : check 35 2=true := by
  decide +kernel

theorem cell_36_0 : check 36 0=true := by
  decide +kernel

theorem cell_36_1 : check 36 1=true := by
  decide +kernel

theorem cell_36_2 : check 36 2=true := by
  decide +kernel

theorem cell_37_0 : check 37 0=true := by
  decide +kernel

theorem cell_37_1 : check 37 1=true := by
  decide +kernel

theorem cell_37_2 : check 37 2=true := by
  decide +kernel

theorem cell_38_0 : check 38 0=true := by
  decide +kernel

theorem cell_38_1 : check 38 1=true := by
  decide +kernel

theorem cell_38_2 : check 38 2=true := by
  decide +kernel

theorem cell_39_0 : check 39 0=true := by
  decide +kernel

theorem cell_39_1 : check 39 1=true := by
  decide +kernel

theorem cell_39_2 : check 39 2=true := by
  decide +kernel

theorem cell_40_0 : check 40 0=true := by
  decide +kernel

theorem cell_40_1 : check 40 1=true := by
  decide +kernel

theorem cell_40_2 : check 40 2=true := by
  decide +kernel

theorem cell_41_0 : check 41 0=true := by
  decide +kernel

theorem cell_41_1 : check 41 1=true := by
  decide +kernel

theorem cell_41_2 : check 41 2=true := by
  decide +kernel

theorem cell_42_0 : check 42 0=true := by
  decide +kernel

theorem cell_42_1 : check 42 1=true := by
  decide +kernel

theorem cell_42_2 : check 42 2=true := by
  decide +kernel

theorem cell_43_0 : check 43 0=true := by
  decide +kernel

theorem cell_43_1 : check 43 1=true := by
  decide +kernel

theorem cell_43_2 : check 43 2=true := by
  decide +kernel

theorem cell_44_0 : check 44 0=true := by
  decide +kernel

theorem cell_44_1 : check 44 1=true := by
  decide +kernel

theorem cell_44_2 : check 44 2=true := by
  decide +kernel

theorem verified_range (j k : ℕ) (hj0 : 25 ≤ j) (hj : j < 45) (hk : k ≤ 2) : check j k=true := by
  interval_cases j <;> interval_cases k
  · exact cell_25_0
  · exact cell_25_1
  · exact cell_25_2
  · exact cell_26_0
  · exact cell_26_1
  · exact cell_26_2
  · exact cell_27_0
  · exact cell_27_1
  · exact cell_27_2
  · exact cell_28_0
  · exact cell_28_1
  · exact cell_28_2
  · exact cell_29_0
  · exact cell_29_1
  · exact cell_29_2
  · exact cell_30_0
  · exact cell_30_1
  · exact cell_30_2
  · exact cell_31_0
  · exact cell_31_1
  · exact cell_31_2
  · exact cell_32_0
  · exact cell_32_1
  · exact cell_32_2
  · exact cell_33_0
  · exact cell_33_1
  · exact cell_33_2
  · exact cell_34_0
  · exact cell_34_1
  · exact cell_34_2
  · exact cell_35_0
  · exact cell_35_1
  · exact cell_35_2
  · exact cell_36_0
  · exact cell_36_1
  · exact cell_36_2
  · exact cell_37_0
  · exact cell_37_1
  · exact cell_37_2
  · exact cell_38_0
  · exact cell_38_1
  · exact cell_38_2
  · exact cell_39_0
  · exact cell_39_1
  · exact cell_39_2
  · exact cell_40_0
  · exact cell_40_1
  · exact cell_40_2
  · exact cell_41_0
  · exact cell_41_1
  · exact cell_41_2
  · exact cell_42_0
  · exact cell_42_1
  · exact cell_42_2
  · exact cell_43_0
  · exact cell_43_1
  · exact cell_43_2
  · exact cell_44_0
  · exact cell_44_1
  · exact cell_44_2

end OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells025To044
