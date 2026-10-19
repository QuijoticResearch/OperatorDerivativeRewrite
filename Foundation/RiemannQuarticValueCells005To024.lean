import Foundation.RiemannQuarticCellWitnesses

/-! Exact rounded value certificates for cells5,...,24, all three channels. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells005To024
open RiemannQuarticCellWitnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cell_5_0 : check 5 0=true := by
  decide +kernel

theorem cell_5_1 : check 5 1=true := by
  decide +kernel

theorem cell_5_2 : check 5 2=true := by
  decide +kernel

theorem cell_6_0 : check 6 0=true := by
  decide +kernel

theorem cell_6_1 : check 6 1=true := by
  decide +kernel

theorem cell_6_2 : check 6 2=true := by
  decide +kernel

theorem cell_7_0 : check 7 0=true := by
  decide +kernel

theorem cell_7_1 : check 7 1=true := by
  decide +kernel

theorem cell_7_2 : check 7 2=true := by
  decide +kernel

theorem cell_8_0 : check 8 0=true := by
  decide +kernel

theorem cell_8_1 : check 8 1=true := by
  decide +kernel

theorem cell_8_2 : check 8 2=true := by
  decide +kernel

theorem cell_9_0 : check 9 0=true := by
  decide +kernel

theorem cell_9_1 : check 9 1=true := by
  decide +kernel

theorem cell_9_2 : check 9 2=true := by
  decide +kernel

theorem cell_10_0 : check 10 0=true := by
  decide +kernel

theorem cell_10_1 : check 10 1=true := by
  decide +kernel

theorem cell_10_2 : check 10 2=true := by
  decide +kernel

theorem cell_11_0 : check 11 0=true := by
  decide +kernel

theorem cell_11_1 : check 11 1=true := by
  decide +kernel

theorem cell_11_2 : check 11 2=true := by
  decide +kernel

theorem cell_12_0 : check 12 0=true := by
  decide +kernel

theorem cell_12_1 : check 12 1=true := by
  decide +kernel

theorem cell_12_2 : check 12 2=true := by
  decide +kernel

theorem cell_13_0 : check 13 0=true := by
  decide +kernel

theorem cell_13_1 : check 13 1=true := by
  decide +kernel

theorem cell_13_2 : check 13 2=true := by
  decide +kernel

theorem cell_14_0 : check 14 0=true := by
  decide +kernel

theorem cell_14_1 : check 14 1=true := by
  decide +kernel

theorem cell_14_2 : check 14 2=true := by
  decide +kernel

theorem cell_15_0 : check 15 0=true := by
  decide +kernel

theorem cell_15_1 : check 15 1=true := by
  decide +kernel

theorem cell_15_2 : check 15 2=true := by
  decide +kernel

theorem cell_16_0 : check 16 0=true := by
  decide +kernel

theorem cell_16_1 : check 16 1=true := by
  decide +kernel

theorem cell_16_2 : check 16 2=true := by
  decide +kernel

theorem cell_17_0 : check 17 0=true := by
  decide +kernel

theorem cell_17_1 : check 17 1=true := by
  decide +kernel

theorem cell_17_2 : check 17 2=true := by
  decide +kernel

theorem cell_18_0 : check 18 0=true := by
  decide +kernel

theorem cell_18_1 : check 18 1=true := by
  decide +kernel

theorem cell_18_2 : check 18 2=true := by
  decide +kernel

theorem cell_19_0 : check 19 0=true := by
  decide +kernel

theorem cell_19_1 : check 19 1=true := by
  decide +kernel

theorem cell_19_2 : check 19 2=true := by
  decide +kernel

theorem cell_20_0 : check 20 0=true := by
  decide +kernel

theorem cell_20_1 : check 20 1=true := by
  decide +kernel

theorem cell_20_2 : check 20 2=true := by
  decide +kernel

theorem cell_21_0 : check 21 0=true := by
  decide +kernel

theorem cell_21_1 : check 21 1=true := by
  decide +kernel

theorem cell_21_2 : check 21 2=true := by
  decide +kernel

theorem cell_22_0 : check 22 0=true := by
  decide +kernel

theorem cell_22_1 : check 22 1=true := by
  decide +kernel

theorem cell_22_2 : check 22 2=true := by
  decide +kernel

theorem cell_23_0 : check 23 0=true := by
  decide +kernel

theorem cell_23_1 : check 23 1=true := by
  decide +kernel

theorem cell_23_2 : check 23 2=true := by
  decide +kernel

theorem cell_24_0 : check 24 0=true := by
  decide +kernel

theorem cell_24_1 : check 24 1=true := by
  decide +kernel

theorem cell_24_2 : check 24 2=true := by
  decide +kernel

theorem verified_range (j k : ℕ) (hj0 : 5 ≤ j) (hj : j < 25) (hk : k ≤ 2) : check j k=true := by
  interval_cases j <;> interval_cases k
  · exact cell_5_0
  · exact cell_5_1
  · exact cell_5_2
  · exact cell_6_0
  · exact cell_6_1
  · exact cell_6_2
  · exact cell_7_0
  · exact cell_7_1
  · exact cell_7_2
  · exact cell_8_0
  · exact cell_8_1
  · exact cell_8_2
  · exact cell_9_0
  · exact cell_9_1
  · exact cell_9_2
  · exact cell_10_0
  · exact cell_10_1
  · exact cell_10_2
  · exact cell_11_0
  · exact cell_11_1
  · exact cell_11_2
  · exact cell_12_0
  · exact cell_12_1
  · exact cell_12_2
  · exact cell_13_0
  · exact cell_13_1
  · exact cell_13_2
  · exact cell_14_0
  · exact cell_14_1
  · exact cell_14_2
  · exact cell_15_0
  · exact cell_15_1
  · exact cell_15_2
  · exact cell_16_0
  · exact cell_16_1
  · exact cell_16_2
  · exact cell_17_0
  · exact cell_17_1
  · exact cell_17_2
  · exact cell_18_0
  · exact cell_18_1
  · exact cell_18_2
  · exact cell_19_0
  · exact cell_19_1
  · exact cell_19_2
  · exact cell_20_0
  · exact cell_20_1
  · exact cell_20_2
  · exact cell_21_0
  · exact cell_21_1
  · exact cell_21_2
  · exact cell_22_0
  · exact cell_22_1
  · exact cell_22_2
  · exact cell_23_0
  · exact cell_23_1
  · exact cell_23_2
  · exact cell_24_0
  · exact cell_24_1
  · exact cell_24_2

end OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells005To024
