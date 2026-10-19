import Foundation.RiemannQuarticCellWitnesses

/-! Exact rounded value certificates for cells45,...,64, all three channels. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells045To064
open RiemannQuarticCellWitnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cell_45_0 : check 45 0=true := by
  decide +kernel

theorem cell_45_1 : check 45 1=true := by
  decide +kernel

theorem cell_45_2 : check 45 2=true := by
  decide +kernel

theorem cell_46_0 : check 46 0=true := by
  decide +kernel

theorem cell_46_1 : check 46 1=true := by
  decide +kernel

theorem cell_46_2 : check 46 2=true := by
  decide +kernel

theorem cell_47_0 : check 47 0=true := by
  decide +kernel

theorem cell_47_1 : check 47 1=true := by
  decide +kernel

theorem cell_47_2 : check 47 2=true := by
  decide +kernel

theorem cell_48_0 : check 48 0=true := by
  decide +kernel

theorem cell_48_1 : check 48 1=true := by
  decide +kernel

theorem cell_48_2 : check 48 2=true := by
  decide +kernel

theorem cell_49_0 : check 49 0=true := by
  decide +kernel

theorem cell_49_1 : check 49 1=true := by
  decide +kernel

theorem cell_49_2 : check 49 2=true := by
  decide +kernel

theorem cell_50_0 : check 50 0=true := by
  decide +kernel

theorem cell_50_1 : check 50 1=true := by
  decide +kernel

theorem cell_50_2 : check 50 2=true := by
  decide +kernel

theorem cell_51_0 : check 51 0=true := by
  decide +kernel

theorem cell_51_1 : check 51 1=true := by
  decide +kernel

theorem cell_51_2 : check 51 2=true := by
  decide +kernel

theorem cell_52_0 : check 52 0=true := by
  decide +kernel

theorem cell_52_1 : check 52 1=true := by
  decide +kernel

theorem cell_52_2 : check 52 2=true := by
  decide +kernel

theorem cell_53_0 : check 53 0=true := by
  decide +kernel

theorem cell_53_1 : check 53 1=true := by
  decide +kernel

theorem cell_53_2 : check 53 2=true := by
  decide +kernel

theorem cell_54_0 : check 54 0=true := by
  decide +kernel

theorem cell_54_1 : check 54 1=true := by
  decide +kernel

theorem cell_54_2 : check 54 2=true := by
  decide +kernel

theorem cell_55_0 : check 55 0=true := by
  decide +kernel

theorem cell_55_1 : check 55 1=true := by
  decide +kernel

theorem cell_55_2 : check 55 2=true := by
  decide +kernel

theorem cell_56_0 : check 56 0=true := by
  decide +kernel

theorem cell_56_1 : check 56 1=true := by
  decide +kernel

theorem cell_56_2 : check 56 2=true := by
  decide +kernel

theorem cell_57_0 : check 57 0=true := by
  decide +kernel

theorem cell_57_1 : check 57 1=true := by
  decide +kernel

theorem cell_57_2 : check 57 2=true := by
  decide +kernel

theorem cell_58_0 : check 58 0=true := by
  decide +kernel

theorem cell_58_1 : check 58 1=true := by
  decide +kernel

theorem cell_58_2 : check 58 2=true := by
  decide +kernel

theorem cell_59_0 : check 59 0=true := by
  decide +kernel

theorem cell_59_1 : check 59 1=true := by
  decide +kernel

theorem cell_59_2 : check 59 2=true := by
  decide +kernel

theorem cell_60_0 : check 60 0=true := by
  decide +kernel

theorem cell_60_1 : check 60 1=true := by
  decide +kernel

theorem cell_60_2 : check 60 2=true := by
  decide +kernel

theorem cell_61_0 : check 61 0=true := by
  decide +kernel

theorem cell_61_1 : check 61 1=true := by
  decide +kernel

theorem cell_61_2 : check 61 2=true := by
  decide +kernel

theorem cell_62_0 : check 62 0=true := by
  decide +kernel

theorem cell_62_1 : check 62 1=true := by
  decide +kernel

theorem cell_62_2 : check 62 2=true := by
  decide +kernel

theorem cell_63_0 : check 63 0=true := by
  decide +kernel

theorem cell_63_1 : check 63 1=true := by
  decide +kernel

theorem cell_63_2 : check 63 2=true := by
  decide +kernel

theorem cell_64_0 : check 64 0=true := by
  decide +kernel

theorem cell_64_1 : check 64 1=true := by
  decide +kernel

theorem cell_64_2 : check 64 2=true := by
  decide +kernel

theorem verified_range (j k : ℕ) (hj0 : 45 ≤ j) (hj : j < 65) (hk : k ≤ 2) : check j k=true := by
  interval_cases j <;> interval_cases k
  · exact cell_45_0
  · exact cell_45_1
  · exact cell_45_2
  · exact cell_46_0
  · exact cell_46_1
  · exact cell_46_2
  · exact cell_47_0
  · exact cell_47_1
  · exact cell_47_2
  · exact cell_48_0
  · exact cell_48_1
  · exact cell_48_2
  · exact cell_49_0
  · exact cell_49_1
  · exact cell_49_2
  · exact cell_50_0
  · exact cell_50_1
  · exact cell_50_2
  · exact cell_51_0
  · exact cell_51_1
  · exact cell_51_2
  · exact cell_52_0
  · exact cell_52_1
  · exact cell_52_2
  · exact cell_53_0
  · exact cell_53_1
  · exact cell_53_2
  · exact cell_54_0
  · exact cell_54_1
  · exact cell_54_2
  · exact cell_55_0
  · exact cell_55_1
  · exact cell_55_2
  · exact cell_56_0
  · exact cell_56_1
  · exact cell_56_2
  · exact cell_57_0
  · exact cell_57_1
  · exact cell_57_2
  · exact cell_58_0
  · exact cell_58_1
  · exact cell_58_2
  · exact cell_59_0
  · exact cell_59_1
  · exact cell_59_2
  · exact cell_60_0
  · exact cell_60_1
  · exact cell_60_2
  · exact cell_61_0
  · exact cell_61_1
  · exact cell_61_2
  · exact cell_62_0
  · exact cell_62_1
  · exact cell_62_2
  · exact cell_63_0
  · exact cell_63_1
  · exact cell_63_2
  · exact cell_64_0
  · exact cell_64_1
  · exact cell_64_2

end OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells045To064
