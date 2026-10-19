import Foundation.RiemannQuarticCellWitnesses

/-! Exact rounded value certificates for cells65,...,84, all three channels. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells065To084
open RiemannQuarticCellWitnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cell_65_0 : check 65 0=true := by
  decide +kernel

theorem cell_65_1 : check 65 1=true := by
  decide +kernel

theorem cell_65_2 : check 65 2=true := by
  decide +kernel

theorem cell_66_0 : check 66 0=true := by
  decide +kernel

theorem cell_66_1 : check 66 1=true := by
  decide +kernel

theorem cell_66_2 : check 66 2=true := by
  decide +kernel

theorem cell_67_0 : check 67 0=true := by
  decide +kernel

theorem cell_67_1 : check 67 1=true := by
  decide +kernel

theorem cell_67_2 : check 67 2=true := by
  decide +kernel

theorem cell_68_0 : check 68 0=true := by
  decide +kernel

theorem cell_68_1 : check 68 1=true := by
  decide +kernel

theorem cell_68_2 : check 68 2=true := by
  decide +kernel

theorem cell_69_0 : check 69 0=true := by
  decide +kernel

theorem cell_69_1 : check 69 1=true := by
  decide +kernel

theorem cell_69_2 : check 69 2=true := by
  decide +kernel

theorem cell_70_0 : check 70 0=true := by
  decide +kernel

theorem cell_70_1 : check 70 1=true := by
  decide +kernel

theorem cell_70_2 : check 70 2=true := by
  decide +kernel

theorem cell_71_0 : check 71 0=true := by
  decide +kernel

theorem cell_71_1 : check 71 1=true := by
  decide +kernel

theorem cell_71_2 : check 71 2=true := by
  decide +kernel

theorem cell_72_0 : check 72 0=true := by
  decide +kernel

theorem cell_72_1 : check 72 1=true := by
  decide +kernel

theorem cell_72_2 : check 72 2=true := by
  decide +kernel

theorem cell_73_0 : check 73 0=true := by
  decide +kernel

theorem cell_73_1 : check 73 1=true := by
  decide +kernel

theorem cell_73_2 : check 73 2=true := by
  decide +kernel

theorem cell_74_0 : check 74 0=true := by
  decide +kernel

theorem cell_74_1 : check 74 1=true := by
  decide +kernel

theorem cell_74_2 : check 74 2=true := by
  decide +kernel

theorem cell_75_0 : check 75 0=true := by
  decide +kernel

theorem cell_75_1 : check 75 1=true := by
  decide +kernel

theorem cell_75_2 : check 75 2=true := by
  decide +kernel

theorem cell_76_0 : check 76 0=true := by
  decide +kernel

theorem cell_76_1 : check 76 1=true := by
  decide +kernel

theorem cell_76_2 : check 76 2=true := by
  decide +kernel

theorem cell_77_0 : check 77 0=true := by
  decide +kernel

theorem cell_77_1 : check 77 1=true := by
  decide +kernel

theorem cell_77_2 : check 77 2=true := by
  decide +kernel

theorem cell_78_0 : check 78 0=true := by
  decide +kernel

theorem cell_78_1 : check 78 1=true := by
  decide +kernel

theorem cell_78_2 : check 78 2=true := by
  decide +kernel

theorem cell_79_0 : check 79 0=true := by
  decide +kernel

theorem cell_79_1 : check 79 1=true := by
  decide +kernel

theorem cell_79_2 : check 79 2=true := by
  decide +kernel

theorem cell_80_0 : check 80 0=true := by
  decide +kernel

theorem cell_80_1 : check 80 1=true := by
  decide +kernel

theorem cell_80_2 : check 80 2=true := by
  decide +kernel

theorem cell_81_0 : check 81 0=true := by
  decide +kernel

theorem cell_81_1 : check 81 1=true := by
  decide +kernel

theorem cell_81_2 : check 81 2=true := by
  decide +kernel

theorem cell_82_0 : check 82 0=true := by
  decide +kernel

theorem cell_82_1 : check 82 1=true := by
  decide +kernel

theorem cell_82_2 : check 82 2=true := by
  decide +kernel

theorem cell_83_0 : check 83 0=true := by
  decide +kernel

theorem cell_83_1 : check 83 1=true := by
  decide +kernel

theorem cell_83_2 : check 83 2=true := by
  decide +kernel

theorem cell_84_0 : check 84 0=true := by
  decide +kernel

theorem cell_84_1 : check 84 1=true := by
  decide +kernel

theorem cell_84_2 : check 84 2=true := by
  decide +kernel

theorem verified_range (j k : ℕ) (hj0 : 65 ≤ j) (hj : j < 85) (hk : k ≤ 2) : check j k=true := by
  interval_cases j <;> interval_cases k
  · exact cell_65_0
  · exact cell_65_1
  · exact cell_65_2
  · exact cell_66_0
  · exact cell_66_1
  · exact cell_66_2
  · exact cell_67_0
  · exact cell_67_1
  · exact cell_67_2
  · exact cell_68_0
  · exact cell_68_1
  · exact cell_68_2
  · exact cell_69_0
  · exact cell_69_1
  · exact cell_69_2
  · exact cell_70_0
  · exact cell_70_1
  · exact cell_70_2
  · exact cell_71_0
  · exact cell_71_1
  · exact cell_71_2
  · exact cell_72_0
  · exact cell_72_1
  · exact cell_72_2
  · exact cell_73_0
  · exact cell_73_1
  · exact cell_73_2
  · exact cell_74_0
  · exact cell_74_1
  · exact cell_74_2
  · exact cell_75_0
  · exact cell_75_1
  · exact cell_75_2
  · exact cell_76_0
  · exact cell_76_1
  · exact cell_76_2
  · exact cell_77_0
  · exact cell_77_1
  · exact cell_77_2
  · exact cell_78_0
  · exact cell_78_1
  · exact cell_78_2
  · exact cell_79_0
  · exact cell_79_1
  · exact cell_79_2
  · exact cell_80_0
  · exact cell_80_1
  · exact cell_80_2
  · exact cell_81_0
  · exact cell_81_1
  · exact cell_81_2
  · exact cell_82_0
  · exact cell_82_1
  · exact cell_82_2
  · exact cell_83_0
  · exact cell_83_1
  · exact cell_83_2
  · exact cell_84_0
  · exact cell_84_1
  · exact cell_84_2

end OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells065To084
