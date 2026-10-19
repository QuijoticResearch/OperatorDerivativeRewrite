import Foundation.RiemannQuarticCellWitnesses

/-! Exact rounded value certificates for cells85,...,104, all three channels. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells085To104
open RiemannQuarticCellWitnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cell_85_0 : check 85 0=true := by
  decide +kernel

theorem cell_85_1 : check 85 1=true := by
  decide +kernel

theorem cell_85_2 : check 85 2=true := by
  decide +kernel

theorem cell_86_0 : check 86 0=true := by
  decide +kernel

theorem cell_86_1 : check 86 1=true := by
  decide +kernel

theorem cell_86_2 : check 86 2=true := by
  decide +kernel

theorem cell_87_0 : check 87 0=true := by
  decide +kernel

theorem cell_87_1 : check 87 1=true := by
  decide +kernel

theorem cell_87_2 : check 87 2=true := by
  decide +kernel

theorem cell_88_0 : check 88 0=true := by
  decide +kernel

theorem cell_88_1 : check 88 1=true := by
  decide +kernel

theorem cell_88_2 : check 88 2=true := by
  decide +kernel

theorem cell_89_0 : check 89 0=true := by
  decide +kernel

theorem cell_89_1 : check 89 1=true := by
  decide +kernel

theorem cell_89_2 : check 89 2=true := by
  decide +kernel

theorem cell_90_0 : check 90 0=true := by
  decide +kernel

theorem cell_90_1 : check 90 1=true := by
  decide +kernel

theorem cell_90_2 : check 90 2=true := by
  decide +kernel

theorem cell_91_0 : check 91 0=true := by
  decide +kernel

theorem cell_91_1 : check 91 1=true := by
  decide +kernel

theorem cell_91_2 : check 91 2=true := by
  decide +kernel

theorem cell_92_0 : check 92 0=true := by
  decide +kernel

theorem cell_92_1 : check 92 1=true := by
  decide +kernel

theorem cell_92_2 : check 92 2=true := by
  decide +kernel

theorem cell_93_0 : check 93 0=true := by
  decide +kernel

theorem cell_93_1 : check 93 1=true := by
  decide +kernel

theorem cell_93_2 : check 93 2=true := by
  decide +kernel

theorem cell_94_0 : check 94 0=true := by
  decide +kernel

theorem cell_94_1 : check 94 1=true := by
  decide +kernel

theorem cell_94_2 : check 94 2=true := by
  decide +kernel

theorem cell_95_0 : check 95 0=true := by
  decide +kernel

theorem cell_95_1 : check 95 1=true := by
  decide +kernel

theorem cell_95_2 : check 95 2=true := by
  decide +kernel

theorem cell_96_0 : check 96 0=true := by
  decide +kernel

theorem cell_96_1 : check 96 1=true := by
  decide +kernel

theorem cell_96_2 : check 96 2=true := by
  decide +kernel

theorem cell_97_0 : check 97 0=true := by
  decide +kernel

theorem cell_97_1 : check 97 1=true := by
  decide +kernel

theorem cell_97_2 : check 97 2=true := by
  decide +kernel

theorem cell_98_0 : check 98 0=true := by
  decide +kernel

theorem cell_98_1 : check 98 1=true := by
  decide +kernel

theorem cell_98_2 : check 98 2=true := by
  decide +kernel

theorem cell_99_0 : check 99 0=true := by
  decide +kernel

theorem cell_99_1 : check 99 1=true := by
  decide +kernel

theorem cell_99_2 : check 99 2=true := by
  decide +kernel

theorem cell_100_0 : check 100 0=true := by
  decide +kernel

theorem cell_100_1 : check 100 1=true := by
  decide +kernel

theorem cell_100_2 : check 100 2=true := by
  decide +kernel

theorem cell_101_0 : check 101 0=true := by
  decide +kernel

theorem cell_101_1 : check 101 1=true := by
  decide +kernel

theorem cell_101_2 : check 101 2=true := by
  decide +kernel

theorem cell_102_0 : check 102 0=true := by
  decide +kernel

theorem cell_102_1 : check 102 1=true := by
  decide +kernel

theorem cell_102_2 : check 102 2=true := by
  decide +kernel

theorem cell_103_0 : check 103 0=true := by
  decide +kernel

theorem cell_103_1 : check 103 1=true := by
  decide +kernel

theorem cell_103_2 : check 103 2=true := by
  decide +kernel

theorem cell_104_0 : check 104 0=true := by
  decide +kernel

theorem cell_104_1 : check 104 1=true := by
  decide +kernel

theorem cell_104_2 : check 104 2=true := by
  decide +kernel

theorem verified_range (j k : ℕ) (hj0 : 85 ≤ j) (hj : j < 105) (hk : k ≤ 2) : check j k=true := by
  interval_cases j <;> interval_cases k
  · exact cell_85_0
  · exact cell_85_1
  · exact cell_85_2
  · exact cell_86_0
  · exact cell_86_1
  · exact cell_86_2
  · exact cell_87_0
  · exact cell_87_1
  · exact cell_87_2
  · exact cell_88_0
  · exact cell_88_1
  · exact cell_88_2
  · exact cell_89_0
  · exact cell_89_1
  · exact cell_89_2
  · exact cell_90_0
  · exact cell_90_1
  · exact cell_90_2
  · exact cell_91_0
  · exact cell_91_1
  · exact cell_91_2
  · exact cell_92_0
  · exact cell_92_1
  · exact cell_92_2
  · exact cell_93_0
  · exact cell_93_1
  · exact cell_93_2
  · exact cell_94_0
  · exact cell_94_1
  · exact cell_94_2
  · exact cell_95_0
  · exact cell_95_1
  · exact cell_95_2
  · exact cell_96_0
  · exact cell_96_1
  · exact cell_96_2
  · exact cell_97_0
  · exact cell_97_1
  · exact cell_97_2
  · exact cell_98_0
  · exact cell_98_1
  · exact cell_98_2
  · exact cell_99_0
  · exact cell_99_1
  · exact cell_99_2
  · exact cell_100_0
  · exact cell_100_1
  · exact cell_100_2
  · exact cell_101_0
  · exact cell_101_1
  · exact cell_101_2
  · exact cell_102_0
  · exact cell_102_1
  · exact cell_102_2
  · exact cell_103_0
  · exact cell_103_1
  · exact cell_103_2
  · exact cell_104_0
  · exact cell_104_1
  · exact cell_104_2

end OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells085To104
