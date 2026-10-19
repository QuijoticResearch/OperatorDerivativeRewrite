import Foundation.RiemannQuarticCellWitnesses

/-! Exact rounded value certificates for cells105,...,124, all three channels. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells105To124
open RiemannQuarticCellWitnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cell_105_0 : check 105 0=true := by
  decide +kernel

theorem cell_105_1 : check 105 1=true := by
  decide +kernel

theorem cell_105_2 : check 105 2=true := by
  decide +kernel

theorem cell_106_0 : check 106 0=true := by
  decide +kernel

theorem cell_106_1 : check 106 1=true := by
  decide +kernel

theorem cell_106_2 : check 106 2=true := by
  decide +kernel

theorem cell_107_0 : check 107 0=true := by
  decide +kernel

theorem cell_107_1 : check 107 1=true := by
  decide +kernel

theorem cell_107_2 : check 107 2=true := by
  decide +kernel

theorem cell_108_0 : check 108 0=true := by
  decide +kernel

theorem cell_108_1 : check 108 1=true := by
  decide +kernel

theorem cell_108_2 : check 108 2=true := by
  decide +kernel

theorem cell_109_0 : check 109 0=true := by
  decide +kernel

theorem cell_109_1 : check 109 1=true := by
  decide +kernel

theorem cell_109_2 : check 109 2=true := by
  decide +kernel

theorem cell_110_0 : check 110 0=true := by
  decide +kernel

theorem cell_110_1 : check 110 1=true := by
  decide +kernel

theorem cell_110_2 : check 110 2=true := by
  decide +kernel

theorem cell_111_0 : check 111 0=true := by
  decide +kernel

theorem cell_111_1 : check 111 1=true := by
  decide +kernel

theorem cell_111_2 : check 111 2=true := by
  decide +kernel

theorem cell_112_0 : check 112 0=true := by
  decide +kernel

theorem cell_112_1 : check 112 1=true := by
  decide +kernel

theorem cell_112_2 : check 112 2=true := by
  decide +kernel

theorem cell_113_0 : check 113 0=true := by
  decide +kernel

theorem cell_113_1 : check 113 1=true := by
  decide +kernel

theorem cell_113_2 : check 113 2=true := by
  decide +kernel

theorem cell_114_0 : check 114 0=true := by
  decide +kernel

theorem cell_114_1 : check 114 1=true := by
  decide +kernel

theorem cell_114_2 : check 114 2=true := by
  decide +kernel

theorem cell_115_0 : check 115 0=true := by
  decide +kernel

theorem cell_115_1 : check 115 1=true := by
  decide +kernel

theorem cell_115_2 : check 115 2=true := by
  decide +kernel

theorem cell_116_0 : check 116 0=true := by
  decide +kernel

theorem cell_116_1 : check 116 1=true := by
  decide +kernel

theorem cell_116_2 : check 116 2=true := by
  decide +kernel

theorem cell_117_0 : check 117 0=true := by
  decide +kernel

theorem cell_117_1 : check 117 1=true := by
  decide +kernel

theorem cell_117_2 : check 117 2=true := by
  decide +kernel

theorem cell_118_0 : check 118 0=true := by
  decide +kernel

theorem cell_118_1 : check 118 1=true := by
  decide +kernel

theorem cell_118_2 : check 118 2=true := by
  decide +kernel

theorem cell_119_0 : check 119 0=true := by
  decide +kernel

theorem cell_119_1 : check 119 1=true := by
  decide +kernel

theorem cell_119_2 : check 119 2=true := by
  decide +kernel

theorem cell_120_0 : check 120 0=true := by
  decide +kernel

theorem cell_120_1 : check 120 1=true := by
  decide +kernel

theorem cell_120_2 : check 120 2=true := by
  decide +kernel

theorem cell_121_0 : check 121 0=true := by
  decide +kernel

theorem cell_121_1 : check 121 1=true := by
  decide +kernel

theorem cell_121_2 : check 121 2=true := by
  decide +kernel

theorem cell_122_0 : check 122 0=true := by
  decide +kernel

theorem cell_122_1 : check 122 1=true := by
  decide +kernel

theorem cell_122_2 : check 122 2=true := by
  decide +kernel

theorem cell_123_0 : check 123 0=true := by
  decide +kernel

theorem cell_123_1 : check 123 1=true := by
  decide +kernel

theorem cell_123_2 : check 123 2=true := by
  decide +kernel

theorem cell_124_0 : check 124 0=true := by
  decide +kernel

theorem cell_124_1 : check 124 1=true := by
  decide +kernel

theorem cell_124_2 : check 124 2=true := by
  decide +kernel

theorem verified_range (j k : ℕ) (hj0 : 105 ≤ j) (hj : j < 125) (hk : k ≤ 2) : check j k=true := by
  interval_cases j <;> interval_cases k
  · exact cell_105_0
  · exact cell_105_1
  · exact cell_105_2
  · exact cell_106_0
  · exact cell_106_1
  · exact cell_106_2
  · exact cell_107_0
  · exact cell_107_1
  · exact cell_107_2
  · exact cell_108_0
  · exact cell_108_1
  · exact cell_108_2
  · exact cell_109_0
  · exact cell_109_1
  · exact cell_109_2
  · exact cell_110_0
  · exact cell_110_1
  · exact cell_110_2
  · exact cell_111_0
  · exact cell_111_1
  · exact cell_111_2
  · exact cell_112_0
  · exact cell_112_1
  · exact cell_112_2
  · exact cell_113_0
  · exact cell_113_1
  · exact cell_113_2
  · exact cell_114_0
  · exact cell_114_1
  · exact cell_114_2
  · exact cell_115_0
  · exact cell_115_1
  · exact cell_115_2
  · exact cell_116_0
  · exact cell_116_1
  · exact cell_116_2
  · exact cell_117_0
  · exact cell_117_1
  · exact cell_117_2
  · exact cell_118_0
  · exact cell_118_1
  · exact cell_118_2
  · exact cell_119_0
  · exact cell_119_1
  · exact cell_119_2
  · exact cell_120_0
  · exact cell_120_1
  · exact cell_120_2
  · exact cell_121_0
  · exact cell_121_1
  · exact cell_121_2
  · exact cell_122_0
  · exact cell_122_1
  · exact cell_122_2
  · exact cell_123_0
  · exact cell_123_1
  · exact cell_123_2
  · exact cell_124_0
  · exact cell_124_1
  · exact cell_124_2

end OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells105To124
