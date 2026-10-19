import Foundation.RiemannQuarticCellWitnesses

/-! Exact rounded value certificates for cells125,...,144, all three channels. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells125To144
open RiemannQuarticCellWitnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cell_125_0 : check 125 0=true := by
  decide +kernel

theorem cell_125_1 : check 125 1=true := by
  decide +kernel

theorem cell_125_2 : check 125 2=true := by
  decide +kernel

theorem cell_126_0 : check 126 0=true := by
  decide +kernel

theorem cell_126_1 : check 126 1=true := by
  decide +kernel

theorem cell_126_2 : check 126 2=true := by
  decide +kernel

theorem cell_127_0 : check 127 0=true := by
  decide +kernel

theorem cell_127_1 : check 127 1=true := by
  decide +kernel

theorem cell_127_2 : check 127 2=true := by
  decide +kernel

theorem cell_128_0 : check 128 0=true := by
  decide +kernel

theorem cell_128_1 : check 128 1=true := by
  decide +kernel

theorem cell_128_2 : check 128 2=true := by
  decide +kernel

theorem cell_129_0 : check 129 0=true := by
  decide +kernel

theorem cell_129_1 : check 129 1=true := by
  decide +kernel

theorem cell_129_2 : check 129 2=true := by
  decide +kernel

theorem cell_130_0 : check 130 0=true := by
  decide +kernel

theorem cell_130_1 : check 130 1=true := by
  decide +kernel

theorem cell_130_2 : check 130 2=true := by
  decide +kernel

theorem cell_131_0 : check 131 0=true := by
  decide +kernel

theorem cell_131_1 : check 131 1=true := by
  decide +kernel

theorem cell_131_2 : check 131 2=true := by
  decide +kernel

theorem cell_132_0 : check 132 0=true := by
  decide +kernel

theorem cell_132_1 : check 132 1=true := by
  decide +kernel

theorem cell_132_2 : check 132 2=true := by
  decide +kernel

theorem cell_133_0 : check 133 0=true := by
  decide +kernel

theorem cell_133_1 : check 133 1=true := by
  decide +kernel

theorem cell_133_2 : check 133 2=true := by
  decide +kernel

theorem cell_134_0 : check 134 0=true := by
  decide +kernel

theorem cell_134_1 : check 134 1=true := by
  decide +kernel

theorem cell_134_2 : check 134 2=true := by
  decide +kernel

theorem cell_135_0 : check 135 0=true := by
  decide +kernel

theorem cell_135_1 : check 135 1=true := by
  decide +kernel

theorem cell_135_2 : check 135 2=true := by
  decide +kernel

theorem cell_136_0 : check 136 0=true := by
  decide +kernel

theorem cell_136_1 : check 136 1=true := by
  decide +kernel

theorem cell_136_2 : check 136 2=true := by
  decide +kernel

theorem cell_137_0 : check 137 0=true := by
  decide +kernel

theorem cell_137_1 : check 137 1=true := by
  decide +kernel

theorem cell_137_2 : check 137 2=true := by
  decide +kernel

theorem cell_138_0 : check 138 0=true := by
  decide +kernel

theorem cell_138_1 : check 138 1=true := by
  decide +kernel

theorem cell_138_2 : check 138 2=true := by
  decide +kernel

theorem cell_139_0 : check 139 0=true := by
  decide +kernel

theorem cell_139_1 : check 139 1=true := by
  decide +kernel

theorem cell_139_2 : check 139 2=true := by
  decide +kernel

theorem cell_140_0 : check 140 0=true := by
  decide +kernel

theorem cell_140_1 : check 140 1=true := by
  decide +kernel

theorem cell_140_2 : check 140 2=true := by
  decide +kernel

theorem cell_141_0 : check 141 0=true := by
  decide +kernel

theorem cell_141_1 : check 141 1=true := by
  decide +kernel

theorem cell_141_2 : check 141 2=true := by
  decide +kernel

theorem cell_142_0 : check 142 0=true := by
  decide +kernel

theorem cell_142_1 : check 142 1=true := by
  decide +kernel

theorem cell_142_2 : check 142 2=true := by
  decide +kernel

theorem cell_143_0 : check 143 0=true := by
  decide +kernel

theorem cell_143_1 : check 143 1=true := by
  decide +kernel

theorem cell_143_2 : check 143 2=true := by
  decide +kernel

theorem cell_144_0 : check 144 0=true := by
  decide +kernel

theorem cell_144_1 : check 144 1=true := by
  decide +kernel

theorem cell_144_2 : check 144 2=true := by
  decide +kernel

theorem verified_range (j k : ℕ) (hj0 : 125 ≤ j) (hj : j < 145) (hk : k ≤ 2) : check j k=true := by
  interval_cases j <;> interval_cases k
  · exact cell_125_0
  · exact cell_125_1
  · exact cell_125_2
  · exact cell_126_0
  · exact cell_126_1
  · exact cell_126_2
  · exact cell_127_0
  · exact cell_127_1
  · exact cell_127_2
  · exact cell_128_0
  · exact cell_128_1
  · exact cell_128_2
  · exact cell_129_0
  · exact cell_129_1
  · exact cell_129_2
  · exact cell_130_0
  · exact cell_130_1
  · exact cell_130_2
  · exact cell_131_0
  · exact cell_131_1
  · exact cell_131_2
  · exact cell_132_0
  · exact cell_132_1
  · exact cell_132_2
  · exact cell_133_0
  · exact cell_133_1
  · exact cell_133_2
  · exact cell_134_0
  · exact cell_134_1
  · exact cell_134_2
  · exact cell_135_0
  · exact cell_135_1
  · exact cell_135_2
  · exact cell_136_0
  · exact cell_136_1
  · exact cell_136_2
  · exact cell_137_0
  · exact cell_137_1
  · exact cell_137_2
  · exact cell_138_0
  · exact cell_138_1
  · exact cell_138_2
  · exact cell_139_0
  · exact cell_139_1
  · exact cell_139_2
  · exact cell_140_0
  · exact cell_140_1
  · exact cell_140_2
  · exact cell_141_0
  · exact cell_141_1
  · exact cell_141_2
  · exact cell_142_0
  · exact cell_142_1
  · exact cell_142_2
  · exact cell_143_0
  · exact cell_143_1
  · exact cell_143_2
  · exact cell_144_0
  · exact cell_144_1
  · exact cell_144_2

end OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells125To144
