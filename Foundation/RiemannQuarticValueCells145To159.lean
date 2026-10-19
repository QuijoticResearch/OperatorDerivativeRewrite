import Foundation.RiemannQuarticCellWitnesses

/-! Exact rounded value certificates for cells145,...,159, all three channels. -/
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells145To159
open RiemannQuarticCellWitnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem cell_145_0 : check 145 0=true := by
  decide +kernel

theorem cell_145_1 : check 145 1=true := by
  decide +kernel

theorem cell_145_2 : check 145 2=true := by
  decide +kernel

theorem cell_146_0 : check 146 0=true := by
  decide +kernel

theorem cell_146_1 : check 146 1=true := by
  decide +kernel

theorem cell_146_2 : check 146 2=true := by
  decide +kernel

theorem cell_147_0 : check 147 0=true := by
  decide +kernel

theorem cell_147_1 : check 147 1=true := by
  decide +kernel

theorem cell_147_2 : check 147 2=true := by
  decide +kernel

theorem cell_148_0 : check 148 0=true := by
  decide +kernel

theorem cell_148_1 : check 148 1=true := by
  decide +kernel

theorem cell_148_2 : check 148 2=true := by
  decide +kernel

theorem cell_149_0 : check 149 0=true := by
  decide +kernel

theorem cell_149_1 : check 149 1=true := by
  decide +kernel

theorem cell_149_2 : check 149 2=true := by
  decide +kernel

theorem cell_150_0 : check 150 0=true := by
  decide +kernel

theorem cell_150_1 : check 150 1=true := by
  decide +kernel

theorem cell_150_2 : check 150 2=true := by
  decide +kernel

theorem cell_151_0 : check 151 0=true := by
  decide +kernel

theorem cell_151_1 : check 151 1=true := by
  decide +kernel

theorem cell_151_2 : check 151 2=true := by
  decide +kernel

theorem cell_152_0 : check 152 0=true := by
  decide +kernel

theorem cell_152_1 : check 152 1=true := by
  decide +kernel

theorem cell_152_2 : check 152 2=true := by
  decide +kernel

theorem cell_153_0 : check 153 0=true := by
  decide +kernel

theorem cell_153_1 : check 153 1=true := by
  decide +kernel

theorem cell_153_2 : check 153 2=true := by
  decide +kernel

theorem cell_154_0 : check 154 0=true := by
  decide +kernel

theorem cell_154_1 : check 154 1=true := by
  decide +kernel

theorem cell_154_2 : check 154 2=true := by
  decide +kernel

theorem cell_155_0 : check 155 0=true := by
  decide +kernel

theorem cell_155_1 : check 155 1=true := by
  decide +kernel

theorem cell_155_2 : check 155 2=true := by
  decide +kernel

theorem cell_156_0 : check 156 0=true := by
  decide +kernel

theorem cell_156_1 : check 156 1=true := by
  decide +kernel

theorem cell_156_2 : check 156 2=true := by
  decide +kernel

theorem cell_157_0 : check 157 0=true := by
  decide +kernel

theorem cell_157_1 : check 157 1=true := by
  decide +kernel

theorem cell_157_2 : check 157 2=true := by
  decide +kernel

theorem cell_158_0 : check 158 0=true := by
  decide +kernel

theorem cell_158_1 : check 158 1=true := by
  decide +kernel

theorem cell_158_2 : check 158 2=true := by
  decide +kernel

theorem cell_159_0 : check 159 0=true := by
  decide +kernel

theorem cell_159_1 : check 159 1=true := by
  decide +kernel

theorem cell_159_2 : check 159 2=true := by
  decide +kernel

theorem verified_range (j k : ℕ) (hj0 : 145 ≤ j) (hj : j < 160) (hk : k ≤ 2) : check j k=true := by
  interval_cases j <;> interval_cases k
  · exact cell_145_0
  · exact cell_145_1
  · exact cell_145_2
  · exact cell_146_0
  · exact cell_146_1
  · exact cell_146_2
  · exact cell_147_0
  · exact cell_147_1
  · exact cell_147_2
  · exact cell_148_0
  · exact cell_148_1
  · exact cell_148_2
  · exact cell_149_0
  · exact cell_149_1
  · exact cell_149_2
  · exact cell_150_0
  · exact cell_150_1
  · exact cell_150_2
  · exact cell_151_0
  · exact cell_151_1
  · exact cell_151_2
  · exact cell_152_0
  · exact cell_152_1
  · exact cell_152_2
  · exact cell_153_0
  · exact cell_153_1
  · exact cell_153_2
  · exact cell_154_0
  · exact cell_154_1
  · exact cell_154_2
  · exact cell_155_0
  · exact cell_155_1
  · exact cell_155_2
  · exact cell_156_0
  · exact cell_156_1
  · exact cell_156_2
  · exact cell_157_0
  · exact cell_157_1
  · exact cell_157_2
  · exact cell_158_0
  · exact cell_158_1
  · exact cell_158_2
  · exact cell_159_0
  · exact cell_159_1
  · exact cell_159_2

end OperatorDerivativeRewrite.Foundation.RiemannQuarticValueCells145To159
