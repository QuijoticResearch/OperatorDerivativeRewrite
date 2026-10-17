import Foundation.FractionalPredictionObstruction
import Foundation.GaussianWickConditionalProjection

/-! Initial-time diagnostic for the precise unified-manuscript remainder exponent. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalUnifiedRemainderDiagnostic
open InfiniteGaussian FractionalGaussianProcess FractionalPredictionObstruction
open GaussianWickConditionalProjection
set_option backward.isDefEq.respectTransparency false
variable (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)

theorem initial_sourceSpan : sourceSpan (pastDirections H hH0 hH1 0) = ⊥ := by
  apply le_antisymm _ bot_le
  refine (Submodule.span ℝ (Set.range (pastDirections H hH0 hH1 0))).topologicalClosure_minimal ?_ ?_
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    rw [pastDirections_zero]
    exact Submodule.zero_mem _
  · exact isClosed_singleton

theorem initial_sourceProjection (u : CoefficientSpace) :
    sourceProjection (pastDirections H hH0 hH1 0) u = 0 := by
  have hm := (sourceSpan (pastDirections H hH0 hH1 0)).starProjection_apply_mem u
  change sourceProjection (pastDirections H hH0 hH1 0) u ∈
    sourceSpan (pastDirections H hH0 hH1 0) at hm
  rw [initial_sourceSpan] at hm
  exact hm

/-- For the terminal linear target, the manuscript's initial projected derivative
pairing is this scalar. -/
def initialLeading (t : ℝ≥0) : ℝ :=
  inner ℝ (sourceProjection (pastDirections H hH0 hH1 0) (direction H hH0 hH1 1))
    (direction H hH0 hH1 t - direction H hH0 hH1 0)

theorem initialLeading_zero (t : ℝ≥0) : initialLeading H hH0 hH1 t = 0 := by
  simp only [initialLeading, initial_sourceProjection, inner_zero_left]

def initialRemainder (t : ℝ≥0) : GaussianL2 :=
  forecast H hH0 hH1 t - forecast H hH0 hH1 0 - initialLeading H hH0 hH1 t • gaussianOne

theorem claimed_exponent_gt (hpos : 0 < H) : 2*H < min (4*H) (2*H+1) := by
  exact lt_min (by linarith) (by linarith)

/-- Every proposed big-O constant and every positive initial neighbourhood fail
for the actual conditional prediction remainder. -/
theorem no_claimed_remainder_bound (C δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ≥0, 0 < t ∧ (t:ℝ) < δ ∧ t ≤ 1 ∧
      C * (t:ℝ)^(min (4*H) (2*H+1)) < ‖initialRemainder H hH0 hH1 t‖^2 := by
  simpa only [initialRemainder, initialLeading_zero, zero_smul, sub_zero] using
    no_higher_prediction_increment_bound H hH0 hH1 (min (4*H) (2*H+1))
      (claimed_exponent_gt H hH0) C δ hδ

end OperatorDerivativeRewrite.Foundation.FractionalUnifiedRemainderDiagnostic
