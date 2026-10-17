import Foundation.StickyBoundaryGeneratorCore
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A necessary maximum-principle check at the sticky boundary, using actual
one-sided derivatives. Full dissipativity and range conditions remain separate. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyBoundaryMaximumPrinciple
open StickyC2MartingaleProblem StickyBoundaryGeneratorCore
set_option backward.isDefEq.respectTransparency false

theorem right_derivative_nonpositive {F : ℝ → ℝ} {r : ℝ}
    (hF : HasDerivWithinAt F r (Ici 0) 0) (hmax : ∀ x, F x ≤ F 0) : r ≤ 0 := by
  have ht : Tendsto (slope F 0) (𝓝[>] (0 : ℝ)) (𝓝 r) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp hF.Ioi_of_Ici
  apply le_of_tendsto_of_tendsto ht tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  rw [slope_def_field, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmax x)) hx.le

theorem left_derivative_nonnegative {F : ℝ → ℝ} {l : ℝ}
    (hF : HasDerivWithinAt F l (Iic 0) 0) (hmax : ∀ x, F x ≤ F 0) : 0 ≤ l := by
  have ht : Tendsto (slope F 0) (𝓝[<] (0 : ℝ)) (𝓝 l) :=
    (hasDerivWithinAt_iff_tendsto_slope' (s := Iio (0 : ℝ)) (x := 0) (by simp)).mp hF.Iio_of_Iic
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  change x < 0 at hx
  rw [slope_def_field, sub_zero]
  exact div_nonneg_of_nonpos (sub_nonpos.mpr (hmax x)) hx.le

theorem boundary_maximum_principle (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (κ : ℝ≥0) (hκ : 0 < κ) (hmax : ∀ x, boundaryTest f κ x ≤ boundaryTest f κ 0) :
    candidateGenerator f 0 ≤ 0 := by
  have hr := right_derivative_nonpositive (right_derivative f hf κ) hmax
  have hl := left_derivative_nonnegative (left_derivative f hf κ) hmax
  have hj := generator_boundary_jump f κ
  have hp : 0 < (κ : ℝ) := hκ
  nlinarith

end OperatorDerivativeRewrite.Foundation.StickyBoundaryMaximumPrinciple
