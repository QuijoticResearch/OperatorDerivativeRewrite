import Foundation.IBMMollifier

/-! The verified mollifier sequence is an exact dilation of one fixed
admissible even profile. This does not assert a continuum-parameter limit. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMMollifierProfileAudit
open IBMMollifier
set_option backward.isDefEq.respectTransparency false

theorem bump_dilation (n : ℕ) (x : ℝ) :
    bump n x = bump 0 (((n : ℝ) + 1) * x) := by
  have hp : (n : ℝ) + 1 ≠ 0 := by positivity
  have hr : (bump n).rOut / (bump n).rIn = 2 := by
    change (2 / ((n : ℝ) + 1)) / (1 / ((n : ℝ) + 1)) = 2
    field_simp
  rw [ContDiffBump.apply,ContDiffBump.apply,hr]
  simp only [bump,Nat.cast_zero,zero_add,div_one,inv_one,sub_zero,one_smul,
    one_div,inv_inv,smul_eq_mul,one_mul]

theorem bump_integral_dilation (n : ℕ) :
    (∫ x, bump n x) = ((n : ℝ) + 1)⁻¹ * ∫ x, bump 0 x := by
  have he : (fun x : ℝ => bump n x) = fun x => bump 0 (((n : ℝ) + 1) * x) :=
    funext (bump_dilation n)
  rw [he,Measure.integral_comp_mul_left]
  simp only [smul_eq_mul,abs_inv,abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)]

theorem kernel_dilation (n : ℕ) (x : ℝ) :
    kernel n x = ((n : ℝ) + 1) * kernel 0 (((n : ℝ) + 1) * x) := by
  change bump n x / (∫ y, bump n y) = ((n : ℝ) + 1) *
    (bump 0 (((n : ℝ) + 1) * x) / (∫ y, bump 0 y))
  rw [bump_dilation,bump_integral_dilation]
  have hp : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem kernel_even (n : ℕ) (x : ℝ) : kernel n (-x) = kernel n x :=
  ContDiffBump.normed_neg (bump n) x

def width (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem width_pos (n : ℕ) : 0 < width n := by unfold width; positivity

theorem width_tendsto_zero : Tendsto width atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Exactly the paper's fixed-profile dilation along epsilon_n=1/(n+1). -/
theorem kernel_fixed_profile (n : ℕ) (x : ℝ) :
    kernel n x = (width n)⁻¹ * kernel 0 (x / width n) := by
  rw [kernel_dilation]
  simp only [width,one_div,inv_inv,div_inv_eq_mul,mul_comm x]

end OperatorDerivativeRewrite.Foundation.IBMMollifierProfileAudit
