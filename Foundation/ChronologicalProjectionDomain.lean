import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! A simplex restriction targets ordered fields, not symmetric cube tensors. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.ChronologicalProjectionDomain

def symmetric (Y : ℝ × ℝ → ℝ) : Prop := ∀ s t, Y (s, t) = Y (t, s)

def orderedProjection (Y : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.1 < z.2 then Y z else 0

theorem nonzero_restriction_not_symmetric (Y : ℝ × ℝ → ℝ) (s t : ℝ)
    (hst : s < t) (hY : Y (s, t) ≠ 0) : ¬ symmetric (orderedProjection Y) := by
  intro h
  have he := h s t
  simp only [orderedProjection, hst, ↓reduceIte, not_lt.mpr hst.le] at he
  exact hY he

theorem symmetric_gaussian (s t : ℝ) :
    Real.exp (-(s^2+t^2)) = Real.exp (-(t^2+s^2)) := by rw [add_comm]

theorem gaussian_projection_failure :
    symmetric (fun z : ℝ × ℝ => Real.exp (-(z.1^2+z.2^2))) ∧
      ¬ symmetric (orderedProjection (fun z : ℝ × ℝ => Real.exp (-(z.1^2+z.2^2)))) := by
  constructor
  · exact symmetric_gaussian
  · exact nonzero_restriction_not_symmetric _ 0 1 (by norm_num) (Real.exp_ne_zero _)

theorem all_times_cutoff (s t u : ℝ) : (s ≤ u ∧ t ≤ u) ↔ max s t ≤ u := max_le_iff.symm

theorem minimum_cutoff_failure :
    min (0:ℝ) 1 ≤ (1/2:ℝ) ∧ ¬ ((0:ℝ) ≤ (1/2:ℝ) ∧ (1:ℝ) ≤ (1/2:ℝ)) := by norm_num

end OperatorDerivativeRewrite.Foundation.ChronologicalProjectionDomain
