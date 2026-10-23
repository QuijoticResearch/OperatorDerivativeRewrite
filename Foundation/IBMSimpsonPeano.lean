import Foundation.IBMThirdPeano

/-! Signed spatial Simpson quadrature and its compact C4 primitive error.
The quadrature is defined from the one-form, independently of a primitive. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.IBMSimpsonPeano

def simpson (g : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (y - x) / 6 * (g x + 4 * g ((x + y) / 2) + g y)

theorem error_identity (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (x y : ℝ) :
    simpson (deriv f) x y - (f y - f x) =
      (y - x) / 6 * (4 * IBMThirdPeano.remainder (deriv f) x ((x + y) / 2) +
        IBMThirdPeano.remainder (deriv f) x y) - IBMFourthTaylor.remainder f x y := by
  have h := IBMFourthPeano.increment_identity f hf x y
  unfold simpson IBMThirdPeano.remainder IBMThirdPeano.polynomial
  simp only [← iteratedDeriv_succ']
  simp only [IBMFourthPeano.lower, iteratedDeriv_one] at h
  linear_combination -h

theorem compact_error_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 4 f) (R ε : ℝ)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y : ℝ, |x| ≤ R → |y| ≤ R → |y - x| < δ →
      |simpson (deriv f) x y - (f y - f x)| ≤ ε * |y - x|^4 := by
  have hg : ContDiff ℝ 3 (deriv f) := hf.deriv'
  obtain ⟨δ3, hδ3, h3⟩ := IBMThirdPeano.compact_remainder_bound (deriv f) hg R
    (ε / 4) (by positivity)
  obtain ⟨δ4, hδ4, h4⟩ := IBMFourthPeano.compact_remainder_bound f hf R
    (ε / 4) (by positivity)
  refine ⟨min δ3 δ4, lt_min hδ3 hδ4, ?_⟩
  intro x y hx hy hxy
  have hmR : |(x + y) / 2| ≤ R := by
    rw [abs_div]
    norm_num
    have h := abs_add_le x y
    linarith
  have hmd : |(x + y) / 2 - x| ≤ |y - x| := by
    have he : (x + y) / 2 - x = (y - x) / 2 := by ring
    rw [he, abs_div]
    norm_num
  have hm := h3 x ((x + y) / 2) hx hmR (hmd.trans_lt (hxy.trans_le (min_le_left _ _)))
  have hy3 := h3 x y hx hy (hxy.trans_le (min_le_left _ _))
  have hy4 := h4 x y hx hy (hxy.trans_le (min_le_right _ _))
  have hm' : |IBMThirdPeano.remainder (deriv f) x ((x + y) / 2)| ≤
      (ε / 4) * |y - x|^3 := hm.trans (by gcongr)
  rw [error_identity f hf]
  calc
    |(y - x) / 6 * (4 * IBMThirdPeano.remainder (deriv f) x ((x + y) / 2) +
        IBMThirdPeano.remainder (deriv f) x y) - IBMFourthTaylor.remainder f x y| ≤
        |(y - x) / 6 * (4 * IBMThirdPeano.remainder (deriv f) x ((x + y) / 2) +
          IBMThirdPeano.remainder (deriv f) x y)| + |IBMFourthTaylor.remainder f x y| :=
      abs_sub _ _
    _ ≤ |y - x| / 6 *
        (4 * |IBMThirdPeano.remainder (deriv f) x ((x + y) / 2)| +
          |IBMThirdPeano.remainder (deriv f) x y|) +
        |IBMFourthTaylor.remainder f x y| := by
      rw [abs_mul, abs_div]
      norm_num
      gcongr
      simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] using
        abs_add_le (4 * IBMThirdPeano.remainder (deriv f) x ((x + y) / 2))
          (IBMThirdPeano.remainder (deriv f) x y)
    _ ≤ |y - x| / 6 * (4 * ((ε / 4) * |y - x|^3) +
        (ε / 4) * |y - x|^3) + (ε / 4) * |y - x|^4 := by gcongr
    _ ≤ ε * |y - x|^4 := by
      nlinarith [mul_nonneg hε.le (pow_nonneg (abs_nonneg (y - x)) 4)]

end OperatorDerivativeRewrite.Foundation.IBMSimpsonPeano
