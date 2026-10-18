import Foundation.CyclicRootProbabilityNoise
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Genuine cyclic innovations with the dissipative higher-even-heat moment sign. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.HigherEvenRootInnovation
open CyclicRootProbabilityNoise

def phase (m : ℕ) : ℂ := Complex.exp (((Real.pi*(m+1)/(2*m) : ℝ) : ℂ)*Complex.I)

theorem phase_norm (m : ℕ) : ‖phase m‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem phase_power (m : ℕ) [NeZero m] : (phase m)^(2*m) = (-1 : ℂ)^(m+1) := by
  rw [phase,← Complex.exp_nat_mul]
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have he : ((2*m : ℕ) : ℂ)*(((Real.pi*(m+1)/(2*m) : ℝ) : ℂ)*Complex.I) =
      ((m+1 : ℕ) : ℂ)*((Real.pi : ℂ)*Complex.I) := by
    push_cast
    field_simp
  rw [he,Complex.exp_nat_mul,Complex.exp_pi_mul_I]

def innovation (m : ℕ) [NeZero m] (a : ℝ) (k : ZMod (2*m)) : ℂ :=
  noise (2*m) ((a : ℂ)*phase m) k

theorem lower_moment (m : ℕ) [NeZero m] (a : ℝ) (r : ℕ) (hr : 0 < r) (hm : r < 2*m) :
    (∫ k, (innovation m a k)^r ∂probability (2*m)) = 0 :=
  CyclicRootProbabilityNoise.lower_moment (2*m) _ r hr hm

theorem leading_moment (m : ℕ) [NeZero m] (a : ℝ) :
    (∫ k, (innovation m a k)^(2*m) ∂probability (2*m)) =
      (a : ℂ)^(2*m)*(-1 : ℂ)^(m+1) := by
  change (∫ k, (noise (2*m) ((a : ℂ)*phase m) k)^(2*m) ∂probability (2*m)) = _
  rw [CyclicRootProbabilityNoise.nth_moment,mul_pow,phase_power]

theorem absolute_second (m : ℕ) [NeZero m] (a : ℝ) :
    (∫ k, ‖innovation m a k‖^2 ∂probability (2*m)) = a^2 := by
  change (∫ k, ‖noise (2*m) ((a : ℂ)*phase m) k‖^2 ∂probability (2*m)) = _
  rw [CyclicRootProbabilityNoise.absolute_second,norm_mul,phase_norm,mul_one,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

theorem fourier_leading_moment (m : ℕ) [NeZero m] (a ξ : ℝ) :
    (∫ k, (Complex.I*(ξ : ℂ)*innovation m a k)^(2*m) ∂probability (2*m)) =
      -((a : ℂ)*(ξ : ℂ))^(2*m) := by
  simp_rw [mul_pow]
  rw [integral_const_mul,leading_moment]
  have hs : (-1 : ℂ)^m*(-1 : ℂ)^(m+1) = -1 := by
    rw [pow_succ,← mul_assoc,← mul_pow]
    norm_num
  have hi : Complex.I^(2*m) = (-1 : ℂ)^m := by rw [pow_mul,Complex.I_sq]
  rw [hi]
  calc
    _ = ((-1 : ℂ)^m*(-1 : ℂ)^(m+1))*((a : ℂ)*(ξ : ℂ))^(2*m) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hs]; ring

theorem not_real_valued (m : ℕ) [NeZero m] (hm : 1 < m) (a : ℝ) (ha : a ≠ 0) :
    ¬ ∀ k : ZMod (2*m), (innovation m a k).im = 0 := by
  intro hr
  have hp (k : ZMod (2*m)) : (innovation m a k)^2 = ((‖innovation m a k‖^2 : ℝ) : ℂ) := by
    rw [Complex.sq_norm]
    apply Complex.ext <;>
      simp [pow_two,Complex.mul_re,Complex.mul_im,Complex.normSq_apply,hr k]
  have he := integral_congr_ae (μ := probability (2*m)) (Filter.Eventually.of_forall hp)
  rw [lower_moment m a 2 (by decide) (by omega),integral_complex_ofReal,absolute_second] at he
  have hz : a^2 = 0 := Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using he.symm)
  exact pow_ne_zero 2 ha hz

end OperatorDerivativeRewrite.Foundation.HigherEvenRootInnovation
