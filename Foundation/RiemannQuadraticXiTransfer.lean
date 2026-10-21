import Foundation.RiemannRealOrderFlow
import Foundation.RiemannXiBridge

/-! Actual zero-time normalization and exact half-plane coordinates.
No external zero-free theorem or reality of quadratic zeros is assumed. -/
noncomputable section
open Complex
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticXiTransfer

def criticalCoordinate (z : ℂ) : ℂ := 1/2+Complex.I*z/2

theorem real_order_zero_time (a : ℝ) (z : ℂ) :
    RiemannRealOrderFlow.flow a 0 z = RiemannXiBridge.normalizedXi z := by
  calc
    _ = RiemannRealOrderFlow.flow 2 0 z := by
      rw [RiemannRealOrderFlow.flow_zero_time, RiemannRealOrderFlow.flow_zero_time]
    _ = RiemannQuarticFlow.flow 0 z := by
      simpa only [Nat.cast_ofNat, RiemannEvenFlow.flow_quartic] using
        RiemannRealOrderFlow.flow_nat 2 0 z
    _ = _ := congrFun RiemannXiBridge.flow_zero_eq_normalizedXi z

theorem criticalCoordinate_re (z : ℂ) :
    (criticalCoordinate z).re = 1/2-z.im/2 := by
  simp [criticalCoordinate, Complex.mul_re, Complex.div_ofNat_re]
  ring

theorem criticalCoordinate_im (z : ℂ) :
    (criticalCoordinate z).im = z.re/2 := by
  simp [criticalCoordinate, Complex.mul_im, Complex.div_ofNat_im]

theorem seven_eighths_coordinate (z : ℂ) :
    (7/8 : ℝ) < (criticalCoordinate z).re ↔ z.im < -(3/4 : ℝ) := by
  rw [criticalCoordinate_re]
  constructor <;> intro h <;> linarith

theorem zero_iff_completed (a : ℝ) (z : ℂ)
    (h0 : criticalCoordinate z ≠ 0) (h1 : criticalCoordinate z ≠ 1) :
    RiemannRealOrderFlow.flow a 0 z = 0 ↔ completedRiemannZeta (criticalCoordinate z) = 0 := by
  rw [real_order_zero_time]
  change RiemannXiNormalization.entireXi (criticalCoordinate z)/8=0 ↔ _
  rw [RiemannXiNormalization.entireXi_eq_completed _ h0 h1]
  simp [h0, sub_ne_zero.mpr h1]

theorem nonzero_of_completed_half_plane (theta : ℝ)
    (hfree : ∀ s : ℂ, theta < s.re → s ≠ 0 → s ≠ 1 → completedRiemannZeta s ≠ 0)
    (a : ℝ) (z : ℂ) (hz : z.im < 1-2*theta)
    (h0 : criticalCoordinate z ≠ 0) (h1 : criticalCoordinate z ≠ 1) :
    RiemannRealOrderFlow.flow a 0 z ≠ 0 := by
  intro hzero
  have hr : theta < (criticalCoordinate z).re := by rw [criticalCoordinate_re]; linarith
  exact hfree _ hr h0 h1 ((zero_iff_completed a z h0 h1).mp hzero)

theorem nonzero_of_zeta_half_plane (theta : ℝ)
    (hfree : ∀ s : ℂ, theta < s.re → riemannZeta s ≠ 0)
    (a : ℝ) (z : ℂ) (hz : z.im < 1-2*theta) :
    RiemannRealOrderFlow.flow a 0 z ≠ 0 := by
  by_cases hre : z.re = 0
  · have he : z = Complex.I*(z.im : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rw [real_order_zero_time, he]
    exact RiemannXiBridge.normalizedXi_ne_zero_on_imaginary_axis _
  · have h0 : criticalCoordinate z ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      rw [criticalCoordinate_im] at hi
      simp only [Complex.zero_im] at hi
      exact hre (by linarith)
    have h1 : criticalCoordinate z ≠ 1 := by
      intro h
      have hi := congrArg Complex.im h
      rw [criticalCoordinate_im] at hi
      simp only [Complex.one_im] at hi
      exact hre (by linarith)
    intro hf
    have hc := (zero_iff_completed a z h0 h1).mp hf
    have hr : theta < (criticalCoordinate z).re := by
      rw [criticalCoordinate_re]; linarith
    apply hfree _ hr
    rw [riemannZeta_def_of_ne_zero h0, hc, zero_div]

theorem nonzero_below_seven_eighths_strip
    (hfree : ∀ s : ℂ, (7/8 : ℝ) < s.re → riemannZeta s ≠ 0)
    (a : ℝ) (z : ℂ) (hz : z.im < -(3/4 : ℝ)) :
    RiemannRealOrderFlow.flow a 0 z ≠ 0 := by
  apply nonzero_of_zeta_half_plane (7/8) hfree a z
  linarith

theorem zero_im_strip_of_seven_eighths
    (hfree : ∀ s : ℂ, (7/8 : ℝ) < s.re → riemannZeta s ≠ 0)
    (a : ℝ) (ha : 0 ≤ a) (z : ℂ) (hz : RiemannRealOrderFlow.flow a 0 z = 0) :
    |z.im| ≤ (3/4 : ℝ) := by
  rw [abs_le]
  constructor
  · by_contra h
    exact nonzero_below_seven_eighths_strip hfree a z (lt_of_not_ge h) hz
  · by_contra h
    have hc : RiemannRealOrderFlow.flow a 0 (conj z) = 0 := by
      rw [RiemannRealOrderFlow.flow_conj a ha, hz]
      simp
    have hi : (conj z).im < -(3/4 : ℝ) := by
      simp only [Complex.conj_im]
      linarith [lt_of_not_ge h]
    exact nonzero_below_seven_eighths_strip hfree a (conj z) hi hc

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticXiTransfer
