import Foundation.RiemannQuarticCosineNormalization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
/-! Actual-flow zero localization in the growing saddle window.
Zeros lie in an arbitrarily thin saddle-scaled horizontal strip at late times.
This does not assert reality, simplicity, or exclude far-field zeros. -/
noncomputable section
open Set Metric Complex Filter
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticZeroStrip
open RiemannQuarticCosineNormalization RiemannQuarticSaddleTimes RiemannQuarticDomain

theorem sinh_im_le_norm_cos (z : ℂ) : |Real.sinh z.im| ≤ ‖Complex.cos z‖ := by
  have h := abs_norm_sub_norm_le (Complex.exp (z*Complex.I)) (-Complex.exp (-z*Complex.I))
  simp only [norm_neg,sub_neg_eq_add,← Complex.two_cos,norm_mul,Complex.norm_ofNat,Complex.norm_exp] at h
  have h1 : (z*Complex.I).re= -z.im := by simp [Complex.mul_re]
  have h2 : (-z*Complex.I).re=z.im := by simp [Complex.mul_re]
  rw [h1,h2,abs_sub_comm] at h
  rw [Real.sinh_eq,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ)<2)).mpr (by linarith)

theorem small_cos_im (z : ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1/2)
    (hcos : ‖Complex.cos z‖ ≤ ε*Real.cosh z.im) : |z.im| ≤ 2*ε := by
  have hs := (sinh_im_le_norm_cos z).trans hcos
  have hcpos := Real.cosh_pos z.im
  have hsq := Real.cosh_sq z.im
  have habsq : |Real.sinh z.im|^2=Real.sinh z.im^2 := sq_abs _
  have hhalf : |Real.sinh z.im| ≤ Real.cosh z.im/2 := by nlinarith
  have hmul := mul_self_le_mul_self (abs_nonneg (Real.sinh z.im)) hhalf
  have hc2 : Real.cosh z.im ≤ 2 := by nlinarith
  have hs2 : |Real.sinh z.im| ≤ 2*ε := by nlinarith
  have hy := (Real.self_le_sinh_iff).mpr (abs_nonneg z.im)
  rw [← Real.abs_sinh] at hy
  exact hy.trans hs2

theorem uniform_zero_strip (γ : ℝ) (hγ : γ < 2/3) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop, ∀ (ht : 0 < t) (u : ℝ) (hu : 2 ≤ u),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → ∀ (hs : phaseSlope t u=0) (z : ℂ),
      ‖z‖ ≤ (t*u^3+1)^γ → RiemannQuarticFlow.flow t z=0 → u*|z.im| ≤ δ := by
  let ε := min (1/2) (δ/2)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  filter_upwards [uniform_normalized_cosine γ hγ ε hε] with t happrox
  intro ht u hu hm hs z hz hzero
  have h := happrox ht u hu hm hs z hz
  rw [hzero,zero_div,zero_sub,norm_neg] at h
  have hi : ((u : ℂ)*z).im=u*z.im := by simp [Complex.mul_im]
  have hbound := small_cos_im ((u : ℂ)*z) ε hε.le (min_le_left _ _) (by simpa only [hi] using h)
  rw [hi,abs_mul,abs_of_nonneg (by linarith : 0 ≤ u)] at hbound
  exact hbound.trans (by have hm := min_le_right (1/2 : ℝ) (δ/2); dsimp [ε]; linarith)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticZeroStrip
