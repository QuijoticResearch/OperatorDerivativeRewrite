import Foundation.RiemannQuarticGaussianNormalization
import Mathlib.Analysis.RCLike.Sqrt
/-! Quantitative stability of the principal actual-curvature Gaussian factor.
The relative estimate retains the branch using its nonnegative real part. -/
noncomputable section
open Set Metric Complex
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticGaussianPrefactor

theorem norm_sub_one_le_norm_sq_sub_one (r : ℂ) (hr : 0 ≤ r.re) :
    ‖r-1‖ ≤ ‖r^2-1‖ := by
  have hp : 1 ≤ ‖r+1‖ := by
    have h := Complex.re_le_norm (r+1)
    simp only [Complex.add_re,Complex.one_re] at h
    linarith
  calc
    _ ≤ ‖r-1‖*‖r+1‖ := le_mul_of_one_le_right (norm_nonneg _) hp
    _ = ‖r^2-1‖ := by rw [← norm_mul]; congr 1; ring

theorem gaussian_relative_coefficient (a : ℂ) (b : ℝ) (ha : a ≠ 0) (hb : 0 < b) :
    ‖((Real.pi : ℂ)/a)^(1/2 : ℂ) / (((Real.pi/b : ℝ) : ℂ)^(1/2 : ℂ))-1‖ ≤
      ‖(b : ℂ)-a‖/‖a‖ := by
  simp only [one_div]
  let g := ((Real.pi : ℂ)/a)^(2⁻¹ : ℂ)
  let h := (((Real.pi/b : ℝ) : ℂ)^(2⁻¹ : ℂ))
  have hpb : 0 < Real.pi/b := div_pos Real.pi_pos hb
  have hh : h = (Real.sqrt (Real.pi/b) : ℂ) := by
    change Complex.sqrt (((Real.pi/b : ℝ) : ℂ)) = _
    apply Complex.sqrt_of_nonneg
    exact_mod_cast hpb.le
  have hhn : h ≠ 0 := by rw [hh]; exact_mod_cast (Real.sqrt_pos.mpr hpb).ne'
  have hgs : g^2=(Real.pi : ℂ)/a := by
    exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)
  have hhs : h^2=((Real.pi/b : ℝ) : ℂ) := by
    exact Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)
  have hgr : 0 ≤ g.re := by
    dsimp [g]
    change 0 ≤ (Complex.sqrt ((Real.pi : ℂ)/a)).re
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    positivity
  have hrr : 0 ≤ (g/h).re := by
    rw [hh,Complex.div_ofReal_re]
    positivity
  have heq : (g/h)^2-1=((b : ℂ)-a)/a := by
    rw [div_pow,hgs,hhs,Complex.ofReal_div]
    field_simp
  have h := norm_sub_one_le_norm_sq_sub_one (g/h) hrr
  rw [heq,norm_div] at h
  exact h

open RiemannQuarticSaddleGeometry RiemannQuarticSaddleBranch RiemannQuarticSaddleTimes
open RiemannQuarticQuantitativeSaddle RiemannQuarticGaussianTail RiemannQuarticFrequencyBranch

def gaussianFactor (t : ℝ) (w : ℂ) : ℂ :=
  ((Real.pi : ℂ)/(-(deriv (complexSlope t) w)/2))^(1/2 : ℂ)

theorem actual_relative_center (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (w : ℂ) (hw : w ∈ closedBall (u : ℂ) (1/102400)) :
    ‖gaussianFactor t w/gaussianFactor t (u : ℂ)-1‖ ≤ 102400*‖w-(u : ℂ)‖ := by
  let Q := t*u^3+1
  let a := -(deriv (complexSlope t) w)/2
  let b := -(deriv (phaseSlope t) u)/2
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hb : 0 < b := by
    have hn := RiemannQuarticCurvature.stationary_phaseSlope_deriv_neg t u ht hu hs
    dsimp [b]; linarith
  have haRe : Q ≤ a.re := gaussian_coefficient_lower t u ht hu hs w hw
  have haNorm : Q ≤ ‖a‖ := haRe.trans (Complex.re_le_norm a)
  have ha : a ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hQ haNorm)
  have hc : -(deriv (complexSlope t) (u : ℂ))/2=(b : ℂ) := by
    rw [slope_deriv_real t u (by linarith)]
    dsimp [b]
    push_cast
    rfl
  have hbound := stationary_slope_deriv_inner_lipschitz t u ht hu hs (u : ℂ) w
    (mem_closedBall_self (by norm_num)) (closedBall_subset_closedBall (by norm_num) hw)
  have hcoef : ‖(b : ℂ)-a‖ ≤ 102400*Q*‖w-(u : ℂ)‖ := by
    have he : (b : ℂ)-a=(deriv (complexSlope t) w-deriv (complexSlope t) (u : ℂ))/2 := by
      rw [← hc]; dsimp [a]; ring
    rw [he,norm_div,Complex.norm_ofNat]
    dsimp [Q] at *
    linarith
  have h := gaussian_relative_coefficient a b ha hb
  have hid : gaussianFactor t (u : ℂ)=(((Real.pi/b : ℝ) : ℂ)^(1/2 : ℂ)) := by
    change ((Real.pi : ℂ)/(-(deriv (complexSlope t) (u : ℂ))/2))^(1/2 : ℂ)=_
    rw [hc,← Complex.ofReal_div]
  rw [← hid] at h
  change ‖gaussianFactor t w/gaussianFactor t (u : ℂ)-1‖ ≤ _ at h
  apply h.trans
  apply (div_le_iff₀ (lt_of_lt_of_le hQ haNorm)).mpr
  nlinarith [mul_le_mul_of_nonneg_left haNorm (by positivity : 0 ≤ 102400*‖w-(u : ℂ)‖)]

theorem branch_relative_center (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0)
    (z : ℂ) (hz : ‖z‖ ≤ (t*u^3+1)/51200) :
    ‖gaussianFactor t (branch t u ht hu hs z)/gaussianFactor t (u : ℂ)-1‖ ≤
      51200*‖z‖/(t*u^3+1) := by
  have h := actual_relative_center t u ht hu hs _ (branch_spec t u ht hu hs z hz).1
  have hd := branch_displacement_bound t u ht hu hs z hz
  calc
    _ ≤ 102400*‖branch t u ht hu hs z-(u : ℂ)‖ := h
    _ ≤ 102400*(‖z‖/(2*(t*u^3+1))) := mul_le_mul_of_nonneg_left hd (by norm_num)
    _ = _ := by
      have hQ : t*u^3+1 ≠ 0 := ne_of_gt (by positivity : 0 < t*u^3+1)
      field_simp
      <;> ring

end OperatorDerivativeRewrite.Foundation.RiemannQuarticGaussianPrefactor
