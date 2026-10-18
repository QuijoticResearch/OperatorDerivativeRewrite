import Foundation.IBMQuarticTimeProjection

/-! Polynomial growth of the actual unprojected quartic source class. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticSourceGrowth
open InfiniteGaussian GaussianQuarticWick IBMEvenCorrectionProjection
open IBMGaussianSteinMoments IBMQuarticSecondGeometry

theorem quartic_norm_sq (u : CoefficientSpace) : ‖quartic u‖^2 = 105*‖u‖^8 := by
  rw [← real_inner_self_eq_norm_sq, quartic_inner, real_inner_self_eq_norm_sq]
  ring

theorem quartic_norm_le (u : CoefficientSpace) : ‖quartic u‖ ≤ 11*‖u‖^4 := by
  have he := quartic_norm_sq u
  nlinarith [norm_nonneg (quartic u), pow_nonneg (norm_nonneg u) 4]

theorem squareProduct_norm_le (u v : CoefficientSpace) {B : ℝ} (hB : 0 ≤ B)
    (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) : ‖squareProduct u v‖ ≤ 33*B^4 := by
  have hp : ‖quartic (u+v)‖ ≤ 11*(2*B)^4 :=
    (quartic_norm_le _).trans (by gcongr; exact (norm_add_le _ _).trans (by linarith))
  have hm : ‖quartic (u-v)‖ ≤ 11*(2*B)^4 :=
    (quartic_norm_le _).trans (by gcongr; exact (norm_sub_le _ _).trans (by linarith))
  have hqu : ‖quartic u‖ ≤ 11*B^4 := (quartic_norm_le _).trans (by gcongr)
  have hqv : ‖quartic v‖ ≤ 11*B^4 := (quartic_norm_le _).trans (by gcongr)
  have h₁ := norm_sub_le (quartic (u+v)+quartic (u-v)-(2 : ℝ) • quartic u) ((2 : ℝ) • quartic v)
  have h₂ := norm_sub_le (quartic (u+v)+quartic (u-v)) ((2 : ℝ) • quartic u)
  have h₃ := norm_add_le (quartic (u+v)) (quartic (u-v))
  simp only [norm_smul] at h₁ h₂
  norm_num at h₁ h₂
  rw [squareProduct, norm_smul]
  norm_num
  nlinarith

theorem cubeProduct_norm_le (u w : CoefficientSpace) {B : ℝ} (hB : 0 ≤ B)
    (hu : ‖u‖ ≤ B) (hw : ‖w‖ ≤ B) : ‖cubeProduct u w‖ ≤ 52*B^4 := by
  have h2 : ‖(2 : ℝ) • u‖ ≤ 2*B := by
    rw [norm_smul]
    norm_num
    linarith
  have hp : ‖quartic ((2 : ℝ) • u+w)‖ ≤ 11*(3*B)^4 :=
    (quartic_norm_le _).trans (by gcongr; exact (norm_add_le _ _).trans (by linarith))
  have hm : ‖quartic ((2 : ℝ) • u-w)‖ ≤ 11*(3*B)^4 :=
    (quartic_norm_le _).trans (by gcongr; exact (norm_sub_le _ _).trans (by linarith))
  have hpu : ‖quartic (u+w)‖ ≤ 11*(2*B)^4 :=
    (quartic_norm_le _).trans (by gcongr; exact (norm_add_le _ _).trans (by linarith))
  have hmu : ‖quartic (u-w)‖ ≤ 11*(2*B)^4 :=
    (quartic_norm_le _).trans (by gcongr; exact (norm_sub_le _ _).trans (by linarith))
  have h₁ := norm_add_le (quartic ((2 : ℝ) • u+w)-quartic ((2 : ℝ) • u-w)-
    (2 : ℝ) • quartic (u+w)) ((2 : ℝ) • quartic (u-w))
  have h₂ := norm_sub_le (quartic ((2 : ℝ) • u+w)-quartic ((2 : ℝ) • u-w))
    ((2 : ℝ) • quartic (u+w))
  have h₃ := norm_sub_le (quartic ((2 : ℝ) • u+w)) (quartic ((2 : ℝ) • u-w))
  simp only [norm_smul] at h₁ h₂
  norm_num at h₁ h₂
  rw [cubeProduct, norm_smul]
  norm_num
  nlinarith [pow_nonneg hB 4]

theorem correction_norm_le (u v w : CoefficientSpace) {B : ℝ} (hB : 0 ≤ B)
    (hu : ‖u‖ ≤ B) (hv : ‖v‖ ≤ B) (hw : ‖w‖ ≤ B) :
    ‖quarticCorrection u v w‖ ≤ 26*B^4 := by
  have hs := squareProduct_norm_le u v hB hu hv
  have hc := cubeProduct_norm_le u w hB hu hw
  have he := norm_add_le ((1/2 : ℝ) • squareProduct u v) ((1/6 : ℝ) • cubeProduct u w)
  simp only [norm_smul] at he
  norm_num at he
  rw [quarticCorrection]
  nlinarith [pow_nonneg hB 4]

theorem spatialQuartic_growth (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖spatialQuartic n r‖ ≤ C*(1+|r|)^4 := by
  obtain ⟨A,hA,ha⟩ := IBMSceneryGlobalGrowth.tripleCoefficient_global_growth n 0
  obtain ⟨B,hB,hb⟩ := IBMSceneryGlobalGrowth.tripleCoefficient_global_growth n 1
  obtain ⟨D,hD,hd⟩ := IBMSceneryGlobalGrowth.tripleCoefficient_global_growth n 2
  refine ⟨26*(A+B+D)^4, by positivity, fun r => ?_⟩
  have hu : ‖tripleCoefficient n r 0‖ ≤ (A+B+D)*(1+|r|) :=
    (ha r).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hv : ‖tripleCoefficient n r 1‖ ≤ (A+B+D)*(1+|r|) :=
    (hb r).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hw : ‖tripleCoefficient n r 2‖ ≤ (A+B+D)*(1+|r|) :=
    (hd r).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  simpa only [spatialQuartic, mul_pow, mul_assoc] using correction_norm_le _ _ _
    (by positivity : 0 ≤ (A+B+D)*(1+|r|)) hu hv hw

end OperatorDerivativeRewrite.Foundation.IBMQuarticSourceGrowth
