import Foundation.CubeFiniteQuasimode

/-! Exact finite-ground complements for the actual stationary transfer. -/
noncomputable section
open Filter Topology
namespace OperatorDerivativeRewrite.Foundation.CubeFiniteGroundQuasimode
open CubeFiniteQuasimode CubeBoundaryChartL2 CubeGroundNormLimit CubeSlabGround CubeChordOperator

def coefficient (t : ℝ) (F : EuclideanL2) : ℝ :=
  inner ℝ (backFamily t F) (chordGround (ground (1/t^2)))

def centered (t : ℝ) (F : EuclideanL2) : ChordL2 :=
  backFamily t F-coefficient t F • chordGround (ground (1/t^2))

theorem centered_orthogonal (t : ℝ) (F : EuclideanL2) :
    inner ℝ (centered t F) (chordGround (ground (1/t^2))) = 0 := by
  rw [centered,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
    chordGround_norm]
  simp [coefficient]

theorem error_ground (t ρ : ℝ) (F : EuclideanL2) :
    inner ℝ (finiteError t ρ F) (chordGround (ground (1/t^2))) =
      (1-ρ)*coefficient t F := by
  have h := ContinuousLinearMap.adjoint_inner_right (chordOperator (ground (1/t^2)))
    (backFamily t F) (chordGround (ground (1/t^2)))
  rw [chordOperator_selfadjoint,chordGround_fixed] at h
  simp only [finiteError,inner_sub_left,real_inner_smul_left]
  unfold coefficient
  nlinarith [h]

theorem coefficient_bound (t ρ : ℝ) (hρ : ρ < 1) (F : EuclideanL2) :
    |coefficient t F| ≤ ‖finiteError t ρ F‖/(1-ρ) := by
  have h := abs_real_inner_le_norm (finiteError t ρ F) (chordGround (ground (1/t^2)))
  rw [error_ground,abs_mul,abs_of_pos (by linarith : 0 < 1-ρ),chordGround_norm,mul_one] at h
  apply (le_div_iff₀ (by linarith : 0 < 1-ρ)).mpr
  nlinarith [h]

theorem coefficient_tendsto (ρ : ℝ) (hρ : ρ < 1) (F : EuclideanL2)
    (he : normalizedLimitOperator F = ρ • F) :
    Tendsto (fun t : ℝ => |coefficient t F|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply squeeze_zero (fun _ => abs_nonneg _) (fun t => coefficient_bound t ρ hρ F) ?_
  simpa using (finiteError_tendsto ρ F he).div_const (1-ρ)

def centeredError (t ρ : ℝ) (F : EuclideanL2) : ChordL2 :=
  chordOperator (ground (1/t^2)) (centered t F)-ρ • centered t F

theorem centeredError_eq (t ρ : ℝ) (F : EuclideanL2) :
    centeredError t ρ F = finiteError t ρ F-
      inner ℝ (finiteError t ρ F) (chordGround (ground (1/t^2))) •
        chordGround (ground (1/t^2)) := by
  rw [error_ground]
  simp only [centeredError,centered,map_sub,map_smul,chordGround_fixed,smul_sub,
    finiteError,sub_smul,one_smul,mul_smul]
  abel

theorem centeredError_bound (t ρ : ℝ) (F : EuclideanL2) :
    ‖centeredError t ρ F‖ ≤ 2*‖finiteError t ρ F‖ := by
  rw [centeredError_eq]
  have h := abs_real_inner_le_norm (finiteError t ρ F) (chordGround (ground (1/t^2)))
  rw [chordGround_norm,mul_one] at h
  have hn := norm_sub_le (finiteError t ρ F)
    (inner ℝ (finiteError t ρ F) (chordGround (ground (1/t^2))) • chordGround (ground (1/t^2)))
  rw [norm_smul,Real.norm_eq_abs,chordGround_norm,mul_one] at hn
  linarith

theorem centeredError_tendsto (ρ : ℝ) (F : EuclideanL2)
    (he : normalizedLimitOperator F = ρ • F) :
    Tendsto (fun t : ℝ => ‖centeredError t ρ F‖) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _) (fun t => centeredError_bound t ρ F) ?_
  simpa using (finiteError_tendsto ρ F he).const_mul 2

theorem centered_norm_lower (ρ : ℝ) (hρ : 0 < ρ) (h1 : ρ < 1)
    (F : EuclideanL2) (hF : F ≠ 0) (he : normalizedLimitOperator F = ρ • F) :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ρ*‖F‖/4 < ‖centered t F‖ := by
  have hp : 0 < ρ*‖F‖ := mul_pos hρ (norm_pos_iff.mpr hF)
  have hc := (coefficient_tendsto ρ h1 F he).eventually
    (eventually_lt_nhds (by linarith : (0:ℝ) < ρ*‖F‖/4))
  filter_upwards [back_norm_lower ρ hρ F hF he,hc] with t hl hc
  have hn := norm_sub_le (centered t F) (-coefficient t F • chordGround (ground (1/t^2)))
  have hi : centered t F-(-coefficient t F • chordGround (ground (1/t^2))) = backFamily t F := by
    unfold centered
    simp only [neg_smul]
    abel
  rw [hi,norm_smul,Real.norm_eq_abs,abs_neg,chordGround_norm,mul_one] at hn
  linarith

def unit (t : ℝ) (F : EuclideanL2) : ChordL2 := ‖centered t F‖⁻¹ • centered t F

theorem unit_orthogonal (t : ℝ) (F : EuclideanL2) :
    inner ℝ (unit t F) (chordGround (ground (1/t^2))) = 0 := by
  rw [unit,real_inner_smul_left,centered_orthogonal,mul_zero]

theorem unit_norm (t : ℝ) (F : EuclideanL2) (hc : centered t F ≠ 0) : ‖unit t F‖ = 1 := by
  rw [unit,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc)]

theorem unit_error (t ρ : ℝ) (F : EuclideanL2) :
    chordOperator (ground (1/t^2)) (unit t F)-ρ • unit t F =
      ‖centered t F‖⁻¹ • centeredError t ρ F := by
  simp only [unit,centeredError,map_smul,smul_sub,smul_smul,mul_comm]

theorem unit_error_tendsto (ρ : ℝ) (hρ : 0 < ρ) (h1 : ρ < 1)
    (F : EuclideanL2) (hF : F ≠ 0) (he : normalizedLimitOperator F = ρ • F) :
    Tendsto (fun t : ℝ => ‖chordOperator (ground (1/t^2)) (unit t F)-ρ • unit t F‖)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hp : 0 < ρ*‖F‖/4 := div_pos (mul_pos hρ (norm_pos_iff.mpr hF)) (by norm_num)
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (by simpa using (centeredError_tendsto ρ F he).div_const (ρ*‖F‖/4))
  filter_upwards [centered_norm_lower ρ hρ h1 F hF he] with t hl
  rw [unit_error,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
  have h := div_le_div_of_nonneg_left (norm_nonneg (centeredError t ρ F)) hp hl.le
  simpa only [div_eq_mul_inv,mul_comm] using h

theorem eventually_unit_norm (ρ : ℝ) (hρ : 0 < ρ) (h1 : ρ < 1)
    (F : EuclideanL2) (hF : F ≠ 0) (he : normalizedLimitOperator F = ρ • F) :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ‖unit t F‖ = 1 := by
  have hp : 0 < ρ*‖F‖/4 := div_pos (mul_pos hρ (norm_pos_iff.mpr hF)) (by norm_num)
  filter_upwards [centered_norm_lower ρ hρ h1 F hF he] with t hl
  exact unit_norm t F (norm_pos_iff.mp (hp.trans hl))

end OperatorDerivativeRewrite.Foundation.CubeFiniteGroundQuasimode
