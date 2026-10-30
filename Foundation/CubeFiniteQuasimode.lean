import Foundation.CubeGaussianRadialEigenvector

/-! Genuine finite stationary quasimodes from nonzero limiting eigenvectors. -/
noncomputable section
open Filter Topology
namespace OperatorDerivativeRewrite.Foundation.CubeFiniteQuasimode
open CubeBoundaryChartL2 CubeBoundaryChartInverse CubeChartCompressedKernel
open CubeGroundNormLimit CubeSlabGround CubeChordOperator CubeCompressedNormLimit
open CubeFullCompressionError CubeBoundaryExterior CubeGaussianSchurBound

def backFamily (t : ℝ) (F : EuclideanL2) : ChordL2 :=
  if ht : 0 < t then backward t ht F else 0

theorem backFamily_pos (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    backFamily t F=backward t ht F := dif_pos ht

def finiteError (t : ℝ) (ρ : ℝ) (F : EuclideanL2) : ChordL2 :=
  chordOperator (ground (1/t^2)) (backFamily t F)-ρ • backFamily t F

theorem compressed_contraction (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    ‖normalizedOperatorFamily t F‖ ≤ ‖backFamily t F‖ := by
  rw [normalizedOperatorFamily_pos t ht,backFamily_pos t ht]
  exact (forward_contraction t ht _).trans (chordOperator_contraction _ _)

theorem local_back (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    localOperator t ht (ground (1/t^2)) (backward t ht F)=
      groundScale t • backward t ht (normalizedOperatorFamily t F) := by
  simp only [localOperator,ContinuousLinearMap.comp_apply,forward_backward]
  have he : compressed t ht (ground (1/t^2)) (cutoffClass t F)=
      compressed t ht (ground (1/t^2)) F := by
    simp only [compressed,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
      backward_cutoff]
  rw [he,normalizedOperatorFamily_pos]
  simp only [compressed,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,map_smul]
  rfl

theorem finite_bridge (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (F : EuclideanL2) :
    ‖chordOperator (ground (1/t^2)) (backFamily t F)-
      backward t ht (normalizedOperatorFamily t F)‖ ≤
        (groundScale t)⁻¹*(errorConstant*t)*‖F‖ := by
  have hs : 0<groundScale t := div_pos (ground (1/t^2)).value_pos (pow_pos ht 36)
  have he : CubeFullCompressionError.residual t ht (ground (1/t^2)) (backward t ht F)=
      groundScale t • (chordOperator (ground (1/t^2)) (backward t ht F)-
        backward t ht (normalizedOperatorFamily t F)) := by
    simp only [CubeFullCompressionError.residual,ContinuousLinearMap.sub_apply,bare,ContinuousLinearMap.smul_apply,
      local_back,smul_sub]
    rfl
  have h := ((CubeFullCompressionError.residual t ht (ground (1/t^2))).le_opNorm (backward t ht F)).trans
    (mul_le_mul_of_nonneg_right (residual_norm_bound t ht _ h1) (norm_nonneg _))
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at h
  rw [backFamily_pos t ht]
  rw [mul_assoc]
  apply (le_inv_mul_iff₀ hs).mpr
  exact h.trans (mul_le_mul_of_nonneg_left (backward_contraction t ht F)
    ((norm_nonneg _).trans (residual_norm_bound t ht (ground (1/t^2)) h1)))

theorem finiteError_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (ρ : ℝ) (F : EuclideanL2) :
    ‖finiteError t ρ F‖ ≤ (groundScale t)⁻¹*(errorConstant*t)*‖F‖+
      ‖normalizedOperatorFamily t F-ρ • F‖ := by
  have he : finiteError t ρ F=
      (chordOperator (ground (1/t^2)) (backFamily t F)-
        backward t ht (normalizedOperatorFamily t F))+
      backward t ht (normalizedOperatorFamily t F-ρ • F) := by
    rw [finiteError,backFamily_pos t ht]
    simp only [map_sub,map_smul]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (finite_bridge t ht h1 F)
    (backward_contraction t ht _))

theorem limit_error_tendsto (ρ : ℝ) (F : EuclideanL2)
    (he : normalizedLimitOperator F = ρ • F) :
    Tendsto (fun t : ℝ => normalizedOperatorFamily t F-ρ • F)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have h := ((ContinuousLinearMap.apply ℝ EuclideanL2 F).continuous.tendsto
    normalizedLimitOperator).comp normalizedOperatorFamily_tendsto
  change Tendsto (fun t : ℝ => normalizedOperatorFamily t F) (𝓝[>] (0:ℝ))
    (𝓝 (normalizedLimitOperator F)) at h
  simpa only [he,sub_self] using h.sub_const (ρ • F)

theorem finiteError_tendsto (ρ : ℝ) (F : EuclideanL2)
    (he : normalizedLimitOperator F = ρ • F) :
    Tendsto (fun t : ℝ => ‖finiteError t ρ F‖) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => (groundScale t)⁻¹*(errorConstant*t)*‖F‖)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := (exact_groundScale_limit.inv₀ CubeGaussianGroundEigenvector.eigenvalue_positive.ne').mul
      ((tendsto_const_nhds (x := errorConstant)).mul
        (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ)))
    simpa only [mul_zero,zero_mul] using h.mul_const ‖F‖
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (by simpa using h0.add (limit_error_tendsto ρ F he).norm)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht h1
  exact finiteError_bound t ht h1 ρ F

theorem back_norm_lower (ρ : ℝ) (hρ : 0 < ρ) (F : EuclideanL2) (hF : F ≠ 0)
    (he : normalizedLimitOperator F = ρ • F) :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), ρ*‖F‖/2 < ‖backFamily t F‖ := by
  have hp : 0 < ρ*‖F‖ := mul_pos hρ (norm_pos_iff.mpr hF)
  have h := ((limit_error_tendsto ρ F he).add_const (ρ • F))
  simp only [sub_add_cancel,zero_add] at h
  have hn : Tendsto (fun t : ℝ => ‖normalizedOperatorFamily t F‖)
      (𝓝[>] (0:ℝ)) (𝓝 (ρ*‖F‖)) := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hρ] using h.norm
  filter_upwards [hn.eventually (eventually_gt_nhds (by linarith : ρ*‖F‖/2 < ρ*‖F‖)),
    self_mem_nhdsWithin] with t hl ht
  exact hl.trans_le (compressed_contraction t ht F)

end OperatorDerivativeRewrite.Foundation.CubeFiniteQuasimode
