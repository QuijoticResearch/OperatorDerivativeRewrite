import Foundation.CubeFullCompressionError

/-! The full finite-slab normalization is determined by the local operator limit. -/
noncomputable section
open Filter Topology
namespace OperatorDerivativeRewrite.Foundation.CubeGroundNormLimit
open CubeSlabGround CubeChordOperator CubeBoundaryChartL2 CubeBoundaryChartInverse
open CubeChartCompressedKernel CubeFullCompressionError CubeCompressedNormLimit

theorem forward_norm_le (t : ℝ) (ht : 0 < t) : ‖forward t ht‖ ≤ 1 := by
  apply (forward t ht).opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using forward_contraction t ht f

theorem backward_norm_le (t : ℝ) (ht : 0 < t) : ‖backward t ht‖ ≤ 1 := by
  change ‖(forward t ht).adjoint‖ ≤ 1
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact forward_norm_le t ht

theorem backward_contraction (t : ℝ) (ht : 0 < t) (F : EuclideanL2) :
    ‖backward t ht F‖ ≤ ‖F‖ := by
  exact ((backward t ht).le_opNorm F).trans
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (backward_norm_le t ht) (norm_nonneg F))

theorem compressed_cutoff (t : ℝ) (ht : 0 < t)
    (d : GroundData (1 / t ^ 2)) (F : EuclideanL2) :
    cutoffClass t (compressed t ht d F)=compressed t ht d F := by
  rw [← forward_backward t ht]
  change forward t ht (backward t ht
    ((d.value / t ^ 36) • forward t ht (chordOperator d (backward t ht F)))) = _
  simp only [map_smul,backward_forward,forward_localClass]
  rfl

theorem compressed_recover (t : ℝ) (ht : 0 < t)
    (d : GroundData (1 / t ^ 2)) (F : EuclideanL2) :
    forward t ht (localOperator t ht d (backward t ht F))=compressed t ht d F := by
  change forward t ht (backward t ht
    (compressed t ht d (forward t ht (backward t ht F)))) = _
  rw [forward_backward]
  have he : compressed t ht d (cutoffClass t F)=compressed t ht d F := by
    simp only [compressed,ContinuousLinearMap.comp_apply,smul_apply,backward_cutoff]
  rw [forward_backward,he,compressed_cutoff]

theorem local_norm_eq (t : ℝ) (ht : 0 < t) (d : GroundData (1 / t ^ 2)) :
    ‖localOperator t ht d‖=‖compressed t ht d‖ := by
  apply le_antisymm
  · apply (localOperator t ht d).opNorm_le_bound (norm_nonneg _)
    intro f
    change ‖backward t ht (compressed t ht d (forward t ht f))‖ ≤ _
    exact (backward_contraction t ht _).trans
      (((compressed t ht d).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (forward_contraction t ht f) (norm_nonneg _)))
  · apply (compressed t ht d).opNorm_le_bound (norm_nonneg _)
    intro F
    rw [← compressed_recover t ht d F]
    exact (forward_contraction t ht _).trans
      (((localOperator t ht d).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (backward_contraction t ht F) (norm_nonneg _)))

theorem bare_norm (t : ℝ) (ht : 0 < t) (d : GroundData (1 / t ^ 2)) :
    ‖bare t d‖=d.value / t ^ 36 := by
  rw [bare,norm_smul,chordOperator_norm,mul_one,Real.norm_eq_abs,
    abs_of_pos (div_pos d.value_pos (pow_pos ht 36))]

/-- Both omitted off-diagonal blocks are included in this normalization estimate. -/
theorem normalization_error (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1)
    (d : GroundData (1 / t ^ 2)) :
    |d.value / t ^ 36-‖compressed t ht d‖| ≤ CubeBoundaryExterior.errorConstant*t := by
  rw [← bare_norm t ht d,← local_norm_eq t ht d]
  exact (abs_norm_sub_norm_le (bare t d) (localOperator t ht d)).trans
    (residual_norm_bound t ht d h1)

def groundScale (t : ℝ) : ℝ := (ground (1 / t ^ 2)).value / t ^ 36

theorem groundScale_tendsto :
    Tendsto groundScale (𝓝[>] (0:ℝ)) (𝓝 ‖actualLimitOperator‖) := by
  have hz : Tendsto (fun t : ℝ =>
      |groundScale t-‖actualOperatorFamily t‖|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_
      (by simpa using (tendsto_const_nhds.mul
        (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ)) :
          Tendsto (fun t : ℝ => CubeBoundaryExterior.errorConstant*t)
            (𝓝[>] (0:ℝ)) (𝓝 (CubeBoundaryExterior.errorConstant*0))))
    filter_upwards [self_mem_nhdsWithin,
      (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds]
      with t ht h1
    change |groundScale t-‖operatorFamily (fun t _ => ground (1/t^2)) t‖| ≤ _
    rw [operatorFamily_pos _ t ht]
    exact normalization_error t ht h1 (ground (1/t^2))
  have hs : Tendsto (fun t : ℝ => groundScale t-‖actualOperatorFamily t‖)
      (𝓝[>] (0:ℝ)) (𝓝 0) := (tendsto_zero_iff_abs_tendsto_zero _).mpr hz
  have h := hs.add actualOperatorFamily_tendsto.norm
  simpa only [sub_add_cancel,zero_add] using h

theorem limit_norm_lower : CubeRootGround.lowerConstant ≤ ‖actualLimitOperator‖ := by
  apply ge_of_tendsto groundScale_tendsto
  filter_upwards [self_mem_nhdsWithin,
    (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds]
    with t ht h1
  exact (CubeMatchedGround.rescaled_value_bounds t ht h1 (ground (1/t^2))).1

theorem limit_norm_positive : 0 < ‖actualLimitOperator‖ :=
  CubeRootGround.lowerConstant_pos.trans_le limit_norm_lower

theorem limit_nonzero : actualLimitOperator ≠ 0 :=
  norm_pos_iff.mp limit_norm_positive

def normalizedOperatorFamily (t : ℝ) : EuclideanL2 →L[ℝ] EuclideanL2 :=
  (groundScale t)⁻¹ • actualOperatorFamily t

def normalizedLimitOperator : EuclideanL2 →L[ℝ] EuclideanL2 :=
  ‖actualLimitOperator‖⁻¹ • actualLimitOperator

/-- The normalization is the actual stationary chord operator, with the chart maps retained. -/
theorem normalizedOperatorFamily_pos (t : ℝ) (ht : 0 < t) :
    normalizedOperatorFamily t=(forward t ht).comp
      ((chordOperator (ground (1 / t ^ 2))).comp (backward t ht)) := by
  have hn : groundScale t ≠ 0 :=
    (div_pos (ground (1 / t ^ 2)).value_pos (pow_pos ht 36)).ne'
  change (groundScale t)⁻¹ • operatorFamily (fun t _ => ground (1/t^2)) t = _
  rw [operatorFamily_pos _ t ht]
  change (groundScale t)⁻¹ • (groundScale t • _) = _
  rw [smul_smul,inv_mul_cancel₀ hn,one_smul]

theorem normalizedOperatorFamily_tendsto :
    Tendsto normalizedOperatorFamily (𝓝[>] (0:ℝ)) (𝓝 normalizedLimitOperator) :=
  (groundScale_tendsto.inv₀ limit_norm_positive.ne').smul actualOperatorFamily_tendsto

theorem normalizedLimitOperator_norm : ‖normalizedLimitOperator‖=1 := by
  rw [normalizedLimitOperator,norm_smul,norm_inv,norm_norm,
    inv_mul_cancel₀ limit_norm_positive.ne']

end OperatorDerivativeRewrite.Foundation.CubeGroundNormLimit
