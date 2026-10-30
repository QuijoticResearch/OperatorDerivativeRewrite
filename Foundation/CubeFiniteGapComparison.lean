import Foundation.CubeRankOneComparison

/-! Actual finite operator comparison with the proved limiting rank-one remainder. -/
noncomputable section
open Filter Topology
namespace OperatorDerivativeRewrite.Foundation.CubeFiniteGapComparison
open CubeBoundaryChartL2 CubeGroundNormLimit CubeSlabGround CubeChordOperator CubeCompressedNormLimit
open CubeFullCompressionError CubeBoundaryExterior CubeChartCompressedKernel
open CubeGaussianGroundEigenvector CubeGaussianSchurBound CubeLimitComplementGap CubeKernelOperatorBound

def vacuumCoefficient : ℝ := (‖stateClass‖^2)⁻¹

def exteriorRate (t : ℝ) : ℝ := (groundScale t)⁻¹*(errorConstant*t)

def distance (t : ℝ) : ℝ := ‖normalizedOperatorFamily t-normalizedLimitOperator‖

def rate (t : ℝ) : ℝ := gapConstant+exteriorRate t+distance t

theorem limiting_form (F : EuclideanL2) :
    -gapConstant*‖F‖^2 ≤ inner ℝ (normalizedLimitOperator F) F ∧
    inner ℝ (normalizedLimitOperator F) F ≤ gapConstant*‖F‖^2+
      vacuumCoefficient*(inner ℝ stateClass F)^2 := by
  have h := abs_real_inner_le_norm CubeLimitComplementGap.remainder (tensorClass F F)
  rw [CubeLimitComplementGap.remainder,inner_sub_left,← normalized_pairing,
    groundKernel_pairing,tensorClass_norm] at h
  have hb := h.trans (mul_le_mul_of_nonneg_right remainder_norm_lt.le
    (mul_nonneg (norm_nonneg F) (norm_nonneg F)))
  have he : |inner ℝ (normalizedLimitOperator F) F-vacuumCoefficient*(inner ℝ stateClass F)^2| ≤
      gapConstant*‖F‖^2 := by simpa only [vacuumCoefficient,← pow_two] using hb
  have hk : 0 ≤ vacuumCoefficient*(inner ℝ stateClass F)^2 :=
    mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (sq_nonneg _)
  constructor <;> nlinarith [abs_le.mp he]

theorem exterior_bound (t : ℝ) (ht : 0<t) (h1 : t≤1) (f : ChordL2) :
    ‖chordOperator (ground (1/t^2)) f-
      backward t ht (normalizedOperatorFamily t (forward t ht f))‖ ≤ exteriorRate t*‖f‖ := by
  have hs : 0<groundScale t := div_pos (ground (1/t^2)).value_pos (pow_pos ht 36)
  have he : CubeFullCompressionError.residual t ht (ground (1/t^2)) f=
      groundScale t • (chordOperator (ground (1/t^2)) f-
        backward t ht (normalizedOperatorFamily t (forward t ht f))) := by
    simp only [CubeFullCompressionError.residual,ContinuousLinearMap.sub_apply,bare,
      localOperator,compressed,ContinuousLinearMap.comp_apply,smul_apply,map_smul,
      normalizedOperatorFamily_pos t ht,smul_sub]
    rfl
  have h := ((CubeFullCompressionError.residual t ht (ground (1/t^2))).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (residual_norm_bound t ht _ h1) (norm_nonneg f))
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at h
  unfold exteriorRate
  rw [mul_assoc]
  exact (le_inv_mul_iff₀ hs).mpr h

theorem vector_comparison (t : ℝ) (ht : 0<t) (h1 : t≤1) (f : ChordL2) :
    ‖chordOperator (ground (1/t^2)) f-backward t ht (normalizedLimitOperator (forward t ht f))‖ ≤
      (exteriorRate t+distance t)*‖f‖ := by
  have he : chordOperator (ground (1/t^2)) f-backward t ht (normalizedLimitOperator (forward t ht f))=
      (chordOperator (ground (1/t^2)) f-backward t ht (normalizedOperatorFamily t (forward t ht f)))+
        backward t ht ((normalizedOperatorFamily t-normalizedLimitOperator) (forward t ht f)) := by
    simp only [sub_apply,map_sub]
    abel
  have hd : ‖backward t ht ((normalizedOperatorFamily t-normalizedLimitOperator) (forward t ht f))‖ ≤
      distance t*‖f‖ := by
    exact (backward_contraction t ht _).trans
      (((normalizedOperatorFamily t-normalizedLimitOperator).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (forward_contraction t ht f) (norm_nonneg _)))
  rw [he]
  exact (norm_add_le _ _).trans (by nlinarith [exterior_bound t ht h1 f,hd])

theorem quadratic_comparison (t : ℝ) (ht : 0<t) (h1 : t≤1) (f : ChordL2) :
    |inner ℝ (chordOperator (ground (1/t^2)) f) f-
      inner ℝ (normalizedLimitOperator (forward t ht f)) (forward t ht f)| ≤
        (exteriorRate t+distance t)*‖f‖^2 := by
  have he : inner ℝ (chordOperator (ground (1/t^2)) f) f-
      inner ℝ (normalizedLimitOperator (forward t ht f)) (forward t ht f)=
        inner ℝ (chordOperator (ground (1/t^2)) f-
          backward t ht (normalizedLimitOperator (forward t ht f))) f := by
    rw [inner_sub_left]
    change _ = inner ℝ (chordOperator (ground (1/t^2)) f) f-
      inner ℝ ((forward t ht).adjoint (normalizedLimitOperator (forward t ht f))) f
    rw [ContinuousLinearMap.adjoint_inner_left]
  rw [he]
  exact (abs_real_inner_le_norm _ f).trans
    (by nlinarith [mul_le_mul_of_nonneg_right (vector_comparison t ht h1 f) (norm_nonneg f)])

theorem finite_form (t : ℝ) (ht : 0<t) (h1 : t≤1) (f : ChordL2) :
    -rate t*‖f‖^2 ≤ inner ℝ (chordOperator (ground (1/t^2)) f) f ∧
    inner ℝ (chordOperator (ground (1/t^2)) f) f ≤ rate t*‖f‖^2+
      vacuumCoefficient*(inner ℝ (backward t ht stateClass) f)^2 := by
  have hl := limiting_form (forward t ht f)
  have hc := abs_le.mp (quadratic_comparison t ht h1 f)
  have hn := pow_le_pow_left₀ (norm_nonneg (forward t ht f)) (forward_contraction t ht f) 2
  have hq := mul_le_mul_of_nonneg_left hn gapConstant_bounds.1.le
  have hi : inner ℝ (backward t ht stateClass) f=inner ℝ stateClass (forward t ht f) :=
    ContinuousLinearMap.adjoint_inner_left (forward t ht) f stateClass
  rw [hi]
  unfold rate
  constructor <;> nlinarith [hl.1,hl.2,hc.1,hc.2]

theorem exteriorRate_tendsto : Tendsto exteriorRate (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have h := (exact_groundScale_limit.inv₀ eigenvalue_positive.ne').mul
    ((tendsto_const_nhds (x := errorConstant)).mul
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ)))
  change Tendsto (fun t : ℝ => (groundScale t)⁻¹*(errorConstant*t)) (𝓝[>] (0:ℝ)) (𝓝 0)
  simpa only [mul_zero] using h

theorem distance_tendsto : Tendsto distance (𝓝[>] (0:ℝ)) (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.mp normalizedOperatorFamily_tendsto

theorem rate_tendsto : Tendsto rate (𝓝[>] (0:ℝ)) (𝓝 gapConstant) := by
  change Tendsto (fun t : ℝ => gapConstant+exteriorRate t+distance t) (𝓝[>] (0:ℝ)) (𝓝 gapConstant)
  simpa only [add_zero] using (tendsto_const_nhds.add exteriorRate_tendsto).add distance_tendsto

end OperatorDerivativeRewrite.Foundation.CubeFiniteGapComparison
