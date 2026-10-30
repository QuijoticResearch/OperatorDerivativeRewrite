import Foundation.CubeNormalizedKernelSquare

/-! A genuine upper contraction bound on the entire limiting ground complement. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeLimitComplementGap
open CubeBoundaryChartL2 CubeKernelOperatorBound CubeNormalizedKernelSquare
open CubeGaussianGroundEigenvector CubeCompressedNormLimit CubeGaussianSchurBound
open CubeGaussianSquareRoot

theorem tensor_inner (A B F G : EuclideanL2) :
    inner ℝ (tensorClass A B) (tensorClass F G)=inner ℝ A F*inner ℝ B G := by
  rw [L2.inner_def]
  calc
    _ = ∫ p : CubeChartAction.Boundary × CubeChartAction.Boundary,
        (B p.1*G p.1)*(A p.2*F p.2) := by
      apply integral_congr_ae
      filter_upwards [tensorClass_coe A B,tensorClass_coe F G] with p hp hq
      rw [hp,hq,Real.inner_apply]
      unfold tensor
      ring
    _ = (∫ x : CubeChartAction.Boundary,B x*G x)*(∫ y : CubeChartAction.Boundary,A y*F y) :=
      integral_prod_mul (μ := (volume : Measure CubeChartAction.Boundary))
        (ν := (volume : Measure CubeChartAction.Boundary))
        (fun x : CubeChartAction.Boundary => B x*G x)
        (fun y : CubeChartAction.Boundary => A y*F y)
    _ = _ := by
      rw [L2.inner_def,L2.inner_def]
      simp_rw [Real.inner_apply]
      ring

def groundKernel : KernelL2 := (‖stateClass‖^2)⁻¹ • tensorClass stateClass stateClass

theorem groundKernel_norm : ‖groundKernel‖=1 := by
  have hn := norm_pos_iff.mpr stateClass_nonzero
  rw [groundKernel,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (sq_nonneg _),tensorClass_norm]
  rw [← pow_two,inv_mul_cancel₀ (pow_ne_zero 2 hn.ne')]

theorem normalized_pairing (F G : EuclideanL2) :
    inner ℝ (CubeGroundNormLimit.normalizedLimitOperator F) G=
      inner ℝ normalizedKernel (tensorClass F G) := by
  simp only [CubeGroundNormLimit.normalizedLimitOperator,smul_apply,real_inner_smul_left,
    normalizedKernel,norm_eq_eigenvalue,actualLimitOperator_pairing]

theorem normalized_ground_inner : inner ℝ normalizedKernel groundKernel=1 := by
  rw [groundKernel,real_inner_smul_right,← normalized_pairing,
    normalized_ground_fixed,real_inner_self_eq_norm_sq]
  exact inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr stateClass_nonzero))

theorem groundKernel_pairing (F G : EuclideanL2) :
    inner ℝ groundKernel (tensorClass F G)=
      (‖stateClass‖^2)⁻¹*(inner ℝ stateClass F*inner ℝ stateClass G) := by
  rw [groundKernel,real_inner_smul_left,tensor_inner]

def remainder : KernelL2 := normalizedKernel-groundKernel

def gapConstant : ℝ := 23/25

theorem gapConstant_bounds : 0 < gapConstant ∧ gapConstant < 1 := by norm_num [gapConstant]

theorem remainder_norm_sq : ‖remainder‖^2=‖normalizedKernel‖^2-1 := by
  rw [remainder,norm_sub_sq_real,groundKernel_norm,normalized_ground_inner]
  ring

theorem remainder_norm_lt : ‖remainder‖ < gapConstant := by
  have hb := normalizedKernel_norm_sq.trans factorBound_le
  have hr := remainder_norm_sq
  have hq : (25/24:ℝ)^15-1 < (23/25:ℝ)^2 := by norm_num
  have hn := norm_nonneg remainder
  unfold gapConstant
  nlinarith

theorem complement_pairing (F G : EuclideanL2) (hF : inner ℝ stateClass F=0) :
    inner ℝ (CubeGroundNormLimit.normalizedLimitOperator F) G=
      inner ℝ remainder (tensorClass F G) := by
  rw [remainder,inner_sub_left,groundKernel_pairing,hF,zero_mul,mul_zero,sub_zero]
  exact normalized_pairing F G

theorem complement_contraction (F : EuclideanL2) (hF : inner ℝ stateClass F=0) :
    ‖CubeGroundNormLimit.normalizedLimitOperator F‖ ≤ gapConstant*‖F‖ := by
  let A := CubeGroundNormLimit.normalizedLimitOperator
  by_cases hz : A F=0
  · simp only [show CubeGroundNormLimit.normalizedLimitOperator F=0 from hz,norm_zero]
    exact mul_nonneg gapConstant_bounds.1.le (norm_nonneg _)
  have hn := norm_pos_iff.mpr hz
  have h := abs_real_inner_le_norm remainder (tensorClass F (A F))
  rw [← complement_pairing F (A F) hF,real_inner_self_eq_norm_sq,
    abs_of_nonneg (sq_nonneg _),tensorClass_norm] at h
  have hb : ‖A F‖*‖A F‖ ≤ (gapConstant*‖F‖)*‖A F‖ := by
    calc
      _ = ‖A F‖^2 := by ring
      _ ≤ ‖remainder‖*(‖A F‖*‖F‖) := h
      _ ≤ gapConstant*(‖A F‖*‖F‖) :=
        mul_le_mul_of_nonneg_right remainder_norm_lt.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  exact (mul_le_mul_iff_left₀ hn).mp (by nlinarith [hb])

end OperatorDerivativeRewrite.Foundation.CubeLimitComplementGap
