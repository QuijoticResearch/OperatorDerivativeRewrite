import Foundation.CubeGaussianSquareRoot

/-! Quantitative squared norm of the actual normalized kernel. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeNormalizedKernelSquare
open CubeGaussianModes CubeGaussianChannelGround CubeGaussianSquareChannel CubeGaussianSquareRoot
open CubeChartAction CubeGaussianKernelChannels CubeGaussianGroundEigenvector
open CubeCompressedNormLimit CubeKernelOperatorBound

attribute [local irreducible] precision width CubeBoundaryHaarL2.limit

def average (p : Boundary × Boundary) : ℝ := ∫ c,fixedKernel c p ∂QuaternionSU2Representation.law

theorem average_measurable : Measurable average :=
  fixedKernel_continuous.measurable.stronglyMeasurable.integral_prod_left'.measurable

theorem average_sq_integrable : Integrable (fun p : Boundary × Boundary => (average p)^2) := by
  apply averageSquare_integrable.mono' (average_measurable.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact root_jensen p)

theorem average_sq_integral_le : (∫ p : Boundary × Boundary,(average p)^2) ≤ squareMass := by
  rw [← averageSquare_integral]
  exact integral_mono average_sq_integrable averageSquare_integrable root_jensen

theorem original_square_integral :
    (∫ p : Boundary × Boundary,(CubeBoundaryHaarL2.limit p)^2)=
      4096*constant^2*(∫ p : Boundary × Boundary,(average p)^2) := by
  change (∫ p : Boundary × Boundary,(CubeBoundaryHaarL2.limit p)^2 ∂(volume.prod volume))=_
  rw [integral_prod _ CubeBoundaryHaarL2.limit_memLp.integrable_sq]
  rw [coordinate_integral]
  have hi (x : Boundary) : (∫ Y : Boundary,(CubeBoundaryHaarL2.limit (synthesis x,Y))^2)=
      64*(∫ y : Boundary,(CubeBoundaryHaarL2.limit (synthesis x,synthesis y))^2) := coordinate_integral _
  simp_rw [hi,actual_kernel_channels,analysis_synthesis,mul_pow]
  change 64*(∫ x : Boundary,64*(∫ y : Boundary,constant^2*(average (x,y))^2))=_
  simp_rw [integral_const_mul]
  have hp := integral_prod (fun p : Boundary × Boundary => (average p)^2) average_sq_integrable
  rw [← hp]
  ring_nf
  rfl

theorem orders_ge_four (i : Fin 5) : 4 ≤ orders i := by
  fin_cases i <;> norm_num [orders]

theorem channel_factor_bound (i : Fin 5) : (precision i+width i)/(2*width i) ≤ (25/24:ℝ) := by
  have hw := weights_positive i
  have ha := precision_positive i
  have hs := width_positive i
  have hl : 3*weights i ≤ 2*precision i := by
    unfold precision
    have hm := mul_nonneg hw.le (sub_nonneg.mpr (orders_ge_four i))
    nlinarith
  have hl2 : 9*(weights i)^2 ≤ 4*(precision i)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (by positivity : 0 ≤ 2*precision i+3*weights i)]
  have hx : (12*precision i)^2 < (13*width i)^2 := by
    nlinarith [width_relation i,sq_pos_of_pos hw]
  have hlin := (sq_lt_sq₀ (by positivity : 0 ≤ 12*precision i)
    (by positivity : 0 ≤ 13*width i)).mp hx
  apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hs)).mpr
  linarith

theorem factorBound_le : factorBound ≤ (25/24:ℝ)^15 := by
  have h : factorBound ≤ ∏ _i : Fin 5,(25/24:ℝ)^3 := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact pow_nonneg (div_nonneg (add_pos (precision_positive i) (width_positive i)).le
        (mul_pos (by norm_num : (0:ℝ)<2) (width_positive i)).le) 3
    · intro i _
      exact pow_le_pow_left₀ (div_nonneg (add_pos (precision_positive i) (width_positive i)).le
        (mul_pos (by norm_num : (0:ℝ)<2) (width_positive i)).le) (channel_factor_bound i) 3
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← pow_mul] using h

theorem factorBound_lt_two : factorBound < 2 :=
  factorBound_le.trans_lt (by norm_num)

def normalizedKernel : KernelL2 := eigenvalue⁻¹ • limitKernelClass

theorem normalizedKernel_norm_sq : ‖normalizedKernel‖^2 ≤ factorBound := by
  have hn : ‖limitKernelClass‖^2=(∫ p : Boundary × Boundary,(CubeBoundaryHaarL2.limit p)^2) := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [limitKernelClass_coe] with p hp
    rw [hp,Real.norm_eq_abs,sq_abs]
  have hb : ‖limitKernelClass‖^2 ≤ eigenvalue^2*factorBound := by
    rw [hn,original_square_integral]
    have h := mul_le_mul_of_nonneg_left average_sq_integral_le
      (by positivity : 0 ≤ 4096*constant^2)
    convert h using 1 <;> unfold eigenvalue squareMass <;> ring
  rw [normalizedKernel,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos eigenvalue_positive,mul_pow]
  have h := mul_le_mul_of_nonneg_left hb (sq_nonneg eigenvalue⁻¹)
  simpa only [← mul_assoc,← mul_pow,inv_mul_cancel₀ eigenvalue_positive.ne',one_pow,one_mul] using h

end OperatorDerivativeRewrite.Foundation.CubeNormalizedKernelSquare
