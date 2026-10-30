import Foundation.CubeChartCompressedKernel

/-! The L2 kernel bound for the actual compressed operators, on their entire Hilbert domain. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeKernelOperatorBound
open CubeChartAction CubeBoundaryChartL2 CubeChartCompressedKernel CubeSlabGround

abbrev KernelL2 := Lp ℝ 2 (volume : Measure (Boundary × Boundary))
def tensor (F G : EuclideanL2) (p : Boundary × Boundary) : ℝ := G p.1*F p.2

theorem tensor_memLp (F G : EuclideanL2) : MemLp (tensor F G) 2 volume := by
  have hm : Measurable (tensor F G) :=
    ((Lp.stronglyMeasurable G).measurable.comp measurable_fst).mul
      ((Lp.stronglyMeasurable F).measurable.comp measurable_snd)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  convert (Lp.memLp G).integrable_sq.mul_prod (Lp.memLp F).integrable_sq using 1
  funext p
  unfold tensor
  ring

def tensorClass (F G : EuclideanL2) : KernelL2 := (tensor_memLp F G).toLp (tensor F G)
theorem tensorClass_coe (F G : EuclideanL2) : tensorClass F G =ᵐ[volume] tensor F G := MemLp.coeFn_toLp _

theorem tensorClass_norm (F G : EuclideanL2) : ‖tensorClass F G‖=‖G‖*‖F‖ := by
  have hF : (∫ Y : Boundary,F Y^2)=‖F‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using (BochnerL2Dominated.norm_sq_integral F).symm
  have hG : (∫ X : Boundary,G X^2)=‖G‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using (BochnerL2Dominated.norm_sq_integral G).symm
  have hh : ‖tensorClass F G‖^2=(‖G‖*‖F‖)^2 := by
    rw [BochnerL2Dominated.norm_sq_integral]
    calc
      _ = ∫ p : Boundary × Boundary,G p.1^2*F p.2^2 := by
        apply integral_congr_ae
        filter_upwards [tensorClass_coe F G] with p hp
        rw [hp,Real.norm_eq_abs,sq_abs]
        unfold tensor
        ring
      _ = (∫ X : Boundary,G X^2)*(∫ Y : Boundary,F Y^2) :=
        integral_prod_mul (μ := (volume : Measure Boundary)) (ν := (volume : Measure Boundary))
          (fun X => G X^2) (fun Y => F Y^2)
      _ = _ := by rw [hF,hG]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hh

/-- L2 against a true tensor gives joint integrability before the Fubini identification. -/
theorem pairing_eq_integral (k : Boundary × Boundary → ℝ) (hk : MemLp k 2 volume)
    (F G : EuclideanL2) : inner ℝ (hk.toLp k) (tensorClass F G)=
      ∫ X : Boundary,G X*(∫ Y : Boundary,k (X,Y)*F Y) := by
  have hi : Integrable (fun p : Boundary × Boundary => k p*(G p.1*F p.2)) :=
    hk.integrable_mul (tensor_memLp F G)
  rw [L2.inner_def]
  calc
    _ = ∫ p : Boundary × Boundary,k p*(G p.1*F p.2) := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hk,tensorClass_coe F G] with p hK hT
      rw [hK,hT,Real.inner_apply]
      rfl
    _ = ∫ X : Boundary,∫ Y : Boundary,k (X,Y)*(G X*F Y) := integral_prod _ hi
    _ = ∫ X : Boundary,∫ Y : Boundary,G X*(k (X,Y)*F Y) := by
      apply integral_congr_ae
      filter_upwards with X
      apply integral_congr_ae
      filter_upwards with Y
      ring
    _ = _ := by simp_rw [integral_const_mul]

theorem opNorm_le_of_pairing (A : EuclideanL2 →L[ℝ] EuclideanL2) (K : KernelL2)
    (hA : ∀ F G : EuclideanL2,inner ℝ (A F) G=inner ℝ K (tensorClass F G)) : ‖A‖ ≤ ‖K‖ := by
  apply A.opNorm_le_bound (norm_nonneg K)
  intro F
  have h := norm_inner_le_norm (𝕜 := ℝ) K (tensorClass F (A F))
  rw [← hA F (A F),real_inner_self_eq_norm_sq,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),
    tensorClass_norm] at h
  by_cases h0 : ‖A F‖=0
  · rw [h0]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · have hp : 0 < ‖A F‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    apply (mul_le_mul_iff_left₀ hp).mp
    rw [pow_two] at h
    exact h.trans_eq (by rw [mul_comm ‖A F‖ ‖F‖,← mul_assoc])

def kernelClass (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) : KernelL2 :=
  (CubeBoundaryHaarL2.kernel_memLp t ht h1).toLp (CubeBoundaryHaarL2.kernel t)
theorem kernelClass_coe (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    kernelClass t ht h1 =ᵐ[volume] CubeBoundaryHaarL2.kernel t := MemLp.coeFn_toLp _

theorem compressed_pairing (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1)
    (d : GroundData (1/t^2)) (F G : EuclideanL2) :
    inner ℝ (compressed t ht d F) G=inner ℝ (kernelClass t ht h1) (tensorClass F G) := by
  rw [compressed_kernel_pairing]
  exact (pairing_eq_integral _ (CubeBoundaryHaarL2.kernel_memLp t ht h1) F G).symm

/-- Quantitative norm estimate for the ACTUAL operators and their genuine weighted kernels. -/
theorem compressed_difference_bound (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (h1 : t ≤ 1) (hs1 : s ≤ 1)
    (d : GroundData (1/t^2)) (e : GroundData (1/s^2)) :
    ‖compressed t ht d-compressed s hs e‖ ≤ ‖kernelClass t ht h1-kernelClass s hs hs1‖ := by
  apply opNorm_le_of_pairing
  intro F G
  simp only [ContinuousLinearMap.sub_apply,inner_sub_left]
  rw [compressed_pairing t ht h1,compressed_pairing s hs hs1]

end OperatorDerivativeRewrite.Foundation.CubeKernelOperatorBound
