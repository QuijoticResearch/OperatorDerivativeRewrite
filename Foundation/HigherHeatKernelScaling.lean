import Foundation.HigherHeatPathObstruction

/-! Exact self-similarity of the constructed even-order heat kernels. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped NNReal SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatKernelScaling
open GaussianSchwartzKernel HigherHeatSignedLaws

theorem symbol_scaling (m : ℕ) (t c : ℝ≥0) (x : ℝ) :
    HigherHeatL2.symbol m (t*c^(2*m)) x = HigherHeatL2.symbol m t ((c : ℝ)*x) := by
  simp only [HigherHeatL2.symbol,NNReal.coe_mul,NNReal.coe_pow,mul_pow]
  congr 2
  ring

theorem kernel_scaling (m : ℕ) (hm : 0 < m) (t c : ℝ≥0)
    (ht : 0 < t) (hc : 0 < c) (x : ℝ) :
    evenKernel m hm (t*c^(2*m)) (mul_pos ht (pow_pos hc _)) x =
      (c : ℝ)⁻¹ • evenKernel m hm t ht (x/(c : ℝ)) := by
  let g : ℝ → ℂ := fun y => Complex.exp (((2*Real.pi*(y*(x/(c : ℝ)))) : ℝ)*Complex.I) *
    HigherHeatL2.symbol m t y
  have hi : evenKernel m hm (t*c^(2*m)) (mul_pos ht (pow_pos hc _)) x =
      ∫ y : ℝ, g ((c : ℝ)*y) := by
    simp only [evenKernel,SchwartzMap.fourierInv_coe,Real.fourierInv_eq',evenSymbol_apply,
      RCLike.inner_apply,conj_trivial,smul_eq_mul,symbol_scaling]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [g]
      congr 3
      field_simp
  rw [hi,Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr hc)]
  congr 1
  simp only [evenKernel,SchwartzMap.fourierInv_coe,Real.fourierInv_eq',evenSymbol_apply,
    RCLike.inner_apply,conj_trivial,smul_eq_mul,g]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [mul_comm y (x/(c : ℝ))]

theorem realKernel_scaling (m : ℕ) (hm : 0 < m) (t c : ℝ≥0)
    (ht : 0 < t) (hc : 0 < c) (x : ℝ) :
    realKernel m hm (t*c^(2*m)) (mul_pos ht (pow_pos hc _)) x =
      (c : ℝ)⁻¹ * realKernel m hm t ht (x/(c : ℝ)) := by
  have h := congrArg Complex.re (kernel_scaling m hm t c ht hc x)
  simpa only [realKernel,SchwartzMap.postcompCLM_apply,Complex.reCLM_apply,
    Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using h

theorem norm_integral_scaling (m : ℕ) (hm : 0 < m) (t c : ℝ≥0)
    (ht : 0 < t) (hc : 0 < c) :
    (∫ x : ℝ, ‖realKernel m hm (t*c^(2*m)) (mul_pos ht (pow_pos hc _)) x‖) =
      ∫ x : ℝ, ‖realKernel m hm t ht x‖ := by
  have hcR : 0 < (c : ℝ) := hc
  simp_rw [realKernel_scaling m hm t c ht hc,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hcR.le)]
  rw [integral_const_mul]
  have hi := Measure.integral_comp_inv_mul_left (fun y : ℝ => ‖realKernel m hm t ht y‖) (c : ℝ)
  have he : (∫ x : ℝ, ‖realKernel m hm t ht (x/(c : ℝ))‖) =
      (c : ℝ) * ∫ x : ℝ, ‖realKernel m hm t ht x‖ := by
    simpa only [div_eq_mul_inv,mul_comm,abs_of_pos hcR,smul_eq_mul] using hi
  rw [he,← mul_assoc,inv_mul_cancel₀ (ne_of_gt hcR),one_mul]

end OperatorDerivativeRewrite.Foundation.HigherHeatKernelScaling
