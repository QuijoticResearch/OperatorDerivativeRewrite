import Foundation.EvenEntireZeroFreeRigidity
import Foundation.RiemannQuarticEntireGrowth

/-! The actual quartic transform is never constant and has a complex zero
at every real time. This neither locates that zero nor supplies the missing
global product and polynomial-approximation construction. -/
noncomputable section
open MeasureTheory Set Complex
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticZeroFreeRigidity
open RiemannQuarticDomain RiemannQuarticKernel RiemannQuarticFlow
open RiemannQuarticReality RiemannQuarticEvolution

theorem imaginary_value_strict (t : ℝ) : imaginaryValue t 0 < imaginaryValue t 1 := by
  let F : ℝ → ℝ := fun u => weighted 0 t 0 u * (Real.cosh u - 1)
  have hint : Integrable F halfLine := by
    have h := (imaginary_integrable t 1).sub (weighted_integrable 0 t 0)
    change Integrable (fun u => weighted 0 t 0 u * Real.cosh (u*1) -
      weighted 0 t 0 u) halfLine at h
    simpa only [F,mul_one,mul_sub,mul_one] using h
  have hw (u : ℝ) (hu : 0 ≤ u) : 0 < weighted 0 t 0 u := by
    unfold weighted
    simp only [pow_zero,one_mul,zero_mul,add_zero]
    exact mul_pos (Real.exp_pos _) (kernel_pos u hu)
  have hpos : 0 < ∫ u, F u ∂halfLine := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae (μ := volume) (s := Ici (0 : ℝ))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
        exact mul_nonneg (hw u hu).le (sub_nonneg.mpr (Real.one_le_cosh u))) hint).mpr
    have hsub : Icc (1 : ℝ) 2 ⊆ Function.support F ∩ Ici 0 := by
      intro u hu
      have hu1 : 1 ≤ u := hu.1
      have hc : 0 < Real.cosh u - 1 := sub_pos.mpr (Real.one_lt_cosh.mpr (by linarith))
      exact ⟨(mul_pos (hw u (by linarith)) hc).ne',le_trans (by norm_num : (0 : ℝ) ≤ 1) hu1⟩
    exact lt_of_lt_of_le (by simp : 0 < volume (Icc (1 : ℝ) 2)) (measure_mono hsub)
  have hid : imaginaryValue t 1 - imaginaryValue t 0 = ∫ u, F u ∂halfLine := by
    rw [imaginaryValue,imaginaryValue,← integral_sub
      (imaginary_integrable t 1) (imaginary_integrable t 0)]
    congr 1
    funext u
    simp [F,mul_sub]
  linarith

theorem flow_not_constant (t : ℝ) : ¬ ∀ z : ℂ, flow t z = flow t 0 := by
  intro h
  have hz := h Complex.I
  have hi := flow_imaginary t 1
  have h0 := flow_imaginary t 0
  simp only [Complex.ofReal_one,mul_one] at hi
  simp only [Complex.ofReal_zero,mul_zero] at h0
  rw [hi,h0] at hz
  have he := congrArg Complex.re hz
  simp only [Complex.ofReal_re] at he
  exact (ne_of_gt (imaginary_value_strict t)) he

theorem exists_complex_zero (t : ℝ) : ∃ z : ℂ, flow t z = 0 := by
  by_contra h
  have hne : ∀ z, flow t z ≠ 0 := by simpa using h
  obtain ⟨C,hC,hb⟩ := RiemannQuarticEntireGrowth.exists_subquadratic_growth t
  exact flow_not_constant t
    (EvenEntireZeroFreeRigidity.even_zero_free_constant (flow t) (flow_differentiable t)
      (flow_even t) hne C hC hb)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticZeroFreeRigidity
