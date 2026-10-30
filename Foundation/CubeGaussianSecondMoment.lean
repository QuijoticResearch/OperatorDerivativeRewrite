import Foundation.CubeGaussianSchurBound
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Genuine Gaussian volume moments needed by the actual radial channel test. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianSecondMoment
open CubeGaussianChannelGround SU2GaussianConeCoordinates SU2HemisphereJets

private def varianceParam (b : ℝ) (hb : 0 < b) : ℝ≥0 := ⟨(2*b)⁻¹,by positivity⟩
private def coefficient (b : ℝ) (hb : 0 < b) : ℝ :=
  (Real.sqrt (2*Real.pi*(varianceParam b hb : ℝ)))⁻¹

private theorem varianceParam_positive (b : ℝ) (hb : 0 < b) : 0 < varianceParam b hb := by
  change 0 < (2*b)⁻¹
  positivity

private theorem coefficient_positive (b : ℝ) (hb : 0 < b) : 0 < coefficient b hb := by
  unfold coefficient
  have h := varianceParam_positive b hb
  positivity

private theorem pdf_eq (b : ℝ) (hb : 0 < b) (y : ℝ) :
    gaussianPDFReal 0 (varianceParam b hb) y=coefficient b hb*Real.exp (-b*y^2) := by
  unfold gaussianPDFReal coefficient
  congr 1
  congr 1
  change -(y-0)^2/(2*((2*b)⁻¹))= -b*y^2
  field_simp [hb.ne']
  <;> ring

theorem scalar_pow_integrable (b : ℝ) (hb : 0 < b) (n : ℕ) :
    Integrable (fun y : ℝ => y^n*Real.exp (-b*y^2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := b) (s := (n:ℝ)) hb
    (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  simpa only [Real.rpow_natCast] using h

theorem scalar_first_integral (b : ℝ) (hb : 0 < b) :
    (∫ y : ℝ,y*Real.exp (-b*y^2))=0 := by
  have hv := (varianceParam_positive b hb).ne'
  have h : (∫ y : ℝ,y ∂gaussianReal 0 (varianceParam b hb))=0 := integral_id_gaussianReal
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  simp_rw [pdf_eq,smul_eq_mul] at h
  have he : (fun y : ℝ => coefficient b hb*Real.exp (-b*y^2)*y)=
      (fun y : ℝ => coefficient b hb*(y*Real.exp (-b*y^2))) := by funext y; ring
  rw [he,integral_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (coefficient_positive b hb).ne'

theorem scalar_second_integral (b : ℝ) (hb : 0 < b) :
    (∫ y : ℝ,y^2*Real.exp (-b*y^2))=(2*b)⁻¹*(∫ y : ℝ,Real.exp (-b*y^2)) := by
  have hv := (varianceParam_positive b hb).ne'
  have h0 : (∫ y : ℝ,(1:ℝ) ∂gaussianReal 0 (varianceParam b hb))=1 := by simp
  rw [integral_gaussianReal_eq_integral_smul hv] at h0
  simp_rw [pdf_eq,smul_eq_mul,mul_one] at h0
  rw [integral_const_mul] at h0
  have h2 := variance_fun_id_gaussianReal (μ := 0) (v := varianceParam b hb)
  rw [variance_eq_integral (by fun_prop),integral_id_gaussianReal] at h2
  simp only [sub_zero] at h2
  rw [integral_gaussianReal_eq_integral_smul hv] at h2
  simp_rw [pdf_eq,smul_eq_mul] at h2
  have he : (fun y : ℝ => coefficient b hb*Real.exp (-b*y^2)*y^2)=
      (fun y : ℝ => coefficient b hb*(y^2*Real.exp (-b*y^2))) := by funext y; ring
  rw [he,integral_const_mul] at h2
  apply mul_left_cancel₀ (coefficient_positive b hb).ne'
  rw [h2]
  change (2*b)⁻¹=coefficient b hb*((2*b)⁻¹*(∫ y : ℝ,Real.exp (-b*y^2)))
  rw [mul_left_comm,h0,mul_one]

end OperatorDerivativeRewrite.Foundation.CubeGaussianSecondMoment
