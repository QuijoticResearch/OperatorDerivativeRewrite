import Foundation.GaussianRandomDensityKernel

/-! Exact weighted Gaussian translation for each fixed past coefficient. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianDensityTranslation
open GaussianCore GaussianRandomDensityKernel
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def tilted (a : ℝ) : Measure ℝ := γ.withDensity (fun y => ENNReal.ofReal (kernel a y))

theorem kernel_measurable (a : ℝ) : Measurable (kernel a) := by
  unfold kernel
  fun_prop

theorem pdf_product (a y : ℝ) :
    gaussianPDFReal 0 1 y*kernel a y=gaussianPDFReal (-a) 1 y := by
  simp only [gaussianPDFReal,kernel,NNReal.coe_one,mul_one,sub_zero,sub_neg_eq_add]
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem tilted_eq_gaussian (a : ℝ) : tilted a=gaussianReal (-a) 1 := by
  rw [tilted,γ,gaussianReal_of_var_ne_zero 0 (by norm_num),
    ← withDensity_mul volume (measurable_gaussianPDF 0 1)
      (kernel_measurable a).ennreal_ofReal,
    gaussianReal_of_var_ne_zero (-a) (by norm_num)]
  congr 1
  funext y
  change gaussianPDF 0 1 y*ENNReal.ofReal (kernel a y)=gaussianPDF (-a) 1 y
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 y),pdf_product]

theorem shifted_map (a : ℝ) : (tilted a).map (fun y => y+a)=γ := by
  rw [tilted_eq_gaussian,gaussianReal_map_add_const]
  simp [γ]

theorem shift_hasLaw (a : ℝ) : HasLaw (fun y : ℝ => y+a) γ (tilted a) :=
  ⟨by fun_prop,shifted_map a⟩

theorem fiber_lintegral (a : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, ENNReal.ofReal (kernel a y)*f (y+a) ∂γ)=∫⁻ z, f z ∂γ := by
  have ht := (shift_hasLaw a).lintegral_comp hf.aemeasurable
  rw [tilted] at ht
  have hw := lintegral_withDensity_eq_lintegral_mul γ
    (f := fun y => ENNReal.ofReal (kernel a y)) (kernel_measurable a).ennreal_ofReal
    (g := fun y => f (y+a)) (hf.comp (measurable_id.add_const a))
  exact hw.symm.trans ht

end OperatorDerivativeRewrite.Foundation.GaussianDensityTranslation
