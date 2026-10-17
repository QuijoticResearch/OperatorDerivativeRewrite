import Foundation.SignedDensityIntegral

/-! Actual signed integration on the full L1 domain of the total-variation measure. -/
noncomputable section
open MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.SignedAbsoluteIntegration

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

def absoluteDensity (f : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun x => ENNReal.ofReal |f x|)

theorem variation_density (f : Ω → ℝ) (hf : Integrable f μ) :
    (μ.withDensityᵥ f).variation=absoluteDensity μ f := by
  rw [Measure.variation_withDensityᵥ hf]
  simp only [absoluteDensity,Real.enorm_eq_ofReal_abs]

theorem signed_integrable_iff (f : Ω → ℝ) (hf : Integrable f μ) (g : Ω → ℂ) :
    (μ.withDensityᵥ f).Integrable g ↔ Integrable g (absoluteDensity μ f) := by
  simp only [VectorMeasure.Integrable,variation_density μ f hf]

theorem integral_density (f : Ω → ℝ) (hf : Integrable f μ) (hfm : Measurable f)
    (g : Ω → ℂ) (hi : Integrable g (absoluteDensity μ f)) :
    (∫ᵛ x, g x ∂<•μ.withDensityᵥ f)=(∫ x, f x • g x ∂μ) := by
  let P := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let N := μ.withDensity (fun x => ENNReal.ofReal (-f x))
  letI : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hf.2
  letI : IsFiniteMeasure N := isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hP : P ≤ absoluteDensity μ f := withDensity_mono
    (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (le_abs_self (f x)))
  have hN : N ≤ absoluteDensity μ f := withDensity_mono
    (Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (neg_le_abs (f x)))
  have hiP : Integrable g P := hi.mono_measure hP
  have hiN : Integrable g N := hi.mono_measure hN
  have hvP : P.toSignedMeasure.Integrable g := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using hiP
  have hvN : N.toSignedMeasure.Integrable g := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using hiN
  have hmn : Measurable (fun x => -f x) := hfm.neg
  have hrP := (integrable_withDensity_iff_integrable_smul₀' hfm.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hiP
  have hrN := (integrable_withDensity_iff_integrable_smul₀' hmn.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hiN
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hf]
  rw [VectorMeasure.integral_sub_vectorMeasure hvP hvN,
    VectorMeasure.integral_toSignedMeasure,VectorMeasure.integral_toSignedMeasure]
  change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x)))-
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (-f x)))=_
  rw [integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hmn.ennreal_ofReal
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top),← integral_sub hrP hrN]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 ≤ f x
  · rw [ENNReal.toReal_ofReal hx,ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hx)]
    simp
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hx),
      ENNReal.toReal_ofReal (neg_nonneg.mpr (le_of_not_ge hx))]
    simp

theorem absolute_integrable_iff (f : Ω → ℝ) (hfm : Measurable f) (g : Ω → ℂ) :
    Integrable g (absoluteDensity μ f) ↔ Integrable (fun x => |f x| • g x) μ := by
  have hmabs : Measurable (fun x => |f x|) := by
    simpa only [Real.norm_eq_abs] using hfm.norm
  change Integrable g (μ.withDensity (fun x => ENNReal.ofReal |f x|)) ↔ _
  rw [integrable_withDensity_iff_integrable_smul₀' hmabs.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _)]

end OperatorDerivativeRewrite.Foundation.SignedAbsoluteIntegration
