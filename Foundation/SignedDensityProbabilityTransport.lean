import Foundation.SignedDensityProbabilitySampling

/-! Exact signed-density recovery and measurable pushforward of the actual probability sampler. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.SignedDensityProbabilityTransport
open SignedDensityProbabilitySampling SignedAbsoluteIntegration
variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]

theorem weighted_integral (μ : Measure Ω) (f : Ω → ℝ) (hfm : Measurable f)
    (hp : 0 < mass μ f) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (g : Ω → V) :
    (∫ x, weight μ f x • g x ∂sampler μ f)=∫ x, f x • g x ∂μ := by
  rw [sampler, integral_smul_measure]
  have he : (fun x => weight μ f x • g x)=fun x => mass μ f • (orientation f x • g x) := by
    funext x
    rw [weight, mul_smul]
  rw [he, integral_smul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le,
    smul_smul, inv_mul_cancel₀ (ne_of_gt hp), one_smul, integral_orientation μ f hfm g]

theorem weighted_set_integral (μ : Measure Ω) (f : Ω → ℝ) (hfm : Measurable f)
    (hp : 0 < mass μ f) (s : Set Ω) (hs : MeasurableSet s) :
    (∫ x in s, weight μ f x ∂sampler μ f)=∫ x in s, f x ∂μ := by
  have hh := weighted_integral μ f hfm hp (s.indicator (fun _ => (1:ℝ)))
  have hl : (fun x => weight μ f x • s.indicator (fun _ => (1:ℝ)) x)=s.indicator (weight μ f) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hr : (fun x => f x • s.indicator (fun _ => (1:ℝ)) x)=s.indicator f := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hl, hr, integral_indicator hs, integral_indicator hs] at hh
  exact hh

theorem signed_density_eq (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ) (hfm : Measurable f)
    (hp : 0 < mass μ f) :
    (sampler μ f).withDensityᵥ (weight μ f)=μ.withDensityᵥ f := by
  ext s hs
  rw [withDensityᵥ_apply (weight_integrable μ f hf hfm hp) hs, withDensityᵥ_apply hf hs]
  exact weighted_set_integral μ f hfm hp s hs

theorem map_withDensity (Q : Measure Ω) (F : Ω → Y) (hF : Measurable F)
    (W : Y → ℝ) (hW : Measurable W) (hiW : Integrable W (Q.map F)) :
    (Q.map F).withDensityᵥ W=(Q.withDensityᵥ (W ∘ F)).map F := by
  have hiWF : Integrable (W ∘ F) Q :=
    (integrable_map_measure hW.aestronglyMeasurable hF.aemeasurable).mp hiW
  ext s hs
  rw [withDensityᵥ_apply hiW hs, VectorMeasure.map_apply _ hF hs,
    withDensityᵥ_apply hiWF (hF hs), ← integral_indicator hs,
    integral_map hF.aemeasurable (hW.indicator hs).aestronglyMeasurable,
    ← integral_indicator (hF hs)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : F x ∈ s <;> simp [hx]

theorem signed_sampler_pushforward (μ : Measure Ω) (f : Ω → ℝ) (hf : Integrable f μ)
    (hfm : Measurable f) (hp : 0 < mass μ f) (F : Ω → Y) (hF : Measurable F)
    (W : Y → ℝ) (hW : Measurable W) (hw : ∀ x, W (F x)=weight μ f x) :
    ((sampler μ f).map F).withDensityᵥ W=(μ.withDensityᵥ f).map F := by
  have he : W ∘ F=weight μ f := funext hw
  have hiW : Integrable W ((sampler μ f).map F) := by
    apply (integrable_map_measure hW.aestronglyMeasurable hF.aemeasurable).mpr
    rw [he]
    exact weight_integrable μ f hf hfm hp
  rw [map_withDensity _ F hF W hW hiW, he, signed_density_eq μ f hf hfm hp]

end OperatorDerivativeRewrite.Foundation.SignedDensityProbabilityTransport
