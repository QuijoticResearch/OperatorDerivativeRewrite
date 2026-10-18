import Foundation.HigherHeatFourierInnovations
import Foundation.SignedAbsoluteIntegration

/-! Actual signed predictable product integration on its full explicit weighted-L1 domain. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPredictableL1
open HigherHeatSignedLaws HigherHeatFourierInnovations SignedAbsoluteIntegration

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem weighted_product_integrable (past : Ω → ℝ) (m : ℕ) (hm : 0 < m)
    (t : ℝ≥0) (ht : 0 < t) (G : Ω → ℂ) (W : ℝ → ℂ)
    (hG : Integrable (fun w => (past w : ℂ)*G w) μ)
    (hW : Integrable (fun z => W z*(realKernel m hm t ht z : ℂ))) :
    Integrable (fun w : Ω × ℝ => (past w.1*realKernel m hm t ht w.2) • (G w.1*W w.2))
      (μ.prod volume) := by
  have he : (fun w : Ω × ℝ => (past w.1*realKernel m hm t ht w.2) • (G w.1*W w.2)) =
      (fun w => ((past w.1:ℂ)*G w.1)*(W w.2*(realKernel m hm t ht w.2 : ℂ))) := by
    funext w
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [he]
  exact hG.mul_prod hW

theorem product_absolute_integrable (past : Ω → ℝ) (hp : Measurable past)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hGm : Measurable G) (W : ℝ → ℂ) (hWm : Measurable W)
    (hG : Integrable (fun w => (past w : ℂ)*G w) μ)
    (hW : Integrable (fun z => W z*(realKernel m hm t ht z : ℂ))) :
    Integrable (fun w : Ω × ℝ => G w.1*W w.2)
      (absoluteDensity (μ.prod volume) (fun w => past w.1*realKernel m hm t ht w.2)) := by
  have hd : Measurable (fun w : Ω × ℝ => past w.1*realKernel m hm t ht w.2) :=
    (hp.comp measurable_fst).mul ((realKernel m hm t ht).continuous.measurable.comp measurable_snd)
  have hg : Measurable (fun w : Ω × ℝ => G w.1*W w.2) :=
    (hGm.comp measurable_fst).mul (hWm.comp measurable_snd)
  apply (absolute_integrable_iff (μ.prod volume) _ hd _).mpr
  apply (weighted_product_integrable μ past m hm t ht G W hG hW).norm.mono'
    (hd.norm.smul hg).aestronglyMeasurable
  exact Eventually.of_forall (fun w => by
    change ‖|past w.1*realKernel m hm t ht w.2| • (G w.1*W w.2)‖ ≤
      ‖(past w.1*realKernel m hm t ht w.2) • (G w.1*W w.2)‖
    simp only [norm_smul, Real.norm_eq_abs, abs_abs]
    exact le_rfl)

theorem product_signed_integrable (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hGm : Measurable G) (W : ℝ → ℂ) (hWm : Measurable W)
    (hG : Integrable (fun w => (past w : ℂ)*G w) μ)
    (hW : Integrable (fun z => W z*(realKernel m hm t ht z : ℂ))) :
    (extendedLaw μ past m hm t ht).Integrable (fun w : Ω × ℝ => G w.1*W w.2) := by
  apply (signed_integrable_iff (μ.prod volume) _
    (hi.mul_prod ((realKernel m hm t ht).integrable (μ := volume))) _).mpr
  exact product_absolute_integrable μ past hp m hm t ht G hGm W hWm hG hW

theorem product_integral (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hGm : Measurable G) (W : ℝ → ℂ) (hWm : Measurable W)
    (hG : Integrable (fun w => (past w : ℂ)*G w) μ)
    (hW : Integrable (fun z => W z*(realKernel m hm t ht z : ℂ))) :
    (∫ᵛ w, G w.1*W w.2 ∂<•extendedLaw μ past m hm t ht) =
      (∫ w, (past w : ℂ)*G w ∂μ) * (∫ z, W z*(realKernel m hm t ht z : ℂ)) := by
  have hd : Measurable (fun w : Ω × ℝ => past w.1*realKernel m hm t ht w.2) :=
    (hp.comp measurable_fst).mul ((realKernel m hm t ht).continuous.measurable.comp measurable_snd)
  rw [extendedLaw, integral_density (μ.prod volume) _
    (hi.mul_prod ((realKernel m hm t ht).integrable (μ := volume))) hd _
    (product_absolute_integrable μ past hp m hm t ht G hGm W hWm hG hW)]
  have he : (fun w : Ω × ℝ => (past w.1*realKernel m hm t ht w.2) • (G w.1*W w.2)) =
      (fun w => ((past w.1:ℂ)*G w.1)*(W w.2*(realKernel m hm t ht w.2 : ℂ))) := by
    funext w
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [he]
  exact integral_prod_mul (fun w => (past w : ℂ)*G w)
    (fun z => W z*(realKernel m hm t ht z : ℂ))

end OperatorDerivativeRewrite.Foundation.HigherHeatPredictableL1
