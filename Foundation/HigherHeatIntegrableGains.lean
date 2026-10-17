import Foundation.SignedAbsoluteIntegration
import Foundation.HigherHeatFourierInnovations
import Foundation.HigherHeatPredictablePairing

/-! Genuine signed stochastic gains on an L1 total-variation domain, without boundedness. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatIntegrableGains
open SignedAbsoluteIntegration HigherHeatSignedLaws HigherHeatFourierInnovations HigherHeatCylinderFourier

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]

theorem separable_absolute_integrable (past : Ω → ℝ) (hp : Measurable past)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hiG : Integrable G (absoluteDensity μ past))
    (W : ℝ → ℂ) (hiW : Integrable W (absoluteDensity volume (realKernel m hm t ht))) :
    Integrable (fun w : Ω × ℝ => G w.1*W w.2)
      (absoluteDensity (μ.prod volume) (fun w => past w.1*realKernel m hm t ht w.2)) := by
  have hmK := (realKernel m hm t ht).continuous.measurable
  have hdm := (hp.comp measurable_fst).mul (hmK.comp measurable_snd)
  apply (absolute_integrable_iff (μ.prod volume) _ hdm _).mpr
  have hG := (absolute_integrable_iff μ past hp G).mp hiG
  have hW := (absolute_integrable_iff volume _ hmK W).mp hiW
  apply (hG.mul_prod hW).congr
  exact Eventually.of_forall fun w => by
    change (|past w.1| • G w.1)*(|realKernel m hm t ht w.2| • W w.2)=
      |past w.1*realKernel m hm t ht w.2| • (G w.1*W w.2)
    simp only [Complex.real_smul,abs_mul,Complex.ofReal_mul]
    ring

theorem separable_signed_integrable (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hiG : Integrable G (absoluteDensity μ past))
    (W : ℝ → ℂ) (hiW : Integrable W (absoluteDensity volume (realKernel m hm t ht))) :
    (extendedLaw μ past m hm t ht).Integrable (fun w => G w.1*W w.2) := by
  exact (signed_integrable_iff (μ.prod volume) _
    (hi.mul_prod ((realKernel m hm t ht).integrable (μ := volume))) _).mpr
    (separable_absolute_integrable μ past hp m hm t ht G hiG W hiW)

theorem separable_integral (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (G : Ω → ℂ) (hiG : Integrable G (absoluteDensity μ past))
    (W : ℝ → ℂ) (hiW : Integrable W (absoluteDensity volume (realKernel m hm t ht))) :
    (∫ᵛ w, G w.1*W w.2 ∂<•extendedLaw μ past m hm t ht)=
      (∫ w, (past w:ℂ)*G w ∂μ)*(∫ z : ℝ, W z*(realKernel m hm t ht z:ℂ)) := by
  have hd := hi.mul_prod ((realKernel m hm t ht).integrable (μ := volume))
  have hdm : Measurable (fun w : Ω × ℝ => past w.1*realKernel m hm t ht w.2) :=
    (hp.comp measurable_fst).mul ((realKernel m hm t ht).continuous.measurable.comp measurable_snd)
  rw [extendedLaw,SignedAbsoluteIntegration.integral_density (μ.prod volume) _ hd hdm _
    (separable_absolute_integrable μ past hp m hm t ht G hiG W hiW)]
  have he : (fun w : Ω × ℝ => (past w.1*realKernel m hm t ht w.2) • (G w.1*W w.2))=
      (fun w : Ω × ℝ => ((past w.1:ℂ)*G w.1)*(W w.2*(realKernel m hm t ht w.2:ℂ))) := by
    funext w
    simp only [Complex.real_smul,Complex.ofReal_mul]
    ring
  rw [he]
  exact integral_prod_mul (fun w => (past w:ℂ)*G w) (fun z => W z*(realKernel m hm t ht z:ℂ))

theorem kernel_absolute_finite (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    IsFiniteMeasure (absoluteDensity volume (realKernel m hm t ht)) := by
  simpa only [absoluteDensity,Real.norm_eq_abs] using
    (isFiniteMeasure_withDensity_ofReal ((realKernel m hm t ht).integrable (μ := volume)).norm.2)

theorem innovation_absolute_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ : ℝ) :
    Integrable (innovation m t ξ) (absoluteDensity volume (realKernel m hm t ht)) := by
  letI := kernel_absolute_finite m hm t ht
  exact Integrable.of_bound (innovation_measurable m t ξ).aestronglyMeasurable 2
    (Eventually.of_forall (innovation_bound m t ξ))

theorem predictable_gain_zero (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ : ℝ)
    (G : Ω → ℂ) (hiG : Integrable G (absoluteDensity μ past)) :
    (∫ᵛ w, G w.1*innovation m t ξ w.2 ∂<•extendedLaw μ past m hm t ht)=0 := by
  rw [separable_integral μ past hp hi m hm t ht G hiG (innovation m t ξ)
    (innovation_absolute_integrable m hm t ht ξ),kernel_innovation_zero,mul_zero]

theorem product_absolute_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ η : ℝ) :
    Integrable (fun z => innovation m t ξ z*innovation m t η z)
      (absoluteDensity volume (realKernel m hm t ht)) := by
  letI := kernel_absolute_finite m hm t ht
  exact Integrable.of_bound
    ((innovation_measurable m t ξ).mul (innovation_measurable m t η)).aestronglyMeasurable
    4 (Eventually.of_forall (HigherHeatPredictablePairing.product_innovation_bound m t ξ η))

theorem predictable_pairing (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ η : ℝ)
    (G : Ω → ℂ) (hiG : Integrable G (absoluteDensity μ past)) :
    (∫ᵛ w, G w.1*(innovation m t ξ w.2*innovation m t η w.2)
      ∂<•extendedLaw μ past m hm t ht)=
      (∫ w, (past w:ℂ)*G w ∂μ)*HigherHeatFourierCovariance.covariance m t ξ η := by
  rw [separable_integral μ past hp hi m hm t ht G hiG _
    (product_absolute_integrable m hm t ht ξ η),HigherHeatFourierCovariance.kernel_product]

theorem compensated_absolute_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ η : ℝ) :
    Integrable (fun z => innovation m t ξ z*innovation m t η z-
      HigherHeatFourierCovariance.covariance m t ξ η)
      (absoluteDensity volume (realKernel m hm t ht)) := by
  letI := kernel_absolute_finite m hm t ht
  exact (product_absolute_integrable m hm t ht ξ η).sub (integrable_const _)

theorem compensated_product_zero (past : Ω → ℝ) (hp : Measurable past) (hi : Integrable past μ)
    (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ η : ℝ)
    (G : Ω → ℂ) (hiG : Integrable G (absoluteDensity μ past)) :
    (∫ᵛ w, G w.1*(innovation m t ξ w.2*innovation m t η w.2-
      HigherHeatFourierCovariance.covariance m t ξ η) ∂<•extendedLaw μ past m hm t ht)=0 := by
  calc
    _ = (∫ w, (past w:ℂ)*G w ∂μ)*
        (∫ z : ℝ, (innovation m t ξ z*innovation m t η z-
          HigherHeatFourierCovariance.covariance m t ξ η)*(realKernel m hm t ht z:ℂ)) :=
      separable_integral μ past hp hi m hm t ht G hiG _
        (compensated_absolute_integrable m hm t ht ξ η)
    _ = 0 := by rw [HigherHeatFourierCovariance.centered_product_zero,mul_zero]

end OperatorDerivativeRewrite.Foundation.HigherHeatIntegrableGains
