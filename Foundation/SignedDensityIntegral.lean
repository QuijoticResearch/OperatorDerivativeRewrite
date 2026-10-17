import Foundation.HigherHeatCylinderFourier
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Bounded Fourier observables integrated against actual signed density measures. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.SignedDensityIntegral

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem integral_density (f : α → ℝ) (hf : Integrable f μ) (hfm : Measurable f)
    (g : α → ℂ) (hgm : Measurable g) (C : ℝ) (hg : ∀ x, ‖g x‖ ≤ C) :
    (∫ᵛ x, g x ∂<•μ.withDensityᵥ f) = ∫ x, f x • g x ∂μ := by
  let P := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let N := μ.withDensity (fun x => ENNReal.ofReal (-f x))
  letI : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hf.2
  letI : IsFiniteMeasure N := isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hiP : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable C (Eventually.of_forall hg)
  have hiN : Integrable g N := Integrable.of_bound hgm.aestronglyMeasurable C (Eventually.of_forall hg)
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
  change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) -
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (-f x))) = _
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

theorem bounded_signed_integrable (ν : SignedMeasure α) (g : α → ℂ)
    (hgm : Measurable g) (C : ℝ) (hg : ∀ x, ‖g x‖ ≤ C) : ν.Integrable g := by
  letI : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  exact Integrable.of_bound hgm.aestronglyMeasurable C (Eventually.of_forall hg)

open HigherHeatSignedLaws HigherHeatCylinderFourier
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def configurationPhase (ξ : κ → ℝ) (y : κ → ℝ) : ℂ :=
  Real.fourierChar (-(∑ i, ξ i*y i))

theorem configurationPhase_measurable (ξ : κ → ℝ) : Measurable (configurationPhase ξ) := by
  unfold configurationPhase
  fun_prop

theorem configurationPhase_norm (ξ : κ → ℝ) (y : κ → ℝ) : ‖configurationPhase ξ y‖=1 := by
  simp [configurationPhase]

theorem configurationLaw_fourier (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j)
    (B : κ → ι → ℝ) (ξ : κ → ℝ) :
    (∫ᵛ y, configurationPhase ξ y ∂<•configurationLaw m hm t ht B) =
      ∏ j, HigherHeatL2.symbol m (t j) (dualImage B ξ j) := by
  have hgm := (configurationPhase_measurable ξ).comp (linearImage_measurable B)
  have hgb : ∀ x : ι → ℝ, ‖configurationPhase ξ (linearImage B x)‖ ≤ 1 := by
    intro x
    rw [configurationPhase_norm]
  have hi := bounded_signed_integrable (incrementLaw m hm t ht) _ hgm 1 hgb
  rw [configurationLaw,VectorMeasure.integral_map (linearImage_measurable B)
    (configurationPhase_measurable ξ).aestronglyMeasurable hi]
  have hdm : Measurable (incrementDensity m hm t ht) := by
    unfold incrementDensity
    apply Finset.measurable_prod
    intro j _
    exact (realKernel m hm (t j) (ht j)).continuous.measurable.comp (measurable_pi_apply j)
  rw [incrementLaw,integral_density _ _ (incrementDensity_integrable m hm t ht) hdm
    (fun x => configurationPhase ξ (linearImage B x)) hgm 1 hgb]
  rw [← cylinderFourier_eq m hm t ht B ξ]
  unfold cylinderFourier
  apply integral_congr_ae
  filter_upwards with x
  simp [cylinderIntegrand,configurationPhase,smul_eq_mul,mul_comm]

theorem positionLaw_fourier (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ j, 0 < t j)
    (ξ : Fin n → ℝ) :
    (∫ᵛ y, configurationPhase ξ y ∂<•positionLaw n m hm t ht) =
      ∏ j, HigherHeatL2.symbol m (t j) (∑ i ∈ Finset.univ.filter (fun i => j ≤ i), ξ i) := by
  simpa only [positionLaw,cumulative_dual] using configurationLaw_fourier m hm t ht (cumulativeMatrix n) ξ

end OperatorDerivativeRewrite.Foundation.SignedDensityIntegral
