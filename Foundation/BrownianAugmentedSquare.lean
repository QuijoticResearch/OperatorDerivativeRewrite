import Foundation.BrownianAugmentedMartingales

/-! The actual continuous Brownian square minus elapsed time remains a
martingale in the already constructed ambient-null-augmented filtration. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianAugmentedSquare
open InfiniteGaussian GaussianTimeProcess IBMConstructedSources
open BrownianAugmentedMartingales BrownianMassClockStoppingTime
set_option backward.isDefEq.respectTransparency false

def value (t : ℝ≥0) (ω : SampleSpace) : ℝ := (clockPath ω t)^2-(t : ℝ)

theorem coordinate_ae (t : ℝ≥0) : value t =ᵐ[gaussianProduct]
    (fun ω => GaussianTimeSpaceHermite.value 2 (process t ω) t) := by
  filter_upwards [clockPath_coordinate_ae t] with ω hω
  simp only [value, hω, GaussianTimeSpaceHermite.value_two]

theorem value_integrable (t : ℝ≥0) : Integrable (value t) gaussianProduct :=
  (GaussianHermiteMartingale.hermite_integrable 2 t).congr (coordinate_ae t).symm

theorem value_stronglyAdapted : StronglyAdapted augmentedPast value := by
  intro t
  exact ((brownian_stronglyAdapted t).measurable.pow_const 2 |>.sub measurable_const).stronglyMeasurable

theorem value_continuous (ω : SampleSpace) : Continuous (fun t => value t ω) :=
  ((clockPath ω).continuous.pow 2).sub NNReal.continuous_coe

theorem value_martingale : Martingale value augmentedPast gaussianProduct := by
  refine ⟨value_stronglyAdapted, ?_⟩
  intro s t hst
  exact (condExp_unchanged s _ (value_integrable t)).symm.trans
    ((condExp_congr_ae (coordinate_ae t)).trans
      ((GaussianHermiteMartingale.hermite_condExp 2 s t hst).trans (coordinate_ae s).symm))

theorem value_centered (t : ℝ≥0) : (∫ ω, value t ω ∂gaussianProduct) = 0 := by
  have hi : Integrable (fun ω => (process t ω)^2) gaussianProduct :=
    (process_memLp t 2 (by simp)).integrable_sq
  rw [integral_congr_ae (coordinate_ae t)]
  simp only [GaussianTimeSpaceHermite.value_two]
  rw [integral_sub hi (integrable_const (t : ℝ))]
  have hs := process_product_integral t t
  simp only [← pow_two, min_self] at hs
  rw [hs]
  simp

end OperatorDerivativeRewrite.Foundation.BrownianAugmentedSquare
