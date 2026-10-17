import Foundation.ContinuousFractionalBrownian
import Foundation.ObservationModificationAugmentation
import Foundation.FractionalPredictionObstruction

/-! The existing Gaussian conditional projection is the actual conditional
expectation given the past of the constructed continuous fractional process. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.ContinuousFractionalPrediction
open InfiniteGaussian ContinuousFractionalBrownian GaussianConditionalGraph
open ObservationModificationAugmentation AmbientNullAugmentation
set_option backward.isDefEq.respectTransparency false
variable (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)

def naturalPast : Filtration ℝ≥0 (inferInstance : MeasurableSpace SampleSpace) :=
  Filtration.natural (process H hH0 hH1) (fun t =>
    ((ContinuousMap.measurable_eval t).comp (path_measurable H hH0 hH1)).stronglyMeasurable)

theorem naturalPast_eq (t : ℝ≥0) :
    naturalPast H hH0 hH1 t = observationSpace
      (fun r : Iic t => process H hH0 hH1 r) := Filtration.natural_eq_comap _ _ _

theorem augmented_past_eq (t : ℝ≥0) :
    augment (naturalPast H hH0 hH1 t) gaussianProduct =
      augment (MeasurableSpace.comap (firstChaosFamily
        (FractionalPredictionObstruction.pastDirections H hH0 hH1 t)) inferInstance)
        gaussianProduct := by
  rw [naturalPast_eq]
  exact augmented_observationSpace_eq gaussianProduct
    (fun r : Iic t => process H hH0 hH1 r)
    (fun r : Iic t => FractionalGaussianProcess.process H hH0 hH1 r)
    (fun r => (ContinuousMap.measurable_eval (r : ℝ≥0)).comp (path_measurable H hH0 hH1))
    (fun r => FractionalGaussianProcess.process_measurable H hH0 hH1 r)
    (fun r => process_coordinate_ae H hH0 hH1 r)

theorem conditionalProjection_actual_past (t : ℝ≥0) (F : GaussianL2) :
    conditionalProjection (FractionalPredictionObstruction.pastDirections H hH0 hH1 t) F
      =ᵐ[gaussianProduct] gaussianProduct[F | naturalPast H hH0 hH1 t] := by
  have hF : Integrable F gaussianProduct := (Lp.memLp F).integrable (by norm_num)
  have hobs := condExp_observation_eq gaussianProduct
    (fun r : Iic t => FractionalGaussianProcess.process H hH0 hH1 r)
    (fun r : Iic t => process H hH0 hH1 r)
    (fun r => FractionalGaussianProcess.process_measurable H hH0 hH1 r)
    (fun r => (ContinuousMap.measurable_eval (r : ℝ≥0)).comp (path_measurable H hH0 hH1))
    (fun r => (process_coordinate_ae H hH0 hH1 r).symm) F hF
  rw [naturalPast_eq]
  exact (conditionalProjection_ae_condExp _ F).trans hobs

theorem terminal_forecast_actual_past (t : ℝ≥0) :
    FractionalPredictionObstruction.forecast H hH0 hH1 t =ᵐ[gaussianProduct]
      gaussianProduct[process H hH0 hH1 1 | naturalPast H hH0 hH1 t] := by
  exact (conditionalProjection_actual_past H hH0 hH1 t
    (FractionalGaussianProcess.value H hH0 hH1 1)).trans
      (condExp_congr_ae (process_coordinate_ae H hH0 hH1 1).symm)

theorem prediction_preserves_closed_domain (t : ℝ≥0) (F : GaussianL2)
    (hF : F ∈ closedCylindricalDerivative.domain) :
    ∃ G : GaussianL2, G ∈ closedCylindricalDerivative.domain ∧
      G =ᵐ[gaussianProduct] gaussianProduct[F | naturalPast H hH0 hH1 t] :=
  ⟨_, conditionalProjection_mem_domain _ hF, conditionalProjection_actual_past H hH0 hH1 t F⟩

end OperatorDerivativeRewrite.Foundation.ContinuousFractionalPrediction
