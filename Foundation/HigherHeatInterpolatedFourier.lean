import Foundation.HigherHeatCylinderPathLimit
import Foundation.HigherHeatFourierSeries

/-! Uniform spectral bounds for arbitrary finite observations of the actual interpolated paths. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatInterpolatedFourier
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatCylinderFourier
open HigherHeatInterpolatedPaths HigherHeatSignedLaws HigherHeatPositionVariation

def nodeLinear (n : ℕ) : Grid n →ₗ[ℝ] (Option (Fin (gridSize n)) → ℝ) where
  toFun := nodeValue n
  map_add' x y := by funext o; cases o <;> simp [nodeValue]
  map_smul' a x := by funext o; cases o <;> simp [nodeValue]

def evaluation (n : ℕ) (t : ℝ) : Grid n →ₗ[ℝ] ℝ :=
  (Polynomial.leval t).comp ((Lagrange.interpolate Finset.univ (interpolationNode n)).comp (nodeLinear n))

theorem evaluation_apply (n : ℕ) (t : ℝ) (y : Grid n) : evaluation n t y=process n t y := rfl

def incrementEvaluation (n : ℕ) (t : ℝ) : Grid n →ₗ[ℝ] ℝ :=
  (evaluation n t).comp (cumulativeEquiv (gridSize n)).toLinearMap

theorem incrementEvaluation_apply (n : ℕ) (t : ℝ) (x : Grid n) :
    incrementEvaluation n t x=coordinate t (incrementPath n x) := by
  change process n t (cumulativeEquiv (gridSize n) x)=
    process n t (linearImage (cumulativeMatrix (gridSize n)) x)
  rw [cumulativeEquiv_apply]

variable {ι : Type*} [Fintype ι]

def observe (times : ι → ℝ) (ω : Path) : ι → ℝ := fun i => coordinate (times i) ω

theorem observe_continuous (times : ι → ℝ) : Continuous (observe times) :=
  continuous_pi (fun i => coordinate_continuous (times i))

def observationLinear (n : ℕ) (times : ι → ℝ) : Grid n →ₗ[ℝ] (ι → ℝ) :=
  LinearMap.pi (fun i => incrementEvaluation n (times i))

def observationMatrix (n : ℕ) (times : ι → ℝ) : Matrix ι (Fin (gridSize n)) ℝ :=
  LinearMap.toMatrix' (observationLinear n times)

theorem observationMatrix_apply (n : ℕ) (times : ι → ℝ) (x : Grid n) :
    linearImage (observationMatrix n times) x=observe times (incrementPath n x) := by
  calc
    linearImage (observationMatrix n times) x=Matrix.toLin' (observationMatrix n times) x := by
      funext i
      rfl
    _ = observationLinear n times x := by rw [observationMatrix, Matrix.toLin'_toMatrix']
    _ = observe times (incrementPath n x) := by
      funext i
      exact incrementEvaluation_apply n (times i) x

theorem signed_observation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) (times : ι → ℝ) :
    (signedPath m hm T hT n).map (observe times)=
      configurationLaw m hm (fun _ : Fin (gridSize n) => duration T n)
        (fun _ => duration_pos T hT n) (observationMatrix n times) := by
  rw [signedPath, HigherHeatObservationRefinement.map_comp _ _ _
    (incrementPath_continuous n).measurable (observe_continuous times).measurable]
  unfold configurationLaw
  congr 1
  funext x
  exact (observationMatrix_apply n times x).symm

theorem phase_expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ)
    (times : ι → ℝ) (ξ : ι → ℝ) :
    (∫ᵛ ω, SignedDensityIntegral.configurationPhase ξ (observe times ω) ∂<•signedPath m hm T hT n)=
      ∏ j : Fin (gridSize n), HigherHeatL2.symbol m (duration T n)
        (dualImage (observationMatrix n times) ξ j) := by
  have hi := SignedDensityIntegral.bounded_signed_integrable (signedPath m hm T hT n)
    (fun ω => SignedDensityIntegral.configurationPhase ξ (observe times ω))
    ((SignedDensityIntegral.configurationPhase_measurable ξ).comp (observe_continuous times).measurable)
    1 (fun ω => by rw [SignedDensityIntegral.configurationPhase_norm])
  calc
    (∫ᵛ ω, SignedDensityIntegral.configurationPhase ξ (observe times ω) ∂<•signedPath m hm T hT n) =
        ∫ᵛ y, SignedDensityIntegral.configurationPhase ξ y ∂<•(signedPath m hm T hT n).map (observe times) :=
      (VectorMeasure.integral_map (observe_continuous times).measurable
        (SignedDensityIntegral.configurationPhase_measurable ξ).aestronglyMeasurable hi).symm
    _ = _ := by
      rw [signed_observation]
      exact SignedDensityIntegral.configurationLaw_fourier m hm _ _ _ ξ

theorem phase_expectation_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ)
    (times : ι → ℝ) (ξ : ι → ℝ) :
    ‖∫ᵛ ω, SignedDensityIntegral.configurationPhase ξ (observe times ω) ∂<•signedPath m hm T hT n‖ ≤ 1 := by
  rw [phase_expectation, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => HigherHeatL2.symbol_norm_le _ _ _)

end OperatorDerivativeRewrite.Foundation.HigherHeatInterpolatedFourier
