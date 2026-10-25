import Foundation.IBMRidgeNativeSource
import Foundation.IBMBoundedMixedClockTesting

/-! Original native IBM pairings against genuine nonlinear multitime ridges.
This is an actual observable testing theorem, not full-output convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRidgeNativeLimit
open InfiniteGaussian IBMTimeAveragedObservable IBMRawStepSources
open IBMRidgeNativeSource IBMRawGridSecondChaos IBMRawGridMixedObservable
open IBMRawGridObservableTests IBMSourceProductBounds IBMSchwartzSourceContinuity
open IBMCorrectionStein IBMShiftedJetMoments IBMSchwartzSourceDerivative
open IBMUniformClockGridEnergy IBMIntrinsicOperators IBMJointIntrinsicDerivative
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _ IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] jointDerivative LinearPMap.adjoint LinearPMap.graph
variable {d : ℕ}

theorem raw_coefficient_expansion (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (Y : SampleSpace) :
    rawProduct (coefficient c τ Y) (coefficient c τ Y) =
      ∑ i, ∑ j, (c i*c j) • rawProduct (clockDirection (τ i) Y) (clockDirection (τ j) Y) := by
  change rawBilinear (∑ i, c i • clockDirection (τ i) Y) (∑ j, c j • clockDirection (τ j) Y) = _
  simp only [map_sum,ContinuousLinearMap.sum_apply,map_smul,ContinuousLinearMap.smul_apply,
    rawBilinear_apply,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

theorem source_ridge_pair (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u : ℕ → CoefficientSpace) (n : ℕ) (k : CoefficientSpace) :
    inner ℝ (sourceSum u n) (observable g a 0 k) =
      (IBMShiftedJetMoments.M g a k 2 0/2)*inner ℝ (sourceSum u n) (rawProduct k k) := by
  rw [source_ridge_test,raw_square_test]

theorem source_ridge_pairing_ae (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (h : ℝ≥0) (n : ℕ) :
    (fun Y => inner ℝ (sourceGrid h n Y) (ridgeSource g a c τ Y)) =ᵐ[gaussianProduct]
      fun Y => (1/2:ℝ)*(∑ i, ∑ j, (c i*c j)*
        (curvature g a c τ Y*mixedEnergy h n (τ i) (τ j) Y)) := by
  filter_upwards [sourceGrid_ae h n,ridgeSource_actual g a c τ,clockCurve_initial h]
    with Y hs hr h0
  rw [hs,hr,source_ridge_pair,raw_coefficient_expansion]
  have he (i j : Fin d) :
      inner ℝ (sourceSum (clockCurve h Y) n)
        (rawProduct (clockDirection (τ i) Y) (clockDirection (τ j) Y)) =
          mixedEnergy h n (τ i) (τ j) Y := by
    rw [source_mixed_test,h0,inner_zero_left,inner_zero_left,zero_mul,sub_zero]
    simp only [clockCurve,direction_overlap]
    rfl
  simp only [inner_sum,inner_smul_right,he]
  rw [curvature_actual]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem weighted_energy_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (h : ℝ≥0) (n : ℕ) (i j : Fin d) :
    Integrable (fun Y => curvature g a c τ Y*mixedEnergy h n (τ i) (τ j) Y) gaussianProduct :=
  IBMBoundedMixedClockTesting.weighted_integrable _ (curvature_measurable g a c τ)
    (curvature_bound g a c τ) (mixedEnergy_integrable h n (τ i) (τ j))

theorem observable_ridge_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (h : ℝ≥0) (n : ℕ) :
    inner ℝ (jointDivergence (IBMRawGridCompensation.gridInput h n)) (ridgeObservation g a c τ) =
      (1/2:ℝ)*∑ i, ∑ j, (c i*c j)*
        (∫ Y, curvature g a c τ Y*mixedEnergy h n (τ i) (τ j) Y ∂gaussianProduct) := by
  rw [native_grid_value]
  have hp := IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right
    (ridgeObservation g a c τ) (jointRealization (sourceGrid h n))
  rw [hp]
  change inner ℝ (jointRealization (sourceGrid h n)) (jointRealization (ridgeSource g a c τ)) = _
  rw [jointRealization.inner_map_map,L2_inner_eq_integral]
  rw [integral_congr_ae (source_ridge_pairing_ae g a c τ h n),integral_const_mul]
  congr 1
  have hi (i j : Fin d) := (weighted_energy_integrable g a c τ h n i j).const_mul (c i*c j)
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finset_sum _ fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro i hmem
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
  simp only [integral_const_mul]

def nativeRidgePairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (H : ℝ≥0) (N : ℕ) : ℝ :=
  inner ℝ (jointDivergence (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1)))
    (ridgeObservation g a c τ)

def ridgeLimit (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (H : ℝ≥0) : ℝ :=
  (1/2:ℝ)*∑ i, ∑ j, (c i*c j)*(∫ Y, curvature g a c τ Y*
    (IBMClippedClockCrossing.cap (GaussianTimeProcess.process (τ i) Y) (GaussianTimeProcess.process H Y)*
      IBMClippedClockCrossing.cap (GaussianTimeProcess.process (τ j) Y) (GaussianTimeProcess.process H Y)-
        IBMMixedClockLimit.mixedOccupation H (τ i) (τ j) Y) ∂gaussianProduct)

theorem nativeRidgePairing_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (nativeRidgePairing g a c τ H) atTop (𝓝 (ridgeLimit g a c τ H)) := by
  have h (i j : Fin d) := (IBMBoundedMixedClockTesting.weighted_energy_tendsto
    (curvature g a c τ) (curvature_measurable g a c τ) (curvature_bound g a c τ)
      H (τ i) (τ j) hH).const_mul (c i*c j)
  have hs := (tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => h i j).const_mul (1/2:ℝ)
  change Tendsto (fun N : ℕ => (1/2:ℝ)*∑ i, ∑ j, (c i*c j)*
    (∫ Y, curvature g a c τ Y*mixedEnergy (H/(N+1)) (N+1) (τ i) (τ j) Y ∂gaussianProduct))
      atTop (𝓝 (ridgeLimit g a c τ H)) at hs
  exact hs.congr' (Eventually.of_forall fun N => (observable_ridge_pairing g a c τ _ _).symm)

theorem ridgeLimit_eq_of_observation_eq {e : ℕ}
    (g f : SchwartzMap ℝ ℝ) (a b : ℝ) (c : Fin d → ℝ) (τ : Fin d → ℝ≥0)
    (v : Fin e → ℝ) (σ : Fin e → ℝ≥0) (H : ℝ≥0) (hH : 0 < H)
    (he : ridgeObservation g a c τ = ridgeObservation f b v σ) :
    ridgeLimit g a c τ H = ridgeLimit f b v σ H := by
  have hl := nativeRidgePairing_tendsto g a c τ H hH
  have hr := nativeRidgePairing_tendsto f b v σ H hH
  apply tendsto_nhds_unique hl
  exact hr.congr' (Eventually.of_forall fun N => by
    change inner ℝ _ (ridgeObservation f b v σ) = inner ℝ _ (ridgeObservation g a c τ)
    rw [he])

theorem finite_relation_preserved {m : ℕ}
    (g : Fin m → SchwartzMap ℝ ℝ) (a weights : Fin m → ℝ)
    (c : Fin m → Fin d → ℝ) (τ : Fin m → Fin d → ℝ≥0)
    (H : ℝ≥0) (hH : 0 < H)
    (hz : (∑ i, weights i • ridgeObservation (g i) (a i) (c i) (τ i)) = 0) :
    (∑ i, weights i*ridgeLimit (g i) (a i) (c i) (τ i) H) = 0 := by
  have hs := tendsto_finsetSum Finset.univ fun i _ =>
    (nativeRidgePairing_tendsto (g i) (a i) (c i) (τ i) H hH).const_mul (weights i)
  have he (N : ℕ) : (∑ i, weights i*nativeRidgePairing (g i) (a i) (c i) (τ i) H N) = 0 := by
    have h := congrArg (fun F : IntrinsicSpace => inner ℝ
      (jointDivergence (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))) F) hz
    simpa only [inner_sum,inner_smul_right,inner_zero_right,nativeRidgePairing] using h
  have hzero : Tendsto (fun _ : ℕ => (0:ℝ)) atTop
      (𝓝 (∑ i, weights i*ridgeLimit (g i) (a i) (c i) (τ i) H)) :=
    hs.congr' (Eventually.of_forall he)
  exact tendsto_nhds_unique hzero tendsto_const_nhds

end OperatorDerivativeRewrite.Foundation.IBMRidgeNativeLimit
