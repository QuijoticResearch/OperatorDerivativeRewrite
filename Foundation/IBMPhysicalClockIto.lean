import Foundation.GaussianParameterizedIto
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

/-! A physical H^-1-valued Brownian integral on the native finite-horizon
predictable domain, transported from the ACTUAL scalar Ito isometry. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalClockIto
open InfiniteGaussian GaussianTimeProcess GaussianComplexHorizonIto
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

abbrev Domain (T : ℝ≥0) := lpMeas H^{(-1 : ℝ)}(ℝ) ℂ
  (PredictableRealL2.predictable naturalFiltration) 2
  (PredictableRealL2.horizonMeasure T gaussianProduct)

local instance (T : ℝ≥0) : NormedSpace ℝ (Domain T) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance : NormedSpace ℝ (Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct) :=
  NormedSpace.restrictScalars ℝ ℂ _

def trimEquiv (T : ℝ≥0) : Domain T ≃ₗᵢ[ℂ]
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 (predictableMeasure T) :=
  lpMeasToLpTrimLie H^{(-1 : ℝ)}(ℝ) ℂ 2
    (PredictableRealL2.horizonMeasure T gaussianProduct)
    (PredictableRealL2.predictable_le naturalFiltration)

def encode (T : ℝ≥0) : Lp (H^{(-1 : ℝ)}(ℝ)) 2 (predictableMeasure T) →ₗᵢ[ℂ]
    Lp (Lp ℂ 2 (volume : Measure ℝ)) 2 (predictableMeasure T) := by
  letI : MeasurableSpace (ℝ × SampleSpace) := PredictableRealL2.predictable naturalFiltration
  exact BochnerLinearIsometry.lift (predictableMeasure T)
    (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).toLinearIsometry

def decode : Lp (Lp ℂ 2 (volume : Measure ℝ)) 2 gaussianProduct →ₗᵢ[ℂ]
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  BochnerLinearIsometry.lift gaussianProduct
    (BesselPotentialSpace.toLpₗᵢ ℝ ℂ (-1 : ℝ) 2).symm.toLinearIsometry

def integral (T : ℝ≥0) (u : Domain T) : Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct :=
  decode (GaussianParameterizedIto.integral (volume : Measure ℝ) T (encode T (trimEquiv T u)))

theorem integral_norm (T : ℝ≥0) (u : Domain T) : ‖integral T u‖ = ‖u‖ := by
  rw [integral, decode.norm_map, GaussianParameterizedIto.integral_norm,
    (encode T).norm_map, (trimEquiv T).norm_map]

theorem integral_isometry (T : ℝ≥0) : Isometry (integral T) :=
  decode.isometry.comp ((GaussianParameterizedIto.integral (volume : Measure ℝ) T).isometry.comp
    ((encode T).isometry.comp (trimEquiv T).isometry))

theorem integral_add (T : ℝ≥0) (u v : Domain T) :
    integral T (u+v) = integral T u+integral T v := by
  simp only [integral, map_add]

theorem integral_zero (T : ℝ≥0) : integral T 0 = 0 := by
  apply norm_eq_zero.mp
  rw [integral_norm, norm_zero]

theorem integral_real_smul (T : ℝ≥0) (r : ℝ) (u : Domain T) :
    integral T ((r : ℂ) • u) = (r : ℂ) • integral T u := by
  have hp (v : Lp (Lp ℂ 2 (volume : Measure ℝ)) 2 (predictableMeasure T)) :
      GaussianParameterizedIto.integral (volume : Measure ℝ) T ((r : ℂ) • v) =
        (r : ℂ) • GaussianParameterizedIto.integral (volume : Measure ℝ) T v := by
    rw [Complex.coe_smul, map_smul, Complex.coe_smul]
    rfl
  simp only [integral, map_smul, hp]

def integralIsometry (T : ℝ≥0) : Domain T →ₗᵢ[ℝ]
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 gaussianProduct where
  toLinearMap :=
    { toFun := integral T
      map_add' := integral_add T
      map_smul' := fun r u => by
        change integral T ((r : ℂ) • u) = (r : ℂ) • integral T u
        exact integral_real_smul T r u }
  norm_map' := integral_norm T

end OperatorDerivativeRewrite.Foundation.IBMPhysicalClockIto
