import Foundation.IBMPhysicalHorizonCompatibility

/-! Stopping the EXISTING actual signed-Dirac physical running integral in a
larger horizon preserves its value. This is an application of the proved
physical horizon theorem, not a newly defined substitute stochastic process. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalStoppedClockIntegral
open InfiniteGaussian IBMPhysicalWeakWiener GaussianTimeProductL2 IBMPhysicalClockIto
open IBMPhysicalPointClockField IBMPhysicalPointClockIntegral
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

def stopped (a T : ℝ≥0) : Domain T :=
  ⟨IBMSchwartzPhysicalClockIntegral.restriction T (limitField a),
    (limitField_predictable a).restrict.congr
      (LpToLpRestrictCLM_coeFn ℂ (PredictableRealL2.horizon T) (limitField a)).symm⟩

theorem stopped_self (a : ℝ≥0) : stopped a a = limitIntegrand a := rfl

theorem stopped_restrict_ae (a T : ℝ≥0) : (stopped a T).val =ᵐ[
    PredictableRealL2.horizonMeasure T gaussianProduct] limitField a :=
  LpToLpRestrictCLM_coeFn ℂ (PredictableRealL2.horizon T) (limitField a)

theorem zero_extension_ae (a T : ℝ≥0) (haT : a ≤ T) :
    (PredictableRealL2.horizon T).indicator (fun z => (stopped a T).val z) =ᵐ[timeProbability]
      limitField a := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp
    (stopped_restrict_ae a T)
  apply h.trans
  filter_upwards [limitField_ae a] with z hf
  by_cases hzT : z ∈ PredictableRealL2.horizon T
  · simp only [indicator_of_mem hzT]
  · have hza : z ∉ PredictableRealL2.horizon a := by
      intro hz
      apply hzT
      exact ⟨⟨hz.1.1, hz.1.2.trans (show (a : ℝ) ≤ T from haT)⟩, mem_univ _⟩
    rw [indicator_of_notMem hzT, hf, indicator_of_notMem hza]

theorem integral_stopped (a T : ℝ≥0) (haT : a ≤ T) :
    IBMPhysicalClockIto.integral T (stopped a T) = limitIntegralValue a := by
  change IBMPhysicalClockIto.integral T (stopped a T) =
    IBMPhysicalClockIto.integral a (stopped a a)
  exact IBMPhysicalHorizonCompatibility.compatible T a (stopped a T) (stopped a a)
    ((zero_extension_ae a T haT).trans (zero_extension_ae a a le_rfl).symm)

def interval (a b T : ℝ≥0) : Domain T := stopped b T - stopped a T

theorem interval_integral (a b T : ℝ≥0) (haT : a ≤ T) (hbT : b ≤ T) :
    IBMPhysicalClockIto.integral T (interval a b T) = limitIntegralValue b - limitIntegralValue a := by
  change (integralIsometry T) (stopped b T - stopped a T) = _
  rw [map_sub]
  exact congrArg₂ (fun x y : Lp Kernel 2 gaussianProduct => x-y)
    (integral_stopped b T hbT) (integral_stopped a T haT)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalStoppedClockIntegral
