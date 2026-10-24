import Foundation.IBMPhysicalOriginSplit
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! Exact local-time decomposition of the ORIGINAL physical IBM correction.
The actual continuous Tanaka mass is retained, rather than discarded. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectionLocalTime
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalDirac IBMConstructedSources
open IBMPhysicalOriginSplit IBMPhysicalCorrectedRunning IBMPhysicalCorrectedVariation
open IBMPhysicalClockItoTensor
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul

theorem original_correction_actual (T : ℝ≥0) :
    IBMPhysicalPointKernelIto.correctionLimit T =ᵐ[gaussianProduct] fun Y =>
      residual T Y+BrownianMassContinuousLimit.limitPath Y T • dirac 0 := by
  have hi := Lp.coeFn_add (running T)
    (coefficientTensor (BrownianSignIntegral.terminal T) (dirac 0))
  rw [← original_integral_split T] at hi
  filter_upwards [Lp.coeFn_sub (IBMPhysicalPointKernelIto.point T)
      (IBMPhysicalPointClockIntegral.limitIntegralValue T), hi,
    coefficientTensor_ae (BrownianSignIntegral.terminal T) (dirac 0),
    value_actual_ae T, BrownianMassLimitIdentification.tanaka_ae T]
    with Y hc hi ht hv htanaka
  simp only [Pi.sub_apply, Pi.add_apply] at hc hi
  change (IBMPhysicalPointKernelIto.point T-IBMPhysicalPointClockIntegral.limitIntegralValue T) Y = _
  rw [hc, hi, ht, Complex.coe_smul]
  change IBMPhysicalPointKernelIto.point T Y-
      (running T Y+BrownianSignIntegral.terminal T Y • dirac 0) =
    value T Y-running T Y+BrownianMassContinuousLimit.limitPath Y T • dirac 0
  rw [hv, htanaka]
  module

def localTimeClass (T : ℝ≥0) : Lp Kernel 2 gaussianProduct :=
  coefficientTensor (BrownianTanakaResidual.mass T) (dirac 0)

theorem localTimeClass_ae (T : ℝ≥0) : localTimeClass T =ᵐ[gaussianProduct] fun Y =>
    BrownianMassContinuousLimit.limitPath Y T • dirac 0 := by
  filter_upwards [coefficientTensor_ae (BrownianTanakaResidual.mass T) (dirac 0),
    BrownianMassLimitIdentification.coordinate_ae T] with Y ht hc
  change localTimeClass T Y = ((BrownianTanakaResidual.mass T) Y : ℂ) • dirac 0 at ht
  rw [ht, ← hc, Complex.coe_smul]
  module

theorem original_correction_split (T : ℝ≥0) :
    IBMPhysicalPointKernelIto.correctionLimit T = residualClass T+localTimeClass T := by
  apply Lp.ext
  filter_upwards [original_correction_actual T, residualClass_ae T, localTimeClass_ae T,
    Lp.coeFn_add (residualClass T) (localTimeClass T)] with Y ho hr hl ha
  simp only [Pi.add_apply] at ha
  rw [ho, ha, hr, hl]

theorem native_correction_tendsto (T : ℝ≥0) :
    Tendsto (fun n => IBMPhysicalPointKernelIto.correction n T) atTop
      (nhds (residualClass T+localTimeClass T)) := by
  rw [← original_correction_split T]
  exact IBMPhysicalPointKernelIto.correction_tendsto T

def originPath (Y : SampleSpace) (t : ℝ≥0) : Kernel :=
  BrownianMassContinuousLimit.limitPath Y t • dirac 0

theorem originPath_continuous (Y : SampleSpace) : Continuous (originPath Y) :=
  (BrownianMassContinuousLimit.limitPath Y).continuous.smul continuous_const

theorem originPath_boundedVariation : ∀ᵐ Y ∂gaussianProduct, ∀ T : ℝ≥0,
    BoundedVariationOn (originPath Y) (Set.Icc 0 T) := by
  filter_upwards [BrownianMassContinuousLimit.limitPath_properties] with Y hp T
  have hb : BoundedVariationOn (fun t => BrownianMassContinuousLimit.limitPath Y t)
      (Set.Icc 0 T) := (hp.2.1.monotoneOn (Set.Icc 0 T)).boundedVariationOn (C :=
        BrownianMassContinuousLimit.limitPath Y T) (fun t ht => by
          rw [abs_of_nonneg (hp.2.2 t)]
          exact hp.2.1 ht.2)
  let C : ℝ →L[ℝ] Kernel := (ContinuousLinearMap.id ℝ ℝ).smulRight (dirac 0)
  exact C.lipschitzWith.comp_boundedVariationOn hb

end OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectionLocalTime
