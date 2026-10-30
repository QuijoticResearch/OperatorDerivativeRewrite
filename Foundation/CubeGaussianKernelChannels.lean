import Foundation.CubeGaussianModes
import Foundation.CubeGroundNormLimit

/-! Actual limiting Wilson kernel in Gaussian channels with a COMMON Haar root. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianKernelChannels
open CubeGaussianModes CubeChartAction QuaternionSU2Representation
open CubeBoundaryChartL2 CubeCompressedNormLimit

def constant : ℝ := (SU2GaussianConeCoordinates.chartDensity 0)^12*CubeSchurIntegral.temporalConstant

/-- This is one Haar integral of a product, not a product of independent root integrals. -/
theorem actual_kernel_channels (X Y : Boundary) :
    CubeBoundaryHaarL2.limit (X,Y)=constant*
      ∫ c : SU2, (∏ i : Fin 5,Real.exp (-channel i (analysis X i) (analysis Y i) c))
        ∂QuaternionSU2Representation.law := by
  have he (c : SU2) : Real.exp (-CubeRootSchur.effective X Y c)=
      ∏ i : Fin 5,Real.exp (-channel i (analysis X i) (analysis Y i) c) := by
    simpa only [synthesis_analysis] using exponential_channels (analysis X) (analysis Y) c
  unfold CubeBoundaryHaarL2.limit CubeBoundaryKernelL2.limitKernel constant
  simp_rw [he]
  ring

/-- The coordinate identity identifies the actual limiting operator on ALL L2 pairs. -/
theorem actual_operator_channels (F G : EuclideanL2) :
    inner ℝ (actualLimitOperator F) G=
      ∫ X : Boundary,G X*(∫ Y : Boundary,(constant*
        ∫ c : SU2,(∏ i : Fin 5,Real.exp (-channel i (analysis X i) (analysis Y i) c))
          ∂QuaternionSU2Representation.law)*F Y) := by
  rw [actualLimitOperator_integral_pairing]
  simp_rw [actual_kernel_channels]

end OperatorDerivativeRewrite.Foundation.CubeGaussianKernelChannels
