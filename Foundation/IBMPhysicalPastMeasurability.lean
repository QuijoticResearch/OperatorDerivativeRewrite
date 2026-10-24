import Foundation.IBMPhysicalClockProductRule

/-! Raw clock-past measurability of ORIGINAL physical Ito outputs and the
actual physical correction. Conditional L2 projection avoids any uncountable
intersection of exceptional sets over physical scalar tests. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalPastMeasurability
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianPredictableFull
open GaussianConditionalIto GaussianPredictableCutoff IBMPhysicalWeakWiener
open IBMPhysicalHorizonCompatibility IBMConstructedSources IBMPhysicalPrimitiveDerivative
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

theorem past_of_scalar_tests (T : ℝ≥0) (U : Lp Kernel 2 gaussianProduct)
    (hU : ∀ L : Tests, AEStronglyMeasurable[naturalFiltration T]
      (L.compLpL 2 gaussianProduct U) gaussianProduct) :
    AEStronglyMeasurable[naturalFiltration T] U gaussianProduct := by
  let V : Lp Kernel 2 gaussianProduct := (condExpL2 Kernel ℝ (naturalFiltration.le T) U).val
  have hV : AEStronglyMeasurable[naturalFiltration T] V gaussianProduct :=
    aestronglyMeasurable_condExpL2 (naturalFiltration.le T) U
  have he : V = U := by
    apply IBMPhysicalLpSeparation.ext
    intro L
    have hp : (condExpL2 ℝ ℝ (naturalFiltration.le T)
        (L.compLpL 2 gaussianProduct U)).val = L.compLpL 2 gaussianProduct U := by
      change (pastL2 T).starProjection (L.compLpL 2 gaussianProduct U) = _
      exact (pastL2 T).starProjection_eq_self_iff.mpr (hU L)
    have hc := condExpL2_comp_continuousLinearMap ℝ ℝ (naturalFiltration.le T) L U
    change (condExpL2 ℝ ℝ (naturalFiltration.le T)
      (L.compLpL 2 gaussianProduct U)).val =ᵐ[gaussianProduct]
        L.compLpL 2 gaussianProduct V at hc
    rw [hp] at hc
    exact Lp.ext hc.symm
  rwa [he] at hV

theorem scalarField_cut (T : ℝ≥0) (L : Tests) (u : IBMPhysicalClockIto.Domain T) :
    predictableCut T (scalarField T L u) = scalarField T L u := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [cut_coeFn T (scalarField T L u).val, scalarField_ae T L u] with z hc hs
  change cut T (scalarField T L u).val z = (scalarField T L u).val z
  rw [hc, hs]
  by_cases hz : z ∈ PredictableRealL2.horizon T
  · simp only [indicator_of_mem hz]
    simpa only [indicator_of_mem hz] using hs
  · simp only [indicator_of_notMem hz]

theorem scalar_integral_past (T : ℝ≥0) (L : Tests) (u : IBMPhysicalClockIto.Domain T) :
    AEStronglyMeasurable[naturalFiltration T]
      (L.compLpL 2 gaussianProduct (IBMPhysicalClockIto.integral T u)) gaussianProduct := by
  rw [scalarization]
  have h := integral_cut_mem_past T (scalarField T L u)
  rw [scalarField_cut] at h
  exact h

theorem integral_past (T : ℝ≥0) (u : IBMPhysicalClockIto.Domain T) :
    AEStronglyMeasurable[naturalFiltration T] (IBMPhysicalClockIto.integral T u) gaussianProduct :=
  past_of_scalar_tests T _ (fun L => scalar_integral_past T L u)

theorem clock_past (T : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration T] (fun Y => clockPath Y T) gaussianProduct :=
  (process_stronglyAdapted T).aestronglyMeasurable.congr (clockPath_coordinate_ae T).symm

theorem point_past (T : ℝ≥0) : AEStronglyMeasurable[naturalFiltration T]
    (IBMPhysicalPointKernelIto.point T) gaussianProduct := by
  have hm : AEStronglyMeasurable[naturalFiltration T]
      (fun Y => primitive |clockPath Y T|) gaussianProduct :=
    (primitive_C1.continuous.comp continuous_abs).comp_aestronglyMeasurable (clock_past T)
  apply hm.congr
  filter_upwards [IBMPhysicalNegativeEmbedding.embedding.coeFn_compLpL
    (IBMPhysicalNoiseClock.sourceKernel T), IBMPhysicalNoiseClock.sourceKernel_ae T] with Y he hk
  change IBMPhysicalPointKernelIto.point T Y =
    IBMPhysicalNegativeEmbedding.embedding (IBMPhysicalNoiseClock.sourceKernel T Y) at he
  rw [he, hk]
  rfl

theorem correction_past (T : ℝ≥0) : AEStronglyMeasurable[naturalFiltration T]
    (IBMPhysicalPointKernelIto.correctionLimit T) gaussianProduct :=
  ((point_past T).sub (integral_past T (IBMPhysicalPointClockIntegral.limitIntegrand T))).congr
    (Lp.coeFn_sub (IBMPhysicalPointKernelIto.point T) (IBMPhysicalPointClockIntegral.limitIntegralValue T)).symm

theorem corrected_running_past (T : ℝ≥0) : AEStronglyMeasurable[naturalFiltration T]
    (IBMPhysicalCorrectedRunning.running T) gaussianProduct :=
  integral_past T (IBMPhysicalCorrectedRunning.stopped T T)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalPastMeasurability
