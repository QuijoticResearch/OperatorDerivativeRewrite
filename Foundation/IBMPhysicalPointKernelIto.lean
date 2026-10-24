import Foundation.IBMPhysicalPointClockIntegral

/-! A physical H^-1 realization of the running point correction. Every scalar
test agrees with the actual local-time/curvature correction, and the physical
classes converge strongly before taking any particular test. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalPointKernelIto
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalNegativeEmbedding
open IBMPhysicalNoiseClock IBMPhysicalNoiseCalculus IBMPhysicalNoiseVectors
open IBMPhysicalPointClockIntegral
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _

def endpoint (n : ℕ) (T : ℝ≥0) : Lp Kernel 2 gaussianProduct :=
  embedding.compLpL 2 gaussianProduct (mollifiedKernel n T) -
    Lp.const 2 gaussianProduct (embedding (convolutionKernel (IBMMollifier.kernel n) 0))

def point (T : ℝ≥0) : Lp Kernel 2 gaussianProduct :=
  embedding.compLpL 2 gaussianProduct (sourceKernel T)

theorem endpoint_tendsto (T : ℝ≥0) :
    Tendsto (fun n => endpoint n T) atTop (nhds (point T)) := by
  have hc := embedding.continuous.tendsto _ |>.comp (mollifier_kernel_tendsto 0)
  have h0 : Tendsto (fun n => Lp.const 2 gaussianProduct
      (embedding (convolutionKernel (IBMMollifier.kernel n) 0))) atTop (nhds 0) := by
    have h := (Lp.constL 2 gaussianProduct ℝ).continuous.tendsto _ |>.comp hc
    simpa only [Lp.constL_apply, Function.comp_def, vector_zero, map_zero] using h
  have h := (embedding.compLpL 2 gaussianProduct).continuous.tendsto _ |>.comp
    (mollifiedKernel_tendsto T)
  simpa only [endpoint, point, sub_zero, Function.comp_def] using h.sub h0

theorem endpoint_test (n : ℕ) (T : ℝ≥0) (L : Tests) :
    L.compLpL 2 gaussianProduct (endpoint n T) = IBMPhysicalRunningIto.endpoint n T L := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLpL (endpoint n T),
    Lp.coeFn_sub (embedding.compLpL 2 gaussianProduct (mollifiedKernel n T))
      (Lp.const 2 gaussianProduct (embedding (convolutionKernel (IBMMollifier.kernel n) 0))),
    embedding.coeFn_compLpL (mollifiedKernel n T), mollifiedKernel_ae n T,
    Lp.coeFn_const 2 gaussianProduct (embedding (convolutionKernel (IBMMollifier.kernel n) 0)),
    IBMPhysicalRunningIto.endpoint_coeFn n T L] with Y he hs hj hk hc hp
  rw [he, endpoint, hs, Pi.sub_apply, hj, hk, hc, map_sub, hp]
  simp only [Function.const_apply, IBMPhysicalRunningPrimitive.value,
    IBMPhysicalRunningPrimitive.source_pairing _ (IBMMollifier.kernel_smooth _).continuous
      (IBMMollifier.kernel_compactSupport _)]

theorem point_test (T : ℝ≥0) (L : Tests) :
    L.compLpL 2 gaussianProduct (point T) = IBMPhysicalSceneryTestClockGraph.point T L := by
  have h := (L.compLpL 2 gaussianProduct).continuous.tendsto _ |>.comp (endpoint_tendsto T)
  simp only [Function.comp_def, endpoint_test] at h
  exact tendsto_nhds_unique h (IBMPhysicalRunningIto.endpoint_tendsto T L)

def correction (n : ℕ) (T : ℝ≥0) : Lp Kernel 2 gaussianProduct :=
  endpoint n T - integralValue n T

def correctionLimit (T : ℝ≥0) : Lp Kernel 2 gaussianProduct :=
  point T - limitIntegralValue T

theorem correction_tendsto (T : ℝ≥0) :
    Tendsto (fun n => correction n T) atTop (nhds (correctionLimit T)) :=
  (endpoint_tendsto T).sub (integralValue_tendsto T)

theorem correction_test (n : ℕ) (T : ℝ≥0) (L : Tests) :
    L.compLpL 2 gaussianProduct (correction n T) = IBMPhysicalRunningIto.correction n T L := by
  rw [correction, map_sub, endpoint_test, integralValue_test,
    IBMPhysicalRunningIto.native_identity]
  abel

theorem correctionLimit_test (T : ℝ≥0) (L : Tests) :
    L.compLpL 2 gaussianProduct (correctionLimit T) = IBMPhysicalRunningIto.correctionLimit T L := by
  rw [correctionLimit, map_sub, point_test, limitIntegralValue_test]
  rfl

theorem correction_actual_ae (n : ℕ) (T : ℝ≥0) (L : Tests) :
    (fun Y => L (correction n T Y)) =ᵐ[gaussianProduct] fun Y =>
      L (IBMPhysicalDirac.translated n 0) * BrownianMassContinuousLimit.limitPath Y T +
        (1/2 : ℝ) * ∫ s in 0..(T : ℝ), IBMPhysicalRunningPrimitive.second n L
          |IBMConstructedSources.clockPath Y s.toNNReal| := by
  have he := L.coeFn_compLpL (correction n T)
  rw [correction_test] at he
  exact he.symm.trans (IBMPhysicalRunningIto.correction_coeFn n T L)

theorem physical_running_identity (T : ℝ≥0) :
    point T = limitIntegralValue T + correctionLimit T := by
  unfold correctionLimit
  abel

end OperatorDerivativeRewrite.Foundation.IBMPhysicalPointKernelIto
