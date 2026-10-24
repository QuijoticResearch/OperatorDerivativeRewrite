import Foundation.IBMPhysicalWeakWiener
import Foundation.IBMSchwartzPhysicalReflectedIto

/-! Actual finite-width first-source scenery pairings converge in a specified
physical test dual, including the whole reflected-Ito correction. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzWeakWienerClosure
open InfiniteGaussian GaussianTimeHilbert IBMPhysicalNoiseRealization
open IBMPhysicalWeakWiener IBMSchwartzPhysicalFirstKernel
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _

def weakField : Lp Kernel 2 gaussianProduct →L[ℝ]
    Lp (StrongDual ℝ Tests) 2 gaussianProduct := integral.compLpL 2 gaussianProduct

theorem weakField_norm (U : Lp Kernel 2 gaussianProduct) : ‖weakField U‖ = ‖U‖ :=
  (BochnerLinearIsometry.lift gaussianProduct
    (NormedSpace.inclusionInDoubleDualLi ℝ (E := Kernel))).norm_map U

def noiseField : Lp TimeHilbert 2 gaussianProduct →L[ℝ]
    Lp GaussianL2 2 gaussianProduct := physicalNoise.toContinuousLinearMap.compLpL 2 gaussianProduct

def nativeField : Lp GaussianL2 2 gaussianProduct →L[ℝ]
    Lp (StrongDual ℝ Tests) 2 gaussianProduct := native.compLpL 2 gaussianProduct

def evaluate (L : Tests) : Lp (StrongDual ℝ Tests) 2 gaussianProduct →L[ℝ]
    GaussianL2 := (ContinuousLinearMap.apply ℝ ℝ L).compLpL 2 gaussianProduct

theorem nativeField_test_consistency (F : Lp GaussianL2 2 gaussianProduct)
    (L M : Tests) (h : testNoise L = testNoise M) :
    evaluate L (nativeField F) = evaluate M (nativeField F) := by
  apply Lp.ext
  filter_upwards [(ContinuousLinearMap.apply ℝ ℝ L).coeFn_compLpL (nativeField F),
    (ContinuousLinearMap.apply ℝ ℝ M).coeFn_compLpL (nativeField F),
    native.coeFn_compLpL F] with Y hL hM hF
  change evaluate L (nativeField F) Y = nativeField F Y L at hL
  change evaluate M (nativeField F) Y = nativeField F Y M at hM
  change nativeField F Y = native (F Y) at hF
  rw [hL, hM, hF, native_apply, native_apply, h]

theorem field_agreement (u : Lp TimeHilbert 2 gaussianProduct) :
    nativeField (noiseField u) = weakField
      (IBMPhysicalNegativeEmbedding.embedding.compLpL 2 gaussianProduct u) := by
  apply Lp.ext
  filter_upwards [native.coeFn_compLpL (noiseField u),
    physicalNoise.toContinuousLinearMap.coeFn_compLpL u,
    integral.coeFn_compLpL
      (IBMPhysicalNegativeEmbedding.embedding.compLpL 2 gaussianProduct u),
    IBMPhysicalNegativeEmbedding.embedding.coeFn_compLpL u] with Y hn hp hi he
  change noiseField u Y = physicalNoise (u Y) at hp
  change nativeField (noiseField u) Y = native (noiseField u Y) at hn
  change weakField (IBMPhysicalNegativeEmbedding.embedding.compLpL 2 gaussianProduct u) Y =
    integral ((IBMPhysicalNegativeEmbedding.embedding.compLpL 2 gaussianProduct u) Y) at hi
  rw [hn, hp, hi, he, native_agreement]

def correction (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :=
  nativeField (noiseField (wholeKernelClass g a n T))

def correctionLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :=
  weakField (IBMSchwartzPhysicalReflectedIto.endpointLimitClass g a T-
    IBMSchwartzPhysicalClockIntegral.limitIntegralValue g a T)

theorem correction_eq (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    correction g a n T = weakField (IBMSchwartzPhysicalReflectedIto.wholeClass g a n T) :=
  field_agreement _

theorem correction_actual_projection (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    correction g a n T = nativeField
      (GaussianPastFirstChaos.projection.compLpL 2 gaussianProduct
        (IBMSchwartzBochnerDomain.wholeClass g a n T)) := by
  exact congrArg nativeField (wholeKernelClass_realizes_projection g a n T)

theorem correction_error_norm (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    ‖correction g a n T-correctionLimit g a T‖ =
      ‖IBMSchwartzPhysicalReflectedIto.wholeClass g a n T-
        (IBMSchwartzPhysicalReflectedIto.endpointLimitClass g a T-
          IBMSchwartzPhysicalClockIntegral.limitIntegralValue g a T)‖ := by
  rw [correction_eq, correctionLimit, ← map_sub]
  exact weakField_norm _

theorem correction_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => correction g a n T) atTop (nhds (correctionLimit g a T)) := by
  simp only [correction_eq, correctionLimit]
  exact weakField.continuous.tendsto _ |>.comp
    (IBMSchwartzPhysicalReflectedIto.wholeClass_tendsto g a T)

theorem limit_actual_test_consistency (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (L M : Tests) (h : testNoise L = testNoise M) :
    evaluate L (correctionLimit g a T) = evaluate M (correctionLimit g a T) := by
  have hL := (evaluate L).continuous.tendsto _ |>.comp (correction_tendsto g a T)
  have hM := (evaluate M).continuous.tendsto _ |>.comp (correction_tendsto g a T)
  have he : (fun n => evaluate L (correction g a n T)) =
      (fun n => evaluate M (correction g a n T)) := by
    funext n
    exact nativeField_test_consistency _ L M h
  have hM' : Tendsto (fun n => evaluate L (correction g a n T)) atTop
      (nhds (evaluate M (correctionLimit g a T))) := by
    simpa only [Function.comp_def, he] using hM
  exact tendsto_nhds_unique hL hM'

/-- A common full-measure clock set works for EVERY physical dual test.
The right side is an ordinary actual scenery expectation at finite width. -/
theorem correction_actual_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, ∀ L : Tests,
      correction g a n T Y L =
        ∫ X, physicalNoise (wholeKernelClass g a n T Y) X * testNoise L X ∂gaussianProduct := by
  have he := field_agreement (wholeKernelClass g a n T)
  have ha := integral.coeFn_compLpL
    (IBMPhysicalNegativeEmbedding.embedding.compLpL 2 gaussianProduct (wholeKernelClass g a n T))
  have hb := IBMPhysicalNegativeEmbedding.embedding.coeFn_compLpL (wholeKernelClass g a n T)
  filter_upwards [ha, hb] with Y ha hb
  intro L
  have hc : correction g a n T = weakField
      (IBMPhysicalNegativeEmbedding.embedding.compLpL 2 gaussianProduct
        (wholeKernelClass g a n T)) := he
  rw [hc]
  change weakField _ Y = _ at ha
  rw [ha, hb, integral_apply, expectation_pairing]

theorem limiting_identity (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    weakField (IBMSchwartzPhysicalReflectedIto.endpointLimitClass g a T) =
      weakField (IBMSchwartzPhysicalClockIntegral.limitIntegralValue g a T)+
        correctionLimit g a T := by
  rw [correctionLimit, map_sub]
  abel

end OperatorDerivativeRewrite.Foundation.IBMSchwartzWeakWienerClosure
