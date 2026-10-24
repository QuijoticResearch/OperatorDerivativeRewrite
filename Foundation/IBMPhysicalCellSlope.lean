import Foundation.IBMPhysicalTaylorMean
import Foundation.GaussianPastStepCompletion

/-! The actual corrected-slope cell error belongs to the ORIGINAL physical
Ito domain. No alternative integral or assumed predictable coefficient is used. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalCellSlope
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeProductL2
open GaussianPredictableFull GaussianHermiteIntegrand GaussianPastStepCompletion
open GaussianHermiteRepresentation
open IBMPhysicalWeakWiener IBMPhysicalReflectedPrimitive IBMPhysicalReflectedTaylor
open IBMPhysicalNoiseClock
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul
attribute [local irreducible] IBMPhysicalReflectedPrimitive.corrected
  IBMPhysicalReflectedPrimitive.slope IBMConstructedSources.clockPath

def current (a b : ℝ≥0) : fullPredictable := hermiteIntegrand 1 b - hermiteIntegrand 1 a

def past (a b : ℝ≥0) : fullPredictable :=
  ⟨productTensor (intervalVector a b) (wienerL2 a),
    past_step_mem_fullPredictable a b (wienerL2 a)
      (process_stronglyAdapted a).aestronglyMeasurable⟩

def restriction (b : ℝ≥0) : TimeProbabilityL2 →L[ℝ]
    Lp ℝ 2 (PredictableRealL2.horizonMeasure b gaussianProduct) :=
  LpToLpRestrictCLM _ ℝ ℝ timeProbability 2 (PredictableRealL2.horizon b)

def currentClass (a b : ℝ≥0) := restriction b (current a b)
def pastClass (a b : ℝ≥0) := restriction b (past a b)

theorem restriction_predictable (b : ℝ≥0) (u : fullPredictable) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (restriction b u) (PredictableRealL2.horizonMeasure b gaussianProduct) :=
  ((mem_fullPredictable_iff _).mp u.property).1.restrict.congr
    (LpToLpRestrictCLM_coeFn ℝ (PredictableRealL2.horizon b) u.val).symm

def error (a b : ℝ≥0) (z : ℝ × SampleSpace) : Kernel :=
  slope (currentClass a b z) - slope (pastClass a b z)

theorem error_predictable (a b : ℝ≥0) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (error a b) (PredictableRealL2.horizonMeasure b gaussianProduct) :=
  (slope_continuous.comp_aestronglyMeasurable (restriction_predictable b (current a b))).sub
    (slope_continuous.comp_aestronglyMeasurable (restriction_predictable b (past a b)))

theorem error_square_bound (a b : ℝ≥0) (z : ℝ × SampleSpace) :
    ‖error a b z‖^2 ≤ 4*‖physicalDerivative‖^2 * |pastClass a b z-currentClass a b z| := by
  have h := slope_holder (currentClass a b z) (pastClass a b z)
  calc
    _ ≤ ((2*‖physicalDerivative‖)*Real.sqrt |pastClass a b z-currentClass a b z|)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt (abs_nonneg _)]
      ring

theorem error_memLp (a b : ℝ≥0) :
    MemLp (error a b) 2 (PredictableRealL2.horizonMeasure b gaussianProduct) := by
  have hm : AEStronglyMeasurable (error a b)
      (PredictableRealL2.horizonMeasure b gaussianProduct) :=
    (slope_continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (currentClass a b))).sub
      (slope_continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (pastClass a b)))
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hd := ((Lp.memLp (pastClass a b)).sub (Lp.memLp (currentClass a b))).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply (hd.norm.const_mul (4*‖physicalDerivative‖^2)).mono' (hm.norm.pow 2)
  exact Eventually.of_forall fun z => by
    change ‖‖error a b z‖^2‖ ≤ 4*‖physicalDerivative‖^2 *
      ‖pastClass a b z-currentClass a b z‖
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact error_square_bound a b z

def errorClass (a b : ℝ≥0) : Lp Kernel 2 (PredictableRealL2.horizonMeasure b gaussianProduct) :=
  (error_memLp a b).toLp (error a b)

theorem errorClass_ae (a b : ℝ≥0) : errorClass a b =ᵐ[
    PredictableRealL2.horizonMeasure b gaussianProduct] error a b :=
  (error_memLp a b).coeFn_toLp

def integrand (a b : ℝ≥0) : IBMPhysicalClockIto.Domain b :=
  ⟨errorClass a b, (error_predictable a b).congr (errorClass_ae a b).symm⟩

def integral (a b : ℝ≥0) : Lp Kernel 2 gaussianProduct :=
  IBMPhysicalClockIto.integral b (integrand a b)

theorem integral_norm (a b : ℝ≥0) : ‖integral a b‖ = ‖errorClass a b‖ :=
  IBMPhysicalClockIto.integral_norm b (integrand a b)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalCellSlope
