import Foundation.IBMPhysicalFrozenSlope

/-! A coherent corrected running integral built with the ORIGINAL physical
Ito map. The old cell-error integral is identified with its actual increments
minus the actual random frozen coefficient product. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectedRunning
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianHermiteIntegrand
open GaussianHermiteRepresentation
open IBMPhysicalWeakWiener IBMPhysicalNoiseClock IBMPhysicalReflectedPrimitive
open IBMPhysicalCellSlope BrownianClockWeightedEnergy IBMConstructedSources
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul
attribute [local irreducible] IBMPhysicalReflectedPrimitive.slope IBMConstructedSources.clockPath

def scalarStopped (a T : ℝ≥0) := restriction T (hermiteIntegrand 1 a)

theorem stopped_memLp (a T : ℝ≥0) :
    MemLp (fun z => slope (scalarStopped a T z)) 2
      (PredictableRealL2.horizonMeasure T gaussianProduct) := by
  have hm := slope_continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (scalarStopped a T))
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (Lp.memLp (scalarStopped a T)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply (hi.norm.const_mul (‖physicalDerivative‖^2)).mono' (hm.norm.pow 2)
  exact Eventually.of_forall fun z => by
    change ‖‖slope (scalarStopped a T z)‖^2‖ ≤ ‖physicalDerivative‖^2 * ‖scalarStopped a T z‖
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    exact IBMPhysicalFrozenSlope.slope_square_bound _

def stopped (a T : ℝ≥0) : IBMPhysicalClockIto.Domain T :=
  ⟨(stopped_memLp a T).toLp _,
    (slope_continuous.comp_aestronglyMeasurable
      (restriction_predictable T (hermiteIntegrand 1 a))).congr
        (stopped_memLp a T).coeFn_toLp.symm⟩

theorem stopped_ae (a T : ℝ≥0) : (stopped a T).val =ᵐ[
    PredictableRealL2.horizonMeasure T gaussianProduct] fun z =>
      (PredictableRealL2.horizon a).indicator (fun z => slope (sigma z)) z := by
  filter_upwards [(stopped_memLp a T).coeFn_toLp,
    LpToLpRestrictCLM_coeFn ℝ (PredictableRealL2.horizon T) (hermiteIntegrand 1 a).val,
    ae_restrict_of_ae (BrownianSignIntegral.brownian_field_joint a)] with z hs hr hb
  change (stopped a T).val z = slope (scalarStopped a T z) at hs
  change scalarStopped a T z = (hermiteIntegrand 1 a).val z at hr
  rw [hs, hr, hb]
  by_cases hz : z ∈ PredictableRealL2.horizon a
  · simp only [indicator_of_mem hz]
  · simp only [indicator_of_notMem hz, slope_zero]

theorem stopped_zero_extension (a T : ℝ≥0) (haT : a ≤ T) :
    (PredictableRealL2.horizon T).indicator (fun z => (stopped a T).val z) =ᵐ[timeProbability]
      (PredictableRealL2.horizon a).indicator (fun z => slope (sigma z)) := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable T)).mp
    (stopped_ae a T)
  apply h.trans
  apply Eventually.of_forall
  intro z
  by_cases hzT : z ∈ PredictableRealL2.horizon T
  · exact indicator_of_mem hzT _
  · have hza : z ∉ PredictableRealL2.horizon a := by
      intro hz
      exact hzT ⟨⟨hz.1.1, hz.1.2.trans (show (a : ℝ) ≤ T from haT)⟩, mem_univ _⟩
    simp only [indicator_of_notMem hzT, indicator_of_notMem hza]

def running (a : ℝ≥0) : Lp Kernel 2 gaussianProduct :=
  IBMPhysicalClockIto.integral a (stopped a a)

theorem stopped_integral (a T : ℝ≥0) (haT : a ≤ T) :
    IBMPhysicalClockIto.integral T (stopped a T) = running a :=
  IBMPhysicalHorizonCompatibility.compatible T a (stopped a T) (stopped a a)
    ((stopped_zero_extension a T haT).trans (stopped_zero_extension a a le_rfl).symm)

theorem error_domain (a b : ℝ≥0) : IBMPhysicalCellSlope.integrand a b =
    stopped b b - stopped a b - IBMPhysicalFrozenSlope.frozen a b := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [IBMPhysicalCellSlopeActual.errorClass_actual_ae a b,
    stopped_ae b b, stopped_ae a b, IBMPhysicalFrozenSlope.frozen_ae a b,
    Lp.coeFn_sub (stopped b b).val (stopped a b).val,
    Lp.coeFn_sub ((stopped b b).val-(stopped a b).val)
      (IBMPhysicalFrozenSlope.frozen a b).val,
    ae_restrict_mem (PredictableRealL2.horizon_measurable b)] with z he hb ha hf hd hd' hz
  change (IBMPhysicalCellSlope.integrand a b).val z = _ at he
  simp only [Pi.sub_apply] at hd hd'
  change (IBMPhysicalCellSlope.integrand a b).val z =
    ((stopped b b).val-(stopped a b).val-(IBMPhysicalFrozenSlope.frozen a b).val) z
  rw [he, hd', hd, hb, ha, hf, indicator_of_mem hz]
  by_cases hza : z ∈ PredictableRealL2.horizon a
  · have hc : z.1 ∉ Ioc (a : ℝ) (b : ℝ) := by
      intro hc
      linarith [hza.1.2, hc.1]
    simp only [indicator_of_mem hza, indicator_of_notMem hc, sub_self, sub_zero]
  · have hc : z.1 ∈ Ioc (a : ℝ) (b : ℝ) := by
      refine ⟨?_, hz.1.2⟩
      by_contra hn
      exact hza ⟨⟨hz.1.1, le_of_not_gt hn⟩, mem_univ _⟩
    simp only [indicator_of_notMem hza, indicator_of_mem hc, sub_zero]

theorem error_integral (a b : ℝ≥0) (hab : a ≤ b) :
    IBMPhysicalCellSlope.integral a b = running b-running a-
      IBMPhysicalPastIncrement.product a b hab (IBMPhysicalFrozenSlope.point a)
        (IBMPhysicalFrozenSlope.point_past a) := by
  change IBMPhysicalClockIto.integral b (IBMPhysicalCellSlope.integrand a b) = _
  rw [error_domain]
  change IBMPhysicalClockIto.integralIsometry b
    (stopped b b-stopped a b-IBMPhysicalFrozenSlope.frozen a b) = _
  rw [map_sub, map_sub]
  exact congrArg₂ (fun x y : Lp Kernel 2 gaussianProduct => x-y)
    (congrArg₂ (fun x y : Lp Kernel 2 gaussianProduct => x-y)
      (stopped_integral b b le_rfl) (stopped_integral a b hab))
    (IBMPhysicalFrozenSlope.frozen_integral a b hab)

theorem error_integral_actual (a b : ℝ≥0) (hab : a ≤ b) :
    IBMPhysicalCellSlope.integral a b =ᵐ[gaussianProduct] fun Y =>
      running b Y-running a Y-
        (clockPath Y b-clockPath Y a) • slope (clockPath Y a) := by
  rw [error_integral a b hab]
  filter_upwards [Lp.coeFn_sub (running b) (running a),
    Lp.coeFn_sub (running b-running a)
      (IBMPhysicalPastIncrement.product a b hab (IBMPhysicalFrozenSlope.point a)
        (IBMPhysicalFrozenSlope.point_past a)),
    IBMPhysicalPastIncrement.product_ae a b hab (IBMPhysicalFrozenSlope.point a)
      (IBMPhysicalFrozenSlope.point_past a), IBMPhysicalFrozenSlope.point_ae a,
    clockPath_coordinate_ae a, clockPath_coordinate_ae b] with Y hd he hp hs ha hb
  simp only [Pi.sub_apply] at hd he
  rw [he, hd, hp, hs, ha, hb]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectedRunning
