import Foundation.IBMPhysicalPastIncrement

/-! The actual unbounded random corrected slope at the left clock time is
in the original physical Ito domain. Its frozen step integral is the actual
physical slope times the Brownian increment, not a constant tensor formula. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalFrozenSlope
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2
open IBMPhysicalWeakWiener IBMPhysicalNoiseClock IBMPhysicalReflectedPrimitive
open IBMPhysicalCellSlope IBMConstructedSources
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] IBMPhysicalNegativeEmbedding.realNormSMul
  IBMPhysicalNegativeEmbedding.realContinuousSMul
attribute [local irreducible] IBMPhysicalReflectedPrimitive.slope IBMConstructedSources.clockPath

theorem slope_square_bound (r : ℝ) : ‖slope r‖^2 ≤ ‖physicalDerivative‖^2 * |r| := by
  calc
    _ ≤ (‖physicalDerivative‖ * Real.sqrt |r|)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (slope_origin_bound r) 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt (abs_nonneg r)]

theorem point_memLp (a : ℝ≥0) :
    MemLp (fun Y => slope (process a Y)) 2 gaussianProduct := by
  have hm : AEStronglyMeasurable (fun Y => slope (process a Y)) gaussianProduct :=
    slope_continuous.comp_aestronglyMeasurable
    (process_stronglyMeasurable a).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (Lp.memLp (wienerL2 a)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply (hi.norm.const_mul (‖physicalDerivative‖^2)).mono' (hm.norm.pow 2)
  exact Eventually.of_forall fun Y => by
    change ‖‖slope (process a Y)‖^2‖ ≤ ‖physicalDerivative‖^2 * ‖process a Y‖
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    exact slope_square_bound _

def point (a : ℝ≥0) : Lp Kernel 2 gaussianProduct := (point_memLp a).toLp _

theorem point_ae (a : ℝ≥0) : point a =ᵐ[gaussianProduct] fun Y => slope (clockPath Y a) := by
  filter_upwards [(point_memLp a).coeFn_toLp, clockPath_coordinate_ae a] with Y hp hc
  change point a Y = slope (process a Y) at hp
  rw [hp, hc]

theorem point_past (a : ℝ≥0) :
    AEStronglyMeasurable[naturalFiltration a] (point a) gaussianProduct :=
  (slope_continuous.comp_aestronglyMeasurable
    (process_stronglyAdapted a).aestronglyMeasurable).congr
      (point_memLp a).coeFn_toLp.symm

theorem frozen_memLp (a b : ℝ≥0) :
    MemLp (fun z => slope (pastClass a b z)) 2
      (PredictableRealL2.horizonMeasure b gaussianProduct) := by
  have hm := slope_continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (pastClass a b))
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (Lp.memLp (pastClass a b)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply (hi.norm.const_mul (‖physicalDerivative‖^2)).mono' (hm.norm.pow 2)
  exact Eventually.of_forall fun z => by
    change ‖‖slope (pastClass a b z)‖^2‖ ≤ ‖physicalDerivative‖^2 * ‖pastClass a b z‖
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    exact slope_square_bound _

def frozen (a b : ℝ≥0) : IBMPhysicalClockIto.Domain b :=
  ⟨(frozen_memLp a b).toLp _,
    (slope_continuous.comp_aestronglyMeasurable (restriction_predictable b (past a b))).congr
      (frozen_memLp a b).coeFn_toLp.symm⟩

theorem frozen_ae (a b : ℝ≥0) : (frozen a b).val =ᵐ[
    PredictableRealL2.horizonMeasure b gaussianProduct] fun z =>
      (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => slope (clockPath z.2 a)) z.1 := by
  filter_upwards [(frozen_memLp a b).coeFn_toLp,
    IBMPhysicalCellSlopeActual.pastClass_ae a b] with z hf hp
  change (frozen a b).val z = slope (pastClass a b z) at hf
  rw [hf, hp]
  by_cases hz : z.1 ∈ Ioc (a : ℝ) (b : ℝ)
  · simp only [indicator_of_mem hz]
  · simp only [indicator_of_notMem hz, slope_zero]

theorem frozen_zero_extension (a b : ℝ≥0) :
    (PredictableRealL2.horizon b).indicator (fun z => (frozen a b).val z) =ᵐ[timeProbability]
      fun z => (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => (point a) z.2) z.1 := by
  have hf := (ae_eq_restrict_iff_indicator_ae_eq (PredictableRealL2.horizon_measurable b)).mp
    (frozen_ae a b)
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (point_ae a)
  filter_upwards [hf, hp] with z hf hp
  simp only [Function.comp_apply] at hp
  rw [hf]
  by_cases hh : z ∈ PredictableRealL2.horizon b
  · rw [indicator_of_mem hh]
    by_cases hz : z.1 ∈ Ioc (a : ℝ) (b : ℝ) <;> simp only [hz, indicator_of_mem,
      indicator_of_notMem, hp]
  · have hz : z.1 ∉ Ioc (a : ℝ) (b : ℝ) := by
      intro hz
      exact hh ⟨⟨lt_of_le_of_lt a.coe_nonneg hz.1, hz.2⟩, mem_univ _⟩
    simp only [indicator_of_notMem hh, indicator_of_notMem hz]

theorem frozen_integral (a b : ℝ≥0) (hab : a ≤ b) :
    IBMPhysicalClockIto.integral b (frozen a b) =
      IBMPhysicalPastIncrement.product a b hab (point a) (point_past a) :=
  IBMPhysicalPastIncrement.integral_eq_product a b b hab (point a) (point_past a)
    (frozen a b) (frozen_zero_extension a b)

theorem frozen_integral_actual (a b : ℝ≥0) (hab : a ≤ b) :
    IBMPhysicalClockIto.integral b (frozen a b) =ᵐ[gaussianProduct] fun Y =>
      (clockPath Y b-clockPath Y a) • slope (clockPath Y a) := by
  rw [frozen_integral a b hab]
  filter_upwards [IBMPhysicalPastIncrement.product_ae a b hab (point a) (point_past a),
    point_ae a, clockPath_coordinate_ae a, clockPath_coordinate_ae b] with Y hp hs ha hb
  rw [hp, hs, ha, hb]

theorem frozen_energy (a b : ℝ≥0) (hab : a ≤ b) :
    ‖IBMPhysicalClockIto.integral b (frozen a b)‖^2 = ((b : ℝ)-a)*‖point a‖^2 := by
  rw [frozen_integral a b hab]
  exact IBMPhysicalPastIncrement.product_energy a b hab (point a) (point_past a)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalFrozenSlope
