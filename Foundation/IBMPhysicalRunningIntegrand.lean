import Foundation.IBMPhysicalRunningPrimitive
import Foundation.GaussianReflectedC2Ito

/-! The ACTUAL running signed-Dirac coefficient has a genuine predictable
Brownian L2 realization, obtained from the original smooth Ito integrands. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalRunningIntegrand
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalRunningPrimitive
open IBMPhysicalNoiseClock IBMPhysicalDirac BrownianClockWeightedEnergy
open GaussianTimeProductL2 GaussianPredictableFull GaussianTimeProcess
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _

def spatial (n : ℕ) (L : Tests) (r : ℝ) : ℝ :=
  BrownianSignIntegral.signum r * first n L |r|

def spatialLimit (L : Tests) (r : ℝ) : ℝ :=
  BrownianSignIntegral.signum r * L (dirac |r|)

def growthConstant (L : Tests) : ℝ :=
  ‖L‖*(‖IBMDeltaBoundary.deltaZeroHminusOne‖+3*‖physicalDerivative‖)

theorem growthConstant_nonneg (L : Tests) : 0 ≤ growthConstant L := by
  unfold growthConstant
  positivity

theorem spatial_growth (n : ℕ) (L : Tests) (r : ℝ) :
    ‖spatial n L r‖ ≤ growthConstant L*(1+|r|) := by
  have h : ‖first n L |r|‖ ≤ growthConstant L*(1+|r|) := by
    rw [first_physical]
    have hb := (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (IBMSchwartzPhysicalSlope.translated_growth n |r|) (norm_nonneg L))
    simpa only [growthConstant, abs_abs, mul_assoc] using hb
  rw [spatial, norm_mul]
  exact (mul_le_mul_of_nonneg_right (BrownianSignIntegral.signum_bound r)
    (norm_nonneg _)).trans (by simpa only [one_mul] using h)

theorem spatial_tendsto (L : Tests) (r : ℝ) :
    Tendsto (fun n => spatial n L r) atTop (nhds (spatialLimit L r)) :=
  tendsto_const_nhds.mul (first_tendsto L |r|)

theorem spatialLimit_growth (L : Tests) (r : ℝ) :
    ‖spatialLimit L r‖ ≤ growthConstant L*(1+|r|) :=
  le_of_tendsto (spatial_tendsto L r).norm (Eventually.of_forall fun n => spatial_growth n L r)

theorem spatialLimit_measurable (L : Tests) : StronglyMeasurable (spatialLimit L) :=
  BrownianSignIntegral.signum_measurable.stronglyMeasurable.mul
    ((L.continuous.comp (dirac_continuous.comp continuous_abs)).stronglyMeasurable)

def native (n : ℕ) (T : ℝ≥0) (L : Tests) : fullPredictable :=
  GaussianReflectedC2Ito.running (value n L) (value_C2 n L) (bound1 n L) (second_bound n L) T

theorem native_coeFn (n : ℕ) (T : ℝ≥0) (L : Tests) :
    (native n T L : TimeProbabilityL2) =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => spatial n L (sigma z)) := by
  simpa only [native, value_deriv, spatial] using
    GaussianReflectedC2Ito.running_coeFn (value n L) (value_C2 n L)
      (bound1 n L) (second_bound n L) T

def majorant (T : ℝ≥0) (L : Tests) (z : ℝ × SampleSpace) : ℝ :=
  (PredictableRealL2.horizon T).indicator (fun z => growthConstant L*(1+|sigma z|)) z

theorem majorant_memLp (T : ℝ≥0) (L : Tests) : MemLp (majorant T L) 2 timeProbability :=
  (memLp_indicator_iff_restrict (PredictableRealL2.horizon_measurable T)).mpr
    ((IBMSchwartzPhysicalSlopeClock.horizon_growth_memLp T).const_mul (growthConstant L))

theorem limit_memLp (T : ℝ≥0) (L : Tests) :
    MemLp ((PredictableRealL2.horizon T).indicator (fun z => spatialLimit L (sigma z)))
      2 timeProbability := by
  apply (majorant_memLp T L).mono'
    (((spatialLimit_measurable L).comp_measurable sigma_measurable).indicator
      (PredictableRealL2.horizon_measurable T)).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [majorant, indicator_of_mem hz]
      exact spatialLimit_growth L (sigma z)
    · simp [majorant, hz]

def limitField (T : ℝ≥0) (L : Tests) : TimeProbabilityL2 := (limit_memLp T L).toLp _

theorem limitField_coeFn (T : ℝ≥0) (L : Tests) : limitField T L =ᵐ[timeProbability]
    (PredictableRealL2.horizon T).indicator (fun z => spatialLimit L (sigma z)) :=
  MemLp.coeFn_toLp _

theorem native_field_tendsto (T : ℝ≥0) (L : Tests) :
    Tendsto (fun n => (native n T L : TimeProbabilityL2)) atTop (nhds (limitField T L)) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _ ((majorant_memLp T L).toLp _)
  · intro n
    filter_upwards [native_coeFn n T L, (majorant_memLp T L).coeFn_toLp] with z hn hm
    rw [hn, hm]
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [majorant, indicator_of_mem hz]
      rw [Real.norm_of_nonneg (mul_nonneg (growthConstant_nonneg L) (by positivity))]
      exact spatial_growth n L (sigma z)
    · simp [majorant, hz]
  · filter_upwards [limitField_coeFn T L, (majorant_memLp T L).coeFn_toLp] with z hl hm
    rw [hl, hm]
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [majorant, indicator_of_mem hz]
      rw [Real.norm_of_nonneg (mul_nonneg (growthConstant_nonneg L) (by positivity))]
      exact spatialLimit_growth L (sigma z)
    · simp [majorant, hz]
  · filter_upwards [ae_all_iff.mpr (fun n => native_coeFn n T L), limitField_coeFn T L]
      with z hn hl
    simp only [hn, hl]
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simpa only [indicator_of_mem hz] using spatial_tendsto L (sigma z)
    · simpa only [indicator_of_notMem hz] using tendsto_const_nhds

theorem limitField_mem (T : ℝ≥0) (L : Tests) : limitField T L ∈ fullPredictable :=
  fullPredictable_isClosed.mem_of_tendsto (native_field_tendsto T L)
    (Eventually.of_forall fun n => (native n T L).property)

def limitIntegrand (T : ℝ≥0) (L : Tests) : fullPredictable := ⟨limitField T L, limitField_mem T L⟩

theorem native_tendsto (T : ℝ≥0) (L : Tests) :
    Tendsto (fun n => native n T L) atTop (nhds (limitIntegrand T L)) :=
  tendsto_subtype_rng.mpr (native_field_tendsto T L)

theorem stochastic_tendsto (T : ℝ≥0) (L : Tests) :
    Tendsto (fun n => itoIntegral (native n T L)) atTop (nhds (itoIntegral (limitIntegrand T L))) :=
  itoIntegral.continuous.tendsto _ |>.comp (native_tendsto T L)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalRunningIntegrand
