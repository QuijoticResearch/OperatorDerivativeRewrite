import Foundation.IBMSchwartzPhysicalSlope
import Foundation.BochnerL2Approximation

/-! Actual predictable H^-1-valued candidate clock integrands for the full
first-source slope, and their strong time-clock L2 limit. This module does
not assume or define a target-valued Ito integral. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal BesselPotentialSpace SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalSlopeClock
open InfiniteGaussian IBMConstructedSources IBMSchwartzPhysicalSlope
open IBMPhysicalNegativeEmbedding BrownianClockWeightedEnergy GaussianTimeProductL2
open GaussianPredictableFull GaussianTimeProcess GaussianHermiteIntegrand GaussianHermiteRepresentation
local instance : InnerProductSpace ℝ H^{(-1 : ℝ)}(ℝ) :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] realNormSMul realContinuousSMul

def spatial (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : H^{(-1 : ℝ)}(ℝ) :=
  BrownianSignIntegral.signum r • value g a n |r|

def spatialLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) : H^{(-1 : ℝ)}(ℝ) :=
  BrownianSignIntegral.signum r • limitValue g a |r|

theorem spatial_stronglyMeasurable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    StronglyMeasurable (spatial g a n) :=
  BrownianSignIntegral.signum_measurable.stronglyMeasurable.smul
    ((value_continuous g a n).stronglyMeasurable.comp_measurable continuous_abs.measurable)

theorem spatialLimit_stronglyMeasurable (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    StronglyMeasurable (spatialLimit g a) :=
  BrownianSignIntegral.signum_measurable.stronglyMeasurable.smul
    ((limitValue_stronglyMeasurable g a).comp_measurable continuous_abs.measurable)

theorem spatial_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) :
    Tendsto (fun n => spatial g a n r) atTop (𝓝 (spatialLimit g a r)) :=
  tendsto_const_nhds.smul (value_tendsto g a |r|)

theorem spatial_growth (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    ‖spatial g a n r‖ ≤ growthConstant g*(1+|r|) := by
  rw [spatial, norm_smul]
  exact (mul_le_mul (BrownianSignIntegral.signum_bound r) (value_growth g a n |r|)
    (norm_nonneg _) (by norm_num)).trans_eq (by simp only [abs_abs, one_mul])

theorem spatialLimit_growth (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) :
    ‖spatialLimit g a r‖ ≤ growthConstant g*(1+|r|) :=
  le_of_tendsto (spatial_tendsto g a r).norm
    (Eventually.of_forall fun n => spatial_growth g a n r)

theorem horizon_growth_memLp (T : ℝ≥0) :
    MemLp (fun z : ℝ × SampleSpace => 1+|sigma z|) 2
      (PredictableRealL2.horizonMeasure T gaussianProduct) := by
  have hm : StronglyMeasurable (fun z : ℝ × SampleSpace => 1+|sigma z|) :=
    (measurable_const.add sigma_measurable.norm).stronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  rw [PredictableRealL2.horizonMeasure_eq_product]
  apply (IBMClockEighthMoment.horizon_growth_integrable T).mono'
    (hm.norm.pow 2).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    change ‖‖1+|sigma z|‖^2‖ ≤ (1+|sigma z|)^8
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_right₀ (by linarith [abs_nonneg (sigma z)]) (by norm_num)

def majorant (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (z : ℝ × SampleSpace) : ℝ :=
  (PredictableRealL2.horizon T).indicator (fun z => growthConstant g*(1+|sigma z|)) z

theorem majorant_memLp (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) :
    MemLp (majorant g T) 2 timeProbability :=
  (memLp_indicator_iff_restrict (PredictableRealL2.horizon_measurable T)).mpr
    ((horizon_growth_memLp T).const_mul (growthConstant g))

theorem field_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp ((PredictableRealL2.horizon T).indicator (fun z => spatial g a n (sigma z)))
      2 timeProbability := by
  apply (majorant_memLp g T).mono'
    (((spatial_stronglyMeasurable g a n).comp_measurable sigma_measurable).indicator
      (PredictableRealL2.horizon_measurable T)).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [majorant, indicator_of_mem hz, Function.comp_apply]
      exact spatial_growth g a n (sigma z)
    · simp [majorant, hz]

theorem limitField_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    MemLp ((PredictableRealL2.horizon T).indicator (fun z => spatialLimit g a (sigma z)))
      2 timeProbability := by
  apply (majorant_memLp g T).mono'
    (((spatialLimit_stronglyMeasurable g a).comp_measurable sigma_measurable).indicator
      (PredictableRealL2.horizon_measurable T)).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [majorant, indicator_of_mem hz, Function.comp_apply]
      exact spatialLimit_growth g a (sigma z)
    · simp [majorant, hz]

def field (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 timeProbability := (field_memLp g a n T).toLp _

def limitField (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 timeProbability := (limitField_memLp g a T).toLp _

theorem field_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    field g a n T =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => spatial g a n (sigma z)) :=
  MemLp.coeFn_toLp _

theorem limitField_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    limitField g a T =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => spatialLimit g a (sigma z)) :=
  MemLp.coeFn_toLp _

theorem field_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => field g a n T) atTop (𝓝 (limitField g a T)) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _ ((majorant_memLp g T).toLp _)
  · intro n
    filter_upwards [field_ae g a n T, (majorant_memLp g T).coeFn_toLp] with z hf hm
    rw [hf, hm]
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [majorant, indicator_of_mem hz]
      rw [Real.norm_of_nonneg (mul_nonneg (growthConstant_nonneg g)
        (by linarith [abs_nonneg (sigma z)]))]
      exact spatial_growth g a n (sigma z)
    · simp [majorant, hz]
  · filter_upwards [limitField_ae g a T, (majorant_memLp g T).coeFn_toLp] with z hf hm
    rw [hf, hm]
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [majorant, indicator_of_mem hz]
      rw [Real.norm_of_nonneg (mul_nonneg (growthConstant_nonneg g)
        (by linarith [abs_nonneg (sigma z)]))]
      exact spatialLimit_growth g a (sigma z)
    · simp [majorant, hz]
  · filter_upwards [ae_all_iff.mpr (fun n => field_ae g a n T), limitField_ae g a T] with z hn hl
    simp only [hn, hl]
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simpa only [indicator_of_mem hz] using spatial_tendsto g a (sigma z)
    · simpa only [indicator_of_notMem hz] using tendsto_const_nhds

/-- The actual fields have predictable representatives for the existing
Brownian clock filtration; this is not an assumed target Ito domain. -/
theorem field_predictable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (field g a n T) timeProbability := by
  obtain ⟨b,hb,he⟩ := ((mem_fullPredictable_iff _).mp (hermiteIntegrand 1 T).property).1
  refine ⟨spatial g a n ∘ b, (spatial_stronglyMeasurable g a n).comp_measurable hb.measurable, ?_⟩
  filter_upwards [field_ae g a n T, BrownianSignIntegral.brownian_field_joint T, he] with z hf hB hb
  rw [hf]
  change _ = spatial g a n (b z)
  rw [← hb, hB]
  by_cases hz : z ∈ PredictableRealL2.horizon T
  · simp [hz]
  · simp only [indicator_of_notMem hz, spatial, BrownianSignIntegral.signum_zero, abs_zero]
    symm
    apply norm_eq_zero.mp
    rw [norm_smul, norm_zero, zero_mul]

theorem limitField_predictable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (limitField g a T) timeProbability := by
  obtain ⟨b,hb,he⟩ := ((mem_fullPredictable_iff _).mp (hermiteIntegrand 1 T).property).1
  refine ⟨spatialLimit g a ∘ b, (spatialLimit_stronglyMeasurable g a).comp_measurable hb.measurable, ?_⟩
  filter_upwards [limitField_ae g a T, BrownianSignIntegral.brownian_field_joint T, he] with z hf hB hb
  rw [hf]
  change _ = spatialLimit g a (b z)
  rw [← hb, hB]
  by_cases hz : z ∈ PredictableRealL2.horizon T
  · simp [hz]
  · simp only [indicator_of_notMem hz, spatialLimit, BrownianSignIntegral.signum_zero, abs_zero]
    symm
    apply norm_eq_zero.mp
    rw [norm_smul, norm_zero, zero_mul]

end OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalSlopeClock
