import Foundation.IBMPhysicalRunningPrimitive
import Foundation.IBMSchwartzPhysicalSlopeClock

/-! The actual point signed-Dirac clock coefficient in physical H^-1,
with native strong Bochner convergence and proved predictability. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal BesselPotentialSpace SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalPointClockField
open InfiniteGaussian IBMConstructedSources
open IBMPhysicalDirac IBMPhysicalNoiseClock IBMPhysicalNoiseCalculus
open IBMPhysicalNoiseVectors
open IBMPhysicalNegativeEmbedding BrownianClockWeightedEnergy GaussianTimeProductL2
open GaussianPredictableFull GaussianTimeProcess GaussianHermiteIntegrand GaussianHermiteRepresentation
local instance : InnerProductSpace ℝ H^{(-1 : ℝ)}(ℝ) :=
  InnerProductSpace.rclikeToReal ℂ _
attribute [local instance] realNormSMul realContinuousSMul

def growthConstant : ℝ :=
  ‖IBMDeltaBoundary.deltaZeroHminusOne‖+3*‖physicalDerivative‖

theorem growth_nonneg : 0 ≤ growthConstant := by
  unfold growthConstant
  positivity

theorem translated_continuous (n : ℕ) : Continuous (translated n) := by
  change Continuous (fun r => translated n r)
  simp_rw [translated_eq]
  have he : convolutionKernel (IBMMollifier.kernel n) = fun r =>
      kernelPullback (IBMContinuousScenery.wholeLineScenery (IBMMollifier.kernel n) r) :=
    funext fun r => (kernelPullback_convolution (IBMMollifier.kernel_smooth n).continuous
      (IBMMollifier.kernel_compactSupport n) r).symm
  rw [he]
  exact continuous_const.sub (physicalDerivative.continuous.comp
    (kernelPullback.continuous.comp (IBMRandomTimeHilbert.mollifiedScenery_continuous n)))

def spatial (n : ℕ) (r : ℝ) : H^{(-1 : ℝ)}(ℝ) :=
  BrownianSignIntegral.signum r • translated n |r|

def spatialLimit (r : ℝ) : H^{(-1 : ℝ)}(ℝ) :=
  BrownianSignIntegral.signum r • dirac |r|

theorem spatial_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (spatial n) :=
  BrownianSignIntegral.signum_measurable.stronglyMeasurable.smul
    ((translated_continuous n).stronglyMeasurable.comp_measurable continuous_abs.measurable)

theorem spatialLimit_stronglyMeasurable :
    StronglyMeasurable (spatialLimit) :=
  BrownianSignIntegral.signum_measurable.stronglyMeasurable.smul
    (dirac_continuous.stronglyMeasurable.comp_measurable continuous_abs.measurable)

theorem spatial_tendsto (r : ℝ) :
    Tendsto (fun n => spatial n r) atTop (𝓝 (spatialLimit r)) :=
  tendsto_const_nhds.smul (translated_tendsto |r|)

theorem spatial_growth (n : ℕ) (r : ℝ) :
    ‖spatial n r‖ ≤growthConstant*(1+|r|) := by
  rw [spatial, norm_smul]
  exact (mul_le_mul (BrownianSignIntegral.signum_bound r) (IBMSchwartzPhysicalSlope.translated_growth n |r|)
    (norm_nonneg _) (by norm_num)).trans_eq (by simp only [abs_abs, one_mul, growthConstant])

theorem spatialLimit_growth (r : ℝ) :
    ‖spatialLimit r‖ ≤growthConstant*(1+|r|) :=
  le_of_tendsto (spatial_tendsto  r).norm
    (Eventually.of_forall fun n => spatial_growth n r)

def majorant (T : ℝ≥0) (z : ℝ × SampleSpace) : ℝ :=
  (PredictableRealL2.horizon T).indicator (fun z =>growthConstant*(1+|sigma z|)) z

theorem majorant_memLp (T : ℝ≥0) :
    MemLp (majorant T) 2 timeProbability :=
  (memLp_indicator_iff_restrict (PredictableRealL2.horizon_measurable T)).mpr
    ((IBMSchwartzPhysicalSlopeClock.horizon_growth_memLp T).const_mul growthConstant)

theorem field_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp ((PredictableRealL2.horizon T).indicator (fun z => spatial n (sigma z)))
      2 timeProbability := by
  apply (majorant_memLp T).mono'
    (((spatial_stronglyMeasurable n).comp_measurable sigma_measurable).indicator
      (PredictableRealL2.horizon_measurable T)).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [majorant, indicator_of_mem hz, Function.comp_apply]
      exact spatial_growth n (sigma z)
    · simp [majorant, hz]

theorem limitField_memLp (T : ℝ≥0) :
    MemLp ((PredictableRealL2.horizon T).indicator (fun z => spatialLimit (sigma z)))
      2 timeProbability := by
  apply (majorant_memLp T).mono'
    (((spatialLimit_stronglyMeasurable).comp_measurable sigma_measurable).indicator
      (PredictableRealL2.horizon_measurable T)).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [majorant, indicator_of_mem hz, Function.comp_apply]
      exact spatialLimit_growth  (sigma z)
    · simp [majorant, hz]

def field (n : ℕ) (T : ℝ≥0) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 timeProbability := (field_memLp n T).toLp _

def limitField (T : ℝ≥0) :
    Lp (H^{(-1 : ℝ)}(ℝ)) 2 timeProbability := (limitField_memLp  T).toLp _

theorem field_ae (n : ℕ) (T : ℝ≥0) :
    field n T =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => spatial n (sigma z)) :=
  MemLp.coeFn_toLp _

theorem limitField_ae (T : ℝ≥0) :
    limitField T =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (fun z => spatialLimit (sigma z)) :=
  MemLp.coeFn_toLp _

theorem field_tendsto (T : ℝ≥0) :
    Tendsto (fun n => field n T) atTop (𝓝 (limitField T)) := by
  apply BochnerL2Approximation.tendsto_of_dominated _ _ ((majorant_memLp T).toLp _)
  · intro n
    filter_upwards [field_ae n T, (majorant_memLp T).coeFn_toLp] with z hf hm
    rw [hf, hm]
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [majorant, indicator_of_mem hz]
      rw [Real.norm_of_nonneg (mul_nonneg (growth_nonneg)
        (by linarith [abs_nonneg (sigma z)]))]
      exact spatial_growth n (sigma z)
    · simp [majorant, hz]
  · filter_upwards [limitField_ae  T, (majorant_memLp T).coeFn_toLp] with z hf hm
    rw [hf, hm]
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simp only [majorant, indicator_of_mem hz]
      rw [Real.norm_of_nonneg (mul_nonneg (growth_nonneg)
        (by linarith [abs_nonneg (sigma z)]))]
      exact spatialLimit_growth  (sigma z)
    · simp [majorant, hz]
  · filter_upwards [ae_all_iff.mpr (fun n => field_ae n T), limitField_ae  T] with z hn hl
    simp only [hn, hl]
    by_cases hz : z ∈ PredictableRealL2.horizon T
    · simpa only [indicator_of_mem hz] using spatial_tendsto  (sigma z)
    · simpa only [indicator_of_notMem hz] using tendsto_const_nhds

/-- The actual fields have predictable representatives for the existing
Brownian clock filtration; this is not an assumed target Ito domain. -/
theorem field_predictable (n : ℕ) (T : ℝ≥0) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (field n T) timeProbability := by
  obtain ⟨b,hb,he⟩ := ((mem_fullPredictable_iff _).mp (hermiteIntegrand 1 T).property).1
  refine ⟨spatial n ∘ b, (spatial_stronglyMeasurable n).comp_measurable hb.measurable, ?_⟩
  filter_upwards [field_ae n T, BrownianSignIntegral.brownian_field_joint T, he] with z hf hB hb
  rw [hf]
  change _ = spatial n (b z)
  rw [← hb, hB]
  by_cases hz : z ∈ PredictableRealL2.horizon T
  · simp [hz]
  · simp only [indicator_of_notMem hz, spatial, BrownianSignIntegral.signum_zero, abs_zero]
    symm
    apply norm_eq_zero.mp
    rw [norm_smul, norm_zero, zero_mul]

theorem limitField_predictable (T : ℝ≥0) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration]
      (limitField T) timeProbability := by
  obtain ⟨b,hb,he⟩ := ((mem_fullPredictable_iff _).mp (hermiteIntegrand 1 T).property).1
  refine ⟨spatialLimit ∘ b, (spatialLimit_stronglyMeasurable).comp_measurable hb.measurable, ?_⟩
  filter_upwards [limitField_ae  T, BrownianSignIntegral.brownian_field_joint T, he] with z hf hB hb
  rw [hf]
  change _ = spatialLimit (b z)
  rw [← hb, hB]
  by_cases hz : z ∈ PredictableRealL2.horizon T
  · simp [hz]
  · simp only [indicator_of_notMem hz, spatialLimit, BrownianSignIntegral.signum_zero, abs_zero]
    symm
    apply norm_eq_zero.mp
    rw [norm_smul, norm_zero, zero_mul]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalPointClockField
