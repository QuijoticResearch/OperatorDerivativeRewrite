import Foundation.IBMPhysicalJointStepPairing
import Foundation.GaussianFiniteHorizonAdjoint

/-! Actual finite and full predictable physical-test fields, with genuine
ambient step inner products supplied by the verified joint covariance theorem. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedPhysicalPredictable
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeProductL2
open GaussianPredictableFull GaussianPredictableHorizon GaussianFiniteHorizonAdjoint
open GaussianConditionalIto IBMPhysicalWeakWiener IBMPhysicalJointStepPairing

def finite (T : ℝ≥0) (L : Tests) : PredictableDomain T :=
  ⟨(L.comp IBMPhysicalNegativeEmbedding.embedding).compLpL 2
      (BrownianClockWeightedEnergy.base T) (IBMFoldedHeatPredictable.input T).val,
    (((L.comp IBMPhysicalNegativeEmbedding.embedding).continuous.comp_aestronglyMeasurable
      (IBMFoldedHeatPredictable.input T).property).congr
        ((L.comp IBMPhysicalNegativeEmbedding.embedding).coeFn_compLpL
          (IBMFoldedHeatPredictable.input T).val).symm)⟩

theorem finite_ae (T : ℝ≥0) (L : Tests) :
    (finite T L).val =ᵐ[BrownianClockWeightedEnergy.base T] joint T L := by
  filter_upwards [(L.comp IBMPhysicalNegativeEmbedding.embedding).coeFn_compLpL
    (IBMFoldedHeatPredictable.input T).val, IBMFoldedHeatPredictable.input_ae T] with z hc hi
  change ((L.comp IBMPhysicalNegativeEmbedding.embedding).compLpL 2
    (BrownianClockWeightedEnergy.base T) (IBMFoldedHeatPredictable.input T).val) z = _
  rw [hc,hi]
  rfl

def full (T : ℝ≥0) (L : Tests) : fullPredictable := extendPredictable T (finite T L)

theorem full_ae (T : ℝ≥0) (L : Tests) :
    (full T L : TimeProbabilityL2) =ᵐ[timeProbability]
      (PredictableRealL2.horizon T).indicator (joint T L) := by
  have hf := (ae_eq_restrict_iff_indicator_ae_eq
    (PredictableRealL2.horizon_measurable T)).mp (finite_ae T L)
  exact (L2ZeroExtension_coeFn (PredictableRealL2.horizon_measurable T) (finite T L).val).trans hf

theorem full_supported (T : ℝ≥0) (L : Tests) :
    GaussianPredictableCutoff.predictableCut T (full T L) = full T L :=
  cut_extended T (finite T L)

theorem inner_step (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (L : Tests) (V : GaussianL2) (hV : V ∈ pastL2 a) :
    inner ℝ (full T L : TimeProbabilityL2) (productTensor (intervalVector a b) V) =
      ((b : ℝ)-a)*inner ℝ (IBMSchwartzWeakWienerClosure.evaluate L
        (IBMPhysicalPointSlope.slopeLimit T)) V := by
  rw [L2_inner_eq_integral]
  have ht := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn a b)
  have he : (fun z : ℝ × SampleSpace => inner ℝ
      ((full T L : TimeProbabilityL2) z) (productTensor (intervalVector a b) V z))
      =ᵐ[timeProbability] (Ioc (a : ℝ) b ×ˢ (univ : Set SampleSpace)).indicator
        (fun z => joint T L z*V z.2) := by
    filter_upwards [full_ae T L, productTensor_coeFn (intervalVector a b) V, ht]
      with z hf hp ht
    simp only [Function.comp_def] at ht
    rw [hf,hp,ht,Real.inner_apply]
    by_cases hz : z.1 ∈ Ioc (a : ℝ) b
    · have hT : z ∈ PredictableRealL2.horizon T :=
        ⟨⟨lt_of_le_of_lt a.coe_nonneg hz.1, hz.2.trans hbT⟩, mem_univ _⟩
      simp only [indicator_of_mem hz, indicator_of_mem hT,
        indicator_of_mem (show z ∈ Ioc (a : ℝ) b ×ˢ (univ : Set SampleSpace) from ⟨hz,mem_univ _⟩),
        one_mul]
    · simp [hz]
  rw [integral_congr_ae he, integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
  rw [← Measure.restrict_prod_eq_prod_univ]
  exact joint_step_covariance a b T hab hbT L V hV

end OperatorDerivativeRewrite.Foundation.IBMFoldedPhysicalPredictable
