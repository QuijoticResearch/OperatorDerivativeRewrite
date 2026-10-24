import Foundation.IBMFoldedHeatField
import Foundation.IBMFoldedHeatClockEnergy
import Foundation.IBMSpatialPointClockEnergy

/-! The explicit folded heat candidate belongs to the ORIGINAL spatial
predictable Ito domain. Its equality with the canonical IBM input is not assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedHeatPredictable
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess BrownianClockWeightedEnergy
open GaussianTimeProductL2 GaussianPredictableFull GaussianHermiteIntegrand
open GaussianHermiteRepresentation GaussianComplexHorizonIto IBMFoldedHeatField
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

private theorem nnTime_predictable :
    @Measurable (ℝ × SampleSpace) ℝ≥0 (PredictableRealL2.predictable naturalFiltration)
      inferInstance (fun z => z.1.toNNReal) := by
  apply measurable_of_Ioi
  intro a
  have hp : @Measurable (ℝ × SampleSpace) (ℝ≥0 × SampleSpace)
      (PredictableRealL2.predictable naturalFiltration) naturalFiltration.predictable
      PredictableRealL2.toNonnegative := Measurable.of_comap_le le_rfl
  have hs := (measurableSet_predictable_Ioi_prod
    (𝓕 := naturalFiltration) (i := a) MeasurableSet.univ).preimage hp
  have he : (fun z : ℝ × SampleSpace => z.1.toNNReal) ⁻¹' Ioi a =
      PredictableRealL2.toNonnegative ⁻¹' (Ioi a ×ˢ (univ : Set SampleSpace)) := by
    ext z
    simp [PredictableRealL2.toNonnegative]
  rw [he]
  exact hs

def raw (T : ℝ≥0) (z : ℝ × SampleSpace) : TimeHilbert :=
  column (sigma z, Real.toNNReal ((T : ℝ)-z.1))

theorem raw_stronglyMeasurable (T : ℝ≥0) : StronglyMeasurable (raw T) :=
  column_stronglyMeasurable.comp_measurable
    (sigma_measurable.prodMk ((measurable_const.sub measurable_fst).real_toNNReal))

theorem raw_energy (T : ℝ≥0) (z : ℝ × SampleSpace) (hz : z.1 ≤ T) :
    ‖raw T z‖^2 = IBMFoldedHeatClockEnergy.raw T z := by
  rw [raw, column_energy]
  simp only [Real.coe_toNNReal ((T : ℝ)-z.1) (sub_nonneg.mpr hz),
    IBMFoldedHeatClockEnergy.raw, IBMFoldedHeatTimeEnergy.energy]

theorem raw_memLp (T : ℝ≥0) : MemLp (raw T) 2 (base T) := by
  apply (memLp_two_iff_integrable_sq_norm (raw_stronglyMeasurable T).aestronglyMeasurable).mpr
  apply (IBMFoldedHeatClockEnergy.raw_integrable T).congr
  filter_upwards [ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hz
  exact (raw_energy T z hz.1.2).symm

theorem raw_predictable (T : ℝ≥0) :
    AEStronglyMeasurable[PredictableRealL2.predictable naturalFiltration] (raw T) (base T) := by
  obtain ⟨b,hb,he⟩ := ((mem_fullPredictable_iff _).mp (hermiteIntegrand 1 T).property).1
  have ht : @Measurable (ℝ × SampleSpace) ℝ (PredictableRealL2.predictable naturalFiltration)
      inferInstance (fun z => (z.1.toNNReal : ℝ)) :=
    NNReal.continuous_coe.measurable.comp nnTime_predictable
  refine ⟨fun z => column (b z, Real.toNNReal ((T : ℝ)-(z.1.toNNReal : ℝ))),
    column_stronglyMeasurable.comp_measurable
      (hb.measurable.prodMk ((measurable_const.sub ht).real_toNNReal)), ?_⟩
  filter_upwards [ae_restrict_of_ae he,
    ae_restrict_of_ae (BrownianSignIntegral.brownian_field_joint T),
    ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hb hB hz
  change column (sigma z, Real.toNNReal ((T : ℝ)-z.1)) = _
  rw [← hb, hB, indicator_of_mem hz,
    Real.coe_toNNReal z.1 hz.1.1.le]

def input (T : ℝ≥0) : lpMeas TimeHilbert ℝ
    (PredictableRealL2.predictable naturalFiltration) 2 (base T) :=
  ⟨(raw_memLp T).toLp (raw T), (raw_predictable T).congr (raw_memLp T).coeFn_toLp.symm⟩

theorem input_ae (T : ℝ≥0) : (input T).val =ᵐ[base T] raw T :=
  (raw_memLp T).coeFn_toLp

def trim (T : ℝ≥0) : Lp TimeHilbert 2 (predictableMeasure T) :=
  lpMeasToLpTrimLie TimeHilbert ℝ 2 (base T)
    (PredictableRealL2.predictable_le naturalFiltration) (input T)

def integralValue (T : ℝ≥0) : Lp TimeHilbert 2 gaussianProduct :=
  GaussianParameterizedIto.realIntegral volume T (trim T)

theorem integral_energy (T : ℝ≥0) :
    ‖integralValue T‖^2 = ∫ z, IBMFoldedHeatClockEnergy.raw T z ∂base T := by
  rw [integralValue, (GaussianParameterizedIto.realIntegral volume T).norm_map]
  have ht : ‖trim T‖ = ‖(input T).val‖ :=
    (lpMeasToLpTrimLie TimeHilbert ℝ 2 (base T)
      (PredictableRealL2.predictable_le naturalFiltration)).norm_map (input T)
  rw [ht, BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [input_ae T, ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z hi hz
  rw [hi]
  exact raw_energy T z hz.1.2

end OperatorDerivativeRewrite.Foundation.IBMFoldedHeatPredictable
