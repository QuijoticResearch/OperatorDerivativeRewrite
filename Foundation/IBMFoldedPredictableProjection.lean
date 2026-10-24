import Foundation.IBMFoldedPhysicalPredictable
import Foundation.GaussianPredictableStepExt
import Foundation.IBMSpatialTerminalReconstruction

/-! Equality with the ORIGINAL Hilbert predictable projection, obtained from
actual joint step pairings and verified full-domain step density. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedPredictableProjection
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianTimeProcess
open GaussianPredictableFull GaussianPredictableAdjoint GaussianPredictableCutoff
open GaussianConditionalIto GaussianContinuousRigidity GaussianTimeFieldNorm
open GaussianTimeDivergence SeparableHilbertEmbedding
open IBMPhysicalWeakWiener IBMPhysicalSceneryTestClockGraph IBMFoldedPhysicalPredictable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

def projected (T : ℝ≥0) (L : Tests) : fullPredictable := predictableProjection (gradient T L)

theorem point_past (T : ℝ≥0) (L : Tests) : point T L ∈ pastL2 T := by
  rw [← IBMSpatialTerminalReconstruction.physical_source_projection T L]
  exact ((L.comp IBMPhysicalNegativeEmbedding.embedding).continuous.comp_aestronglyMeasurable
    (IBMSpatialTerminalReconstruction.source_past T)).congr
      ((L.comp IBMPhysicalNegativeEmbedding.embedding).coeFn_compLpL
        (IBMPhysicalNoiseClock.sourceKernel T)).symm

theorem projected_eq_adjoint (T : ℝ≥0) (hT : 0 < T) (L : Tests) :
    projected T L = predictableAdjoint (point T L) := by
  have h := predictableAdjoint_eq_projected_derivative ⟨point T L, point_mem T hT L⟩
  rw [derivative_value T hT L] at h
  exact h.symm

theorem projected_supported (T : ℝ≥0) (hT : 0 < T) (L : Tests) :
    predictableCut T (projected T L) = projected T L := by
  rw [projected_eq_adjoint T hT L]
  exact GaussianConditionalClarkOcone.past_representer_supported T _ (point_past T L)

theorem projected_inner_step (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (L : Tests) (V : GaussianL2) (hV : V ∈ pastL2 a) :
    inner ℝ (projected T L : TimeProbabilityL2) (productTensor (intervalVector a b) V) =
      ((b : ℝ)-a)*inner ℝ (IBMSchwartzWeakWienerClosure.evaluate L
        (IBMPhysicalPointSlope.slopeLimit T)) V := by
  let w : fullPredictable := ⟨productTensor (intervalVector a b) V,
    past_step_mem_fullPredictable a b V hV⟩
  change inner ℝ (predictableField.toContinuousLinearMap.adjoint (gradient T L)) w = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (gradient T L) (fieldEmbedding (productTensor (intervalVector a b) V)) = _
  rw [fieldEmbedding_tensor]
  change inner ℝ (scalarTensor (IBMClockAverageCandidate.direction T)
    (IBMSchwartzWeakWienerClosure.evaluate L (IBMPhysicalPointSlope.slopeLimit T)))
      (scalarTensor (hilbertEmbedding TimeHilbert (intervalVector a b)) V) = _
  rw [scalarTensor_pair_inner, IBMClockAverageCandidate.direction, Real.toNNReal_coe,
    (hilbertEmbedding TimeHilbert).inner_map_map, timeVector, intervalVector_inner]
  have he : Ioc (0 : ℝ) T ∩ Ioc (a : ℝ) b = Ioc (a : ℝ) b :=
    inter_eq_right.mpr (fun x hx =>
      ⟨lt_of_le_of_lt a.coe_nonneg hx.1, hx.2.trans hbT⟩)
  rw [he]
  simp only [Measure.real, Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (show (a : ℝ) ≤ b from hab))]
  ring

theorem full_eq_projected (T : ℝ≥0) (hT : 0 < T) (L : Tests) : full T L = projected T L := by
  apply GaussianPredictableStepExt.ext
  intro a b hab V hV
  have hf : cut T (full T L : TimeProbabilityL2) = (full T L : TimeProbabilityL2) :=
    congrArg Subtype.val (full_supported T L)
  have hp : cut T (projected T L : TimeProbabilityL2) = (projected T L : TimeProbabilityL2) :=
    congrArg Subtype.val (projected_supported T hT L)
  calc
    _ = inner ℝ (full T L : TimeProbabilityL2)
        (cut T (productTensor (intervalVector a b) V)) := by rw [← cut_inner, hf]
    _ = inner ℝ (projected T L : TimeProbabilityL2)
        (cut T (productTensor (intervalVector a b) V)) := by
      rw [cut_tensor, ← NNReal.coe_min]
      by_cases haT : a ≤ T
      · rw [inner_step a (min b T) T (le_min hab haT) (min_le_right _ _) L V hV,
          projected_inner_step a (min b T) T (le_min hab haT) (min_le_right _ _) L V hV]
      · have hz := GaussianConditionalIto.tensor_eq_zero_of_le a (min b T)
          ((min_le_right b T).trans (le_of_not_ge haT)) V
        rw [hz, inner_zero_right, inner_zero_right]
    _ = _ := by rw [← cut_inner, hp]

theorem finite_eq_adjoint (T : ℝ≥0) (hT : 0 < T) (L : Tests) :
    finite T L = GaussianFiniteHorizonAdjoint.finiteAdjoint T (point T L) := by
  apply ext_inner_right ℝ
  intro V
  have hf := (GaussianFiniteHorizonAdjoint.extendPredictable T).inner_map_map (finite T L) V
  change inner ℝ (full T L) (GaussianFiniteHorizonAdjoint.extendPredictable T V) = _ at hf
  rw [full_eq_projected T hT L] at hf
  have hp := GaussianFiniteHorizonAdjoint.restriction_extension_duality T (projected T L) V
  have he := GaussianFiniteHorizonAdjoint.finiteAdjoint_on_full_derivative T
    ⟨point T L, point_mem T hT L⟩
  rw [derivative_value T hT L] at he
  rw [he]
  exact hf.symm.trans hp.symm

end OperatorDerivativeRewrite.Foundation.IBMFoldedPredictableProjection
