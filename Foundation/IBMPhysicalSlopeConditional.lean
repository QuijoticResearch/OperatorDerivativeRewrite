import Foundation.IBMPhysicalSceneryTestClockGraph
import Foundation.GaussianBrownianConditionalTransition
import Foundation.IBMPhysicalGaussianFold
import Foundation.IBMFoldedHeatPredictable

/-! Full raw-past conditioning of the ACTUAL physical-test IBM clock slope.
This does not yet identify the spatial folded heat coefficient. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalSlopeConditional
open InfiniteGaussian GaussianTimeProcess IBMPhysicalWeakWiener IBMPhysicalPointSlope
open IBMSchwartzWeakWienerClosure
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _

def testSlope (L : Tests) (r : ℝ) : ℝ :=
  BrownianSignIntegral.signum r * L (IBMPhysicalDirac.dirac |r|)

theorem testSlope_measurable (L : Tests) : Measurable (testSlope L) :=
  BrownianSignIntegral.signum_measurable.mul
    (L.continuous.comp (IBMPhysicalDirac.dirac_continuous.comp continuous_abs)).measurable

theorem actual_ae (T : ℝ≥0) (L : Tests) :
    evaluate L (slopeLimit T) =ᵐ[gaussianProduct] fun Y => testSlope L (process T Y) := by
  filter_upwards [(ContinuousLinearMap.apply ℝ ℝ L).coeFn_compLpL (slopeLimit T),
    slopeLimit_ae T, IBMConstructedSources.clockPath_coordinate_ae T] with Y he hs hc
  change evaluate L (slopeLimit T) Y = slopeLimit T Y L at he
  rw [he, hs L]
  simp only [testSlope, clockSign, hc]

theorem actual_memLp (T : ℝ≥0) (L : Tests) :
    MemLp (fun Y => testSlope L (process T Y)) 2 gaussianProduct :=
  (Lp.memLp (evaluate L (slopeLimit T))).ae_eq (actual_ae T L)

theorem conditional_slope (S T : ℝ≥0) (hST : S ≤ T) (L : Tests) :
    gaussianProduct[evaluate L (slopeLimit T) | naturalFiltration S] =ᵐ[gaussianProduct]
      fun Y => ∫ y, testSlope L (process S Y+y) ∂ProbabilityTheory.gaussianReal 0 (T-S) := by
  exact (condExp_congr_ae (m := naturalFiltration S) (actual_ae T L)).trans
    (GaussianBrownianConditionalTransition.conditional_transition S T hST (testSlope L)
      (testSlope_measurable L).stronglyMeasurable
      ((actual_memLp T L).integrable (by norm_num)))

theorem shifted_mean (L : Tests) (b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ y, testSlope L (b+y) ∂ProbabilityTheory.gaussianReal 0 v) =
      L (IBMPhysicalNegativeEmbedding.embedding (IBMFoldedHeatField.column (b,v))) := by
  have hl : ProbabilityTheory.HasLaw (fun y : ℝ => b+y)
      (ProbabilityTheory.gaussianReal b v) (ProbabilityTheory.gaussianReal 0 v) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [zero_add] using ProbabilityTheory.gaussianReal_map_const_add (μ := 0) (v := v) b
  have he := hl.integral_comp (testSlope_measurable L).stronglyMeasurable.aestronglyMeasurable
  calc
    _ = ∫ r, testSlope L r ∂ProbabilityTheory.gaussianReal b v := he
    _ = _ := IBMPhysicalGaussianFold.physical_test_mean L b hv

theorem conditional_column (S T : ℝ≥0) (hST : S < T) (L : Tests) :
    gaussianProduct[evaluate L (slopeLimit T) | naturalFiltration S] =ᵐ[gaussianProduct]
      fun Y => L (IBMPhysicalNegativeEmbedding.embedding
        (IBMFoldedHeatField.column (process S Y,T-S))) := by
  filter_upwards [conditional_slope S T hST.le L] with Y hy
  rw [hy]
  exact shifted_mean L (process S Y) (ne_of_gt (tsub_pos_iff_lt.mpr hST))

theorem conditional_actual_field (S T : ℝ≥0) (hST : S < T) (L : Tests) :
    gaussianProduct[evaluate L (slopeLimit T) | naturalFiltration S] =ᵐ[gaussianProduct]
      fun Y => L (IBMPhysicalNegativeEmbedding.embedding
        (IBMFoldedHeatPredictable.raw T (S,Y))) := by
  have hv : Real.toNNReal ((T : ℝ)-S) = T-S := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal ((T : ℝ)-S) (sub_nonneg.mpr hST.le), NNReal.coe_sub hST.le]
  filter_upwards [conditional_column S T hST L,
    IBMConstructedSources.clockPath_coordinate_ae S] with Y hy hc
  rw [hy]
  simp only [IBMFoldedHeatPredictable.raw, BrownianClockWeightedEnergy.sigma,
    Real.toNNReal_coe, hc, hv]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalSlopeConditional
