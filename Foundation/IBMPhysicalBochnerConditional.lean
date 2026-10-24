import Foundation.IBMPhysicalSlopeConditional

/-! A kernel-valued conditional version before physical testing.
The common full-measure statement avoids intersecting uncountably many test null sets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalBochnerConditional
open InfiniteGaussian GaussianTimeProcess IBMPhysicalWeakWiener IBMPhysicalPointSlope
open IBMPhysicalGaussianFold
local instance : AddCommGroup Kernel :=
  (inferInstance : NormedAddCommGroup Kernel).toAddCommGroup
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _
local instance : SMul ℝ Kernel := (inferInstance : NormedSpace ℝ Kernel).toModule.toSMul

theorem actual_ae (T : ℝ≥0) :
    signedDirac T =ᵐ[gaussianProduct] fun Y => signed (process T Y) := by
  filter_upwards [signedDirac_ae T, IBMConstructedSources.clockPath_coordinate_ae T] with Y hs hc
  rw [hs]
  simp only [clockSign, signed, hc]
  apply BesselPotentialSpace.ext
  rfl

theorem actual_memLp (T : ℝ≥0) : MemLp (fun Y => signed (process T Y)) 2 gaussianProduct :=
  (Lp.memLp (signedDirac T)).ae_eq (actual_ae T)

theorem shifted_mean (b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ y, signed (b+y) ∂gaussianReal 0 v) =
      IBMPhysicalNegativeEmbedding.embedding (IBMFoldedHeatField.column (b,v)) := by
  have hl : HasLaw (fun y : ℝ => b+y) (gaussianReal b v) (gaussianReal 0 v) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [zero_add] using gaussianReal_map_const_add (μ := 0) (v := v) b
  exact (hl.integral_comp signed_stronglyMeasurable.aestronglyMeasurable).trans
    (gaussian_mean_embedding b hv)

theorem conditional_column (S T : ℝ≥0) (hST : S < T) :
    gaussianProduct[signedDirac T | naturalFiltration S] =ᵐ[gaussianProduct]
      fun Y => IBMPhysicalNegativeEmbedding.embedding
        (IBMFoldedHeatField.column (process S Y,T-S)) := by
  have h := (condExp_congr_ae (m := naturalFiltration S) (actual_ae T)).trans
    (GaussianBrownianConditionalTransition.conditional_transition S T hST.le signed
      signed_stronglyMeasurable ((actual_memLp T).integrable (by norm_num)))
  filter_upwards [h] with Y hy
  rw [hy]
  exact shifted_mean (process S Y) (ne_of_gt (tsub_pos_iff_lt.mpr hST))

theorem conditional_actual_field (S T : ℝ≥0) (hST : S < T) :
    gaussianProduct[signedDirac T | naturalFiltration S] =ᵐ[gaussianProduct]
      fun Y => IBMPhysicalNegativeEmbedding.embedding (IBMFoldedHeatPredictable.raw T (S,Y)) := by
  have hv : Real.toNNReal ((T : ℝ)-S) = T-S := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal ((T : ℝ)-S) (sub_nonneg.mpr hST.le), NNReal.coe_sub hST.le]
  filter_upwards [conditional_column S T hST,
    IBMConstructedSources.clockPath_coordinate_ae S] with Y hy hc
  rw [hy]
  simp only [IBMFoldedHeatPredictable.raw, BrownianClockWeightedEnergy.sigma,
    Real.toNNReal_coe, hc, hv]

theorem common_physical_tests (S T : ℝ≥0) (hST : S < T) : ∀ᵐ Y ∂gaussianProduct,
    ∀ L : Tests, L (gaussianProduct[signedDirac T | naturalFiltration S] Y) =
      L (IBMPhysicalNegativeEmbedding.embedding (IBMFoldedHeatPredictable.raw T (S,Y))) :=
  (conditional_actual_field S T hST).mono fun _ h L => congrArg L h

end OperatorDerivativeRewrite.Foundation.IBMPhysicalBochnerConditional
