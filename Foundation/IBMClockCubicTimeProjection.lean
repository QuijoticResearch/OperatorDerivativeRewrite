import Foundation.GaussianWickContinuity
import Foundation.IBMClockCubicCorrection

/-! Unconditional per-path Bochner time projection of the actual cubic IBM
scenery correction. Joint clock moment and stochastic local-time limits remain separate. -/
noncomputable section
open MeasureTheory
open scoped NNReal
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.IBMClockCubicTimeProjection
open InfiniteGaussian IBMGaussianSteinMoments IBMJointMollifierGaussian
open IBMContinuousScenery IBMSceneryCubicProjection IBMClockCubicCorrection IBMConstructedSources
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

theorem tripleCoefficient_continuous (n : ℕ) (i : Fin 3) :
    Continuous (fun x : ℝ => tripleCoefficient n x i) := by
  apply firstChaosEmbedding.isometry.comp_continuous_iff.mp
  have he : (firstChaosEmbedding ∘ (fun x : ℝ => tripleCoefficient n x i)) =
      wholeLineScenery (derivativeKernel n i) := by
    funext x
    exact (wholeLineScenery_eq_sourceEmbedding _ _).symm
  rw [he]
  exact wholeLineScenery_continuous (IBMDyadicExtension.derivativeKernel_regular n i).1
    (IBMDyadicExtension.derivativeKernel_regular n i).2

theorem spatialCorrection_continuous (n : ℕ) : Continuous (spatialCorrection n) :=
  GaussianWickContinuity.correction_continuous_of _ _ _
    (tripleCoefficient_continuous n 0) (tripleCoefficient_continuous n 1)
    (tripleCoefficient_continuous n 2)

theorem sourceVector_continuous (n : ℕ) : Continuous (sourceVector n) := by
  apply (GaussianHilbertProcess.isonormalEmbedding
    FractionalSpectralKernel.SpectralSpace).isometry.comp_continuous_iff.mp
  have he : (GaussianHilbertProcess.isonormalEmbedding FractionalSpectralKernel.SpectralSpace ∘
      sourceVector n) = GaussianPastFirstChaos.projection ∘ spatialCorrection n := by
    funext x
    exact (projection_eq_sourceEmbedding n x).symm
  rw [he]
  exact GaussianPastFirstChaos.projection.continuous.comp (spatialCorrection_continuous n)

theorem sectionClass_time_integrable (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    Integrable (fun s : ℝ => sectionClass n (Real.toNNReal s) ωY)
      (volume.restrict (Set.Icc 0 T)) := by
  have hc : Continuous (fun s : ℝ => sectionClass n (Real.toNNReal s) ωY) :=
    (spatialCorrection_continuous n).comp (continuous_abs.comp
      ((clockPath ωY).continuous.comp continuous_real_toNNReal))
  exact hc.integrableOn_Icc

theorem sourceVector_time_integrable (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    Integrable (fun s : ℝ => sourceVector n |clockPath ωY (Real.toNNReal s)|)
      (volume.restrict (Set.Icc 0 T)) :=
  ((sourceVector_continuous n).comp (continuous_abs.comp
    ((clockPath ωY).continuous.comp continuous_real_toNNReal))).integrableOn_Icc

/-- The earlier conditional time theorem now has its integrability hypothesis
discharged for every constructed clock path and every finite horizon. -/
theorem time_integrated_projection (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    GaussianPastFirstChaos.projection
        (∫ s in Set.Icc 0 T, sectionClass n (Real.toNNReal s) ωY) =
      GaussianHilbertProcess.isonormalEmbedding FractionalSpectralKernel.SpectralSpace
        (∫ s in Set.Icc 0 T, sourceVector n |clockPath ωY (Real.toNNReal s)|) :=
  IBMClockCubicCorrection.time_integrated_source_vector n ωY T
    (sectionClass_time_integrable n ωY T)

end OperatorDerivativeRewrite.Foundation.IBMClockCubicTimeProjection
