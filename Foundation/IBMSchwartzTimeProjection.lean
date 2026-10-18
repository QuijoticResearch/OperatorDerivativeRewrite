import Foundation.IBMSchwartzSourceContinuity

/-! Projection and clock averaging of the actual unprojected nonlinear
Schwartz source-L2 time correction. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzTimeProjection
open InfiniteGaussian GaussianNumberSectors IBMConstructedSources
open IBMSchwartzSecondProjection IBMSchwartzSpatialPrimitive IBMSchwartzClockMean
open IBMSchwartzSourceContinuity

variable (g : SchwartzMap ℝ ℝ) (a : ℝ)

def originClass (n : ℕ) : GaussianL2 :=
  weightedClass g a (IBMGaussianSteinMoments.tripleCoefficient n 0 0) 1
    (firstChaosEmbedding (IBMGaussianSteinMoments.tripleCoefficient n 0 1))

theorem origin_projection (n : ℕ) :
    projection 2 (originClass g a n) = spatialSlope g a n 0 :=
  (spatialSlope_eq_origin_projection g a n 0).symm

theorem mollified_path_continuous (n : ℕ) (ω : SampleSpace) :
    Continuous (fun s : ℝ => mollifiedClass g a n |clockPath ω s.toNNReal|) :=
  (mollifiedClass_continuous g a n).comp (continuous_abs.comp
    ((clockPath ω).continuous.comp continuous_real_toNNReal))

theorem integrated_projection (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    projection 2 (∫ s in 0..(T : ℝ), mollifiedClass g a n |clockPath ω s.toNNReal|) =
      integratedValue g a n T ω := by
  exact ((projection 2).intervalIntegral_comp_comm
    ((mollified_path_continuous g a n ω).intervalIntegrable 0 T)).symm

def wholeCorrection (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) : GaussianL2 :=
  BrownianMassLimitIdentification.coordinateClass T ω • originClass g a n +
    (1/2 : ℝ) • ∫ s in 0..(T : ℝ), mollifiedClass g a n |clockPath ω s.toNNReal|

theorem wholeCorrection_projection (n : ℕ) (T : ℝ≥0) (ω : SampleSpace) :
    projection 2 (wholeCorrection g a n T ω) =
      BrownianMassLimitIdentification.coordinateClass T ω • spatialSlope g a n 0 +
        (1/2 : ℝ) • integratedValue g a n T ω := by
  rw [wholeCorrection, map_add, map_smul, map_smul, origin_projection, integrated_projection]

theorem projected_whole_integrable (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Integrable (fun ω => projection 2 (wholeCorrection g a n T ω)) gaussianProduct := by
  have hm := ((Lp.memLp (BrownianMassLimitIdentification.coordinateClass T)).integrable (by norm_num)).smul_const
    (spatialSlope g a n 0)
  have hi := hm.add ((integratedValue_integrable g a n T hT).smul (1/2 : ℝ))
  convert hi using 1
  funext ω
  exact wholeCorrection_projection g a n T ω

/-- The actual second-source projection of the whole source-valued time
correction has the previously identified clock mean. -/
theorem projected_whole_mean (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    (∫ ω, projection 2 (wholeCorrection g a n T ω) ∂gaussianProduct) = correctedMean g a n T := by
  simp_rw [wholeCorrection_projection]
  have hi : Integrable (fun ω => (1/2 : ℝ) • integratedValue g a n T ω) gaussianProduct :=
    (integratedValue_integrable g a n T hT).smul (1/2 : ℝ)
  have hs : (∫ ω, (1/2 : ℝ) • integratedValue g a n T ω ∂gaussianProduct) =
      (1/2 : ℝ) • ∫ ω, integratedValue g a n T ω ∂gaussianProduct := integral_smul _ _
  rw [integral_add
    (((Lp.memLp (BrownianMassLimitIdentification.coordinateClass T)).integrable (by norm_num)).smul_const
      (spatialSlope g a n 0))
    hi, integral_smul_const, hs]
  rfl

theorem projected_whole_mean_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ∫ ω, projection 2 (wholeCorrection g a n T ω) ∂gaussianProduct) atTop
      (𝓝 (IBMSchwartzPrimitiveLimit.terminalLimit g a T)) := by
  simp_rw [projected_whole_mean g a _ T hT]
  exact correctedMean_tendsto g a T hT

end OperatorDerivativeRewrite.Foundation.IBMSchwartzTimeProjection
