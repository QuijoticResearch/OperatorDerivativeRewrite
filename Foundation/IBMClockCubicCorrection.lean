import Foundation.IBMSceneryCubicProjection

/-! Actual cubic correction along the constructed reflected Brownian clock.
Section L2 and source-domain results are unconditional. The Hilbert-valued
time interchange below explicitly retains its integrability hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.IBMClockCubicCorrection
open InfiniteGaussian IBMConstructedSources IBMSceneryCubicProjection IBMCubicFirstChaos
open IBMGaussianSteinMoments
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable
attribute [local irreducible] IBMConstructedSources.mollifiedValue
attribute [local irreducible] IBMDyadicExtension.field

def value (n : ℕ) (t : ℝ≥0) (ω : IBMSourceLaws.JointSample) : ℝ :=
  mollifiedValue n 0 t ω*(mollifiedValue n 1 t ω)^2 +
    (1/2 : ℝ)*(mollifiedValue n 0 t ω)^2*mollifiedValue n 2 t ω

theorem value_jointly_measurable (n : ℕ) :
    Measurable (fun p : ℝ≥0 × IBMSourceLaws.JointSample => value n p.1 p.2) := by
  exact ((mollifiedValue_jointly_measurable n 0).mul
    ((mollifiedValue_jointly_measurable n 1).pow_const 2)).add
      ((measurable_const.mul ((mollifiedValue_jointly_measurable n 0).pow_const 2)).mul
        (mollifiedValue_jointly_measurable n 2))

theorem value_continuous (n : ℕ) (ω : IBMSourceLaws.JointSample) :
    Continuous (fun t => value n t ω) := by
  exact ((mollifiedValue_continuous n 0 ω).mul
    ((mollifiedValue_continuous n 1 ω).pow 2)).add
      ((continuous_const.mul ((mollifiedValue_continuous n 0 ω).pow 2)).mul
        (mollifiedValue_continuous n 2 ω))

theorem value_time_integrable (n : ℕ) (ω : IBMSourceLaws.JointSample) (T : ℝ) :
    IntegrableOn (fun s : ℝ => value n (Real.toNNReal s) ω) (Set.Icc 0 T) volume :=
  ((value_continuous n ω).comp continuous_real_toNNReal).integrableOn_Icc

def sectionClass (n : ℕ) (t : ℝ≥0) (ωY : SampleSpace) : GaussianL2 :=
  spatialCorrection n |clockPath ωY t|

theorem sectionClass_coeFn (n : ℕ) (t : ℝ≥0) (ωY : SampleSpace) :
    sectionClass n t ωY =ᵐ[gaussianProduct] fun ωX => value n t (ωX, ωY) := by
  filter_upwards [spatialCorrection_coeFn n |clockPath ωY t|] with ωX h
  simpa only [sectionClass, value, IBMConstructedSources.mollifiedValue,
    IBMContinuousComposition.value, IBMContinuousComposition.path, IBMDyadicExtension.path,
    ContinuousMap.coe_mk] using h

theorem section_memLp (n : ℕ) (t : ℝ≥0) (ωY : SampleSpace) :
    MemLp (fun ωX => value n t (ωX, ωY)) 2 gaussianProduct :=
  (Lp.memLp (sectionClass n t ωY)).ae_eq (sectionClass_coeFn n t ωY)

theorem section_closedDerivative_graph (n : ℕ) (t : ℝ≥0) (ωY : SampleSpace) :
    (sectionClass n t ωY,
      polynomialDerivative (correctionCore
        (tripleCoefficient n |clockPath ωY t| 0)
        (tripleCoefficient n |clockPath ωY t| 1)
        (tripleCoefficient n |clockPath ωY t| 2))) ∈ closedCylindricalDerivative.graph :=
  correction_closedDerivative_graph _ _ _

theorem section_projection (n : ℕ) (t : ℝ≥0) (ωY : SampleSpace) :
    GaussianPastFirstChaos.projection (sectionClass n t ωY) =
      GaussianHilbertProcess.isonormalEmbedding FractionalSpectralKernel.SpectralSpace
        (sourceVector n |clockPath ωY t|) :=
  projection_eq_sourceEmbedding n |clockPath ωY t|

/-- This is projection in the scenery factor at a fixed actual clock path.
The explicit Bochner-L2 assumption is not yet a joint clock moment estimate. -/
theorem time_integrated_projection (n : ℕ) (ωY : SampleSpace) (T : ℝ)
    (hi : Integrable (fun s : ℝ => sectionClass n (Real.toNNReal s) ωY)
      (volume.restrict (Set.Icc 0 T))) :
    GaussianPastFirstChaos.projection
        (∫ s in Set.Icc 0 T, sectionClass n (Real.toNNReal s) ωY) =
      ∫ s in Set.Icc 0 T,
        GaussianHilbertProcess.isonormalEmbedding FractionalSpectralKernel.SpectralSpace
          (sourceVector n |clockPath ωY (Real.toNNReal s)|) := by
  rw [← GaussianPastFirstChaos.projection.integral_comp_comm hi]
  exact integral_congr_ae (Filter.Eventually.of_forall fun s => section_projection n _ ωY)

theorem time_integrated_source_vector (n : ℕ) (ωY : SampleSpace) (T : ℝ)
    (hi : Integrable (fun s : ℝ => sectionClass n (Real.toNNReal s) ωY)
      (volume.restrict (Set.Icc 0 T))) :
    GaussianPastFirstChaos.projection
        (∫ s in Set.Icc 0 T, sectionClass n (Real.toNNReal s) ωY) =
      GaussianHilbertProcess.isonormalEmbedding FractionalSpectralKernel.SpectralSpace
        (∫ s in Set.Icc 0 T, sourceVector n |clockPath ωY (Real.toNNReal s)|) := by
  rw [time_integrated_projection n ωY T hi]
  exact (GaussianHilbertProcess.isonormalEmbedding
    FractionalSpectralKernel.SpectralSpace).integral_comp_comm _

end OperatorDerivativeRewrite.Foundation.IBMClockCubicCorrection
