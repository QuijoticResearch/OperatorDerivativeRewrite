import Foundation.IBMQuarticJointRealization

/-! Recover the literal scalar curvature integral from the native
source-L2 Bochner integral, for every constructed clock path. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticScalarRecovery
open InfiniteGaussian IBMConstructedSources IBMQuarticSecondGeometry IBMQuarticTimeProjection

def spatialValue (n : ℕ) (p : ℝ × SampleSpace) : ℝ :=
  (1/2 : ℝ)*(IBMDyadicExtension.field n 0 p.2 p.1)^2*(IBMDyadicExtension.field n 1 p.2 p.1)^2 +
    (1/6 : ℝ)*(IBMDyadicExtension.field n 0 p.2 p.1)^3*IBMDyadicExtension.field n 2 p.2 p.1

theorem spatialValue_measurable (n : ℕ) : Measurable (spatialValue n) := by
  have hm := IBMDyadicExtension.field_jointly_measurable n
  exact (((hm 0).pow_const 2).const_mul (1/2 : ℝ)).mul ((hm 1).pow_const 2) |>.add
    ((((hm 0).pow_const 3).const_mul (1/6 : ℝ)).mul (hm 2))

def timeRepresentative (n : ℕ) (ωY : SampleSpace) (p : ℝ × SampleSpace) : ℝ :=
  spatialValue n (|clockPath ωY p.1.toNNReal|,p.2)

theorem timeRepresentative_measurable (n : ℕ) (ωY : SampleSpace) :
    Measurable (timeRepresentative n ωY) :=
  (spatialValue_measurable n).comp
    (((continuous_abs.comp ((clockPath ωY).continuous.comp continuous_real_toNNReal)).measurable.comp
      measurable_fst).prodMk measurable_snd)

def timeJoint (n : ℕ) (p : ℝ × (SampleSpace × SampleSpace)) : ℝ :=
  spatialValue n (|clockPath p.2.1 p.1.toNNReal|,p.2.2)

theorem timeJoint_measurable (n : ℕ) : Measurable (timeJoint n) :=
  (spatialValue_measurable n).comp
    ((continuous_abs.measurable.comp (BrownianClockWeightedEnergy.sigma_measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).prodMk
      (measurable_snd.comp measurable_snd))

def scalarTimeIntegral (n : ℕ) (T : ℝ≥0) (p : SampleSpace × SampleSpace) : ℝ :=
  ∫ s in 0..(T : ℝ), timeJoint n (s,p)

theorem scalarTimeIntegral_measurable (n : ℕ) (T : ℝ≥0) : Measurable (scalarTimeIntegral n T) := by
  unfold scalarTimeIntegral
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact (timeJoint_measurable n).stronglyMeasurable.integral_prod_left'.measurable

theorem timeRepresentative_integrable (n : ℕ) (ωY : SampleSpace) (T : ℝ≥0) :
    Integrable (timeRepresentative n ωY)
      ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod gaussianProduct) := by
  exact BochnerL2RepresentativeFubini.representative_integrable
    (fun s : ℝ => spatialQuartic n |clockPath ωY s.toNNReal|)
    (spatialQuartic_path_continuous n ωY).integrableOn_Ioc
    (timeRepresentative n ωY) (timeRepresentative_measurable n ωY).aestronglyMeasurable
    (Eventually.of_forall fun s => spatialQuartic_coeFn n |clockPath ωY s.toNNReal|)

/-- Actual time/source Fubini identifies the native Bochner integral with
the literal polynomial in the chosen simultaneous scenery fields. -/
theorem integratedCurvature_coeFn (n : ℕ) (ωY : SampleSpace) (T : ℝ≥0) :
    (∫ s in 0..(T : ℝ), spatialQuartic n |clockPath ωY s.toNNReal|) =ᵐ[gaussianProduct]
      fun ωX => scalarTimeIntegral n T (ωY,ωX) := by
  have he := BochnerL2RepresentativeFubini.integral_coeFn_ae
    (μ := volume.restrict (Set.Ioc 0 (T : ℝ))) (ν := gaussianProduct)
    (fun s : ℝ => spatialQuartic n |clockPath ωY s.toNNReal|)
    (spatialQuartic_path_continuous n ωY).integrableOn_Ioc
    (timeRepresentative n ωY) (timeRepresentative_measurable n ωY).aestronglyMeasurable
    (Eventually.of_forall fun s => spatialQuartic_coeFn n |clockPath ωY s.toNNReal|)
  simpa only [scalarTimeIntegral, timeJoint, timeRepresentative,
    intervalIntegral.integral_of_le T.coe_nonneg] using he

theorem scalarTimeIntegral_section_memLp (n : ℕ) (ωY : SampleSpace) (T : ℝ≥0) :
    MemLp (fun ωX => scalarTimeIntegral n T (ωY,ωX)) 2 gaussianProduct :=
  (Lp.memLp (∫ s in 0..(T : ℝ), spatialQuartic n |clockPath ωY s.toNNReal|)).ae_eq
    (integratedCurvature_coeFn n ωY T)

end OperatorDerivativeRewrite.Foundation.IBMQuarticScalarRecovery
