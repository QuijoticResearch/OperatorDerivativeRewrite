import Foundation.IBMSchwartzTimeProjection

/-! Recover the literal nonlinear Schwartz curvature integral from the native
source-L2 Bochner integral, for every constructed clock path. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzScalarRecovery
open InfiniteGaussian IBMConstructedSources IBMSchwartzSecondProjection IBMSchwartzTimeProjection
open IBMCorrectionStein

variable (g : SchwartzMap ℝ ℝ) (a : ℝ)

def spatialValue (n : ℕ) (p : ℝ × SampleSpace) : ℝ :=
  shiftedJet g a 2 (IBMDyadicExtension.field n 0 p.2 p.1)*(IBMDyadicExtension.field n 1 p.2 p.1)^2 +
    shiftedJet g a 1 (IBMDyadicExtension.field n 0 p.2 p.1)*IBMDyadicExtension.field n 2 p.2 p.1

theorem spatialValue_measurable (n : ℕ) : Measurable (spatialValue g a n) := by
  have hm := IBMDyadicExtension.field_jointly_measurable n
  exact (((shiftedJet_smooth g a 2).continuous.measurable.comp (hm 0)).mul
    ((hm 1).pow_const 2)).add
    (((shiftedJet_smooth g a 1).continuous.measurable.comp (hm 0)).mul (hm 2))

def timeRepresentative (n : ℕ) (ωY : SampleSpace) (p : ℝ × SampleSpace) : ℝ :=
  spatialValue g a n (|clockPath ωY p.1.toNNReal|,p.2)

theorem timeRepresentative_measurable (n : ℕ) (ωY : SampleSpace) :
    Measurable (timeRepresentative g a n ωY) :=
  (spatialValue_measurable g a n).comp
    (((continuous_abs.comp ((clockPath ωY).continuous.comp continuous_real_toNNReal)).measurable.comp
      measurable_fst).prodMk measurable_snd)

def timeJoint (n : ℕ) (p : ℝ × (SampleSpace × SampleSpace)) : ℝ :=
  spatialValue g a n (|clockPath p.2.1 p.1.toNNReal|,p.2.2)

theorem timeJoint_measurable (n : ℕ) : Measurable (timeJoint g a n) :=
  (spatialValue_measurable g a n).comp
    ((continuous_abs.measurable.comp (BrownianClockWeightedEnergy.sigma_measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).prodMk
      (measurable_snd.comp measurable_snd))

def scalarTimeIntegral (n : ℕ) (T : ℝ≥0) (p : SampleSpace × SampleSpace) : ℝ :=
  ∫ s in 0..(T : ℝ), timeJoint g a n (s,p)

theorem scalarTimeIntegral_measurable (n : ℕ) (T : ℝ≥0) : Measurable (scalarTimeIntegral g a n T) := by
  unfold scalarTimeIntegral
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact (timeJoint_measurable g a n).stronglyMeasurable.integral_prod_left'.measurable

theorem timeRepresentative_integrable (n : ℕ) (ωY : SampleSpace) (T : ℝ≥0) :
    Integrable (timeRepresentative g a n ωY)
      ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod gaussianProduct) := by
  exact BochnerL2RepresentativeFubini.representative_integrable
    (fun s : ℝ => mollifiedClass g a n |clockPath ωY s.toNNReal|)
    (mollified_path_continuous g a n ωY).integrableOn_Ioc
    (timeRepresentative g a n ωY) (timeRepresentative_measurable g a n ωY).aestronglyMeasurable
    (Eventually.of_forall fun s => mollifiedClass_coeFn g a n |clockPath ωY s.toNNReal|)

/-- Actual time/source Fubini identifies the native Bochner integral with
the literal Schwartz curvature in the chosen simultaneous scenery fields. -/
theorem integratedCurvature_coeFn (n : ℕ) (ωY : SampleSpace) (T : ℝ≥0) :
    (∫ s in 0..(T : ℝ), mollifiedClass g a n |clockPath ωY s.toNNReal|) =ᵐ[gaussianProduct]
      fun ωX => scalarTimeIntegral g a n T (ωY,ωX) := by
  have he := BochnerL2RepresentativeFubini.integral_coeFn_ae
    (μ := volume.restrict (Set.Ioc 0 (T : ℝ))) (ν := gaussianProduct)
    (fun s : ℝ => mollifiedClass g a n |clockPath ωY s.toNNReal|)
    (mollified_path_continuous g a n ωY).integrableOn_Ioc
    (timeRepresentative g a n ωY) (timeRepresentative_measurable g a n ωY).aestronglyMeasurable
    (Eventually.of_forall fun s => mollifiedClass_coeFn g a n |clockPath ωY s.toNNReal|)
  simpa only [scalarTimeIntegral, timeJoint, timeRepresentative,
    intervalIntegral.integral_of_le T.coe_nonneg] using he

theorem scalarTimeIntegral_section_memLp (n : ℕ) (ωY : SampleSpace) (T : ℝ≥0) :
    MemLp (fun ωX => scalarTimeIntegral g a n T (ωY,ωX)) 2 gaussianProduct :=
  (Lp.memLp (∫ s in 0..(T : ℝ), mollifiedClass g a n |clockPath ωY s.toNNReal|)).ae_eq
    (integratedCurvature_coeFn g a n ωY T)


theorem originClass_coeFn (n : ℕ) :
    originClass g a n =ᵐ[gaussianProduct] fun ω =>
      shiftedJet g a 1 (IBMDyadicExtension.field n 0 ω 0)*IBMDyadicExtension.field n 1 ω 0 := by
  filter_upwards [weightedClass_coeFn g a (IBMGaussianSteinMoments.tripleCoefficient n 0 0) 1
      (firstChaosEmbedding (IBMGaussianSteinMoments.tripleCoefficient n 0 1)),
    IBMDyadicExtension.field_coordinate_ae n 0 0, IBMDyadicExtension.field_coordinate_ae n 1 0]
    with ω hc h0 h1
  rw [IBMGaussianSteinMoments.gaussianTriple_eq_firstChaos] at h0 h1
  exact hc.trans (by rw [h0, h1])

/-- The source-valued whole correction is the actual scalar origin plus
curvature-time integral, for every constructed clock representative. -/
theorem wholeCorrection_coeFn (n : ℕ) (ωY : SampleSpace) (T : ℝ≥0) :
    wholeCorrection g a n T ωY =ᵐ[gaussianProduct] fun ωX =>
      BrownianMassLimitIdentification.coordinateClass T ωY *
        (shiftedJet g a 1 (IBMDyadicExtension.field n 0 ωX 0)*IBMDyadicExtension.field n 1 ωX 0) +
        (1/2 : ℝ)*scalarTimeIntegral g a n T (ωY,ωX) := by
  filter_upwards [Lp.coeFn_add
      (BrownianMassLimitIdentification.coordinateClass T ωY • originClass g a n)
      ((1/2 : ℝ) • ∫ s in 0..(T : ℝ), mollifiedClass g a n |clockPath ωY s.toNNReal|),
    Lp.coeFn_smul (BrownianMassLimitIdentification.coordinateClass T ωY) (originClass g a n),
    Lp.coeFn_smul (1/2 : ℝ) (∫ s in 0..(T : ℝ), mollifiedClass g a n |clockPath ωY s.toNNReal|),
    integratedCurvature_coeFn g a n ωY T, originClass_coeFn g a n] with ωX ha hm hh hi ho
  rw [wholeCorrection, ha, Pi.add_apply, hm, hh, Pi.smul_apply, Pi.smul_apply, hi, ho]
  simp only [smul_eq_mul]

end OperatorDerivativeRewrite.Foundation.IBMSchwartzScalarRecovery
