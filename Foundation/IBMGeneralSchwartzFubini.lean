import Foundation.IBMSceneryAveragedCorrectionLimit
import Foundation.IBMFiniteHorizonEvaluation

/-! Actual joint Schwartz correction integrability and time/scenery Fubini.
The random clock mean is identified on its genuine source integral domain. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMGeneralSchwartzFubini
open InfiniteGaussian IBMConstructedSources IBMSourceLaws IBMCorrectionStein
open IBMFiniteHorizonEvaluation IBMGaussianSteinMoments IBMSceneryAveragedCorrectionLimit
attribute [local irreducible] mollifiedValue IBMDyadicExtension.field

def value (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (t : ℝ≥0) (ω : JointSample) : ℝ :=
  shiftedJet g a 2 (mollifiedValue n 0 t ω) * (mollifiedValue n 1 t ω)^2 +
    shiftedJet g a 1 (mollifiedValue n 0 t ω) * mollifiedValue n 2 t ω

def timeValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (p : ℝ × JointSample) : ℝ :=
  value g a n p.1.toNNReal p.2

theorem timeValue_measurable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    Measurable (timeValue g a n) := by
  have h₁ := (shiftedJet_smooth g a 1).continuous.measurable
  have h₂ := (shiftedJet_smooth g a 2).continuous.measurable
  exact ((h₂.comp (horizonValue_measurable n 0)).mul
    ((horizonValue_measurable n 1).pow_const 2)).add
      ((h₁.comp (horizonValue_measurable n 0)).mul (horizonValue_measurable n 2))

theorem timeValue_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Integrable (timeValue g a n) ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod jointMeasure) := by
  exact secondCoefficient_horizon_integrable (jet g 1) (jet g 2)
    (jet g 1).continuous (jet g 2).continuous
    (SchwartzMap.seminorm ℝ 0 0 (jet g 1)) (SchwartzMap.seminorm ℝ 0 0 (jet g 2)) a T
    (fun x => by simpa only [Real.norm_eq_abs] using IBMBoundaryResidualLimit.schwartz_bound (jet g 1) x)
    (fun x => by simpa only [Real.norm_eq_abs] using IBMBoundaryResidualLimit.schwartz_bound (jet g 2) x) n

def integratedValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0)
    (ω : JointSample) : ℝ := ∫ t in 0..(T : ℝ), value g a n t.toNNReal ω

theorem integratedValue_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    Integrable (integratedValue g a n T) jointMeasure := by
  unfold integratedValue
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  simpa only [timeValue] using
    (timeValue_integrable g a n T).integral_prod_right

theorem section_mean (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (t : ℝ≥0)
    (ωY : SampleSpace) :
    (∫ ωX, value g a n t (ωX,ωY) ∂gaussianProduct) =
      correction g a (tripleCoefficient n |clockPath ωY t| 0)
        (tripleCoefficient n |clockPath ωY t| 1) (tripleCoefficient n |clockPath ωY t| 2) := by
  unfold correction
  apply integral_congr_ae
  filter_upwards [IBMDyadicExtension.field_coordinate_ae n 0 |clockPath ωY t|,
    IBMDyadicExtension.field_coordinate_ae n 1 |clockPath ωY t|,
    IBMDyadicExtension.field_coordinate_ae n 2 |clockPath ωY t|] with ωX h₀ h₁ h₂
  simpa only [value, mollifiedValue, IBMContinuousComposition.value,
    IBMContinuousComposition.path, IBMDyadicExtension.path, ContinuousMap.coe_mk,
    h₀, h₁, h₂, gaussianTriple_eq_firstChaos]

/-- Product associativity supplies the actual time/source slice domain for
almost every clock sample; no sectionwise integrability is assumed. -/
theorem source_time_integrable_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ ωY ∂gaussianProduct, Integrable
      (fun p : ℝ × SampleSpace => timeValue g a n (p.1,(p.2,ωY)))
      ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod gaussianProduct) := by
  have hi := (measurePreserving_prodAssoc (volume.restrict (Set.Ioc 0 (T : ℝ)))
    gaussianProduct gaussianProduct).integrable_comp_of_integrable (timeValue_integrable g a n T)
  exact hi.prod_left_ae

def sourceMean (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) (ωY : SampleSpace) : ℝ :=
  ∫ ωX, integratedValue g a n T (ωX,ωY) ∂gaussianProduct

theorem sourceMean_eq_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    sourceMean g a n T =ᵐ[gaussianProduct] averagedPath g a n T := by
  filter_upwards [source_time_integrable_ae g a n T] with ωY hi
  unfold sourceMean integratedValue averagedPath
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  have hi' : Integrable (fun p : SampleSpace × ℝ => value g a n p.2.toNNReal (p.1,ωY))
      (gaussianProduct.prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := by
    convert hi.swap using 1
    funext p
    rfl
  rw [integral_integral_swap (μ := gaussianProduct)
    (ν := volume.restrict (Set.Ioc 0 (T : ℝ)))
    (f := fun (ωX : SampleSpace) (t : ℝ) => value g a n t.toNNReal (ωX,ωY)) hi']
  apply integral_congr_ae
  exact Eventually.of_forall fun t => section_mean g a n t.toNNReal ωY

theorem sourceMean_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp (sourceMean g a n T) 2 gaussianProduct :=
  (averagedPath_memLp g a n T).ae_eq (sourceMean_eq_ae g a n T).symm

theorem sourceMean_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => (sourceMean_memLp g a n T).toLp _) atTop (𝓝 (averagedLimit g a T)) := by
  have he (n : ℕ) : (sourceMean_memLp g a n T).toLp _ = averagedClass g a n T := by
    apply Lp.ext
    exact (sourceMean_memLp g a n T).coeFn_toLp.trans
      ((sourceMean_eq_ae g a n T).trans (averagedClass_coeFn g a n T).symm)
  simpa only [he] using averagedClass_tendsto g a T

end OperatorDerivativeRewrite.Foundation.IBMGeneralSchwartzFubini
