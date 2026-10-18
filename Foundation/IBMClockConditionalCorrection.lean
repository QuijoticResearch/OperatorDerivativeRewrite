import Foundation.IBMGeneralSchwartzFubini
import Foundation.IndependentInnovationConditioning

/-! Actual clock conditional expectation of the integrable joint correction.
Its L² closure does not assert L² convergence of the full joint correction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockConditionalCorrection
open InfiniteGaussian IBMSourceLaws IBMGeneralSchwartzFubini IBMSceneryAveragedCorrectionLimit

theorem integratedValue_measurable (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    StronglyMeasurable (integratedValue g a n T) := by
  unfold integratedValue
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact (timeValue_measurable g a n).stronglyMeasurable.integral_prod_left'

theorem conditional_eq_sourceMean (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    jointMeasure[integratedValue g a n T |
      MeasurableSpace.comap (Prod.snd : JointSample → SampleSpace) inferInstance] =ᵐ[jointMeasure]
      fun ω => sourceMean g a n T ω.2 := by
  have hi : IndepFun (Prod.snd : JointSample → SampleSpace) Prod.fst jointMeasure :=
    (indepFun_prod (μ := gaussianProduct) (ν := gaussianProduct) measurable_id measurable_id).symm
  have hF : StronglyMeasurable (fun p : SampleSpace × SampleSpace =>
      integratedValue g a n T (p.2,p.1)) :=
    (integratedValue_measurable g a n T).comp_measurable measurable_swap
  have he := IndependentInnovationConditioning.conditional_integral jointMeasure
    (Prod.snd : JointSample → SampleSpace) Prod.fst measurable_snd measurable_fst hi
    (fun p : SampleSpace × SampleSpace => integratedValue g a n T (p.2,p.1)) hF
    (integratedValue_integrable g a n T)
  have hm : jointMeasure.map (Prod.fst : JointSample → SampleSpace) = gaussianProduct :=
    (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).map_eq
  simpa only [hm, sourceMean, Prod.mk.eta] using he

theorem conditional_eq_averagedPath (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    jointMeasure[integratedValue g a n T |
      MeasurableSpace.comap (Prod.snd : JointSample → SampleSpace) inferInstance] =ᵐ[jointMeasure]
      fun ω => averagedPath g a n T ω.2 :=
  (conditional_eq_sourceMean g a n T).trans
    ((measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae
      (sourceMean_eq_ae g a n T))

def clockLift : GaussianL2 →ₗᵢ[ℝ] Lp ℝ 2 jointMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ (Prod.snd : JointSample → SampleSpace)
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct))

theorem clockLift_coeFn (f : GaussianL2) :
    clockLift f =ᵐ[jointMeasure] fun ω => f ω.2 :=
  Lp.coeFn_compMeasurePreserving f _

theorem liftedClass_coeFn (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    clockLift (averagedClass g a n T) =ᵐ[jointMeasure]
      jointMeasure[integratedValue g a n T |
        MeasurableSpace.comap (Prod.snd : JointSample → SampleSpace) inferInstance] := by
  have he : (fun ω : JointSample => averagedClass g a n T ω.2) =ᵐ[jointMeasure]
      (fun ω => averagedPath g a n T ω.2) :=
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae
      (averagedClass_coeFn g a n T)
  exact (clockLift_coeFn _).trans (he.trans (conditional_eq_averagedPath g a n T).symm)

theorem conditional_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (T : ℝ≥0) :
    MemLp (jointMeasure[integratedValue g a n T |
      MeasurableSpace.comap (Prod.snd : JointSample → SampleSpace) inferInstance]) 2 jointMeasure :=
  (Lp.memLp _).ae_eq (liftedClass_coeFn g a n T)

theorem conditional_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => (conditional_memLp g a n T).toLp _) atTop
      (𝓝 (clockLift (averagedLimit g a T))) := by
  have he (n : ℕ) : (conditional_memLp g a n T).toLp _ =
      clockLift (averagedClass g a n T) := by
    apply Lp.ext
    exact (conditional_memLp g a n T).coeFn_toLp.trans (liftedClass_coeFn g a n T).symm
  simp only [he]
  change Tendsto (clockLift ∘ (fun n => averagedClass g a n T)) atTop _
  exact clockLift.continuous.tendsto _ |>.comp (averagedClass_tendsto g a T)

end OperatorDerivativeRewrite.Foundation.IBMClockConditionalCorrection
