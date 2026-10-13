import Foundation.FractionalSpectralGeometry
import Foundation.GaussianTimeProcess
import Mathlib.Probability.Independence.Basic

/-! Actual independent two-sided Gaussian scenery and Brownian clock laws.
These are measurable coordinate families, not yet continuous sample versions;
random-time IBM evaluation is deliberately left to that separate construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSourceLaws
open InfiniteGaussian GaussianHilbertProcess FractionalSpectralKernel
attribute [local instance] spectralSpace_secondCountable

abbrev JointSample := SampleSpace × SampleSpace

def jointMeasure : Measure JointSample := gaussianProduct.prod gaussianProduct

instance joint_probability : IsProbabilityMeasure jointMeasure := by
  unfold jointMeasure
  infer_instance

def sceneryBase (t : ℝ) : SampleSpace → ℝ :=
  isonormal SpectralSpace (FractionalSpectralGeometry.normalized (1/2) (by norm_num) (by norm_num) t)

def scenery (t : ℝ) (ω : JointSample) : ℝ := sceneryBase t ω.1

def clock (t : ℝ≥0) (ω : JointSample) : ℝ := GaussianTimeProcess.process t ω.2

theorem sceneryBase_measurable (t : ℝ) : Measurable (sceneryBase t) :=
  isonormal_measurable _

theorem sceneryBase_isGaussianProcess : IsGaussianProcess sceneryBase gaussianProduct :=
  isonormal_isGaussianProcess.comp_right _

theorem sceneryBase_covariance (s t : ℝ) :
    cov[sceneryBase s, sceneryBase t; gaussianProduct] = (|s|+|t|-|t-s|)/2 := by
  rw [show cov[sceneryBase s, sceneryBase t; gaussianProduct] =
    inner ℝ (FractionalSpectralGeometry.normalized (1/2) (by norm_num) (by norm_num) s)
      (FractionalSpectralGeometry.normalized (1/2) (by norm_num) (by norm_num) t) from
        isonormal_covariance _ _]
  rw [FractionalSpectralGeometry.normalized_inner]
  norm_num [FractionalSpectralGeometry.covariance]

theorem scenery_measurable (t : ℝ) : Measurable (scenery t) :=
  (sceneryBase_measurable t).comp measurable_fst

theorem clock_measurable (t : ℝ≥0) : Measurable (clock t) :=
  (GaussianTimeProcess.process_stronglyMeasurable t).measurable.comp measurable_snd

/-- Independence of entire coordinate families, not merely pairwise covariance zero. -/
theorem scenery_clock_independent :
    IndepFun (fun ω : JointSample => fun t : ℝ => scenery t ω)
      (fun ω : JointSample => fun t : ℝ≥0 => clock t ω) jointMeasure := by
  exact indepFun_prod (Measurable.of_eval sceneryBase_measurable)
    (Measurable.of_eval (fun t => (GaussianTimeProcess.process_stronglyMeasurable t).measurable))

theorem clock_isPreBrownian : IsPreBrownianReal clock jointMeasure where
  hasLaw I := (GaussianTimeProcess.process_isPreBrownian.hasLaw I).comp
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).hasLaw

/-- Every finite scenery law is the law of the actual spectral two-sided realization. -/
theorem scenery_finite_law (I : Finset ℝ) :
    HasLaw (fun ω : JointSample => I.restrict (scenery · ω))
      (gaussianProduct.map (fun ω : SampleSpace => I.restrict (sceneryBase · ω))) jointMeasure := by
  have hm : Measurable (fun ω : SampleSpace => I.restrict (sceneryBase · ω)) :=
    Measurable.of_eval (fun i => sceneryBase_measurable i)
  have hl : HasLaw (fun ω : SampleSpace => I.restrict (sceneryBase · ω))
      (gaussianProduct.map (fun ω : SampleSpace => I.restrict (sceneryBase · ω))) gaussianProduct :=
    ⟨hm.aemeasurable, rfl⟩
  exact hl.comp (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).hasLaw

theorem scenery_isGaussianProcess : IsGaussianProcess scenery jointMeasure where
  hasGaussianLaw I := by
    haveI := (sceneryBase_isGaussianProcess.hasGaussianLaw I).isGaussian_map
    exact (scenery_finite_law I).hasGaussianLaw

theorem scenery_covariance (s t : ℝ) :
    cov[scenery s, scenery t; jointMeasure] = (|s|+|t|-|t-s|)/2 := by
  have hm : jointMeasure.map Prod.fst = gaussianProduct :=
    (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).map_eq
  have hs : AEStronglyMeasurable (sceneryBase s) (jointMeasure.map Prod.fst) := by
    rw [hm]
    exact (sceneryBase_measurable s).aestronglyMeasurable
  have ht : AEStronglyMeasurable (sceneryBase t) (jointMeasure.map Prod.fst) := by
    rw [hm]
    exact (sceneryBase_measurable t).aestronglyMeasurable
  have hc := covariance_map_fun hs ht (measurable_fst.aemeasurable (μ := jointMeasure))
  rw [hm] at hc
  exact hc.symm.trans (sceneryBase_covariance s t)

theorem scenery_law (t : ℝ) :
    HasLaw (scenery t) (gaussianReal 0 ⟨|t|, abs_nonneg t⟩) jointMeasure := by
  have hl : HasLaw (sceneryBase t) (gaussianReal 0 ⟨|t|, abs_nonneg t⟩) gaussianProduct := by
    refine ⟨(sceneryBase_measurable t).aemeasurable, ?_⟩
    unfold sceneryBase
    rw [isonormal_law]
    apply congrArg (gaussianReal 0)
    apply NNReal.eq
    simp only [NNReal.coe_mk]
    norm_num [FractionalSpectralGeometry.normalized_norm_sq] <;> rfl
  exact hl.comp (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).hasLaw

theorem scenery_centered (t : ℝ) : ∫ ω, scenery t ω ∂jointMeasure = 0 := by
  rw [(scenery_law t).integral_eq]
  exact integral_id_gaussianReal

/-- Both half-lines have Brownian finite-dimensional laws. -/
theorem scenery_positive_isPreBrownian :
    IsPreBrownianReal (fun t : ℝ≥0 => scenery (t : ℝ)) jointMeasure := by
  apply (scenery_isGaussianProcess.comp_right (fun t : ℝ≥0 => (t : ℝ))).isPreBrownianReal_of_covariance
  · exact fun t => scenery_centered t
  · intro s t hst
    change cov[scenery (s : ℝ), scenery (t : ℝ); jointMeasure] = (s : ℝ)
    rw [scenery_covariance, abs_of_nonneg s.coe_nonneg, abs_of_nonneg t.coe_nonneg,
      abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))]
    ring

theorem scenery_negative_isPreBrownian :
    IsPreBrownianReal (fun t : ℝ≥0 => scenery (-(t : ℝ))) jointMeasure := by
  apply (scenery_isGaussianProcess.comp_right (fun t : ℝ≥0 => -(t : ℝ))).isPreBrownianReal_of_covariance
  · exact fun t => scenery_centered (-(t : ℝ))
  · intro s t hst
    change cov[scenery (-(s : ℝ)), scenery (-(t : ℝ)); jointMeasure] = (s : ℝ)
    rw [scenery_covariance, abs_neg, abs_neg, abs_of_nonneg s.coe_nonneg,
      abs_of_nonneg t.coe_nonneg]
    rw [show -(t : ℝ) - -(s : ℝ) = -((t : ℝ)-s) by ring, abs_neg,
      abs_of_nonneg (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))]
    ring

/-- Entire positive and negative scenery halves are independent Gaussian families. -/
theorem scenery_halves_independent :
    IndepFun (fun ω : JointSample => fun t : ℝ≥0 => scenery (t : ℝ) ω)
      (fun ω : JointSample => fun t : ℝ≥0 => scenery (-(t : ℝ)) ω) jointMeasure := by
  have hg : IsGaussianProcess
      (Sum.elim (fun t : ℝ≥0 => scenery (t : ℝ))
        (fun t : ℝ≥0 => scenery (-(t : ℝ)))) jointMeasure := by
    convert scenery_isGaussianProcess.comp_right (Sum.elim (fun t : ℝ≥0 => (t : ℝ))
      (fun t : ℝ≥0 => -(t : ℝ))) using 1
    ext z
    cases z <;> rfl
  apply hg.indepFun_of_covariance_eq_zero
  · exact fun t => (scenery_measurable t).aemeasurable
  · exact fun t => (scenery_measurable (-(t : ℝ))).aemeasurable
  · intro s t
    change cov[scenery (s : ℝ), scenery (-(t : ℝ)); jointMeasure] = 0
    rw [scenery_covariance, abs_of_nonneg s.coe_nonneg, abs_neg,
      abs_of_nonneg t.coe_nonneg, abs_of_nonpos (by linarith [s.coe_nonneg, t.coe_nonneg])]
    ring

end OperatorDerivativeRewrite.Foundation.IBMSourceLaws
