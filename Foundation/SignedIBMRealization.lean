import Foundation.ContinuousRandomTimeComposition
import Foundation.IBMConstructedSources

/-! Actual signed-clock iterated Brownian motion, kept distinct from the absolute-clock model. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.SignedIBMRealization
set_option backward.isDefEq.respectTransparency false
open InfiniteGaussian IBMSourceLaws IBMConstructedSources

def path : JointSample → C(ℝ≥0, ℝ) :=
  ContinuousRandomTimeComposition.path sceneryPath clockPath

def value : ℝ≥0 → JointSample → ℝ :=
  ContinuousRandomTimeComposition.value sceneryPath clockPath

theorem value_eq (t : ℝ≥0) (ω : JointSample) :
    value t ω = sceneryPath ω.1 (clockPath ω.2 t) := rfl

theorem path_measurable : Measurable path :=
  ContinuousRandomTimeComposition.path_measurable _ _ sceneryPath_measurable clockPath_measurable

theorem value_continuous (ω : JointSample) : Continuous (fun t => value t ω) :=
  ContinuousRandomTimeComposition.value_continuous _ _ ω

theorem value_jointly_measurable : Measurable (fun p : ℝ≥0 × JointSample => value p.1 p.2) :=
  ContinuousRandomTimeComposition.jointly_measurable _ _ sceneryPath_measurable clockPath_measurable

theorem independent_sources :
    IndepFun (fun ω : JointSample => sceneryPath ω.1) (fun ω : JointSample => clockPath ω.2)
      jointMeasure := sources_independent

theorem conditional_gaussian (ω : SampleSpace) :
    IsGaussianProcess (fun t ξ => value t (ξ,ω)) gaussianProduct :=
  scenery_isGaussianProcess.comp_right (fun t => clockPath ω t)

theorem conditional_covariance (s t : ℝ≥0) (ω : SampleSpace) :
    cov[(fun ξ => value s (ξ,ω)), (fun ξ => value t (ξ,ω)); gaussianProduct] =
      (|clockPath ω s|+|clockPath ω t|-|clockPath ω t-clockPath ω s|)/2 := by
  change cov[(fun ξ => sceneryPath ξ (clockPath ω s)),
    (fun ξ => sceneryPath ξ (clockPath ω t)); gaussianProduct] = _
  exact sceneryPath_covariance _ _

theorem conditional_finite_dim_gaussian (ω : SampleSpace) (I : Finset ℝ≥0) :
    HasGaussianLaw (fun ξ => I.restrict (fun t => value t (ξ,ω))) gaussianProduct :=
  (conditional_gaussian ω).hasGaussianLaw I

theorem opposite_outer_times_covariance :
    cov[(fun ω => sceneryPath ω (1:ℝ)),(fun ω => sceneryPath ω (-1:ℝ)); gaussianProduct] = 0 := by
  norm_num [sceneryPath_covariance]

theorem reflected_outer_times_covariance :
    cov[(fun ω => sceneryPath ω |(1:ℝ)|),
      (fun ω => sceneryPath ω |(-1:ℝ)|); gaussianProduct] = 1 := by
  norm_num [sceneryPath_covariance]

end OperatorDerivativeRewrite.Foundation.SignedIBMRealization
