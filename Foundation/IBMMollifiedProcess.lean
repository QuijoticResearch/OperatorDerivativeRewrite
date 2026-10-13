import Foundation.IBMMollifiedMeasurability

/-! Random-time mollified IBM composition from supplied continuous scenery
and clock coordinate families on their independent product factors. -/
noncomputable section
open MeasureTheory
open scoped Convolution NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMMollifiedProcess
open InfiniteGaussian IBMSourceLaws IBMMollifiedScenery IBMMollifiedMeasurability

variable (ρ : ℝ → ℝ) (S : ℝ → SampleSpace → ℝ)
  (C : ℝ≥0 → SampleSpace → ℝ)

/-- The actual pointwise mollified random-time composition on the joint
source space, conditional on supplied continuous source versions. -/
def Z (t : ℝ≥0) (ω : JointSample) : ℝ :=
  U ρ (fun z => S z ω.1) |C t ω.2|

theorem Z_measurable (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r))
    (hmC : ∀ t, Measurable (C t)) (t : ℝ≥0) :
    Measurable (Z ρ S C t) := by
  have hU := U_joint_measurable ρ S hρs hρ hS hmS
  have harg : Measurable (fun ω : JointSample => (|C t ω.2|, ω.1)) :=
    (((continuous_abs.measurable).comp ((hmC t).comp measurable_snd)).prodMk measurable_fst)
  exact hU.comp harg

theorem Z_path_continuous (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hC : ∀ ω, Continuous (fun t => C t ω)) (ω : JointSample) :
    Continuous (fun t => Z ρ S C t ω) := by
  have hU : Continuous (U ρ (fun z => S z ω.1)) :=
    hρs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      hρ.continuous (hS ω.1).locallyIntegrable
  exact hU.comp (continuous_abs.comp (hC ω.2))

theorem Z_joint_measurable (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (hmC : ∀ t, Measurable (C t)) :
    Measurable (fun p : ℝ≥0 × JointSample => Z ρ S C p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (Z_path_continuous ρ S C hρs hρ hS hC)
    (Z_measurable ρ S C hρs hρ hS hmS hmC)

/-- Package the mollified random-time process as a continuous path for each
joint source sample. -/
def path (hρs : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (ω : JointSample) : C(ℝ≥0, ℝ) :=
  ⟨fun t => Z ρ S C t ω, Z_path_continuous ρ S C hρs hρ hS hC ω⟩

theorem path_measurable (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (hmC : ∀ t, Measurable (C t)) :
    Measurable (path ρ S C hρs hρ hS hC) :=
  ContinuousMap.measurable_iff_eval.mpr (Z_measurable ρ S C hρs hρ hS hmS hmC)

end OperatorDerivativeRewrite.Foundation.IBMMollifiedProcess
