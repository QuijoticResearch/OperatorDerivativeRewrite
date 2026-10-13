import Foundation.IBMMollifiedScenery
import Foundation.IBMModificationBridge
import Mathlib.MeasureTheory.Integral.Prod

/-! Measurability of spatially mollified scenery under explicit continuous
and measurable source-coordinate hypotheses. -/
noncomputable section
open MeasureTheory
open scoped Convolution
namespace OperatorDerivativeRewrite.Foundation.IBMMollifiedMeasurability
open InfiniteGaussian IBMMollifiedScenery

variable (ρ : ℝ → ℝ) (S : ℝ → SampleSpace → ℝ)

private theorem S_joint_measurable
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r)) :
    Measurable (fun p : ℝ × SampleSpace => S p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable hS hmS

/-- Convolution by any continuous deterministic kernel preserves
deterministic-space-coordinate measurability of a continuous random path. -/
theorem convolution_measurable (hρ : Continuous ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r)) (r : ℝ) :
    Measurable (fun ω => (ρ ⋆ (fun z => S z ω)) r) := by
  have hI : StronglyMeasurable (fun p : SampleSpace × ℝ =>
      ρ p.2 * S (r - p.2) p.1) := by
    have hρm : Measurable (fun p : SampleSpace × ℝ => ρ p.2) :=
      hρ.measurable.comp measurable_snd
    have hSm : Measurable (fun p : SampleSpace × ℝ => S (r - p.2) p.1) :=
      (S_joint_measurable S hS hmS).comp
        ((measurable_const.sub measurable_snd).prodMk measurable_fst)
    exact (hρm.mul hSm).stronglyMeasurable
  have hm := hI.integral_prod_right' (ν := (volume : Measure ℝ))
  convert hm.measurable using 1
  ext ω
  rfl

/-- Each spatially mollified scenery coordinate is a genuine measurable
random variable on the scenery factor. -/
theorem U_measurable (hρ : ContDiff ℝ 2 ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r)) (r : ℝ) :
    Measurable (fun ω => U ρ (fun z => S z ω) r) :=
  convolution_measurable ρ S hρ.continuous hS hmS r

theorem V_measurable (hρ : ContDiff ℝ 2 ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r)) (r : ℝ) :
    Measurable (fun ω => V ρ (fun z => S z ω) r) := by
  have hρ' : Continuous (deriv ρ) := (hρ.deriv' (n := 1)).continuous
  exact convolution_measurable (deriv ρ) S hρ' hS hmS r

theorem W_measurable (hρ : ContDiff ℝ 2 ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r)) (r : ℝ) :
    Measurable (fun ω => W ρ (fun z => S z ω) r) := by
  have hρ' : ContDiff ℝ 1 (deriv ρ) := hρ.deriv' (n := 1)
  have hρ'' : Continuous (deriv (deriv ρ)) := (hρ'.deriv' (n := 0)).continuous
  exact convolution_measurable (deriv (deriv ρ)) S hρ'' hS hmS r

/-- Joint spatial-parameter/sample measurability for a compactly supported
continuous convolution kernel. -/
theorem convolution_joint_measurable (hρs : HasCompactSupport ρ)
    (hρ : Continuous ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r)) :
    Measurable (fun p : ℝ × SampleSpace =>
      (ρ ⋆ (fun z => S z p.2)) p.1) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun ω => hρs.continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) hρ (hS ω).locallyIntegrable)
    (convolution_measurable ρ S hρ hS hmS)

theorem U_joint_measurable (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r)) :
    Measurable (fun p : ℝ × SampleSpace =>
      U ρ (fun z => S z p.2) p.1) :=
  convolution_joint_measurable ρ S hρs hρ.continuous hS hmS

theorem V_joint_measurable (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r)) :
    Measurable (fun p : ℝ × SampleSpace =>
      V ρ (fun z => S z p.2) p.1) := by
  have hρ' : Continuous (deriv ρ) := (hρ.deriv' (n := 1)).continuous
  exact convolution_joint_measurable (deriv ρ) S hρs.deriv hρ' hS hmS

theorem W_joint_measurable (hρs : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ)
    (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmS : ∀ r, Measurable (S r)) :
    Measurable (fun p : ℝ × SampleSpace =>
      W ρ (fun z => S z p.2) p.1) := by
  have hρ' : ContDiff ℝ 1 (deriv ρ) := hρ.deriv' (n := 1)
  have hρ'' : Continuous (deriv (deriv ρ)) := (hρ'.deriv' (n := 0)).continuous
  exact convolution_joint_measurable (deriv (deriv ρ)) S
    hρs.deriv.deriv hρ'' hS hmS

end OperatorDerivativeRewrite.Foundation.IBMMollifiedMeasurability
