import Foundation.IBMContinuousComposition

/-! A precise interface between coordinate modifications and measurable continuous
source paths. Existence of such modifications is a separate analytic obligation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMModificationBridge
open InfiniteGaussian IBMSourceLaws

variable (S : ℝ → SampleSpace → ℝ) (C : ℝ≥0 → SampleSpace → ℝ)

def sceneryPath (hS : ∀ ω, Continuous (fun r => S r ω))
    (ω : SampleSpace) : C(ℝ, ℝ) := ⟨fun r => S r ω, hS ω⟩

def clockPath (hC : ∀ ω, Continuous (fun t => C t ω))
    (ω : SampleSpace) : C(ℝ≥0, ℝ) := ⟨fun t => C t ω, hC ω⟩

theorem sceneryPath_measurable (hS : ∀ ω, Continuous (fun r => S r ω))
    (hm : ∀ r, Measurable (S r)) : Measurable (sceneryPath S hS) :=
  ContinuousMap.measurable_iff_eval.mpr hm

theorem clockPath_measurable (hC : ∀ ω, Continuous (fun t => C t ω))
    (hm : ∀ t, Measurable (C t)) : Measurable (clockPath C hC) :=
  ContinuousMap.measurable_iff_eval.mpr hm

/-- Pointwise identity with the supplied modification at each deterministic time. -/
theorem sceneryPath_apply (hS : ∀ ω, Continuous (fun r => S r ω))
    (r : ℝ) (ω : SampleSpace) : sceneryPath S hS ω r = S r ω := rfl

theorem clockPath_apply (hC : ∀ ω, Continuous (fun t => C t ω))
    (t : ℝ≥0) (ω : SampleSpace) : clockPath C hC ω t = C t ω := rfl

/-- The modified scenery retains every verified one-coordinate law. -/
theorem scenery_modified_law (hS : ∀ ω, Continuous (fun r => S r ω))
    (hmod : ∀ r, S r =ᵐ[gaussianProduct] sceneryBase r) (r : ℝ) :
    HasLaw (fun ω => sceneryPath S hS ω r)
      (gaussianProduct.map (sceneryBase r)) gaussianProduct := by
  have hbase : HasLaw (sceneryBase r) (gaussianProduct.map (sceneryBase r))
      gaussianProduct := ⟨(sceneryBase_measurable r).aemeasurable, rfl⟩
  exact hbase.congr (hmod r)

/-- The modified clock retains each Brownian coordinate law. -/
theorem clock_modified_law (hC : ∀ ω, Continuous (fun t => C t ω))
    (hmod : ∀ t, C t =ᵐ[gaussianProduct] GaussianTimeProcess.process t)
    (t : ℝ≥0) :
    HasLaw (fun ω => clockPath C hC ω t) (gaussianReal 0 t) gaussianProduct :=
  (GaussianTimeProcess.process_hasLaw t).congr (hmod t)

/-- Source path maps built from modifications remain independent on the actual
product measure once their coordinate measurability is proved. -/
theorem modified_sources_independent (hS : ∀ ω, Continuous (fun r => S r ω))
    (hC : ∀ ω, Continuous (fun t => C t ω))
    (hmS : ∀ r, Measurable (S r)) (hmC : ∀ t, Measurable (C t)) :
    IndepFun (fun ω : JointSample => sceneryPath S hS ω.1)
      (fun ω : JointSample => clockPath C hC ω.2) jointMeasure :=
  IBMContinuousComposition.sources_independent _ _
    (sceneryPath_measurable S hS hmS) (clockPath_measurable C hC hmC)

end OperatorDerivativeRewrite.Foundation.IBMModificationBridge
