import Foundation.MarkedRootRenewalProcess

/-! An actual probability law on zero-start cadlag complex paths with the coordinate sigma algebra. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RootRenewalPathLaw
open MarkedRootRenewalProcess ExponentialNonexplosiveClock

abbrev Path := {γ : ℝ → ℂ // IsCadlag γ ∧ γ 0 = 0}

def path (a : ℝ) (ω : StateSample) : Path :=
  ⟨fun t => process a t ω, process_cadlag a ω, process_zero a ω⟩

theorem path_measurable (a : ℝ) : Measurable (path a) := by
  have he : Measurable (fun ω : StateSample => fun t : ℝ => process a t ω) :=
    measurable_pi_iff.mpr (fun t => process_measurable a t)
  exact he.subtype_mk

def law (a : ℝ) : Measure Path := MarkedRootRenewalProcess.probability.map (path a)

instance law_isProbability (a : ℝ) : IsProbabilityMeasure (law a) := by
  unfold law
  infer_instance

theorem evaluation_measurable (t : ℝ) : Measurable (fun γ : Path => γ.val t) :=
  (measurable_pi_apply t).comp measurable_subtype_coe

theorem evaluation_law (a t : ℝ) :
    (law a).map (fun γ : Path => γ.val t) =
      MarkedRootRenewalProcess.probability.map (process a t) := by
  rw [law, Measure.map_map (evaluation_measurable t) (path_measurable a)]
  rfl

theorem zero_law (a : ℝ) : (law a).map (fun γ : Path => γ.val 0) = Measure.dirac 0 := by
  rw [evaluation_law]
  have he : process a 0 = (fun _ : StateSample => (0 : ℂ)) := by
    funext ω
    exact process_zero a ω
  rw [he]
  simp only [Measure.map_const, measure_univ, one_smul]

theorem source_nonzero_ae (a : ℝ) (ha : a ≠ 0) :
    ∀ᵐ ω : StateSample ∂MarkedRootRenewalProcess.probability, ∃ t : ℝ, (path a ω).val t ≠ 0 := by
  filter_upwards [clock_good_ae] with ω hω
  exact ⟨clock 1 ω.1, first_jump_nonzero a ha ω hω⟩

end OperatorDerivativeRewrite.Foundation.RootRenewalPathLaw
