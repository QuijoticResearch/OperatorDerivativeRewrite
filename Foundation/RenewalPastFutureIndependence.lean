import Foundation.RenewalPastReconstruction
import Foundation.CountableConditionalIndependence

/-! Stationary future-path laws and independence from the entire observed count past. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.RenewalPastFutureIndependence
open ExponentialHoldingSequence ExponentialRenewalCount ExponentialSourceRegeneration
open RenewalConditionalResidual RenewalConditionalFuturePath RenewalPastReconstruction

theorem past_future_joint_law (s : ℝ≥0) :
    probability.map (fun ω => (pastPath s ω,futurePath s ω)) =
      (probability.map (pastPath s)).prod (probability.map countPath) := by
  apply CountableConditionalIndependence.joint_law probability (probability.map countPath)
    (count s) (count_measurable s) (pastPath s) (futurePath s)
    (pastPath_measurable s) (futurePath_measurable s)
  · intro n hp
    have he : count s ⁻¹' {n} = event n s := by ext ω; simp [event]
    rw [he] at hp ⊢
    exact (futurePath_preserving n s s.coe_nonneg hp).map_eq
  · intro n hp
    have he : count s ⁻¹' {n} = event n s := by ext ω; simp [event]
    rw [he] at hp ⊢
    exact conditional_past_future_independent n s hp

theorem future_law (s : ℝ≥0) : probability.map (futurePath s) = probability.map countPath := by
  have he := congrArg (fun ν : Measure (PastPath s × CountPath) => ν.map Prod.snd)
    (past_future_joint_law s)
  rw [Measure.map_map measurable_snd ((pastPath_measurable s).prodMk (futurePath_measurable s)),
    Measure.map_snd_prod, measure_univ, one_smul] at he
  exact he

theorem past_future_independent (s : ℝ≥0) : IndepFun (pastPath s) (futurePath s) probability := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (pastPath_measurable s).aemeasurable (futurePath_measurable s).aemeasurable).mpr
  rw [future_law]
  exact past_future_joint_law s

theorem future_preserving (s : ℝ≥0) :
    MeasurePreserving (futurePath s) probability (probability.map countPath) :=
  ⟨futurePath_measurable s,future_law s⟩

theorem increment_law (s h : ℝ≥0) :
    probability.map (fun ω => count (s+h : ℝ≥0) ω-count s ω) = poissonMeasure h := by
  have he := congrArg (fun ν : Measure CountPath => ν.map (fun γ => γ h)) (future_law s)
  rw [Measure.map_map (measurable_pi_apply h) (futurePath_measurable s),
    Measure.map_map (measurable_pi_apply h) countPath_measurable] at he
  have hi := ConstructedRenewalPoissonLaw.countLaw_eq_poisson h
  change probability.map (count h) = poissonMeasure h at hi
  have hf : (fun ω => count (s+h : ℝ≥0) ω-count s ω) =
      (fun γ : CountPath => γ h) ∘ futurePath s := by
    funext ω
    simp only [Function.comp_def, futurePath, NNReal.coe_add]
  rw [hf, he]
  exact hi

end OperatorDerivativeRewrite.Foundation.RenewalPastFutureIndependence
