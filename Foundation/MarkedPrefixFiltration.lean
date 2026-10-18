import Foundation.MarkedSourceRegeneration
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! The genuine finite-prefix filtration and fresh iid coordinate on an arbitrary mark source. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.MarkedPrefixFiltration
open MarkedRenewalRealization FiniteMarkedRenewalMarginals
variable (A : Type*) [MeasurableSpace A]

def history : Filtration ℕ (inferInstance : MeasurableSpace (MarkSample A)) where
  seq n := MeasurableSpace.comap (initialSegment n) inferInstance
  mono' := by
    intro n m hnm
    let mPast : MeasurableSpace (MarkSample A) := MeasurableSpace.comap (initialSegment m) inferInstance
    have hp : @Measurable (MarkSample A) (Prefix A m) mPast inferInstance
        (initialSegment m) := comap_measurable _
    have hn : @Measurable (MarkSample A) (Prefix A n) mPast inferInstance (initialSegment n) :=
      Measurable.of_eval fun i : Fin n =>
        (measurable_pi_apply (⟨i.val,lt_of_lt_of_le i.isLt hnm⟩ : Fin m)).comp hp
    exact hn.comap_le
  le' n := (prefix_measurable n).comap_le

theorem prefix_past (n : ℕ) : Measurable[history A n] (initialSegment n) := comap_measurable _

theorem coefficient_past (n : ℕ) (H : Prefix A n → ℂ) (hH : Measurable H) :
    StronglyMeasurable[history A n] (fun η => H (initialSegment n η)) :=
  (hH.comp (prefix_past A n)).stronglyMeasurable

theorem prefix_integrable (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ)
    (F : Prefix A n → ℂ) (hF : Integrable F (finiteProbability μ n)) :
    Integrable (fun η => F (initialSegment n η)) (marks μ) :=
  (prefix_preserving μ n).integrable_comp_of_integrable hF

theorem fresh_independent (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ) :
    Indep (MeasurableSpace.comap (fun η : MarkSample A => η n) inferInstance) (history A n) (marks μ) := by
  have hi := (MarkedSourceRegeneration.past_tail_independent μ n).symm.comp
    (measurable_pi_apply 0) measurable_id
  have he : ((fun f : MarkSample A => f 0) ∘ MarkedSourceRegeneration.tail n) =
      (fun η : MarkSample A => η n) := by
    funext η
    simp [MarkedSourceRegeneration.tail]
  rw [he,Function.id_comp] at hi
  exact hi

theorem adapted_factors (M : ℕ → MarkSample A → ℂ) (hM : StronglyAdapted (history A) M) :
    ∃ F : (n : ℕ) → Prefix A n → ℂ, ∀ n η, M n η = F n (initialSegment n η) := by
  have hf (n : ℕ) : ∃ f : Prefix A n → ℂ,
      StronglyMeasurable f ∧ M n = f ∘ initialSegment n := by
    have hn : StronglyMeasurable[MeasurableSpace.comap (initialSegment n) inferInstance] (M n) := hM n
    exact hn.exists_eq_measurable_comp
  choose F hFm hFe using hf
  exact ⟨F,fun n η => congrFun (hFe n) η⟩

end OperatorDerivativeRewrite.Foundation.MarkedPrefixFiltration
