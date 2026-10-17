import Foundation.RootMarkDoobRepresentation
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! Explicit three-channel representation of genuine finite-prefix martingales. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RootMarkMartingaleRepresentation
open RootMarkStochasticIntegral RootMarkDoobRepresentation
open MarkedRootRenewalProcess (MarkSample marks)
open RootRenewalWalkMarginal (initialSegment)

theorem driftSum_predictable (F : Coefficients) :
    StronglyAdapted history (fun n => driftSum F (n+1)) := by
  intro n
  change StronglyMeasurable[history n]
    (fun η => ∑ j ∈ Finset.range (n+1), driftCoefficient F j (initialSegment j η))
  apply Measurable.stronglyMeasurable
  apply Finset.measurable_sum
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact ((coefficient_past (driftCoefficient F) j).mono (history.mono hjn)).measurable

theorem driftSum_martingale (F : Coefficients) (hF : Martingale (observable F) history marks) :
    Martingale (driftSum F) history marks := by
  have h₀ := martingale_const_fun history marks (hF.stronglyMeasurable 0) (hF.integrable 0)
  have hc := compensated_martingale 1 (by norm_num) F
  have hd := (hF.sub h₀).sub hc
  have he : observable F-(fun _ => observable F 0)-compensated F = driftSum F := by
    funext n η
    simp only [Pi.sub_apply, compensated]
    ring
  rw [he] at hd
  exact hd

theorem driftSum_zero (F : Coefficients) (hF : Martingale (observable F) history marks) (n : ℕ) :
    driftSum F n =ᵐ[marks] (0 : MarkSample → ℂ) := by
  have he := (driftSum_martingale F hF).eq_zero_of_predictable (driftSum_predictable F) n
  have h₀ : driftSum F 0 = (0 : MarkSample → ℂ) := by
    funext η
    simp [driftSum]
  rw [h₀] at he
  exact he

theorem martingale_representation (a : ℝ) (ha : a ≠ 0) (F : Coefficients)
    (hF : Martingale (observable F) history marks) (n : ℕ) :
    (fun η => observable F n η-observable F 0 η) =ᵐ[marks]
      fun η => stochasticIntegral a 0 (channelCoefficients a F 0) n η+
        stochasticIntegral a 1 (channelCoefficients a F 1) n η+
        stochasticIntegral a 2 (channelCoefficients a F 2) n η := by
  have hr := compensated_representation a ha F
  filter_upwards [driftSum_zero F hF n] with η hη
  have he := congrFun (congrFun hr n) η
  change observable F n η-observable F 0 η-driftSum F n η = _ at he
  change driftSum F n η = 0 at hη
  rw [hη, sub_zero] at he
  exact he

theorem adapted_factors (M : ℕ → MarkSample → ℂ) (hM : StronglyAdapted history M) :
    ∃ F : Coefficients, M = observable F := by
  have hf (n : ℕ) : ∃ f : ComplexFourthRootWalk.Sample n → ℂ,
      StronglyMeasurable f ∧ M n = f ∘ initialSegment n := by
    have hn : StronglyMeasurable[MeasurableSpace.comap (initialSegment n) inferInstance] (M n) := hM n
    exact hn.exists_eq_measurable_comp
  choose F hFm hFe using hf
  refine ⟨F, ?_⟩
  funext n η
  exact congrFun (hFe n) η

theorem predictable_representation (a : ℝ) (ha : a ≠ 0) (M : ℕ → MarkSample → ℂ)
    (hM : Martingale M history marks) :
    ∃ H : Fin 3 → Coefficients, ∀ n : ℕ,
      (fun η => M n η-M 0 η) =ᵐ[marks]
        fun η => stochasticIntegral a 0 (H 0) n η+
          stochasticIntegral a 1 (H 1) n η+stochasticIntegral a 2 (H 2) n η := by
  obtain ⟨F,hF⟩ := adapted_factors M hM.stronglyAdapted
  subst M
  exact ⟨fun r => channelCoefficients a F r, fun n => martingale_representation a ha F hM n⟩

end OperatorDerivativeRewrite.Foundation.RootMarkMartingaleRepresentation
