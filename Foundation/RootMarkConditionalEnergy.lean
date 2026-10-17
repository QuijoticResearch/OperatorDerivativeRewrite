import Foundation.ComplexRootChannelGram
import Foundation.RootMarkFiniteClark
import Foundation.IndependentInnovationConditioning

/-! Actual conditional Ito energy for predictable coefficients on the infinite mark source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RootMarkConditionalEnergy
open RootMarkStochasticIntegral
open MarkedRootRenewalProcess (MarkSample marks)
open RootRenewalWalkMarginal (initialSegment prefix_measurable)

def sumIncrement (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ) (η : MarkSample) : ℂ :=
  ∑ r : Fin 3, increment a r (H r) n η

def prefixIncrement (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ)
    (ξ : ComplexFourthRootWalk.Sample (n+1)) : ℂ :=
  ComplexRootChannelGram.channelKernel a (fun r => H r n (Fin.init ξ)) (ξ (Fin.last n))

theorem prefixIncrement_eq (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ) (η : MarkSample) :
    prefixIncrement a H n (initialSegment (n+1) η) = sumIncrement a H n η := rfl

theorem increment_square_integrable (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ) :
    Integrable (fun η => ‖sumIncrement a H n η‖^2) marks := by
  have he := RootMarkFiniteClark.terminal_integrable (n+1)
    (fun ξ => ((‖prefixIncrement a H n ξ‖^2 : ℝ) : ℂ))
  have hr := he.re
  simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re, prefixIncrement_eq] using hr

def energy (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ) (η : MarkSample) : ℝ :=
  ∑ r : Fin 3, ‖H r n (initialSegment n η)‖^2*(2*a^2)^(r.val+1)

theorem conditional_energy (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ) :
    marks[(fun η => ‖sumIncrement a H n η‖^2) | history n] =ᵐ[marks] energy a H n := by
  let F : ComplexFourthRootWalk.Sample n × Fin 4 → ℝ :=
    fun p => ‖ComplexRootChannelGram.channelKernel a (fun r => H r n p.1) p.2‖^2
  have hI : IndepFun (initialSegment n) (fun η : MarkSample => η n) marks :=
    (fresh_independent n).symm
  have hf : (fun η : MarkSample => F (initialSegment n η,η n)) =
      (fun η => ‖sumIncrement a H n η‖^2) := rfl
  have hi : Integrable (fun η : MarkSample => F (initialSegment n η,η n)) marks := by
    rw [hf]
    exact increment_square_integrable a H n
  have he := IndependentInnovationConditioning.conditional_integral marks (initialSegment n)
    (fun η : MarkSample => η n) (prefix_measurable n) (measurable_pi_apply n) hI F
    (measurable_of_countable F).stronglyMeasurable hi
  rw [hf, (MarkedRootRenewalProcess.mark_preserving n).map_eq] at he
  filter_upwards [he] with η he
  exact he.trans (ComplexRootChannelGram.energy_formula a (fun r => H r n (initialSegment n η)))

theorem energy_adapted (a : ℝ) (H : Fin 3 → Coefficients) : StronglyAdapted history (energy a H) := by
  intro n
  exact ((measurable_of_countable (fun ξ : ComplexFourthRootWalk.Sample n =>
    ∑ r : Fin 3, ‖H r n ξ‖^2*(2*a^2)^(r.val+1))).comp (prefix_past n)).stronglyMeasurable

theorem energy_integrable (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ) :
    Integrable (energy a H n) marks :=
  integrable_condExp.congr (conditional_energy a H n)

end OperatorDerivativeRewrite.Foundation.RootMarkConditionalEnergy
