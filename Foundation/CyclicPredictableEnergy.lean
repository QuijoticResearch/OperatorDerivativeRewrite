import Foundation.CyclicPredictableIntegral
import Foundation.IndependentInnovationConditioning

/-! Actual conditional Hermitian energy and finite-horizon Ito isometry for all cyclic channels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.CyclicPredictableEnergy
open CyclicPredictableIntegral FiniteMarkedRenewalMarginals
variable (N : ℕ) [NeZero N]

def sumIncrement (H : ZMod N → Coefficients N) (n : ℕ) (η : Source N) : ℂ :=
  ∑ j ∈ Finset.univ.erase (0 : ZMod N), increment N j (H j) n η

def prefixIncrement (H : ZMod N → Coefficients N) (n : ℕ) (ξ : Prefix (ZMod N) (n+1)) : ℂ :=
  CyclicCenteredKernel.kernel N (fun j => H j n (Fin.init ξ)) (ξ (Fin.last n))

theorem prefixIncrement_eq (H : ZMod N → Coefficients N) (n : ℕ) (η : Source N) :
    prefixIncrement N H n (initialSegment (n+1) η) = sumIncrement N H n η := rfl

def energy (H : ZMod N → Coefficients N) (n : ℕ) (η : Source N) : ℝ :=
  ∑ j ∈ Finset.univ.erase (0 : ZMod N), ‖H j n (initialSegment n η)‖^2

theorem shifted_square_integrable (H : ZMod N → Coefficients N) (n : ℕ)
    (c : Prefix (ZMod N) n → ℂ) :
    Integrable (fun η => ‖c (initialSegment n η)+sumIncrement N H n η‖^2) (probability N) := by
  have he := (prefix_preserving (CyclicRootProbabilityNoise.probability N) (n+1)).integrable_comp_of_integrable
    (show Integrable (fun ξ : Prefix (ZMod N) (n+1) => ‖c (Fin.init ξ)+prefixIncrement N H n ξ‖^2)
      (finiteProbability (CyclicRootProbabilityNoise.probability N) (n+1)) from Integrable.of_finite)
  have hf (η : Source N) : Fin.init (initialSegment (n+1) η) = initialSegment n η := rfl
  simpa only [Function.comp_def,hf,prefixIncrement_eq,CyclicPredictableIntegral.probability] using he

theorem conditional_shifted_energy (H : ZMod N → Coefficients N) (n : ℕ)
    (c : Prefix (ZMod N) n → ℂ) :
    (probability N)[fun η => ‖c (initialSegment n η)+sumIncrement N H n η‖^2 | history N n] =ᵐ[probability N]
      fun η => ‖c (initialSegment n η)‖^2+energy N H n η := by
  let F : Prefix (ZMod N) n × ZMod N → ℝ :=
    fun p => ‖c p.1+CyclicCenteredKernel.kernel N (fun j => H j n p.1) p.2‖^2
  have hI : IndepFun (initialSegment n) (fun η : Source N => η n) (probability N) :=
    (fresh_independent N n).symm
  have hf : (fun η : Source N => F (initialSegment n η,η n)) =
      (fun η => ‖c (initialSegment n η)+sumIncrement N H n η‖^2) := rfl
  have hi : Integrable (fun η : Source N => F (initialSegment n η,η n)) (probability N) := by
    rw [hf]
    exact shifted_square_integrable N H n c
  have he := IndependentInnovationConditioning.conditional_integral (probability N) (initialSegment n)
    (fun η : Source N => η n) (prefix_measurable n) (measurable_pi_apply n) hI F
    (measurable_of_countable F).stronglyMeasurable hi
  have hmap : (probability N).map (fun η : Source N => η n) = CyclicRootProbabilityNoise.probability N :=
    (MarkedRenewalRealization.mark_preserving (CyclicRootProbabilityNoise.probability N) n).map_eq
  rw [hf,hmap] at he
  filter_upwards [he] with η he
  exact he.trans (CyclicCenteredKernel.shifted_kernel_energy N
    (fun j => H j n (initialSegment n η)) (c (initialSegment n η)))

theorem conditional_energy (H : ZMod N → Coefficients N) (n : ℕ) :
    (probability N)[fun η => ‖sumIncrement N H n η‖^2 | history N n] =ᵐ[probability N] energy N H n := by
  simpa only [zero_add,norm_zero,zero_pow (by decide : 2 ≠ 0)] using
    conditional_shifted_energy N H n (fun _ => 0)

theorem energy_integrable (H : ZMod N → Coefficients N) (n : ℕ) :
    Integrable (energy N H n) (probability N) :=
  integrable_condExp.congr (conditional_energy N H n)

theorem shifted_expectation (H : ZMod N → Coefficients N) (n : ℕ)
    (c : Prefix (ZMod N) n → ℂ) :
    (∫ η, ‖c (initialSegment n η)+sumIncrement N H n η‖^2 ∂probability N) =
      (∫ η, ‖c (initialSegment n η)‖^2 ∂probability N)+(∫ η, energy N H n η ∂probability N) := by
  have hc : Integrable (fun η => ‖c (initialSegment n η)‖^2) (probability N) :=
    (prefix_preserving (CyclicRootProbabilityNoise.probability N) n).integrable_comp_of_integrable
      (show Integrable (fun ξ : Prefix (ZMod N) n => ‖c ξ‖^2)
        (finiteProbability (CyclicRootProbabilityNoise.probability N) n) from Integrable.of_finite)
  calc
    _ = ∫ η, (probability N)[fun η => ‖c (initialSegment n η)+sumIncrement N H n η‖^2 |
          history N n] η ∂probability N := (integral_condExp ((history N).le n)).symm
    _ = ∫ η, (‖c (initialSegment n η)‖^2+energy N H n η) ∂probability N :=
      integral_congr_ae (conditional_shifted_energy N H n c)
    _ = _ := integral_add hc (energy_integrable N H n)

theorem totalIntegral_successor (H : ZMod N → Coefficients N) (n : ℕ) (η : Source N) :
    totalIntegral N H (n+1) η = totalIntegral N H n η+sumIncrement N H n η := by
  simp only [totalIntegral,Finset.sum_apply,stochasticIntegral,Finset.sum_range_succ,
    Finset.sum_add_distrib,sumIncrement]

theorem adapted_energy (H : ZMod N → Coefficients N) (M : ℕ → Source N → ℂ)
    (hM : StronglyAdapted (history N) M) (h0 : M 0 = 0)
    (hstep : ∀ n η, M (n+1) η = M n η+sumIncrement N H n η) (L : ℕ) :
    (∫ η, ‖M L η‖^2 ∂probability N) = ∑ i ∈ Finset.range L, ∫ η, energy N H i η ∂probability N := by
  obtain ⟨F,hF⟩ := MarkedPrefixFiltration.adapted_factors (ZMod N) M hM
  have hf (n : ℕ) (η : Source N) : F n (initialSegment n η) = M n η := (hF n η).symm
  induction L with
  | zero => simp [h0]
  | succ n ih =>
    have he := shifted_expectation N H n (F n)
    simp_rw [hf,← hstep n] at he
    rw [he,ih,Finset.sum_range_succ]

theorem ito_isometry (H : ZMod N → Coefficients N) (L : ℕ) :
    (∫ η, ‖totalIntegral N H L η‖^2 ∂probability N) =
      ∑ i ∈ Finset.range L, ∫ η, energy N H i η ∂probability N :=
  adapted_energy N H (totalIntegral N H) (totalIntegral_martingale N H).stronglyAdapted
    (totalIntegral_zero N H) (totalIntegral_successor N H) L

end OperatorDerivativeRewrite.Foundation.CyclicPredictableEnergy
