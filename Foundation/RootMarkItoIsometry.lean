import Foundation.RootMarkConditionalEnergy
import Mathlib.MeasureTheory.Function.L2Space

/-! Native finite-horizon Ito isometry for the actual three-channel predictable integral. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RootMarkItoIsometry
open RootMarkStochasticIntegral RootMarkConditionalEnergy
open MarkedRootRenewalProcess (MarkSample marks)
open RootRenewalWalkMarginal (initialSegment prefix_measurable)
open ComplexRootChannelGram

theorem channelKernel_mean (a : ℝ) (u : Fin 3 → ℂ) :
    (∫ k, channelKernel a u k ∂ComplexFourthRootNoise.probability) = 0 := by
  unfold channelKernel
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  have he (r : Fin 3) :
      (∫ k, u r*(ComplexFourthRootNoise.noise a k)^(r.val+1)
        ∂ComplexFourthRootNoise.probability) = 0 := by
    rw [integral_const_mul]
    fin_cases r
    · simp [ComplexFourthRootNoise.mean]
    · simp [ComplexFourthRootNoise.second]
    · simp [ComplexFourthRootNoise.third]
  simp_rw [he]
  simp

theorem shifted_kernel_energy (a : ℝ) (u : Fin 3 → ℂ) (c : ℂ) :
    (∫ k, ‖c+channelKernel a u k‖^2 ∂ComplexFourthRootNoise.probability) =
      ‖c‖^2+∑ r : Fin 3, ‖u r‖^2*(2*a^2)^(r.val+1) := by
  simp_rw [norm_add_sq_real]
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
    integral_add (Integrable.of_finite) (Integrable.of_finite), integral_const_mul,
    integral_inner (𝕜 := ℝ) (Integrable.of_finite), channelKernel_mean]
  simp [energy_formula]

theorem shifted_square_integrable (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ)
    (c : ComplexFourthRootWalk.Sample n → ℂ) :
    Integrable (fun η => ‖c (initialSegment n η)+sumIncrement a H n η‖^2) marks := by
  have he := RootMarkFiniteClark.terminal_integrable (n+1)
    (fun ξ => ((‖c (Fin.init ξ)+prefixIncrement a H n ξ‖^2 : ℝ) : ℂ))
  have hf (η : MarkSample) : Fin.init (initialSegment (n+1) η) = initialSegment n η := rfl
  simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re, hf, prefixIncrement_eq] using he.re

theorem conditional_shifted_energy (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ)
    (c : ComplexFourthRootWalk.Sample n → ℂ) :
    marks[(fun η => ‖c (initialSegment n η)+sumIncrement a H n η‖^2) | history n] =ᵐ[marks]
      fun η => ‖c (initialSegment n η)‖^2+energy a H n η := by
  let F : ComplexFourthRootWalk.Sample n × Fin 4 → ℝ :=
    fun p => ‖c p.1+channelKernel a (fun r => H r n p.1) p.2‖^2
  have hI : IndepFun (initialSegment n) (fun η : MarkSample => η n) marks :=
    (fresh_independent n).symm
  have hf : (fun η : MarkSample => F (initialSegment n η,η n)) =
      (fun η => ‖c (initialSegment n η)+sumIncrement a H n η‖^2) := rfl
  have hi : Integrable (fun η : MarkSample => F (initialSegment n η,η n)) marks := by
    rw [hf]
    exact shifted_square_integrable a H n c
  have he := IndependentInnovationConditioning.conditional_integral marks (initialSegment n)
    (fun η : MarkSample => η n) (prefix_measurable n) (measurable_pi_apply n) hI F
    (measurable_of_countable F).stronglyMeasurable hi
  rw [hf, (MarkedRootRenewalProcess.mark_preserving n).map_eq] at he
  filter_upwards [he] with η he
  exact he.trans (shifted_kernel_energy a (fun r => H r n (initialSegment n η)) (c (initialSegment n η)))

theorem shifted_expectation (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ)
    (c : ComplexFourthRootWalk.Sample n → ℂ) :
    (∫ η, ‖c (initialSegment n η)+sumIncrement a H n η‖^2 ∂marks) =
      (∫ η, ‖c (initialSegment n η)‖^2 ∂marks)+(∫ η, energy a H n η ∂marks) := by
  have hc := (RootMarkFiniteClark.terminal_integrable n
    (fun ξ => ((‖c ξ‖^2 : ℝ) : ℂ))).re
  have hc' : Integrable (fun η => ‖c (initialSegment n η)‖^2) marks := by
    simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re] using hc
  calc
    _ = ∫ η, marks[(fun η => ‖c (initialSegment n η)+sumIncrement a H n η‖^2) | history n] η
        ∂marks := (integral_condExp (history.le n)).symm
    _ = ∫ η, (‖c (initialSegment n η)‖^2+energy a H n η) ∂marks :=
      integral_congr_ae (conditional_shifted_energy a H n c)
    _ = _ := integral_add hc' (energy_integrable a H n)

theorem adapted_energy (a : ℝ) (H : Fin 3 → Coefficients) (M : ℕ → MarkSample → ℂ)
    (hM : StronglyAdapted history M) (h₀ : M 0 = 0)
    (hstep : ∀ n η, M (n+1) η = M n η+sumIncrement a H n η) (N : ℕ) :
    (∫ η, ‖M N η‖^2 ∂marks) = ∑ j ∈ Finset.range N, ∫ η, energy a H j η ∂marks := by
  obtain ⟨F,hF⟩ := RootMarkMartingaleRepresentation.adapted_factors M hM
  have hf (n : ℕ) (η : MarkSample) : F n (initialSegment n η) = M n η :=
    (congrFun (congrFun hF n) η).symm
  induction N with
  | zero => simp [h₀]
  | succ n ih =>
    have he := shifted_expectation a H n (F n)
    simp_rw [hf, ← hstep n] at he
    rw [he, ih, Finset.sum_range_succ]

def totalIntegral (a : ℝ) (H : Fin 3 → Coefficients) : ℕ → MarkSample → ℂ :=
  stochasticIntegral a 0 (H 0)+stochasticIntegral a 1 (H 1)+stochasticIntegral a 2 (H 2)

theorem totalIntegral_martingale (a : ℝ) (H : Fin 3 → Coefficients) :
    Martingale (totalIntegral a H) history marks := by
  unfold totalIntegral
  exact ((stochasticIntegral_martingale a 0 (H 0)).add
    (stochasticIntegral_martingale a 1 (H 1))).add (stochasticIntegral_martingale a 2 (H 2))

theorem totalIntegral_zero (a : ℝ) (H : Fin 3 → Coefficients) : totalIntegral a H 0 = 0 := by
  funext η
  simp [totalIntegral, stochasticIntegral]

theorem totalIntegral_successor (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ) (η : MarkSample) :
    totalIntegral a H (n+1) η = totalIntegral a H n η+sumIncrement a H n η := by
  have h₀ := congrFun (stochasticIntegral_successor a 0 (H 0) n) η
  have h₁ := congrFun (stochasticIntegral_successor a 1 (H 1) n) η
  have h₂ := congrFun (stochasticIntegral_successor a 2 (H 2) n) η
  simp only [Pi.sub_apply] at h₀ h₁ h₂
  simp only [totalIntegral, Pi.add_apply, sumIncrement, Fin.sum_univ_succ, Fin.sum_univ_zero,
    show (Fin.succ (0 : Fin 2) : Fin 3) = 1 from rfl,
    show (Fin.succ (Fin.succ (0 : Fin 1)) : Fin 3) = 2 from rfl]
  linear_combination h₀+h₁+h₂

theorem ito_isometry (a : ℝ) (H : Fin 3 → Coefficients) (N : ℕ) :
    (∫ η, ‖totalIntegral a H N η‖^2 ∂marks) =
      ∑ j ∈ Finset.range N, ∫ η, energy a H j η ∂marks :=
  adapted_energy a H (totalIntegral a H) (totalIntegral_martingale a H).stronglyAdapted
    (totalIntegral_zero a H) (totalIntegral_successor a H) N

end OperatorDerivativeRewrite.Foundation.RootMarkItoIsometry
