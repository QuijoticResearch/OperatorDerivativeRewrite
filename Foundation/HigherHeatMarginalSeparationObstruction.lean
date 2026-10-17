import Foundation.HigherHeatSchwartzTransition
import Foundation.NormalizedSignedScoreCounterexample

/-! Zero-start even-order heat marginals do not separate the actual Schwartz test class. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped NNReal SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatMarginalSeparationObstruction
open HigherHeatSignedLaws HigherHeatSchwartzTransition NormalizedSignedScoreCounterexample

theorem witness_positive : 0 < oddPart (1 : ℝ) := by
  rw [odd_apply]
  positivity

theorem witness_nonzero : oddPart ≠ (0 : 𝓢(ℝ,ℝ)) := by
  intro h
  have he := congrArg (fun f : 𝓢(ℝ,ℝ) => f 1) h
  exact (ne_of_gt witness_positive) he

theorem witness_odd (x : ℝ) : oddPart (-x) = -oddPart x := by
  simp [odd_apply]

theorem witness_zero : oddPart (0 : ℝ) = 0 := by simp [odd_apply]

theorem pairing_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    Integrable (fun x : ℝ => oddPart x*realKernel m hm t ht x) := by
  have hi := (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) oddPart
    (realKernel m hm t ht)).integrable (μ := volume)
  have he : (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) oddPart
      (realKernel m hm t ht) : ℝ → ℝ) = (fun x => oddPart x*realKernel m hm t ht x) := by
    funext x
    simp only [SchwartzMap.pairing_apply_apply,ContinuousLinearMap.mul_apply']
  rw [← he]
  exact hi

theorem all_marginal_pairings_zero (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    (∫ x : ℝ, oddPart x*realKernel m hm t ht x) = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ => oddPart x*realKernel m hm t ht x) volume
  have he : (fun x : ℝ => oddPart (-x)*realKernel m hm t ht (-x)) =
      -(fun x : ℝ => oddPart x*realKernel m hm t ht x) := by
    funext x
    simp only [witness_odd,realKernel_even,Pi.neg_apply,neg_mul]
  rw [he] at h
  change (∫ x : ℝ, -(oddPart x*realKernel m hm t ht x)) = _ at h
  rw [integral_neg] at h
  linarith

theorem nonseparating (m : ℕ) (hm : 0 < m) :
    ∃ f : 𝓢(ℝ,ℝ), f ≠ 0 ∧
      ∀ (t : ℝ≥0) (ht : 0 < t), (∫ x : ℝ, f x*realKernel m hm t ht x) = 0 :=
  ⟨oddPart,witness_nonzero,fun t ht => all_marginal_pairings_zero m hm t ht⟩

theorem not_marginal_separation (m : ℕ) (hm : 0 < m) :
    ¬ (∀ f : 𝓢(ℝ,ℝ),
      (∀ (t : ℝ≥0) (ht : 0 < t), (∫ x : ℝ, f x*realKernel m hm t ht x) = 0) → f = 0) := by
  intro h
  exact witness_nonzero (h oddPart (fun t ht => all_marginal_pairings_zero m hm t ht))

theorem all_starting_points_separate (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (f : 𝓢(ℝ, ℂ))
    (hf : ∀ x : ℝ, (∫ y : ℝ, f (x+y)*(realKernel m hm t ht y : ℂ)) = 0) : f = 0 := by
  have hz : HigherHeatSchwartzSemigroup.evolve m hm t f = 0 := by
    ext x
    change HigherHeatSchwartzSemigroup.evolve m hm t f x = 0
    rw [← transition_evolve m hm t ht f x]
    exact hf x
  have hfour := congrArg (fun g : 𝓢(ℝ,ℂ) => 𝓕 g) hz
  rw [HigherHeatSchwartzSemigroup.evolve_positive m hm t ht,
    SchwartzMap.fourier_convolution,GaussianSchwartzKernel.evenKernel_fourier] at hfour
  have hF : 𝓕 f = (0 : 𝓢(ℝ,ℂ)) := by
    ext ξ
    have hh := congrArg (fun g : 𝓢(ℝ,ℂ) => g ξ) hfour
    simp only [SchwartzMap.pairing_apply_apply,ContinuousLinearMap.mul_apply',
      GaussianSchwartzKernel.evenSymbol_apply,FourierTransform.fourier_zero] at hh
    change HigherHeatL2.symbol m t ξ*𝓕 f ξ = 0 at hh
    have hn : HigherHeatL2.symbol m t ξ ≠ 0 := by
      unfold HigherHeatL2.symbol
      exact_mod_cast Real.exp_ne_zero (-(t : ℝ)*(2*Real.pi*ξ)^(2*m))
    exact (mul_eq_zero.mp hh).resolve_left hn
  apply (fourierEquiv ℂ 𝓢(ℝ,ℂ)).injective
  simpa only [fourierEquiv_apply,FourierTransform.fourier_zero] using hF

end OperatorDerivativeRewrite.Foundation.HigherHeatMarginalSeparationObstruction
