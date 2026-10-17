import Foundation.GaussianSmoothHeatMartingale

/-! The Brownian half-Laplacian is not symmetric for its finite-time Gaussian law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff
namespace OperatorDerivativeRewrite.Foundation.StickyTerminalLawObstruction
open InfiniteGaussian GaussianTimeProcess GaussianSmoothHeatMartingale
set_option backward.isDefEq.respectTransparency false

def terminalLaw (T : ℝ≥0) : Measure ℝ := gaussianReal 0 T

theorem process_terminal_law (T : ℝ≥0) : HasLaw (process T) (terminalLaw T) gaussianProduct :=
  process_hasLaw T

theorem terminal_cosine_integral (T : ℝ≥0) :
    (∫ x, Real.cos x ∂terminalLaw T) = Real.exp (-((T:ℝ)/2)) := by
  have h := (process_terminal_law T).integral_comp Real.continuous_cos.aestronglyMeasurable
  exact h.symm.trans (cos_mean T)

def heatGenerator (f : ℝ → ℝ) (x : ℝ) : ℝ := (1/2 : ℝ) * deriv (deriv f) x

theorem heatGenerator_cosine (x : ℝ) : heatGenerator Real.cos x = -(1/2 : ℝ)*Real.cos x := by
  simp [heatGenerator, Real.deriv_cos', Real.deriv_sin]

theorem heatGenerator_one (x : ℝ) : heatGenerator (fun _ => 1) x = 0 := by
  simp [heatGenerator]

theorem cosine_generator_pairing (T : ℝ≥0) :
    (∫ x, heatGenerator Real.cos x * 1 ∂terminalLaw T) =
      -(1/2 : ℝ)*Real.exp (-((T:ℝ)/2)) := by
  simp only [heatGenerator_cosine, mul_one, integral_const_mul, terminal_cosine_integral]

theorem constant_generator_pairing (T : ℝ≥0) :
    (∫ x, Real.cos x * heatGenerator (fun _ => 1) x ∂terminalLaw T) = 0 := by
  simp only [heatGenerator_one, mul_zero, integral_zero]

theorem generator_pairings_differ (T : ℝ≥0) :
    (∫ x, heatGenerator Real.cos x * 1 ∂terminalLaw T) ≠
      ∫ x, Real.cos x * heatGenerator (fun _ => 1) x ∂terminalLaw T := by
  rw [cosine_generator_pairing, constant_generator_pairing]
  exact mul_ne_zero (by norm_num) (Real.exp_ne_zero _)

theorem bounded_smooth_witness : ContDiff ℝ ∞ Real.cos ∧ ContDiff ℝ ∞ (fun _ : ℝ => (1:ℝ)) ∧
    (∀ x, ‖Real.cos x‖ ≤ 1) ∧ (∀ _x : ℝ, ‖(1:ℝ)‖ ≤ 1) := by
  exact ⟨Real.contDiff_cos, contDiff_const, fun x => Real.abs_cos_le_one x, by simp⟩

end OperatorDerivativeRewrite.Foundation.StickyTerminalLawObstruction
