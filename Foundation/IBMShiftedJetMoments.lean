import Foundation.IBMPolynomialWeightedStein

/-! Third and fourth actual Gaussian Stein moments for the shifted
Schwartz jets used by the IBM correction. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMShiftedJetMoments
open InfiniteGaussian IBMCorrectionStein IBMPolynomialWeightedStein

def M (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j k : ℕ) : ℝ :=
  moment u (shiftedJet g a j) k

theorem M_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j k : ℕ) :
    Integrable (fun ω => (firstChaosEmbedding u ω)^k*shiftedJet g a j (firstChaosEmbedding u ω))
      gaussianProduct :=
  moment_integrable u k (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)

theorem recurrence (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j k : ℕ) :
    M g a u j (k+1) = (k : ℝ)*‖u‖^2*M g a u j (k-1) + ‖u‖^2*M g a u (j+1) k := by
  have hb : ∀ x, ‖deriv (shiftedJet g a j) x‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g (j+1)) := by
    rw [shiftedJet_deriv]
    exact shiftedJet_bound g a (j+1)
  simpa only [M, shiftedJet_deriv] using moment_recurrence (shiftedJet_smooth g a j)
    (shiftedJet_bound g a j) hb u k

theorem moment_zero (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    M g a u j 0 = ∫ ω, shiftedJet g a j (firstChaosEmbedding u ω) ∂gaussianProduct := by
  simp only [M, moment, pow_zero, one_mul]

theorem moment_one (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    M g a u j 1 = ‖u‖^2*M g a u (j+1) 0 := by
  simpa only [Nat.cast_zero, zero_mul, zero_add] using recurrence g a u j 0

theorem moment_two (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    M g a u j 2 = ‖u‖^2*M g a u j 0 + ‖u‖^4*M g a u (j+2) 0 := by
  rw [recurrence g a u j 1, moment_one]
  norm_num
  ring

theorem moment_three (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    M g a u j 3 = 3*‖u‖^4*M g a u (j+1) 0 + ‖u‖^6*M g a u (j+3) 0 := by
  rw [recurrence g a u j 2, moment_one, moment_two]
  norm_num
  ring

theorem moment_four (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    M g a u j 4 = 3*‖u‖^4*M g a u j 0 + 6*‖u‖^6*M g a u (j+2) 0 +
      ‖u‖^8*M g a u (j+4) 0 := by
  rw [recurrence g a u j 3, moment_two, moment_three]
  norm_num
  ring

theorem centered_third (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    (∫ ω, ((firstChaosEmbedding u ω)^3-3*‖u‖^2*firstChaosEmbedding u ω)*
      shiftedJet g a j (firstChaosEmbedding u ω) ∂gaussianProduct) =
      ‖u‖^6*M g a u (j+3) 0 := by
  have hf : (fun ω => ((firstChaosEmbedding u ω)^3-3*‖u‖^2*firstChaosEmbedding u ω)*
      shiftedJet g a j (firstChaosEmbedding u ω)) = fun ω =>
      (firstChaosEmbedding u ω)^3*shiftedJet g a j (firstChaosEmbedding u ω) -
        (3*‖u‖^2)*((firstChaosEmbedding u ω)^1*shiftedJet g a j (firstChaosEmbedding u ω)) := by
    funext ω; ring
  rw [hf, integral_sub (M_integrable g a u j 3) ((M_integrable g a u j 1).const_mul _), integral_const_mul]
  change M g a u j 3-(3*‖u‖^2)*M g a u j 1 = _
  rw [moment_three, moment_one]
  ring

theorem centered_fourth (g : SchwartzMap ℝ ℝ) (a : ℝ) (u : CoefficientSpace) (j : ℕ) :
    (∫ ω, ((firstChaosEmbedding u ω)^4-6*‖u‖^2*(firstChaosEmbedding u ω)^2+3*‖u‖^4)*
      shiftedJet g a j (firstChaosEmbedding u ω) ∂gaussianProduct) =
      ‖u‖^8*M g a u (j+4) 0 := by
  have hf : (fun ω => ((firstChaosEmbedding u ω)^4-6*‖u‖^2*(firstChaosEmbedding u ω)^2+3*‖u‖^4)*
      shiftedJet g a j (firstChaosEmbedding u ω)) = fun ω =>
      ((firstChaosEmbedding u ω)^4*shiftedJet g a j (firstChaosEmbedding u ω) -
        (6*‖u‖^2)*((firstChaosEmbedding u ω)^2*shiftedJet g a j (firstChaosEmbedding u ω))) +
      (3*‖u‖^4)*((firstChaosEmbedding u ω)^0*shiftedJet g a j (firstChaosEmbedding u ω)) := by
    funext ω; ring
  have hi : Integrable (fun ω =>
      (firstChaosEmbedding u ω)^4*shiftedJet g a j (firstChaosEmbedding u ω) -
      (6*‖u‖^2)*((firstChaosEmbedding u ω)^2*shiftedJet g a j (firstChaosEmbedding u ω)))
      gaussianProduct := (M_integrable g a u j 4).sub ((M_integrable g a u j 2).const_mul _)
  rw [hf, integral_add hi ((M_integrable g a u j 0).const_mul (3*‖u‖^4)),
    integral_sub (M_integrable g a u j 4) ((M_integrable g a u j 2).const_mul _),
    integral_const_mul, integral_const_mul]
  change M g a u j 4-(6*‖u‖^2)*M g a u j 2+(3*‖u‖^4)*M g a u j 0 = _
  rw [moment_four, moment_two]
  ring

end OperatorDerivativeRewrite.Foundation.IBMShiftedJetMoments
