import Foundation.IBMSchwartzSourceSecondDerivative

/-! Full first-source coefficient of the actual shifted Schwartz curvature.
Actual quadratic/cubic product classes justify every test pairing. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzFirstCoefficient
open InfiniteGaussian IBMCorrectionStein IBMShiftedJetMoments IBMFirstChaosMixedStein
open IBMSchwartzSecondProjection IBMSchwartzSourceContinuity IBMSourceProductBounds
open IBMQuarticSecondChaos IBMMixedFourthStein IBMMixedCubicStein IBMCubicFirstChaos
open GaussianTimeSpaceHermite FractionalControlledEstimate

theorem rawProduct_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ) (u w k : CoefficientSpace) (j : ℕ) :
    inner ℝ (rawProduct w k) (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      inner ℝ w k*M g a u j 0+inner ℝ u w*inner ℝ u k*M g a u (j+2) 0 := by
  rw [rawProduct_eq_cross, inner_add_left, real_inner_smul_left, cross]
  simp only [real_inner_smul_left, inner_sub_left, second_mixed_pairing]
  have h0 : inner ℝ gaussianOne
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) = M g a u j 0 := by
    rw [gaussianOne_inner_eq_integral, moment_zero]
    exact integral_congr_ae (testClass_coeFn _ _ _)
  rw [h0, inner_add_right]
  ring

theorem weighted_linear_adjoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (u w : CoefficientSpace) (j : ℕ) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (weightedClass g a u j (firstChaosEmbedding w)) =
      M g a u j 0 • w+(inner ℝ u w*M g a u (j+2) 0) • u := by
  apply ext_inner_right ℝ
  intro k
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (weightedClass g a u j (firstChaosEmbedding w)) (firstChaosEmbedding k) = _
  have he : inner ℝ (weightedClass g a u j (firstChaosEmbedding w)) (firstChaosEmbedding k) =
      inner ℝ (rawProduct w k)
        (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) := by
    rw [L2_inner_eq_integral, L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [weightedClass_coeFn g a u j (firstChaosEmbedding w), rawProduct_coeFn w k,
      testClass_coeFn u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)] with ω hw hp ht
    rw [hw, hp, ht]
    simp only [Real.inner_apply]
    ring
  rw [he, rawProduct_pairing]
  simp only [inner_add_left, real_inner_smul_left]
  ring

theorem weighted_square_adjoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v : CoefficientSpace) (j : ℕ) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (weightedClass g a u j (square v)) =
      (‖v‖^2*M g a u (j+1) 0+(inner ℝ u v)^2*M g a u (j+3) 0) • u+
        (2*inner ℝ u v*M g a u (j+1) 0) • v := by
  apply ext_inner_right ℝ
  intro k
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (weightedClass g a u j (square v)) (firstChaosEmbedding k) = _
  have he : inner ℝ (weightedClass g a u j (square v)) (firstChaosEmbedding k) =
      inner ℝ (mixedCube k v)
        (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) := by
    rw [L2_inner_eq_integral, L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [weightedClass_coeFn g a u j (square v), square_coeFn v, mixedCube_coeFn k v,
      testClass_coeFn u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)] with ω hw hv hm ht
    rw [hw, hv, hm, ht]
    simp only [Real.inner_apply]
    ring
  rw [he, mixedCube_pairing]
  simp only [inner_add_left, real_inner_smul_left, real_inner_comm k v]
  ring

def coefficient (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v w : CoefficientSpace) : CoefficientSpace :=
  ((‖v‖^2+inner ℝ u w)*M g a u 3 0+(inner ℝ u v)^2*M g a u 5 0) • u+
    (2*inner ℝ u v*M g a u 3 0) • v+M g a u 1 0 • w

theorem correction_adjoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v w : CoefficientSpace) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (correctionClass g a u v w) = coefficient g a u v w := by
  rw [correctionClass, map_add, weighted_square_adjoint, weighted_linear_adjoint]
  norm_num
  unfold coefficient
  module

end OperatorDerivativeRewrite.Foundation.IBMSchwartzFirstCoefficient
