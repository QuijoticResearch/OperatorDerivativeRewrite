import Foundation.IBMMixedFourthStein

/-! Actual cubic contractions for the linear-factor part of IBM curvature. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMMixedCubicStein
open InfiniteGaussian GaussianTimeSpaceHermite IBMGaussianSteinMoments IBMCubicFirstChaos
open IBMFirstChaosMixedStein IBMCorrectionStein IBMShiftedJetMoments
open IBMHigherScalarProjection GaussianWickConditionalProjection

theorem wick_three_smul (b : ℝ) (u : CoefficientSpace) :
    (wick (b • u) 3 : GaussianL2) = b^3 • (wick u 3 : GaussianL2) := by
  apply Lp.ext
  filter_upwards [core_coeFn (b • u) (‖b • u‖^2) 3,
    core_coeFn u (‖u‖^2) 3, Lp.coeFn_smul (b^3) (wick u 3 : GaussianL2),
    Lp.coeFn_smul b (firstChaosEmbedding u)] with ω hb hu hs he
  change (wick (b • u) 3 : GaussianL2) ω = _ at hb
  change (wick u 3 : GaussianL2) ω = _ at hu
  rw [hb, hs, Pi.smul_apply, hu, value_three, value_three, map_smul, he,
    Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  simp only [smul_eq_mul, mul_pow, sq_abs]
  ring

theorem third_mixed_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v : CoefficientSpace) (j : ℕ) :
    inner ℝ (wick v 3 : GaussianL2)
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      (inner ℝ u v)^3 * M g a u (j+3) 0 := by
  rw [test_pairing_projection u (shiftedJet_smooth g a j).continuous
    (shiftedJet_bound g a j), conditional_wick_projection,
    FractionalCurrentObservationObstruction.source_projection_single,
    wick_three_smul, real_inner_smul_left, third_pairing]
  have he := congrArg (fun x : ℝ => x^3) (regression_energy u v)
  calc
    (regression u v)^3 * (‖u‖^6 * M g a u (j+3) 0) =
        ((regression u v * ‖u‖^2)^3) * M g a u (j+3) 0 := by ring
    _ = _ := by rw [he]

theorem first_mixed_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v : CoefficientSpace) (j : ℕ) :
    inner ℝ (wick v 1 : GaussianL2)
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      inner ℝ u v * M g a u (j+1) 0 := by
  rw [wick_one_eq_embedding, first_pairing_integral, shifted_first, moment_zero]

theorem cube_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v : CoefficientSpace) (j : ℕ) :
    inner ℝ (cube v)
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      3*‖v‖^2*inner ℝ u v*M g a u (j+1) 0 +
        (inner ℝ u v)^3*M g a u (j+3) 0 := by
  rw [cube, inner_add_left, real_inner_smul_left,
    third_mixed_pairing, first_mixed_pairing]
  ring

theorem mixedCube_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u w k : CoefficientSpace) (j : ℕ) :
    inner ℝ (mixedCube w k)
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      (‖k‖^2*inner ℝ u w+2*inner ℝ w k*inner ℝ u k)*M g a u (j+1) 0 +
        inner ℝ u w*(inner ℝ u k)^2*M g a u (j+3) 0 := by
  simp only [mixedCube, real_inner_smul_left, inner_sub_left, inner_add_left,
    cube_pairing, norm_add_sq_real, norm_sub_sq_real, inner_add_right, inner_sub_right]
  ring

theorem mixedCube_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u w k : CoefficientSpace) (j : ℕ) :
    Integrable (fun ω => firstChaosEmbedding w ω*(firstChaosEmbedding k ω)^2 *
      shiftedJet g a j (firstChaosEmbedding u ω)) gaussianProduct := by
  have hi := (Lp.memLp (mixedCube w k)).integrable_mul
    (Lp.memLp (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)))
  apply hi.congr
  filter_upwards [mixedCube_coeFn w k,
    testClass_coeFn u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)]
    with ω hv ht
  simp only [Pi.mul_apply, hv, ht]

theorem mixedCube_integral (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u w k : CoefficientSpace) (j : ℕ) :
    (∫ ω, firstChaosEmbedding w ω*(firstChaosEmbedding k ω)^2 *
      shiftedJet g a j (firstChaosEmbedding u ω) ∂gaussianProduct) =
      (‖k‖^2*inner ℝ u w+2*inner ℝ w k*inner ℝ u k)*M g a u (j+1) 0 +
        inner ℝ u w*(inner ℝ u k)^2*M g a u (j+3) 0 := by
  rw [← mixedCube_pairing g a u w k j, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [mixedCube_coeFn w k,
    testClass_coeFn u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)]
    with ω hv ht
  simp only [Real.inner_apply, hv, ht]

theorem centered_linear_test (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u w k : CoefficientSpace) (j : ℕ) :
    (∫ ω, firstChaosEmbedding w ω*((firstChaosEmbedding k ω)^2-‖k‖^2) *
      shiftedJet g a j (firstChaosEmbedding u ω) ∂gaussianProduct) =
      2*inner ℝ w k*inner ℝ u k*M g a u (j+1) 0 +
        inner ℝ u w*(inner ℝ u k)^2*M g a u (j+3) 0 := by
  have hi := mixedCube_integrable g a u w k j
  have hs := first_mixed_integrable u w (shiftedJet_smooth g a j).continuous
    (shiftedJet_bound g a j)
  have hf : (fun ω => firstChaosEmbedding w ω *
      ((firstChaosEmbedding k ω)^2-‖k‖^2) *
      shiftedJet g a j (firstChaosEmbedding u ω)) =
      fun ω => firstChaosEmbedding w ω*(firstChaosEmbedding k ω)^2 *
        shiftedJet g a j (firstChaosEmbedding u ω) -
        ‖k‖^2*(firstChaosEmbedding w ω * shiftedJet g a j (firstChaosEmbedding u ω)) := by
    funext ω; ring
  rw [hf, integral_sub hi (hs.const_mul _), integral_const_mul,
    mixedCube_integral, shifted_first]
  simp only [← moment_zero]
  ring

end OperatorDerivativeRewrite.Foundation.IBMMixedCubicStein
