import Foundation.IBMHigherScalarProjection

/-! Actual mixed fourth Gaussian moments against shifted Schwartz jets.
These contractions retain the sixth derivative when the jet index is two. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.IBMMixedFourthStein
open InfiniteGaussian GaussianTimeSpaceHermite GaussianQuarticWick
open IBMFirstChaosMixedStein IBMCorrectionStein IBMShiftedJetMoments
open IBMHigherScalarProjection GaussianWickConditionalProjection

theorem wick_four_smul (b : ℝ) (u : CoefficientSpace) :
    (wick (b • u) 4 : GaussianL2) = b^4 • (wick u 4 : GaussianL2) := by
  apply Lp.ext
  filter_upwards [core_coeFn (b • u) (‖b • u‖^2) 4,
    core_coeFn u (‖u‖^2) 4, Lp.coeFn_smul (b^4) (wick u 4 : GaussianL2),
    Lp.coeFn_smul b (firstChaosEmbedding u)] with ω hb hu hs he
  change (wick (b • u) 4 : GaussianL2) ω = _ at hb
  change (wick u 4 : GaussianL2) ω = _ at hu
  rw [hb, hs, Pi.smul_apply, hu, value_four, value_four, map_smul, he,
    Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  simp only [smul_eq_mul, mul_pow, sq_abs]
  ring

theorem fourth_mixed_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v : CoefficientSpace) (j : ℕ) :
    inner ℝ (wick v 4 : GaussianL2)
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      (inner ℝ u v)^4 * M g a u (j+4) 0 := by
  rw [test_pairing_projection u (shiftedJet_smooth g a j).continuous
    (shiftedJet_bound g a j), conditional_wick_projection,
    FractionalCurrentObservationObstruction.source_projection_single,
    wick_four_smul, real_inner_smul_left, fourth_pairing]
  have he := congrArg (fun x : ℝ => x^4) (regression_energy u v)
  calc
    (regression u v)^4 * (‖u‖^8 * M g a u (j+4) 0) =
        ((regression u v * ‖u‖^2)^4) * M g a u (j+4) 0 := by ring
    _ = _ := by rw [he]

theorem second_mixed_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v : CoefficientSpace) (j : ℕ) :
    inner ℝ (wick v 2 : GaussianL2)
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      (inner ℝ u v)^2 * M g a u (j+2) 0 := by
  rw [second_pairing_integral, second_centered_mixed
    (shiftedJet_smooth g a j)]
  · simp only [shiftedJet_deriv, moment_zero]
  · exact shiftedJet_bound g a j
  · simpa only [shiftedJet_deriv] using shiftedJet_bound g a (j+1)
  · simpa only [shiftedJet_deriv] using shiftedJet_bound g a (j+1+1)

theorem zeroth_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v : CoefficientSpace) (j : ℕ) :
    inner ℝ (wick v 0 : GaussianL2)
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      M g a u j 0 := by
  rw [L2_inner_eq_integral, moment_zero]
  apply integral_congr_ae
  filter_upwards [core_coeFn v (‖v‖^2) 0,
    testClass_coeFn u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)]
    with ω hv ht
  change (wick v 0 : GaussianL2) ω = _ at hv
  simp only [Real.inner_apply, hv, ht, value_zero, one_mul]

theorem quartic_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v : CoefficientSpace) (j : ℕ) :
    inner ℝ (quartic v)
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      3*‖v‖^4*M g a u j 0 +
        6*‖v‖^2*(inner ℝ u v)^2*M g a u (j+2) 0 +
        (inner ℝ u v)^4*M g a u (j+4) 0 := by
  rw [quartic, inner_add_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_left, fourth_mixed_pairing, second_mixed_pairing, zeroth_pairing]
  ring

theorem fourth_mixed_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v : CoefficientSpace) (j : ℕ) :
    Integrable (fun ω => (firstChaosEmbedding v ω)^4 *
      shiftedJet g a j (firstChaosEmbedding u ω)) gaussianProduct := by
  have hi := (Lp.memLp (quartic v)).integrable_mul
    (Lp.memLp (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)))
  apply hi.congr
  filter_upwards [quartic_coeFn v,
    testClass_coeFn u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)]
    with ω hv ht
  simp only [Pi.mul_apply, hv, ht]

/-- A genuine source integral, including zero and collinear observations. -/
theorem fourth_mixed (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v : CoefficientSpace) (j : ℕ) :
    (∫ ω, (firstChaosEmbedding v ω)^4 *
      shiftedJet g a j (firstChaosEmbedding u ω) ∂gaussianProduct) =
      3*‖v‖^4*M g a u j 0 +
        6*‖v‖^2*(inner ℝ u v)^2*M g a u (j+2) 0 +
        (inner ℝ u v)^4*M g a u (j+4) 0 := by
  rw [← quartic_pairing g a u v j, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [quartic_coeFn v,
    testClass_coeFn u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)]
    with ω hv ht
  simp only [Real.inner_apply, hv, ht]

/-- The actual mixed square contraction. Its final coefficient is Q6
when applied to the second jet in the IBM curvature. -/
theorem squareProduct_pairing (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v k : CoefficientSpace) (j : ℕ) :
    inner ℝ (IBMEvenCorrectionProjection.squareProduct v k)
      (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) =
      (‖v‖^2*‖k‖^2+2*(inner ℝ v k)^2)*M g a u j 0 +
      (‖v‖^2*(inner ℝ u k)^2+‖k‖^2*(inner ℝ u v)^2+
        4*inner ℝ v k*inner ℝ u v*inner ℝ u k)*M g a u (j+2) 0 +
      (inner ℝ u v)^2*(inner ℝ u k)^2*M g a u (j+4) 0 := by
  simp only [IBMEvenCorrectionProjection.squareProduct, real_inner_smul_left,
    inner_sub_left, inner_add_left, quartic_pairing,
    show ∀ x : CoefficientSpace, ‖x‖^4 = (‖x‖^2)^2 by intro x; ring,
    norm_add_sq_real, norm_sub_sq_real, inner_add_right, inner_sub_right]
  ring

theorem squareProduct_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v k : CoefficientSpace) (j : ℕ) :
    Integrable (fun ω => (firstChaosEmbedding v ω)^2*(firstChaosEmbedding k ω)^2 *
      shiftedJet g a j (firstChaosEmbedding u ω)) gaussianProduct := by
  have hi := (Lp.memLp (IBMEvenCorrectionProjection.squareProduct v k)).integrable_mul
    (Lp.memLp (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)))
  apply hi.congr
  filter_upwards [IBMEvenCorrectionProjection.squareProduct_coeFn v k,
    testClass_coeFn u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)]
    with ω hv ht
  simp only [Pi.mul_apply, hv, ht]

theorem squareProduct_integral (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v k : CoefficientSpace) (j : ℕ) :
    (∫ ω, (firstChaosEmbedding v ω)^2*(firstChaosEmbedding k ω)^2 *
      shiftedJet g a j (firstChaosEmbedding u ω) ∂gaussianProduct) =
      (‖v‖^2*‖k‖^2+2*(inner ℝ v k)^2)*M g a u j 0 +
      (‖v‖^2*(inner ℝ u k)^2+‖k‖^2*(inner ℝ u v)^2+
        4*inner ℝ v k*inner ℝ u v*inner ℝ u k)*M g a u (j+2) 0 +
      (inner ℝ u v)^2*(inner ℝ u k)^2*M g a u (j+4) 0 := by
  rw [← squareProduct_pairing g a u v k j, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [IBMEvenCorrectionProjection.squareProduct_coeFn v k,
    testClass_coeFn u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)]
    with ω hv ht
  simp only [Real.inner_apply, hv, ht]

/-- Pairing the actual squared derivative factor with a centered quadratic
test. This isolates exactly the source-two testing obligation. -/
theorem centered_square_test (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (u v k : CoefficientSpace) (j : ℕ) :
    (∫ ω, (firstChaosEmbedding v ω)^2 *
      ((firstChaosEmbedding k ω)^2-‖k‖^2) *
      shiftedJet g a j (firstChaosEmbedding u ω) ∂gaussianProduct) =
      2*(inner ℝ v k)^2*M g a u j 0 +
      (‖v‖^2*(inner ℝ u k)^2+
        4*inner ℝ v k*inner ℝ u v*inner ℝ u k)*M g a u (j+2) 0 +
      (inner ℝ u v)^2*(inner ℝ u k)^2*M g a u (j+4) 0 := by
  have hi := squareProduct_integrable g a u v k j
  have hs := second_mixed_integrable u v (shiftedJet_smooth g a j).continuous
    (shiftedJet_bound g a j)
  have hf : (fun ω => (firstChaosEmbedding v ω)^2 *
      ((firstChaosEmbedding k ω)^2-‖k‖^2) *
      shiftedJet g a j (firstChaosEmbedding u ω)) =
      fun ω => (firstChaosEmbedding v ω)^2*(firstChaosEmbedding k ω)^2 *
        shiftedJet g a j (firstChaosEmbedding u ω) -
        ‖k‖^2*((firstChaosEmbedding v ω)^2 * shiftedJet g a j (firstChaosEmbedding u ω)) := by
    funext ω; ring
  rw [hf, integral_sub hi (hs.const_mul _), integral_const_mul,
    squareProduct_integral, shifted_second]
  simp only [← moment_zero]
  ring

end OperatorDerivativeRewrite.Foundation.IBMMixedFourthStein
