import Foundation.IBMSchwartzNativeJointIto
import Foundation.IBMSpatialPointClockEnergy

/-! A lower bound for the ENTIRE nonlinear source slope, using its actual
first-source coefficient. The singular mollifier norm is not hidden by an
upper bound. Nonzero limiting first coefficient is an explicit hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzSlopeLowerBound
open InfiniteGaussian IBMSchwartzSecondProjection IBMShiftedJetMoments
open IBMSchwartzSourceSecondDerivative IBMGaussianSteinMoments

private theorem adjoint_contraction (f : GaussianL2) :
    ‖firstChaosEmbedding.toContinuousLinearMap.adjoint f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖firstChaosEmbedding.toContinuousLinearMap.adjoint‖*‖f‖ :=
      firstChaosEmbedding.toContinuousLinearMap.adjoint.le_opNorm f
    _ = ‖firstChaosEmbedding.toContinuousLinearMap‖*‖f‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right
      firstChaosEmbedding.norm_toContinuousLinearMap_le (norm_nonneg f)
    _ = _ := one_mul _

theorem weighted_lower (g : SchwartzMap ℝ ℝ) (a : ℝ) (u v : CoefficientSpace) (j : ℕ) :
    |M g a u j 0| * ‖v‖ ≤ ‖weightedClass g a u j (firstChaosEmbedding v)‖ +
      |inner ℝ u v| * (|M g a u (j+2) 0| * ‖u‖) := by
  have he : M g a u j 0 • v =
      firstChaosEmbedding.toContinuousLinearMap.adjoint
        (weightedClass g a u j (firstChaosEmbedding v)) -
      (inner ℝ u v*M g a u (j+2) 0) • u := by
    rw [IBMSchwartzFirstCoefficient.weighted_linear_adjoint]
    module
  have hn := norm_sub_le
    (firstChaosEmbedding.toContinuousLinearMap.adjoint
      (weightedClass g a u j (firstChaosEmbedding v)))
    ((inner ℝ u v*M g a u (j+2) 0) • u)
  rw [← he, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul] at hn
  calc
    _ ≤ ‖firstChaosEmbedding.toContinuousLinearMap.adjoint
        (weightedClass g a u j (firstChaosEmbedding v))‖ +
      |inner ℝ u v| * |M g a u (j+2) 0| * ‖u‖ := hn
    _ ≤ _ := by
      rw [mul_assoc]
      exact add_le_add (adjoint_contraction _) le_rfl

theorem spatial_lower (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    |M g a (tripleCoefficient n r 0) 1 0| * ‖tripleCoefficient n r 1‖ ≤
      ‖spatialSlope g a n r‖ + SchwartzMap.seminorm ℝ 0 0 (IBMCorrectionStein.jet g 2) := by
  have h := weighted_lower g a (tripleCoefficient n r 0) (tripleCoefficient n r 1) 1
  have hc := IBMSchwartzPhysicalSlope.covariance_bound n r
  have hj := IBMSchwartzPhysicalGlobalBounds.jet_bound g a 2 (tripleCoefficient n r 0)
  change |inner ℝ (tripleCoefficient n r 0) (tripleCoefficient n r 1)| ≤ 1 at hc
  have hb := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (abs_nonneg (M g a (tripleCoefficient n r 0) 3 0))
      (norm_nonneg (tripleCoefficient n r 0)))
  simp only [one_mul] at hb
  exact h.trans (add_le_add le_rfl (hb.trans hj))

theorem derivative_norm_escape (r : ℝ) :
    Tendsto (fun n => ‖tripleCoefficient n r 1‖) atTop atTop := by
  have hp : Tendsto (fun n => ‖IBMPhysicalWhiteNoiseObstruction.profile n‖) atTop atTop := by
    simpa only [IBMPhysicalNoiseRealization.physicalNoise.norm_map] using
      IBMPhysicalWhiteNoiseObstruction.whiteNoise_norm_escape
  have he (n : ℕ) : ‖tripleCoefficient n r 1‖ =
      ‖IBMPhysicalWhiteNoiseObstruction.profile n‖ := by
    rw [IBMSchwartzFullGlobalBounds.jet_one_norm]
    exact (IBMSchwartzPhysicalGlobalBounds.translated_norm (IBMMollifier.kernel n)
      (IBMMollifier.kernel_smooth n).continuous (IBMMollifier.kernel_compactSupport n) 0).symm
  simpa only [he] using hp

theorem spatial_norm_escape (g : SchwartzMap ℝ ℝ) (a r : ℝ)
    (hm : M g a (IBMQuarticPrimitiveLimit.baseCoefficient r) 1 0 ≠ 0) :
    Tendsto (fun n => ‖spatialSlope g a n r‖) atTop atTop := by
  let c := |M g a (IBMQuarticPrimitiveLimit.baseCoefficient r) 1 0|/2
  have hc : 0 < c := by dsimp [c]; exact half_pos (abs_pos.mpr hm)
  have hM := (IBMSchwartzPhysicalSlope.mean_continuous g a 1).continuousAt.tendsto.comp
    (IBMQuarticPrimitiveLimit.coefficient_tendsto r)
  have hc' : c < |M g a (IBMQuarticPrimitiveLimit.baseCoefficient r) 1 0| := by
    dsimp [c]
    linarith [abs_pos.mpr hm]
  have he : ∀ᶠ n in atTop, c ≤ |M g a (tripleCoefficient n r 0) 1 0| :=
    (hM.abs.eventually (lt_mem_nhds hc')).mono
      (fun _ h => le_of_lt h)
  apply tendsto_atTop.2
  intro b
  filter_upwards [he, (derivative_norm_escape r).eventually_ge_atTop
    ((b+SchwartzMap.seminorm ℝ 0 0 (IBMCorrectionStein.jet g 2))/c)] with n hn hd
  have h1 := (div_le_iff₀ hc).mp hd
  have h2 := mul_le_mul_of_nonneg_right hn (norm_nonneg (tripleCoefficient n r 1))
  have h3 := spatial_lower g a n r
  nlinarith

end OperatorDerivativeRewrite.Foundation.IBMSchwartzSlopeLowerBound
