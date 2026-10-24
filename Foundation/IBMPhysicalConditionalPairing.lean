import Foundation.IBMPhysicalSlopeConditional
import Foundation.GaussianConditionalIto

/-! Actual conditional folded coefficients pair with EVERY unbounded past L2 test.
These are rowwise dualities, not yet a whole predictable-projection theorem. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalConditionalPairing
open InfiniteGaussian GaussianConditionalIto IBMPhysicalWeakWiener IBMPhysicalPointSlope
open IBMSchwartzWeakWienerClosure

def row (S T : ℝ≥0) (L : Tests) : GaussianL2 :=
  pastProjection S (evaluate L (slopeLimit T))

def tested (S T : ℝ≥0) (L : Tests) (Y : SampleSpace) : ℝ :=
  L (IBMPhysicalNegativeEmbedding.embedding (IBMFoldedHeatPredictable.raw T (S,Y)))

theorem row_actual (S T : ℝ≥0) (hST : S < T) (L : Tests) :
    row S T L =ᵐ[gaussianProduct] tested S T L :=
  (pastProjection_ae S (evaluate L (slopeLimit T))).trans
    (IBMPhysicalSlopeConditional.conditional_actual_field S T hST L)

theorem tested_memLp (S T : ℝ≥0) (hST : S < T) (L : Tests) :
    MemLp (tested S T L) 2 gaussianProduct :=
  (Lp.memLp (row S T L)).ae_eq (row_actual S T hST L)

theorem row_norm_le (S T : ℝ≥0) (L : Tests) :
    ‖row S T L‖ ≤ ‖evaluate L (slopeLimit T)‖ :=
  (pastL2 S).norm_starProjection_apply_le _

theorem actual_product_integrable (S T : ℝ≥0) (hST : S < T) (L : Tests) (V : GaussianL2) :
    Integrable (fun Y => tested S T L Y*V Y) gaussianProduct :=
  (tested_memLp S T hST L).integrable_mul (Lp.memLp V)

theorem past_covariance (S T : ℝ≥0) (hST : S < T) (L : Tests) (V : GaussianL2)
    (hV : V ∈ pastL2 S) :
    (∫ Y, tested S T L Y*V Y ∂gaussianProduct) = inner ℝ (evaluate L (slopeLimit T)) V := by
  have hp := (pastL2 S).starProjection_inner_eq_zero (evaluate L (slopeLimit T)) V hV
  rw [inner_sub_left] at hp
  change inner ℝ (evaluate L (slopeLimit T)) V-
    inner ℝ (pastProjection S (evaluate L (slopeLimit T))) V = 0 at hp
  have he : (∫ Y, tested S T L Y*V Y ∂gaussianProduct) = inner ℝ (row S T L) V := by
    rw [L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [row_actual S T hST L] with Y hy
    rw [hy,Real.inner_apply]
  exact he.trans (by change inner ℝ (pastProjection S (evaluate L (slopeLimit T))) V = _; linarith)

theorem earlier_past_covariance (a S T : ℝ≥0) (haS : a ≤ S) (hST : S < T)
    (L : Tests) (V : GaussianL2) (hV : V ∈ pastL2 a) :
    (∫ Y, tested S T L Y*V Y ∂gaussianProduct) = inner ℝ (evaluate L (slopeLimit T)) V :=
  past_covariance S T hST L V (hV.mono (GaussianTimeProcess.naturalFiltration.mono haS))

theorem integrated_covariance (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (L : Tests) (V : GaussianL2) (hV : V ∈ pastL2 a) :
    (∫ s in (a : ℝ)..b, ∫ Y, tested s.toNNReal T L Y*V Y ∂gaussianProduct) =
      ((b : ℝ)-a)*inner ℝ (evaluate L (slopeLimit T)) V := by
  calc
    _ = ∫ _s in (a : ℝ)..b, inner ℝ (evaluate L (slopeLimit T)) V := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [((volume : Measure ℝ).ae_ne (T : ℝ))] with s hs hmem
      rw [uIoc_of_le (show (a : ℝ) ≤ b from hab)] at hmem
      have hsn : 0 ≤ s := a.coe_nonneg.trans hmem.1.le
      have ha : a ≤ s.toNNReal := by
        apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal s hsn]
        exact hmem.1.le
      have ht : s.toNNReal < T := by
        apply NNReal.coe_lt_coe.mp
        rw [Real.coe_toNNReal s hsn]
        exact lt_of_le_of_ne (hmem.2.trans (show (b : ℝ) ≤ T from hbT)) hs
      exact earlier_past_covariance a s.toNNReal T ha ht L V hV
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]

end OperatorDerivativeRewrite.Foundation.IBMPhysicalConditionalPairing
