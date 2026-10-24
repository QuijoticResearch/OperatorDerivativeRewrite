import Foundation.GaussianSignedFold
import Foundation.IBMFoldedHeatField
import Foundation.IBMPhysicalWeakWiener

/-! Actual Bochner Gaussian means of signed physical Dirac masses equal the
physical embedding of the folded spatial L2 column, at positive variance. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TemperedDistribution
open scoped NNReal ENNReal BesselPotentialSpace SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalGaussianFold
open GaussianTimeHilbert IBMPhysicalWeakWiener IBMPhysicalDirac IBMFoldedHeatField
open IBMPhysicalNoiseClock IBMPhysicalNoiseVectors
local instance : AddCommGroup Kernel :=
  (inferInstance : NormedAddCommGroup Kernel).toAddCommGroup
local instance : NormedSpace ℝ Kernel := NormedSpace.restrictScalars ℝ ℂ _
local instance : SMul ℝ Kernel := (inferInstance : NormedSpace ℝ Kernel).toModule.toSMul

def signed (r : ℝ) : Kernel := BrownianSignIntegral.signum r • dirac |r|

theorem signed_stronglyMeasurable : StronglyMeasurable signed :=
  BrownianSignIntegral.signum_measurable.stronglyMeasurable.smul
    (dirac_continuous.comp continuous_abs).stronglyMeasurable

theorem signed_bound (r : ℝ) :
    ‖signed r‖ ≤ ‖IBMDeltaBoundary.deltaZeroHminusOne‖+‖physicalDerivative‖*(1+|r|) := by
  have hv : ‖vector |r|‖ ≤ 1+|r| := by
    have he := vector_norm_sq |r|
    rw [abs_abs] at he
    nlinarith [sq_nonneg (‖vector |r|‖-1), norm_nonneg (vector |r|), abs_nonneg r]
  calc
    ‖signed r‖ = ‖BrownianSignIntegral.signum r‖*‖dirac |r|‖ := norm_smul _ _
    _ ≤ ‖dirac |r|‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (BrownianSignIntegral.signum_bound r) (norm_nonneg (dirac |r|))
    _ ≤ ‖IBMDeltaBoundary.deltaZeroHminusOne‖+‖physicalDerivative (vector |r|)‖ := by
      exact norm_sub_le _ _
    _ ≤ _ := add_le_add_right ((physicalDerivative.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hv (norm_nonneg physicalDerivative))) _

theorem signed_integrable (b : ℝ) (v : ℝ≥0) : Integrable signed (gaussianReal b v) := by
  have hi : Integrable (fun r : ℝ => |r|) (gaussianReal b v) :=
    ((memLp_id_gaussianReal' (μ := b) (v := v) 1 (by norm_num)).integrable (by norm_num)).abs
  apply ((integrable_const ‖IBMDeltaBoundary.deltaZeroHminusOne‖).add
    (((integrable_const (1 : ℝ)).add hi).const_mul ‖physicalDerivative‖)).mono'
      signed_stronglyMeasurable.aestronglyMeasurable
  exact ae_of_all _ signed_bound

theorem folded_dirac_integrable (b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    IntegrableOn (fun x => (gaussianPDFReal b v x-gaussianPDFReal (-b) v x) • dirac x)
      (Ioi (0 : ℝ)) :=
  GaussianSignedFold.folded_integrable b v dirac
    (GaussianSignedFold.weighted_integrable b hv dirac (signed_integrable b v))

theorem gaussian_mean_fold (b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ r, signed r ∂gaussianReal b v) =
      ∫ x in Ioi (0 : ℝ), (gaussianPDFReal b v x-gaussianPDFReal (-b) v x) • dirac x :=
  GaussianSignedFold.gaussian_fold b hv dirac (signed_integrable b v)

theorem column_test (b : ℝ) (v : ℝ≥0) (g : 𝓢(ℝ, ℂ)) :
    test g (IBMPhysicalNegativeEmbedding.embedding (column (b,v))) =
      ∫ x in Ioi (0 : ℝ), (gaussianPDFReal b v x-gaussianPDFReal (-b) v x) • g x := by
  rw [test_apply, IBMPhysicalNegativeEmbedding.embedding_toDistr,
    Lp.toTemperedDistribution_apply]
  calc
    _ = ∫ x, (Ioi (0 : ℝ)).indicator
        (fun y => (gaussianPDFReal b v y-gaussianPDFReal (-b) v y) • g y) x := by
      apply integral_congr_ae
      filter_upwards [Complex.ofRealCLM.coeFn_compLpL (column (b,v)), column_coeFn b v]
        with x hc hf
      change IBMPhysicalNoiseClock.complexify (column (b,v)) x = Complex.ofReal _ at hc
      rw [hc,hf]
      by_cases hx : x ∈ Ioi (0 : ℝ)
      · simp [IBMFoldedHeatEnergy.folded, IBMFoldedHeatEnergy.difference, hx, smul_eq_mul,
          mul_comm]
      · simp [IBMFoldedHeatEnergy.folded, hx]
    _ = _ := integral_indicator measurableSet_Ioi

theorem gaussian_mean_embedding (b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ r, signed r ∂gaussianReal b v) = IBMPhysicalNegativeEmbedding.embedding (column (b,v)) := by
  apply BesselPotentialSpace.ext
  ext g
  rw [← test_apply, ← test_apply]
  calc
    _ = test g (∫ x in Ioi (0 : ℝ),
        (gaussianPDFReal b v x-gaussianPDFReal (-b) v x) • dirac x) :=
      congrArg (test g) (gaussian_mean_fold b hv)
    _ = ∫ x in Ioi (0 : ℝ),
        (gaussianPDFReal b v x-gaussianPDFReal (-b) v x) • g x := by
      rw [← (test g).integral_comp_comm (folded_dirac_integrable b hv)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        change test g ((gaussianPDFReal b v x-gaussianPDFReal (-b) v x) • dirac x) = _
        rw [map_smul, test_apply, dirac_toDistr]
        rfl
    _ = _ := (column_test b v g).symm

theorem physical_test_mean (L : Tests) (b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ r, BrownianSignIntegral.signum r * L (dirac |r|) ∂gaussianReal b v) =
      L (IBMPhysicalNegativeEmbedding.embedding (column (b,v))) := by
  have h := L.integral_comp_comm (signed_integrable b v)
  rw [gaussian_mean_embedding b hv] at h
  calc
    _ = ∫ r, L (signed r) ∂gaussianReal b v := by
      apply integral_congr_ae
      exact ae_of_all _ fun r => by
        change BrownianSignIntegral.signum r * L (dirac |r|) =
          L (BrownianSignIntegral.signum r • dirac |r|)
        rw [map_smul,smul_eq_mul]
    _ = _ := h

theorem zero_variance_mean (b : ℝ) :
    (∫ r, signed r ∂gaussianReal b 0) = signed b := by
  rw [gaussianReal_zero_var]
  exact integral_dirac' signed b signed_stronglyMeasurable

end OperatorDerivativeRewrite.Foundation.IBMPhysicalGaussianFold
