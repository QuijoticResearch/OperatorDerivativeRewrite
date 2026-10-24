import Foundation.BrownianSignIntegral
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Signed Gaussian folding with actual Bochner integrability hypotheses.
The negative branch subtracts the reflected density; it never adds it. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianSignedFold
open BrownianSignIntegral

theorem pdf_reflection (b : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal b v (-x) = gaussianPDFReal (-b) v x := by
  unfold gaussianPDFReal
  rw [show (-x-b)^2 = (x-(-b))^2 by ring]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def weighted (b : ℝ) (v : ℝ≥0) (f : ℝ → E) (x : ℝ) : E :=
  gaussianPDFReal b v x • (signum x • f |x|)

theorem paired (b : ℝ) (v : ℝ≥0) (f : ℝ → E) {x : ℝ} (hx : 0 < x) :
    weighted b v f x + weighted b v f (-x) =
      (gaussianPDFReal b v x-gaussianPDFReal (-b) v x) • f x := by
  have hp : signum x = 1 := by simp [signum,hx]
  have hn : signum (-x) = -1 := by
    simp [signum, not_lt.mpr (neg_nonpos.mpr hx.le), neg_lt_zero.mpr hx]
  rw [weighted, weighted, pdf_reflection, abs_neg, abs_of_pos hx, hp, hn]
  module

theorem signed_integral (b : ℝ) (v : ℝ≥0) (f : ℝ → E)
    (hi : Integrable (weighted b v f) volume) :
    (∫ x, weighted b v f x) =
      ∫ x in Ioi (0 : ℝ), (gaussianPDFReal b v x-gaussianPDFReal (-b) v x) • f x := by
  have hn : (∫ x in Ioi (0 : ℝ), weighted b v f (-x)) =
      ∫ x in Iic (0 : ℝ), weighted b v f x := by
    simpa only [neg_zero] using integral_comp_neg_Ioi (0 : ℝ) (weighted b v f)
  calc
    _ = (∫ x in Ioi (0 : ℝ), weighted b v f x)+
        ∫ x in Iic (0 : ℝ), weighted b v f x := by
      simpa only [compl_Ioi] using (integral_add_compl measurableSet_Ioi hi).symm
    _ = ∫ x in Ioi (0 : ℝ), weighted b v f x+weighted b v f (-x) := by
      rw [← hn]
      exact (integral_add hi.integrableOn hi.comp_neg.integrableOn).symm
    _ = _ := setIntegral_congr_fun measurableSet_Ioi (fun x hx => paired b v f hx)

theorem gaussian_signed_integral (b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (f : ℝ → E)
    (hi : Integrable (weighted b v f) volume) :
    (∫ x, signum x • f |x| ∂gaussianReal b v) =
      ∫ x in Ioi (0 : ℝ), (gaussianPDFReal b v x-gaussianPDFReal (-b) v x) • f x := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  exact signed_integral b v f hi

theorem weighted_integrable (b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (f : ℝ → E)
    (hi : Integrable (fun x => signum x • f |x|) (gaussianReal b v)) :
    Integrable (weighted b v f) volume := by
  rw [gaussianReal_of_var_ne_zero b hv] at hi
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF b v) (ae_of_all _ fun _ => gaussianPDF_lt_top)).mp hi
  convert h using 1
  funext x
  rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  rfl

theorem folded_integrable (b : ℝ) (v : ℝ≥0) (f : ℝ → E)
    (hi : Integrable (weighted b v f) volume) :
    IntegrableOn (fun x => (gaussianPDFReal b v x-gaussianPDFReal (-b) v x) • f x)
      (Ioi (0 : ℝ)) := by
  apply (hi.integrableOn.add hi.comp_neg.integrableOn).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact paired b v f hx

theorem gaussian_fold (b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (f : ℝ → E)
    (hi : Integrable (fun x => signum x • f |x|) (gaussianReal b v)) :
    (∫ x, signum x • f |x| ∂gaussianReal b v) =
      ∫ x in Ioi (0 : ℝ), (gaussianPDFReal b v x-gaussianPDFReal (-b) v x) • f x :=
  gaussian_signed_integral b hv f (weighted_integrable b hv f hi)

end OperatorDerivativeRewrite.Foundation.GaussianSignedFold
