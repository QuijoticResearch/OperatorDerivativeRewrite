import Foundation.SignedSchwartzJetDomain
import Foundation.SchwartzPolynomialSeparation
import Foundation.BochnerL2Approximation

/-! Actual polynomial classes in the positive L2 majorant of an arbitrary real Schwartz density. -/
noncomputable section
open MeasureTheory Polynomial
open scoped SchwartzMap ENNReal
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzPolynomialL2
open SignedSchwartzL2Rigging SchwartzPolynomialSeparation

theorem square_integrable (K : 𝓢(ℝ, ℝ)) (P : Polynomial ℝ) :
    Integrable (fun x : ℝ => (P.eval x)^2) (measure K) := by
  have hi := ((polynomialKernel (P^2) K).integrable (μ := volume)).norm
  have hw : Integrable (fun x : ℝ => |K x| * (P.eval x)^2) := by
    convert hi using 1
    funext x
    simp only [polynomialKernel_apply, eval_pow, Real.norm_eq_abs, abs_mul,
      abs_pow, sq_abs]
    ring
  have hm : Measurable (fun x : ℝ => |K x|) := by
    simpa only [Real.norm_eq_abs] using K.continuous.measurable.norm
  rw [SignedSchwartzL2Rigging.measure, SignedAbsoluteIntegration.absoluteDensity,
    integrable_withDensity_iff_integrable_smul₀' hm.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul] using hw

theorem real_memLp (K : 𝓢(ℝ, ℝ)) (P : Polynomial ℝ) :
    MemLp (fun x : ℝ => P.eval x) 2 (measure K) :=
  (memLp_two_iff_integrable_sq P.continuous.aestronglyMeasurable).mpr (square_integrable K P)

theorem polynomial_memLp (K : 𝓢(ℝ, ℝ)) (P : Polynomial ℝ) :
    MemLp (fun x : ℝ => ((P.eval x : ℝ) : ℂ)) 2 (measure K) := by
  apply (memLp_two_iff_integrable_sq_norm
    (Complex.continuous_ofReal.comp P.continuous).aestronglyMeasurable).mpr
  simpa only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    using square_integrable K P

def polynomialL2 (K : 𝓢(ℝ, ℝ)) (P : Polynomial ℝ) : H K :=
  (polynomial_memLp K P).toLp (fun x : ℝ => ((P.eval x : ℝ) : ℂ))

theorem polynomialL2_ae (K : 𝓢(ℝ, ℝ)) (P : Polynomial ℝ) :
    polynomialL2 K P =ᵐ[measure K] (fun x : ℝ => ((P.eval x : ℝ) : ℂ)) := MemLp.coeFn_toLp _

end OperatorDerivativeRewrite.Foundation.SignedSchwartzPolynomialL2
