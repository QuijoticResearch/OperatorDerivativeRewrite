import Foundation.SchwartzPolynomialSeparation
import Foundation.HigherHeatKernelStein

/-! The unique real polynomial Stein weight under actual Schwartz testing of the signed heat kernel. -/
noncomputable section
open MeasureTheory Polynomial FourierTransform
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSteinWeight
open GaussianSchwartzKernel HigherHeatSignedLaws HigherHeatKernelStein HigherHeatSpatialGenerator
open SchwartzPolynomialSeparation

def alpha (m : ℕ) (t : ℝ≥0) : ℝ := (2*m:ℕ)*(-1:ℝ)^(m+1)*(t:ℝ)

def canonicalWeight (m : ℕ) (t : ℝ≥0) : Polynomial ℝ := C (alpha m t)⁻¹*X

theorem alpha_ne_zero (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) : alpha m t ≠ 0 := by
  unfold alpha
  exact mul_ne_zero (mul_ne_zero (by exact_mod_cast (show 2*m ≠ 0 by omega))
    (pow_ne_zero _ (by norm_num))) (ne_of_gt (by exact_mod_cast ht))

theorem canonical_weight_identity (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (g : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, jet (2*m-1) g x*evenKernel m hm t ht x)=
      (∫ x : ℝ, g x*((((canonicalWeight m t).eval x):ℝ):ℂ)*evenKernel m hm t ht x) := by
  have hs := schwartz_stein m hm t ht g
  have hc : (2*m:ℕ)*(-1:ℂ)^(m+1)*(t:ℝ)=(alpha m t:ℂ) := by
    simp only [alpha,Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_pow,
      Complex.ofReal_neg,Complex.ofReal_one]
  rw [hc] at hs
  have ha : (alpha m t:ℂ) ≠ 0 := by exact_mod_cast alpha_ne_zero m hm t ht
  have he : (∫ x : ℝ, g x*((((canonicalWeight m t).eval x):ℝ):ℂ)*evenKernel m hm t ht x)=
      (alpha m t:ℂ)⁻¹*(∫ x : ℝ, (x:ℂ)*g x*evenKernel m hm t ht x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [canonicalWeight,eval_mul,eval_C,eval_X,Complex.ofReal_mul,Complex.ofReal_inv]
      ring
  rw [he,hs]
  exact (inv_mul_cancel_left₀ ha _).symm

theorem polynomial_weight_unique (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (W : Polynomial ℝ)
    (hW : ∀ g : 𝓢(ℝ,ℂ), (∫ x : ℝ, jet (2*m-1) g x*evenKernel m hm t ht x)=
      (∫ x : ℝ, g x*(((W.eval x):ℝ):ℂ)*evenKernel m hm t ht x)) :
    W=canonicalWeight m t := by
  apply SchwartzPolynomialSeparation.polynomial_weight_unique (realKernel m hm t ht)
    (by rw [realKernel_integral]; norm_num) W (canonicalWeight m t)
  intro g
  let gC : 𝓢(ℝ,ℂ) := g.postcompCLM Complex.ofRealCLM
  have hgC (x : ℝ) : gC x=(g x:ℂ) := rfl
  have he (P : Polynomial ℝ) :
      (∫ x : ℝ, gC x*(((P.eval x):ℝ):ℂ)*evenKernel m hm t ht x)=
        (((∫ x : ℝ, g x*P.eval x*realKernel m hm t ht x):ℝ):ℂ) := by
    simp_rw [hgC,← realKernel_coe m hm t ht,← Complex.ofReal_mul]
    exact integral_complex_ofReal
  have h := (hW gC).symm.trans (canonical_weight_identity m hm t ht gC)
  exact Complex.ofReal_injective ((he W).symm.trans (h.trans (he (canonicalWeight m t))))

end OperatorDerivativeRewrite.Foundation.HigherHeatSteinWeight
