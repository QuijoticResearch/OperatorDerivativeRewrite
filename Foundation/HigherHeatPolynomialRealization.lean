import Foundation.HigherHeatKernelStein
import Foundation.SchwartzPolynomialPairing
import Foundation.PseudoPolynomialStein
import Foundation.PseudoClarkOconeObstruction

/-! Realization of the algebraic pure-order moments by actual signed higher-heat kernels. -/
noncomputable section
open MeasureTheory Polynomial FourierTransform
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialRealization
open HigherHeatL2 HigherHeatSignedLaws HigherHeatSpatialGenerator HigherHeatKernelStein
open GaussianSchwartzKernel SchwartzPolynomialPairing

theorem polynomial_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) :
    Integrable (fun x : ℝ => P.eval x*realKernel m hm t ht x) := by
  convert (SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => P.eval x)
    (realKernel m hm t ht)).integrable (μ := volume) using 1
  funext x
  rw [SchwartzMap.smulLeftCLM_apply (polynomial_growth P)]
  rfl

def kernelExpectation (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun P := ∫ x : ℝ, P.eval x*realKernel m hm t ht x
  map_add' P Q := by
    simp only [eval_add,add_mul]
    exact integral_add (polynomial_integrable m hm t ht P) (polynomial_integrable m hm t ht Q)
  map_smul' c P := by
    simp only [eval_smul,smul_eq_mul,RingHom.id_apply]
    simp_rw [mul_assoc]
    exact integral_const_mul c _

theorem complex_expectation (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) :
    (∫ x : ℝ, ((P.eval x:ℝ):ℂ)*evenKernel m hm t ht x)=(kernelExpectation m hm t ht P:ℂ) := by
  simp_rw [← realKernel_coe m hm t ht,← Complex.ofReal_mul]
  exact integral_complex_ofReal

theorem complex_polynomial_stein (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) :
    (∫ x : ℝ, (((X*P).eval x:ℝ):ℂ)*evenKernel m hm t ht x)=
      (2*m:ℕ)*(-1:ℂ)^(m+1)*(t:ℝ)*
        (∫ x : ℝ, (((derivative^[2*m-1] P).eval x:ℝ):ℂ)*evenKernel m hm t ht x) := by
  have ho : Odd (2*m-1) := ⟨m-1,by omega⟩
  calc
    _ = odeCoefficient m t*(∫ x : ℝ, ((P.eval x:ℝ):ℂ)*jet (2*m-1) (evenKernel m hm t ht) x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        have h := congrArg (fun f : 𝓢(ℝ,ℂ) => f x) (kernel_ode_schwartz m hm t ht)
        simp only [HigherHeatSchwartzJets.weighted_apply,SchwartzMap.smul_apply,smul_eq_mul] at h
        simp only [eval_mul,eval_X,Complex.ofReal_mul]
        linear_combination ((P.eval x:ℝ):ℂ)*h
    _ = _ := by
      rw [polynomial_jet_ibp,ho.neg_one_pow]
      unfold odeCoefficient
      ring

theorem kernelExpectation_stein (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) :
    kernelExpectation m hm t ht (X*P)=
      (2*m:ℕ)*((-1:ℝ)^(m+1)*(t:ℝ))*kernelExpectation m hm t ht (derivative^[2*m-1] P) := by
  have h := complex_polynomial_stein m hm t ht P
  rw [complex_expectation,complex_expectation] at h
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one,
    Complex.ofReal_natCast]
  convert h using 1 <;> ring

theorem kernelExpectation_one (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    kernelExpectation m hm t ht 1=1 := by
  change (∫ x : ℝ, (1:Polynomial ℝ).eval x*realKernel m hm t ht x)=1
  simpa only [eval_one,one_mul] using realKernel_integral m hm t ht

theorem kernelExpectation_eq_moments (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    kernelExpectation m hm t ht=PseudoPolynomialStein.expectation (2*m) ((-1:ℝ)^(m+1)*(t:ℝ)) := by
  exact PseudoPolynomialStein.expectation_unique (2*m) ((-1:ℝ)^(m+1)*(t:ℝ))
    (kernelExpectation m hm t ht) (kernelExpectation_one m hm t ht) (kernelExpectation_stein m hm t ht)

theorem actual_moment (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    (∫ x : ℝ, x^n*realKernel m hm t ht x)=
      PseudoPolynomialStein.moment (2*m) ((-1:ℝ)^(m+1)*(t:ℝ)) n := by
  have h := congrArg (fun E : Polynomial ℝ →ₗ[ℝ] ℝ => E (X^n)) (kernelExpectation_eq_moments m hm t ht)
  simpa only [kernelExpectation,LinearMap.coe_mk,AddHom.coe_mk,eval_pow,eval_X,
    PseudoPolynomialStein.expectation_X_pow] using h

theorem actual_off_order (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (n : ℕ)
    (hn : ¬ 2*m ∣ n) : (∫ x : ℝ, x^n*realKernel m hm t ht x)=0 := by
  rw [actual_moment]
  exact PseudoPolynomialStein.moment_off_order (2*m) (by omega) _ n hn

theorem actual_leading_moment (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    (∫ x : ℝ, x^(2*m)*realKernel m hm t ht x)=
      ((2*m).factorial:ℝ)*((-1:ℝ)^(m+1)*(t:ℝ)) := by
  rw [actual_moment,PseudoPolynomialStein.moment_leading (2*m) (by omega)]

theorem biharmonic_fourth_moment (t : ℝ≥0) (ht : 0 < t) :
    (∫ x : ℝ, x^4*realKernel 2 (by norm_num) t ht x)= -24*(t:ℝ) := by
  rw [actual_moment]
  norm_num [PseudoPolynomialStein.moment]
  ring

theorem biharmonic_eighth_moment (t : ℝ≥0) (ht : 0 < t) :
    (∫ x : ℝ, x^8*realKernel 2 (by norm_num) t ht x)=20160*(t:ℝ)^2 := by
  rw [actual_moment]
  norm_num [PseudoPolynomialStein.moment]
  ring

theorem no_actual_pth_reconstruction (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (R : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ) :
    ¬ ∀ P Q : Polynomial ℝ,
      kernelExpectation m hm t ht
        ((P-C (kernelExpectation m hm t ht P)-R (PseudoClarkOconeObstruction.pDerivative (2*m) P))*Q)=0 := by
  have ha : (-1:ℝ)^(m+1)*(t:ℝ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt (by exact_mod_cast ht))
  have h := PseudoClarkOconeObstruction.pth_derivative_reconstruction_impossible
    (2*m) (by omega) ((-1:ℝ)^(m+1)*(t:ℝ)) ha R
  simpa only [PseudoClarkOconeObstruction.pairing,PseudoClarkOconeObstruction.centered,
    kernelExpectation_eq_moments] using h

end OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialRealization
