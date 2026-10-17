import Foundation.HigherHeatPolynomialRealization
import Foundation.SignedAbsoluteIntegration

/-! Unbounded polynomial observables integrated against the actual finite signed heat law. -/
noncomputable section
open MeasureTheory Polynomial Filter
open scoped NNReal Topology SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSignedPolynomialCalculus
open HigherHeatSignedLaws HigherHeatPolynomialRealization GaussianSchwartzKernel
open SignedAbsoluteIntegration

theorem polynomial_absolute_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) :
    Integrable (fun x : ℝ => ((P.eval x:ℝ):ℂ))
      (absoluteDensity volume (realKernel m hm t ht)) := by
  apply (absolute_integrable_iff volume (realKernel m hm t ht)
    (realKernel m hm t ht).continuous.measurable _).mpr
  refine (polynomial_integrable m hm t ht P).norm.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · exact Eventually.of_forall fun x => by
      simp only [norm_smul,Real.norm_eq_abs,abs_abs,Complex.norm_real,abs_mul]
      rw [mul_comm]

theorem polynomial_signed_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) :
    (law m hm t ht).Integrable (fun x : ℝ => ((P.eval x:ℝ):ℂ)) := by
  exact (signed_integrable_iff volume (realKernel m hm t ht)
    (realKernel m hm t ht).integrable _).mpr (polynomial_absolute_integrable m hm t ht P)

theorem signed_polynomial_integral (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) :
    (∫ᵛ x : ℝ, ((P.eval x:ℝ):ℂ) ∂<•law m hm t ht)=(kernelExpectation m hm t ht P:ℂ) := by
  rw [law,SignedAbsoluteIntegration.integral_density volume _
    (realKernel m hm t ht).integrable (realKernel m hm t ht).continuous.measurable _
    (polynomial_absolute_integrable m hm t ht P)]
  calc
    _ = ∫ x : ℝ, ((P.eval x:ℝ):ℂ)*evenKernel m hm t ht x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← realKernel_coe m hm t ht]
        simp only [Complex.real_smul]
        ring
    _ = _ := complex_expectation m hm t ht P

theorem signed_moment (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    (∫ᵛ x : ℝ, (x:ℂ)^n ∂<•law m hm t ht)=
      (PseudoPolynomialStein.moment (2*m) ((-1:ℝ)^(m+1)*(t:ℝ)) n:ℂ) := by
  have h := signed_polynomial_integral m hm t ht (X^n)
  rw [kernelExpectation_eq_moments,PseudoPolynomialStein.expectation_X_pow] at h
  simpa only [eval_pow,eval_X,Complex.ofReal_pow] using h

theorem signed_polynomial_stein (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (P : Polynomial ℝ) :
    (∫ᵛ x : ℝ, ((((X*P).eval x):ℝ):ℂ) ∂<•law m hm t ht)=
      (2*m:ℕ)*(-1:ℂ)^(m+1)*(t:ℝ)*
        (∫ᵛ x : ℝ, ((((derivative^[2*m-1] P).eval x):ℝ):ℂ) ∂<•law m hm t ht) := by
  rw [signed_polynomial_integral,signed_polynomial_integral]
  have h := complex_polynomial_stein m hm t ht P
  rw [complex_expectation,complex_expectation] at h
  exact h

theorem biharmonic_signed_fourth (t : ℝ≥0) (ht : 0 < t) :
    (∫ᵛ x : ℝ, (x:ℂ)^4 ∂<•law 2 (by norm_num) t ht)= -24*(t:ℝ) := by
  rw [signed_moment]
  norm_num [PseudoPolynomialStein.moment]
  ring

end OperatorDerivativeRewrite.Foundation.HigherHeatSignedPolynomialCalculus
