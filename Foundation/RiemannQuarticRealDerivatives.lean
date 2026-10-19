import Foundation.RiemannQuarticRealCertificate
import Foundation.RiemannQuarticReality
import Mathlib.Analysis.Complex.RealDeriv

/-! Identify every real derivative of the actual cosine transform with the
real part of its holomorphic derivative. No finite cutoff is used. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticRealDerivatives
open RiemannQuarticFlow RiemannQuarticEvolution RiemannQuarticReality
open RiemannQuarticRealCertificate

theorem realFlow_iteratedDeriv (n : ℕ) (t : ℝ) :
    iteratedDeriv n (realFlow t)=fun x : ℝ => (symmetricJet n t (x : ℂ)).re := by
  induction n with
  | zero =>
    funext x
    simp only [iteratedDeriv_zero, symmetricJet_zero, flow_real, Complex.ofReal_re]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (symmetricJet_hasDerivAt n t (x : ℂ)).real_of_complex.deriv

theorem realFlow_complex_derivative_re (n : ℕ) (t x : ℝ) :
    iteratedDeriv n (realFlow t) x=(iteratedDeriv n (flow t) (x : ℂ)).re := by
  rw [realFlow_iteratedDeriv, flow_iteratedDeriv]

theorem actualJet_eq_real_derivative (n : ℕ) (x : ℝ) :
    actualJet n x=iteratedDeriv n (realFlow 8) x :=
  (realFlow_complex_derivative_re n 8 x).symm

theorem realLaguerre_eq (x : ℝ) :
    realLaguerre x=(deriv (realFlow 8) x)^2-
      realFlow 8 x*iteratedDeriv 2 (realFlow 8) x := by
  simp only [realLaguerre, actualJet_eq_real_derivative, iteratedDeriv_zero,
    iteratedDeriv_one]

theorem real_fourth_order_heat_equation (t x : ℝ) :
    HasDerivAt (fun s : ℝ => realFlow s x) (iteratedDeriv 4 (realFlow t) x) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (fourth_order_heat_equation t (x : ℂ))
  simpa only [Function.comp_def, Complex.reCLM_apply, flow_real, Complex.ofReal_re,
    ← realFlow_complex_derivative_re] using h

end OperatorDerivativeRewrite.Foundation.RiemannQuarticRealDerivatives
