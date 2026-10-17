import Foundation.HigherHeatSchwartzJets
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Polynomial tests against actual Schwartz kernels without a polynomial-density assumption. -/
noncomputable section
open MeasureTheory FourierTransform Polynomial
open scoped SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.SchwartzPolynomialPairing
open HigherHeatSpatialGenerator HigherHeatSchwartzJets

theorem polynomial_growth (P : Polynomial ℝ) : (fun x : ℝ => P.eval x).HasTemperateGrowth := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have he : (fun x : ℝ => (P+Q).eval x)=((fun x : ℝ => P.eval x)+(fun x : ℝ => Q.eval x)) := by
      funext x
      exact eval_add
    rw [he]
    exact hP.add hQ
  | monomial n a => simp only [eval_monomial]; fun_prop

def weightedPolynomial (P : Polynomial ℝ) (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => P.eval x) f

theorem weighted_apply (P : Polynomial ℝ) (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    weightedPolynomial P f x=((P.eval x:ℝ):ℂ)*f x := by
  rw [weightedPolynomial,SchwartzMap.smulLeftCLM_apply (polynomial_growth P)]
  exact Complex.real_smul

theorem weighted_integrable (P : Polynomial ℝ) (f : 𝓢(ℝ,ℂ)) :
    Integrable (fun x : ℝ => ((P.eval x:ℝ):ℂ)*f x) := by
  convert (weightedPolynomial P f).integrable (μ := volume) using 1
  funext x
  exact (weighted_apply P f x).symm

theorem integral_deriv_zero (f : 𝓢(ℝ,ℂ)) : (∫ x : ℝ, deriv f x)=0 := by
  have h := jet_fourier 1 f 0
  rw [SchwartzMap.fourier_coe,Real.fourier_eq] at h
  simpa only [inner_zero_right,neg_zero,AddChar.map_zero_eq_one,one_smul,mul_zero,
    Complex.ofReal_zero,zero_pow (by norm_num : (1:ℕ) ≠ 0),zero_mul,jet,
    SchwartzMap.derivCLM_apply] using h

theorem weighted_deriv (P : Polynomial ℝ) (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    deriv (weightedPolynomial P f) x=((P.derivative.eval x:ℝ):ℂ)*f x+((P.eval x:ℝ):ℂ)*deriv f x := by
  have he : (weightedPolynomial P f : ℝ → ℂ)=(fun y : ℝ => ((P.eval y:ℝ):ℂ)*f y) := by
    funext y
    exact weighted_apply P f y
  rw [he]
  exact (((P.hasDerivAt x).ofReal_comp).mul (f.hasDerivAt x)).deriv

theorem polynomial_ibp (P : Polynomial ℝ) (f : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, ((P.eval x:ℝ):ℂ)*deriv f x)= -(∫ x : ℝ, ((P.derivative.eval x:ℝ):ℂ)*f x) := by
  have hi1 := weighted_integrable P.derivative f
  have hi2 := weighted_integrable P (SchwartzMap.derivCLM ℂ ℂ f)
  have ha : (∫ x : ℝ, deriv (weightedPolynomial P f) x)=
      (∫ x : ℝ, ((P.derivative.eval x:ℝ):ℂ)*f x)+(∫ x : ℝ, ((P.eval x:ℝ):ℂ)*deriv f x) := by
    calc
      _ = ∫ x : ℝ, ((P.derivative.eval x:ℝ):ℂ)*f x+((P.eval x:ℝ):ℂ)*deriv f x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => weighted_deriv P f x
      _ = _ := integral_add hi1 hi2
  rw [integral_deriv_zero] at ha
  linear_combination -ha

theorem polynomial_jet_ibp (k : ℕ) (P : Polynomial ℝ) (f : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, ((P.eval x:ℝ):ℂ)*jet k f x)=
      (-1:ℂ)^k*(∫ x : ℝ, (((derivative^[k] P).eval x:ℝ):ℂ)*f x) := by
  induction k generalizing P with
  | zero => simp [jet]
  | succ k ih =>
    change (∫ x : ℝ, ((P.eval x:ℝ):ℂ)*deriv (jet k f) x)=_
    rw [polynomial_ibp,ih]
    rw [Function.iterate_succ_apply,pow_succ]
    ring

end OperatorDerivativeRewrite.Foundation.SchwartzPolynomialPairing
