import Foundation.SchwartzPolynomialPairing
import Mathlib.Algebra.Polynomial.Roots

/-! Schwartz tests determine polynomial weights even for a signed Schwartz kernel. -/
noncomputable section
open MeasureTheory Polynomial Filter
open scoped SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.SchwartzPolynomialSeparation
open SchwartzPolynomialPairing

def polynomialKernel (P : Polynomial ℝ) (K : 𝓢(ℝ,ℝ)) : 𝓢(ℝ,ℝ) :=
  SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => P.eval x) K

theorem polynomialKernel_apply (P : Polynomial ℝ) (K : 𝓢(ℝ,ℝ)) (x : ℝ) :
    polynomialKernel P K x=P.eval x*K x := by
  rw [polynomialKernel,SchwartzMap.smulLeftCLM_apply (polynomial_growth P)]
  rfl

theorem schwartz_pairing_separates (f : 𝓢(ℝ,ℝ))
    (h : ∀ g : 𝓢(ℝ,ℝ), (∫ x : ℝ, g x*f x)=0) : (f : ℝ → ℝ)=ᵐ[volume] 0 := by
  have hi : Integrable (fun x : ℝ => f x*f x) := by
    convert (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f f).integrable (μ := volume) using 1
    funext x
    rfl
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun x : ℝ => mul_self_nonneg (f x)) hi).mp (h f)
  filter_upwards [hz] with x hx
  exact mul_self_eq_zero.mp hx

theorem eval_ne_zero_ae (P : Polynomial ℝ) (hP : P ≠ 0) : ∀ᵐ x : ℝ ∂volume, P.eval x ≠ 0 := by
  have hf : Set.Finite {x : ℝ | P.eval x=0} := finite_setOfPred_isRoot hP
  have hm : volume {x : ℝ | P.eval x=0}=0 := hf.measure_zero volume
  rw [ae_iff]
  simpa only [not_not] using hm

theorem annihilator_zero (K : 𝓢(ℝ,ℝ)) (hK : (∫ x : ℝ, K x) ≠ 0) (P : Polynomial ℝ)
    (h : ∀ g : 𝓢(ℝ,ℝ), (∫ x : ℝ, g x*P.eval x*K x)=0) : P=0 := by
  have hz : (polynomialKernel P K : ℝ → ℝ)=ᵐ[volume] 0 := by
    apply schwartz_pairing_separates
    intro g
    have hh := h g
    simpa only [polynomialKernel_apply,mul_assoc] using hh
  by_contra hP
  have hKzero : (K : ℝ → ℝ)=ᵐ[volume] 0 := by
    filter_upwards [hz,eval_ne_zero_ae P hP] with x hx hp
    change polynomialKernel P K x=0 at hx
    rw [polynomialKernel_apply] at hx
    exact (mul_eq_zero.mp hx).resolve_left hp
  apply hK
  rw [integral_congr_ae hKzero]
  simp

theorem polynomial_weight_unique (K : 𝓢(ℝ,ℝ)) (hK : (∫ x : ℝ, K x) ≠ 0)
    (P Q : Polynomial ℝ)
    (h : ∀ g : 𝓢(ℝ,ℝ), (∫ x : ℝ, g x*P.eval x*K x)=(∫ x : ℝ, g x*Q.eval x*K x)) : P=Q := by
  apply sub_eq_zero.mp
  apply annihilator_zero K hK (P-Q)
  intro g
  have hi (A : Polynomial ℝ) : Integrable (fun x : ℝ => g x*A.eval x*K x) := by
    convert (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) g (polynomialKernel A K)).integrable
      (μ := volume) using 1
    funext x
    simp only [SchwartzMap.pairing_apply,ContinuousLinearMap.mul_apply',polynomialKernel_apply]
    ring
  calc
    _ = ∫ x : ℝ, g x*P.eval x*K x-g x*Q.eval x*K x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp only [eval_sub]; ring
    _ = (∫ x : ℝ, g x*P.eval x*K x)-(∫ x : ℝ, g x*Q.eval x*K x) := integral_sub (hi P) (hi Q)
    _ = 0 := sub_eq_zero.mpr (h g)

end OperatorDerivativeRewrite.Foundation.SchwartzPolynomialSeparation
