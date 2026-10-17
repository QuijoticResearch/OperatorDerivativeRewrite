import Foundation.SchwartzPolynomialSeparation
import Foundation.HigherHeatKernelMoments
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A normalized sign-changing Schwartz kernel cannot have a polynomial first-derivative Stein weight. -/
noncomputable section
open MeasureTheory Polynomial Filter
open scoped SchwartzMap NNReal Topology Interval
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzFirstOrder
open SchwartzPolynomialSeparation HigherHeatSignedLaws

def residual (K : 𝓢(ℝ,ℝ)) (W : Polynomial ℝ) : 𝓢(ℝ,ℝ) :=
  SchwartzMap.derivCLM ℝ ℝ K+polynomialKernel W K

theorem residual_apply (K : 𝓢(ℝ,ℝ)) (W : Polynomial ℝ) (x : ℝ) :
    residual K W x=deriv K x+W.eval x*K x := by
  change (SchwartzMap.derivCLM ℝ ℝ K) x+polynomialKernel W K x=_
  rw [SchwartzMap.derivCLM_apply,polynomialKernel_apply]

theorem residual_ae_zero (K : 𝓢(ℝ,ℝ)) (W : Polynomial ℝ)
    (h : ∀ g : 𝓢(ℝ,ℝ), (∫ x : ℝ, deriv g x*K x)=(∫ x : ℝ, g x*W.eval x*K x)) :
    (residual K W : ℝ → ℝ)=ᵐ[volume] 0 := by
  apply schwartz_pairing_separates
  intro g
  have hiA : Integrable (fun x : ℝ => g x*deriv K x) := by
    convert (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) g
      (SchwartzMap.derivCLM ℝ ℝ K)).integrable (μ := volume) using 1
    funext x
    simp only [SchwartzMap.pairing_apply,ContinuousLinearMap.mul_apply',SchwartzMap.derivCLM_apply]
  have hiB : Integrable (fun x : ℝ => g x*W.eval x*K x) := by
    convert (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) g (polynomialKernel W K)).integrable
      (μ := volume) using 1
    funext x
    simp only [SchwartzMap.pairing_apply,ContinuousLinearMap.mul_apply',polynomialKernel_apply]
    ring
  calc
    _ = ∫ x : ℝ, g x*deriv K x+g x*W.eval x*K x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; rw [residual_apply]; ring
    _ = (∫ x : ℝ, g x*deriv K x)+(∫ x : ℝ, g x*W.eval x*K x) := integral_add hiA hiB
    _ = -(∫ x : ℝ, deriv g x*K x)+(∫ x : ℝ, g x*W.eval x*K x) :=
      congrArg (fun z : ℝ => z+∫ x : ℝ, g x*W.eval x*K x)
        (SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul g K)
    _ = 0 := by rw [h]; ring

theorem kernel_ode (K : 𝓢(ℝ,ℝ)) (W : Polynomial ℝ)
    (h : ∀ g : 𝓢(ℝ,ℝ), (∫ x : ℝ, deriv g x*K x)=(∫ x : ℝ, g x*W.eval x*K x)) (x : ℝ) :
    deriv K x= -W.eval x*K x := by
  have he := ((residual K W).continuous.ae_eq_iff_eq volume continuous_zero).mp (residual_ae_zero K W h)
  have hx := congrFun he x
  change residual K W x=0 at hx
  rw [residual_apply] at hx
  linarith

def primitive (W : Polynomial ℝ) (x : ℝ) : ℝ := ∫ y in (0:ℝ)..x, W.eval y

theorem primitive_hasDerivAt (W : Polynomial ℝ) (x : ℝ) : HasDerivAt (primitive W) (W.eval x) x := by
  have hc : Continuous (fun y : ℝ => W.eval y) := by fun_prop
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

def integratingFactor (K : 𝓢(ℝ,ℝ)) (W : Polynomial ℝ) (x : ℝ) : ℝ := Real.exp (primitive W x)*K x

theorem factor_hasDerivAt_zero (K : 𝓢(ℝ,ℝ)) (W : Polynomial ℝ)
    (h : ∀ g : 𝓢(ℝ,ℝ), (∫ x : ℝ, deriv g x*K x)=(∫ x : ℝ, g x*W.eval x*K x)) (x : ℝ) :
    HasDerivAt (integratingFactor K W) 0 x := by
  convert ((primitive_hasDerivAt W x).exp.mul (K.hasDerivAt x)) using 1
  · funext y
    rfl
  · rw [kernel_ode K W h]
    ring

theorem factor_constant (K : 𝓢(ℝ,ℝ)) (W : Polynomial ℝ)
    (h : ∀ g : 𝓢(ℝ,ℝ), (∫ x : ℝ, deriv g x*K x)=(∫ x : ℝ, g x*W.eval x*K x)) (x y : ℝ) :
    integratingFactor K W x=integratingFactor K W y := by
  exact is_const_of_deriv_eq_zero (fun z => (factor_hasDerivAt_zero K W h z).differentiableAt)
    (fun z => (factor_hasDerivAt_zero K W h z).deriv) x y

theorem no_opposite_signs (K : 𝓢(ℝ,ℝ)) (W : Polynomial ℝ)
    (h : ∀ g : 𝓢(ℝ,ℝ), (∫ x : ℝ, deriv g x*K x)=(∫ x : ℝ, g x*W.eval x*K x)) (x y : ℝ) :
    ¬ (K x < 0 ∧ 0 < K y) := by
  rintro ⟨hx,hy⟩
  have hn := mul_neg_of_pos_of_neg (Real.exp_pos (primitive W x)) hx
  have hp := mul_pos (Real.exp_pos (primitive W y)) hy
  have he := factor_constant K W h x y
  dsimp only [integratingFactor] at he
  linarith

theorem nonnegative_of_positive_mass (K : 𝓢(ℝ,ℝ)) (hmass : 0 < ∫ x : ℝ, K x) (W : Polynomial ℝ)
    (h : ∀ g : 𝓢(ℝ,ℝ), (∫ x : ℝ, deriv g x*K x)=(∫ x : ℝ, g x*W.eval x*K x)) : ∀ x, 0 ≤ K x := by
  have hy : ∃ y : ℝ, 0 < K y := by
    by_contra hh
    push_neg at hh
    have hn : (∫ x : ℝ, K x) ≤ 0 := integral_nonpos hh
    linarith
  obtain ⟨y,hy⟩ := hy
  intro x
  by_contra hx
  exact no_opposite_signs K W h x y ⟨lt_of_not_ge hx,hy⟩

theorem higher_heat_no_first_order_polynomial_weight (m : ℕ) (hm : 2 ≤ m) (t : ℝ≥0) (ht : 0 < t) :
    ¬ ∃ W : Polynomial ℝ, ∀ g : 𝓢(ℝ,ℝ),
      (∫ x : ℝ, deriv g x*realKernel m (by omega) t ht x)=
        (∫ x : ℝ, g x*W.eval x*realKernel m (by omega) t ht x) := by
  rintro ⟨W,h⟩
  have hn := nonnegative_of_positive_mass (realKernel m (by omega) t ht)
    (by rw [realKernel_integral]; norm_num) W h
  obtain ⟨x,hx⟩ := HigherHeatKernelMoments.exists_negative m hm t ht
  exact (not_lt_of_ge (hn x)) hx

end OperatorDerivativeRewrite.Foundation.SignedSchwartzFirstOrder
