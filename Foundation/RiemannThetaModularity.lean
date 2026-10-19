import Foundation.RiemannThetaDifferentiation

/-! The actual modular reflection and endpoint derivative needed by the
arithmetic Fourier/Mellin bridge. -/
noncomputable section
open MeasureTheory Filter Set Real
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannThetaModularity
open RiemannQuarticKernel RiemannThetaDifferentiation

theorem cosKernel_eq_thetaMoment (v : ℝ) (hv : 0 < v) :
    HurwitzZeta.cosKernel 0 v = 1+2*thetaMoment 0 v := by
  have h := thetaMoment_zero_eq_cosKernel v hv
  linarith

theorem psi_reflection (u : ℝ) : psi u-psi (-u) = (exp (-u)-exp u)/2 := by
  have h := HurwitzZeta.evenKernel_functional_equation 0 (exp (4*u))
  rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at h
  have hp : exp (4*u)^(1/2 : ℝ) = exp (2*u) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hi : 1/exp (4*u) = exp (4*(-u)) := by
    rw [one_div, ← exp_neg]
    congr 1
    ring
  rw [hp, hi, cosKernel_eq_thetaMoment _ (exp_pos _),
    cosKernel_eq_thetaMoment _ (exp_pos _)] at h
  have hm : exp u*(1/exp (2*u)) = exp (-u) := by
    rw [one_div, ← exp_neg, ← exp_add]
    congr 1
    ring
  have hh := congrArg (fun x : ℝ => exp u*x) h
  rw [← mul_assoc, hm] at hh
  unfold psi
  linarith

theorem psiPrime_zero : psiPrime 0 = -1/2 := by
  have hl := (psi_hasDerivAt 0).sub
    ((psi_hasDerivAt (-0)).comp 0 (hasDerivAt_neg (0 : ℝ)))
  have hr := ((((hasDerivAt_neg (0 : ℝ)).exp).sub (Real.hasDerivAt_exp 0))).div_const 2
  have he : (fun u : ℝ => psi u-psi (-u)) =
      (fun u : ℝ => (exp (-u)-exp u)/2) := funext psi_reflection
  change HasDerivAt (fun u : ℝ => psi u-psi (-u)) _ 0 at hl
  rw [he] at hl
  have hh := hl.unique hr
  norm_num at hh
  linarith

theorem psi_derivative_zero : deriv psi 0 = -1/2 := by
  rw [(psi_hasDerivAt 0).deriv, psiPrime_zero]

end OperatorDerivativeRewrite.Foundation.RiemannThetaModularity
