import Foundation.RiemannThetaMellin

/-! Normalization of the actual arithmetic cosine transform against Mathlib's
completed Riemann zeta, with the poles canceled in the entire definition. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannXiNormalization
open RiemannQuarticKernel RiemannThetaDifferentiation RiemannThetaModularity
open RiemannThetaDecay RiemannThetaCosine RiemannThetaMellin
open RiemannQuarticFlow RiemannQuarticReality

theorem lambda_zero_critical_integral (x : ℝ) :
    pair.Λ₀ ((1 : ℂ)/4+Complex.I*(x : ℂ)/4) = (16*primitiveCosine x : ℝ) := by
  let s : ℂ := 1/4+Complex.I*(x : ℂ)/4
  let L := logIntegrand s
  have hi := logIntegrand_integrable s
  have hn := hi.comp_neg.integrableOn (s := Ioi (0 : ℝ))
  have hp := hi.integrableOn (s := Ioi (0 : ℝ))
  rw [lambda_zero_log_integral]
  change (∫ w, L w) = _
  have hsplit : (∫ w, L w) = ∫ w in Ioi (0 : ℝ), L w+L (-w) := by
    rw [integral_add hp hn, integral_comp_neg_Ioi, neg_zero, add_comm]
    exact (intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hp).symm
  rw [hsplit]
  have he : (∫ w in Ioi (0 : ℝ), L w+L (-w)) =
      ∫ w in Ioi (0 : ℝ), ((4*Real.exp (w/4)*thetaMoment 0 (Real.exp w)*
        Real.cos (x*w/4) : ℝ) : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w hw
    exact logIntegrand_pair x w hw
  rw [he]
  let g : ℝ → ℂ := fun w => (4*Real.exp (w/4)*thetaMoment 0 (Real.exp w)*
    Real.cos (x*w/4) : ℝ)
  have hscale : (4 : ℝ) • (∫ u in Ioi (0 : ℝ), g (4*u)) = ∫ w in Ioi (0 : ℝ), g w := by
    simpa only [mul_zero] using! integral_comp_mul_left_Ioi' g 0 (b := 4) (by norm_num)
  change (∫ w in Ioi (0 : ℝ), g w) = _
  rw [← hscale]
  have hg : (fun u : ℝ => g (4*u)) =
      (fun u : ℝ => ((4*(psi u*Real.cos (x*u)) : ℝ) : ℂ)) := by
    funext u
    dsimp [g, psi]
    rw [show (4*u)/4=u by ring, show x*(4*u)/4=x*u by ring]
    push_cast
    ring
  rw [hg]
  have hcast : (∫ u in Ioi (0 : ℝ), ((4*(psi u*Real.cos (x*u)) : ℝ) : ℂ)) =
      ((∫ u in Ioi (0 : ℝ), 4*(psi u*Real.cos (x*u))) : ℝ) := by
    simpa using! (integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun u => 4*(psi u*Real.cos (x*u))))
  rw [hcast, integral_const_mul]
  rw [Complex.real_smul]
  change ((4 : ℝ) : ℂ)*(4*(∫ u in Ioi (0 : ℝ), psi u*Real.cos (x*u)) : ℝ) = _
  unfold primitiveCosine
  rw [integral_Ici_eq_integral_Ioi]
  push_cast
  ring

theorem completed_zero_critical_integral (x : ℝ) :
    completedRiemannZeta₀ ((1 : ℂ)/2+Complex.I*(x : ℂ)/2) =
      (8*primitiveCosine x : ℝ) := by
  change pair.Λ₀ (((1 : ℂ)/2+Complex.I*(x : ℂ)/2)/2)/2 = _
  rw [show (((1 : ℂ)/2+Complex.I*(x : ℂ)/2)/2)=1/4+Complex.I*(x : ℂ)/4 by ring,
    lambda_zero_critical_integral]
  push_cast
  ring

def entireXi (s : ℂ) : ℂ := (s*(s-1)*completedRiemannZeta₀ s+1)/2

theorem entireXi_differentiable : Differentiable ℂ entireXi := by
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).div_const 2

theorem entireXi_eq_completed (s : ℂ) (hs : s ≠ 0) (hs1 : s ≠ 1) :
    entireXi s = s*(s-1)*completedRiemannZeta s/2 := by
  rw [completedRiemannZeta_eq]
  unfold entireXi
  field_simp
  <;> ring

theorem realFlow_zero_eq_entireXi (x : ℝ) :
    (realFlow 0 x : ℂ) = entireXi ((1 : ℂ)/2+Complex.I*(x : ℂ)/2)/8 := by
  rw [realFlow_zero_eq_primitive]
  unfold entireXi
  rw [completed_zero_critical_integral]
  push_cast
  have hquad : ((1 : ℂ)/2+Complex.I*(x : ℂ)/2)*
      (((1 : ℂ)/2+Complex.I*(x : ℂ)/2)-1) = -(1+(x : ℂ)^2)/4 := by
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hquad]
  ring

theorem flow_zero_real_eq_entireXi (x : ℝ) :
    flow 0 (x : ℂ) = entireXi ((1 : ℂ)/2+Complex.I*(x : ℂ)/2)/8 := by
  rw [flow_real]
  exact realFlow_zero_eq_entireXi x

end OperatorDerivativeRewrite.Foundation.RiemannXiNormalization
