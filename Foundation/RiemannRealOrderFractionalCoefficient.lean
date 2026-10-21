import Foundation.RiemannRealOrderFractionalZeros
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! The actual fractional asymptotic coefficient and its degeneration at order one. -/
noncomputable section
open Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalCoefficient
open RiemannRealOrderFractionalJets RiemannRealOrderFractionalFourier
open RiemannRealOrderFractionalReconstruction

def leading (a t : ℝ) : ℝ :=
  t*RiemannQuarticKernel.kernel 0*Real.Gamma (2*a+1)*Real.sin (Real.pi*(a-1))

theorem falling_gamma (a : ℝ) (ha : 1 < a) :
    falling (2*a) 3*Real.Gamma (2*a-2)=Real.Gamma (2*a+1) := by
  have h2 : Real.Gamma (2*a+1)=2*a*Real.Gamma (2*a) := Real.Gamma_add_one (by linarith)
  have h1 : Real.Gamma (2*a)=(2*a-1)*Real.Gamma (2*a-1) := by
    convert Real.Gamma_add_one (s := 2*a-1) (by linarith) using 1 <;> congr 1 <;> ring
  have h0 : Real.Gamma (2*a-1)=(2*a-2)*Real.Gamma (2*a-2) := by
    convert Real.Gamma_add_one (s := 2*a-2) (by linarith) using 1 <;> congr 1 <;> ring
  rw [h2,h1,h0]
  norm_num [falling,Finset.prod_range_succ]
  ring

theorem actual_coefficient_eq (a t : ℝ) (ha : 1 < a) :
    endpointCoefficient a t*
      ((Real.Gamma (2*a-2)*Real.sin (Real.pi*(2*a-2)/2) : ℝ) : ℂ)=(leading a t : ℂ) := by
  rw [endpointCoefficient_real,← Complex.ofReal_mul]
  congr 1
  unfold leading
  rw [show Real.pi*(2*a-2)/2=Real.pi*(a-1) by ring]
  calc
    _ = t*RiemannQuarticKernel.kernel 0*(falling (2*a) 3*Real.Gamma (2*a-2))*
        Real.sin (Real.pi*(a-1)) := by ring
    _ = _ := by rw [falling_gamma a ha]

theorem actual_flow_scaled_limit (a t : ℝ) (ha : 1 < a) (ha3 : a < 3/2) :
    Tendsto (fun x : ℝ => ((x^(2*a+1) : ℝ) : ℂ)*RiemannRealOrderFlow.flow a t (x : ℂ))
      atTop (𝓝 (leading a t : ℂ)) := by
  simpa only [actual_coefficient_eq a t ha] using
    RiemannRealOrderFractionalReconstruction.actual_flow_scaled_limit a t ha ha3

theorem leading_one (t : ℝ) : leading 1 t=0 := by simp [leading]

theorem leading_hasDerivAt_one (t : ℝ) :
    HasDerivAt (fun a : ℝ => leading a t) (2*Real.pi*t*RiemannQuarticKernel.kernel 0) 1 := by
  have hg := (Real.differentiableAt_Gamma (s := 2*(1 : ℝ)+1)
    (fun m => by have hm := Nat.cast_nonneg (α := ℝ) m; linarith)).hasDerivAt
  have hp := ((hasDerivAt_id (1 : ℝ)).const_mul 2).add_const 1
  have hgam := hg.comp (h := fun a : ℝ => 2*a+1) 1 hp
  have hs := (((hasDerivAt_id (1 : ℝ)).sub_const 1).const_mul Real.pi).sin
  have hd := (hgam.const_mul (t*RiemannQuarticKernel.kernel 0)).mul hs
  convert hd using 1
  · funext a
    rfl
  · norm_num [Function.comp_def] <;> ring

theorem leading_tendsto_zero (t : ℝ) : Tendsto (fun a : ℝ => leading a t) (𝓝 1) (𝓝 0) := by
  simpa only [leading_one] using (leading_hasDerivAt_one t).continuousAt.tendsto

theorem leading_div_order_gap_limit (t : ℝ) :
    Tendsto (fun a : ℝ => leading a t/(a-1)) (𝓝[>] 1)
      (𝓝 (2*Real.pi*t*RiemannQuarticKernel.kernel 0)) := by
  have h := (leading_hasDerivAt_one t).tendsto_slope.mono_left (nhdsGT_le_nhdsNE (1 : ℝ))
  apply h.congr'
  filter_upwards with a
  simp only [slope_def_field,leading_one,sub_zero]

theorem leading_ne_zero (a t : ℝ) (ha : 1 < a) (ha2 : a < 2) (ht : t ≠ 0) :
    leading a t ≠ 0 := by
  have hk := RiemannQuarticKernel.kernel_pos 0 (by norm_num)
  have hg := Real.Gamma_pos_of_pos (show 0 < 2*a+1 by linarith)
  have hs : 0 < Real.sin (Real.pi*(a-1)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos (by linarith)
    · nlinarith [Real.pi_pos]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero ht hk.ne') hg.ne') hs.ne'

theorem pointwise_relative_asymptotic (a t : ℝ) (ha : 1 < a) (ha3 : a < 3/2) (ht : t ≠ 0) :
    Tendsto (fun x : ℝ => (((x^(2*a+1) : ℝ) : ℂ)*
      RiemannRealOrderFlow.flow a t (x : ℂ))/(leading a t : ℂ)) atTop (𝓝 1) := by
  have h := (actual_flow_scaled_limit a t ha ha3).div_const (leading a t : ℂ)
  simpa only [div_self (Complex.ofReal_ne_zero.mpr (leading_ne_zero a t ha (by linarith) ht))]
    using h

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalCoefficient
