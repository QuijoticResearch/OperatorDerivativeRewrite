import Foundation.RiemannRealOrderFractionalCoefficient

/-! Actual signed cutoff mass at the quadratic endpoint.
All integrals below are over the positive real half-line with Lebesgue measure. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderCutoffBoundary
open RiemannThetaComplexKernel RiemannRealOrderFractionalJets
open RiemannRealOrderFractionalCoefficient RiemannRealOrderFractionalRemainder

/-- The cutoff mass formula for a>1, extended to its limiting value at a=1. -/
def mass (a t : ℝ) : ℝ := t*RiemannQuarticKernel.kernel 0*Real.Gamma (2*a+1)

theorem cutoff_real (a t u : ℝ) (hu : 0 ≤ u) :
    cutoff a t u=((t*falling (2*a) 3*RiemannQuarticKernel.kernel 0*
      u^(2*a-3)*Real.exp (-u) : ℝ) : ℂ) := by
  have hk := kernelComplex_real 0
  simp only [Complex.ofReal_zero] at hk
  rw [cutoff,phaseJet_real a t u 3 hu,hk]
  norm_num only [Nat.cast_ofNat]
  push_cast
  ring

theorem cutoff_norm (a t u : ℝ) (hu : 0 ≤ u) :
    ‖cutoff a t u‖=|t*falling (2*a) 3*RiemannQuarticKernel.kernel 0| *
      u^(2*a-3)*Real.exp (-u) := by
  rw [cutoff_real a t u hu,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hu _),abs_of_pos (Real.exp_pos _)]

theorem cutoff_integral (a t : ℝ) (ha : 1 < a) :
    (∫ u : ℝ in Ioi 0, cutoff a t u)=(mass a t : ℂ) := by
  have hb : 0 < 2*a-2 := by linarith
  have hreal : (∫ u : ℝ in Ioi 0, u^(2*a-3)*Real.exp (-u))=Real.Gamma (2*a-2) := by
    rw [Real.Gamma_eq_integral hb]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    rw [show 2*a-2-1=2*a-3 by ring]
    ring
  calc
    _ = ((t*falling (2*a) 3*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ)*
        ((∫ u : ℝ in Ioi 0, u^(2*a-3)*Real.exp (-u) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal,← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      rw [cutoff_real a t u hu.le]
      push_cast
      ring
    _ = _ := by
      rw [hreal,← Complex.ofReal_mul]
      congr 1
      unfold mass
      calc
        _ = t*RiemannQuarticKernel.kernel 0*(falling (2*a) 3*Real.Gamma (2*a-2)) := by ring
        _ = _ := by rw [falling_gamma a ha]

theorem cutoff_norm_integral (a t : ℝ) (ha : 1 < a) :
    (∫ u : ℝ in Ioi 0, ‖cutoff a t u‖)=|mass a t| := by
  have hb : 0 < 2*a-2 := by linarith
  have hG := Real.Gamma_pos_of_pos hb
  calc
    _ = |t*falling (2*a) 3*RiemannQuarticKernel.kernel 0| * Real.Gamma (2*a-2) := by
      rw [Real.Gamma_eq_integral hb,← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      change ‖cutoff a t u‖ = _
      rw [cutoff_norm a t u hu.le,show 2*a-2-1=2*a-3 by ring]
      ring
    _ = |(t*falling (2*a) 3*RiemannQuarticKernel.kernel 0)*Real.Gamma (2*a-2)| := by
      simp only [abs_mul,abs_of_pos hG]
    _ = _ := by
      congr 1
      unfold mass
      calc
        _ = t*RiemannQuarticKernel.kernel 0*(falling (2*a) 3*Real.Gamma (2*a-2)) := by ring
        _ = _ := by rw [falling_gamma a ha]

theorem cutoff_norm_moment_integrable (a t : ℝ) (ha : 1 < a) :
    IntegrableOn (fun u : ℝ => u*‖cutoff a t u‖) (Ioi 0) := by
  have hi := (FractionalEndpointLaplace.majorant_integrable (2*a-1) 1 (by linarith)
    (by norm_num)).const_mul |t*falling (2*a) 3*RiemannQuarticKernel.kernel 0|
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [cutoff_norm a t u hu.le]
  have hr : u^(2*a-2)=u*u^(2*a-3) := by
    rw [show 2*a-2=1+(2*a-3) by ring,Real.rpow_add hu,Real.rpow_one]
  rw [show 2*a-1-1=2*a-2 by ring,hr]
  norm_num only [neg_one_mul]
  ring

theorem cutoff_norm_first_moment (a t : ℝ) (ha : 1 < a) :
    (∫ u : ℝ in Ioi 0, u*‖cutoff a t u‖)=(2*a-2)*|mass a t| := by
  have hb : 0 < 2*a-2 := by linarith
  have hG : Real.Gamma (2*a-1)=(2*a-2)*Real.Gamma (2*a-2) := by
    convert Real.Gamma_add_one (s := 2*a-2) hb.ne' using 1 <;> congr 1 <;> ring
  calc
    _ = |t*falling (2*a) 3*RiemannQuarticKernel.kernel 0| * Real.Gamma (2*a-1) := by
      rw [Real.Gamma_eq_integral (show 0 < 2*a-1 by linarith),← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      change u*‖cutoff a t u‖ = _
      rw [cutoff_norm a t u hu.le]
      have hr : u^(2*a-1-1)=u*u^(2*a-3) := by
        rw [show 2*a-1-1=1+(2*a-3) by ring,Real.rpow_add hu,Real.rpow_one]
      dsimp only
      rw [hr]
      ring
    _ = (2*a-2)*(∫ u : ℝ in Ioi 0, ‖cutoff a t u‖) := by
      rw [hG,cutoff_norm_integral a t ha]
      have hm : |mass a t|=|t*falling (2*a) 3*RiemannQuarticKernel.kernel 0| * Real.Gamma (2*a-2) := by
        rw [← abs_of_pos (Real.Gamma_pos_of_pos hb),← abs_mul]
        congr 1
        symm
        unfold mass
        calc
          _ = t*RiemannQuarticKernel.kernel 0*(falling (2*a) 3*Real.Gamma (2*a-2)) := by ring
          _ = _ := by rw [falling_gamma a ha]
      rw [hm]
      ring
    _ = _ := by rw [cutoff_norm_integral a t ha]

theorem mass_one (t : ℝ) : mass 1 t=2*t*RiemannQuarticKernel.kernel 0 := by
  norm_num [mass]
  ring

theorem mass_continuousAt_one (t : ℝ) : ContinuousAt (fun a : ℝ => mass a t) 1 := by
  have hg := (Real.differentiableAt_Gamma (s := 2*(1 : ℝ)+1)
    (fun m => by have hm := Nat.cast_nonneg (α := ℝ) m; linarith)).continuousAt
  have hc := hg.comp (f := fun a : ℝ => 2*a+1) (by fun_prop)
  exact continuousAt_const.mul hc

theorem cutoff_integral_tendsto (t : ℝ) :
    Tendsto (fun a : ℝ => ∫ u : ℝ in Ioi 0, cutoff a t u) (𝓝[>] 1)
      (𝓝 ((2*t*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ)) := by
  have h := (Complex.continuous_ofReal.continuousAt.comp (mass_continuousAt_one t)).tendsto
  have hh : Tendsto (fun a : ℝ => (mass a t : ℂ)) (𝓝[>] 1)
      (𝓝 ((2*t*RiemannQuarticKernel.kernel 0 : ℝ) : ℂ)) := by
    simpa only [Function.comp_def,mass_one] using h.mono_left nhdsWithin_le_nhds
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (cutoff_integral a t ha).symm

theorem cutoff_norm_integral_tendsto (t : ℝ) :
    Tendsto (fun a : ℝ => ∫ u : ℝ in Ioi 0, ‖cutoff a t u‖) (𝓝[>] 1)
      (𝓝 |2*t*RiemannQuarticKernel.kernel 0|) := by
  have h := (mass_continuousAt_one t).abs.tendsto
  have hh : Tendsto (fun a : ℝ => |mass a t|) (𝓝[>] 1)
      (𝓝 |2*t*RiemannQuarticKernel.kernel 0|) := by
    simpa only [mass_one] using h.mono_left nhdsWithin_le_nhds
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (cutoff_norm_integral a t ha).symm

theorem cutoff_first_moment_tendsto_zero (t : ℝ) :
    Tendsto (fun a : ℝ => ∫ u : ℝ in Ioi 0, u*‖cutoff a t u‖) (𝓝[>] 1) (𝓝 0) := by
  have hm := (mass_continuousAt_one t).abs.tendsto.mono_left
    (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  have hb : Tendsto (fun a : ℝ => 2*a-2) (𝓝[>] 1) (𝓝 0) := by
    simpa using (show ContinuousAt (fun a : ℝ => 2*a-2) 1 by fun_prop).tendsto.mono_left
      (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply (show Tendsto (fun a : ℝ => (2*a-2)*|mass a t|) (𝓝[>] 1) (𝓝 0) by
    simpa only [zero_mul] using hb.mul hm).congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (cutoff_norm_first_moment a t ha).symm

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderCutoffBoundary
