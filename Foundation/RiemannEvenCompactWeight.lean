import Foundation.RiemannEvenWeightEnvelope
import Foundation.RiemannThetaSmallParameter
/-! Compact horizontal bounds for the literal integer-even weights.
The norm-based power bound keeps all mixed terms rather than using the
quartic-only inequality for the real part of the phase. -/
noncomputable section
open Set Metric Complex MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenCompactWeight
open RiemannEvenComplexWeight RiemannThetaComplexKernel RiemannThetaSmallParameter
open RiemannThetaDerivativeBounds

theorem horizontal_power_real_bound (m : ℕ) (s h L : ℝ) (hs : 0 ≤ s) (hsL : s ≤ L) :
    (((s : ℂ)+(h : ℂ)*Complex.I)^(2*m)).re ≤ (L^2+h^2)^m := by
  let q := (s : ℂ)+(h : ℂ)*Complex.I
  have hn : ‖q‖^2 = s^2+h^2 := by
    rw [Complex.sq_norm]
    simp [q,Complex.normSq_apply,pow_two]
  have hsq : s^2 ≤ L^2 := by nlinarith
  calc
    _ ≤ ‖q^(2*m)‖ := Complex.re_le_norm _
    _ = (s^2+h^2)^m := by rw [norm_pow,pow_mul,hn]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) _

theorem compact_weight_bound (m : ℕ) (t : ℝ) (ht : 0 ≤ t) (z : ℂ) (h L s : ℝ)
    (hh : 0 < Real.cos (4*h)) (hs0 : 0 ≤ s) (hsL : s ≤ L) :
    ‖weight m t z ((s : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      (528/Real.cos (4*h)^3)*Real.exp (t*(L^2+h^2)^m-z.re*h+|z.im| *L) := by
  let q := (s : ℂ)+(h : ℂ)*Complex.I
  have hker := kernel_horizontal_margin_bound s h hs0 hh
  have hconst : 0 ≤ 528/Real.cos (4*h)^3 := by positivity
  have hk : ‖kernelComplex q‖ ≤ 528/Real.cos (4*h)^3 := by
    have he : Real.exp (-3*s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact hker.trans (by nlinarith)
  have hphase : ((t : ℂ)*q^(2*m)+Complex.I*z*q).re =
      t*(q^(2*m)).re-z.re*h-z.im*s := by
    simp [q,Complex.mul_re,Complex.mul_im]
    ring
  have hp := mul_le_mul_of_nonneg_left (horizontal_power_real_bound m s h L hs0 hsL) ht
  have hlin1 := mul_le_mul_of_nonneg_right (neg_le_abs z.im) hs0
  have hlin2 := mul_le_mul_of_nonneg_left hsL (abs_nonneg z.im)
  have hle : ((t : ℂ)*q^(2*m)+Complex.I*z*q).re ≤
      t*(L^2+h^2)^m-z.re*h+|z.im| *L := by rw [hphase]; linarith
  rw [weight,norm_mul,Complex.norm_exp]
  exact (mul_le_mul (Real.exp_le_exp.mpr hle) hk (norm_nonneg _) (Real.exp_pos _).le).trans_eq
    (by ring)

theorem compact_signed_bound (m : ℕ) (t : ℝ) (ht : 0 ≤ t) (z : ℂ) (h L : ℝ)
    (hh : 0 < Real.cos (4*h)) (hL : 0 ≤ L) :
    IntervalIntegrable (fun s : ℝ => weight m t z ((s : ℂ)+(h : ℂ)*Complex.I)) volume 0 L ∧
    ‖∫ s : ℝ in 0..L, weight m t z ((s : ℂ)+(h : ℂ)*Complex.I)‖ ≤
      (528*L/Real.cos (4*h)^3)*Real.exp (t*(L^2+h^2)^m-z.re*h+|z.im| *L) := by
  have hc : Continuous (fun s : ℝ => weight m t z ((s : ℂ)+(h : ℂ)*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    let q := (s : ℂ)+(h : ℂ)*Complex.I
    have hE : (Complex.exp (4*q)).re=Real.exp (4*s)*Real.cos (4*h) := by
      simp [q,Complex.exp_re,Complex.mul_re,Complex.mul_im]
    have hk := kernelComplex_analyticAt q (by rw [hE]; positivity)
    have hw : AnalyticAt ℂ (weight m t z) q := by
      unfold weight
      apply AnalyticAt.mul
      · fun_prop
      · exact hk
    exact ContinuousAt.comp (g := weight m t z)
      (f := fun s : ℝ => (s : ℂ)+(h : ℂ)*Complex.I) hw.continuousAt (by fun_prop)
  refine ⟨hc.intervalIntegrable 0 L,?_⟩
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := L) (f := fun s : ℝ => weight m t z ((s : ℂ)+(h : ℂ)*Complex.I))
    (C := (528/Real.cos (4*h)^3)*Real.exp (t*(L^2+h^2)^m-z.re*h+|z.im| *L)) ?_
  · rw [sub_zero,abs_of_nonneg hL] at hb
    exact hb.trans_eq (by ring)
  · intro s hs
    rw [uIoc_of_le hL] at hs
    exact compact_weight_bound m t ht z h L s hh hs.1.le hs.2

theorem center_weight_lower (m : ℕ) (t : ℝ) (z v : ℂ) (hv : 0 ≤ v.re)
    (hE : 1 ≤ (Complex.exp (4*v)).re) :
    Real.exp (((t : ℂ)*v^(2*m)+Complex.I*z*v).re+9*v.re-
      Real.pi*(Complex.exp (4*v)).re) ≤ ‖weight m t z v‖ := by
  have hk := kernel_norm_lower v hv hE
  have hcoef : 1 ≤ (21/8 : ℝ)*Real.pi := by linarith [Real.pi_gt_three]
  have hm := mul_le_mul_of_nonneg_left hk
    (Real.exp_pos (((t : ℂ)*v^(2*m)+Complex.I*z*v).re)).le
  rw [← show ‖weight m t z v‖ =
    Real.exp (((t : ℂ)*v^(2*m)+Complex.I*z*v).re)*‖kernelComplex v‖ by
      rw [weight,norm_mul,Complex.norm_exp]] at hm
  have he : Real.exp (((t : ℂ)*v^(2*m)+Complex.I*z*v).re+9*v.re-
      Real.pi*(Complex.exp (4*v)).re) =
      Real.exp (((t : ℂ)*v^(2*m)+Complex.I*z*v).re)*Real.exp (9*v.re)*
        Real.exp (-Real.pi*(Complex.exp (4*v)).re) := by
    rw [sub_eq_add_neg,Real.exp_add,Real.exp_add]
    simp only [neg_mul]
  rw [he]
  have hc := mul_le_mul_of_nonneg_right hcoef
    (by positivity : 0 ≤ Real.exp (((t : ℂ)*v^(2*m)+Complex.I*z*v).re)*Real.exp (9*v.re)*
      Real.exp (-Real.pi*(Complex.exp (4*v)).re))
  nlinarith

theorem sixth_sum_power_bound_fails :
    |(1/4 : ℝ)| < Real.pi/8 ∧
      (((1/8 : ℂ)+(1/4 : ℂ)*Complex.I)^6).re > (1/8 : ℝ)^6+(1/4 : ℝ)^6 := by
  constructor
  · have hp := Real.pi_gt_three
    norm_num
    linarith
  · norm_num [pow_succ,Complex.mul_re,Complex.mul_im]

end OperatorDerivativeRewrite.Foundation.RiemannEvenCompactWeight
