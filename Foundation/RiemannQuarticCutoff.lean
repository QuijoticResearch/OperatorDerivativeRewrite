import Foundation.RiemannThetaEffective
import Foundation.RiemannQuarticDomain
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Uniform effective spatial-frequency cutoff bounds for the actual t=8
quartic arithmetic kernel; no quadrature value is assumed. -/
noncomputable section
open MeasureTheory Filter Set Real
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCutoff
open RiemannQuarticKernel RiemannThetaEffective RiemannQuarticDomain

theorem exponent_tail_bound (u : ℝ) (hu : 8/5 ≤ u) :
    8*u^4+9*u-Real.pi*exp (4*u) ≤ -64*u := by
  have hu0 : 0 ≤ u := by linarith
  have ht := Real.pow_div_factorial_le_exp (4*u) (by positivity : 0 ≤ 4*u) 4
  norm_num [Nat.factorial] at ht
  have hp := mul_le_mul_of_nonneg_right Real.pi_gt_three.le (exp_pos (4*u)).le
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8/5) hu 3
  have hpoly : 73*u ≤ 24*u^4 := by
    have hh := mul_nonneg hu0 (show 0 ≤ 24*u^3-73 by nlinarith)
    nlinarith
  nlinarith

theorem weighted_tail_bound (k : ℕ) (u : ℝ) (hu : 8/5 ≤ u) :
    weighted k 8 0 u ≤ (64*(k.factorial : ℝ))*exp (-63*u) := by
  have hu0 : 0 ≤ u := by linarith
  have he := exponent_tail_bound u hu
  have hk := Real.pow_div_factorial_le_exp u hu0 k
  have hfact : (0 : ℝ) < k.factorial := by positivity
  have hk' : u^k ≤ (k.factorial : ℝ)*exp u := by
    simpa only [mul_comm] using (div_le_iff₀ hfact).mp hk
  unfold weighted
  simp only [zero_mul, add_zero]
  calc
    _ ≤ ((k.factorial : ℝ)*exp u)*exp (8*u^4)*
        (64*exp (9*u-Real.pi*exp (4*u))) := by
      gcongr
      · exact kernel_pos u hu0 |>.le
      · exact kernel_effective_bound u hu0
    _ = (64*(k.factorial : ℝ))*exp (u+(8*u^4+9*u-Real.pi*exp (4*u))) := by
      rw [show u+(8*u^4+9*u-Real.pi*exp (4*u))=
        (u+8*u^4)+(9*u-Real.pi*exp (4*u)) by ring, Real.exp_add, Real.exp_add]
      ring
    _ ≤ (64*(k.factorial : ℝ))*exp (-63*u) := by
      gcongr
      linarith

theorem weighted_tail_integral (k : ℕ) (R : ℝ) (hR : 8/5 ≤ R) :
    (∫ u in Ioi R, weighted k 8 0 u) ≤
      (64*(k.factorial : ℝ))/63*exp (-63*R) := by
  have hi := (weighted_integrable k 8 0).mono_set
    (show Ioi R ⊆ Ici (0 : ℝ) by intro u hu; change R < u at hu; change 0 ≤ u; linarith)
  have hj := (exp_neg_integrableOn_Ioi R (by norm_num : (0 : ℝ) < 63)).const_mul
    (64*(k.factorial : ℝ))
  have hh : (∫ u in Ioi R, weighted k 8 0 u) ≤
      ∫ u in Ioi R, (64*(k.factorial : ℝ))*exp (-63*u) := by
    apply integral_mono_ae hi hj
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact weighted_tail_bound k u (by change R < u at hu; linarith)
  apply hh.trans_eq
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-63 : ℝ) < 0)]
  ring

theorem cutoff_numeric_bound (k : ℕ) (hk : k ≤ 2) :
    (64*(k.factorial : ℝ))/63*exp (-63*(8/5)) ≤ (1/10^28 : ℝ) := by
  have hkf : (k.factorial : ℝ) ≤ 2 := by interval_cases k <;> norm_num
  have hexp : (2 : ℝ)^100 ≤ exp 100 := by
    have h : (2 : ℝ) ≤ exp 1 := by have hh := add_one_le_exp (1 : ℝ); linarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h 100
    simpa only [← exp_nat_mul, Nat.cast_ofNat, mul_one] using hp
  have he : exp (-63*(8/5)) ≤ (2 : ℝ)^(-100 : ℤ) := by
    calc
      _ ≤ exp (-(100 : ℝ)) := exp_le_exp.mpr (by norm_num)
      _ = (exp (100 : ℝ))⁻¹ := exp_neg _
      _ ≤ ((2 : ℝ)^100)⁻¹ := (inv_le_inv₀ (exp_pos _) (by positivity)).mpr hexp
      _ = _ := by norm_num
  have hf : 0 ≤ (k.factorial : ℝ) := by positivity
  have hc : (64*(k.factorial : ℝ))/63 ≤ (128/63 : ℝ) := by linarith
  calc
    _ ≤ (128/63 : ℝ)*(2 : ℝ)^(-100 : ℤ) :=
      mul_le_mul hc he (exp_pos _).le (by norm_num)
    _ ≤ _ := by norm_num

theorem weighted_cutoff_error (k : ℕ) (hk : k ≤ 2) :
    (∫ u in Ioi (8/5 : ℝ), weighted k 8 0 u) ≤ (1/10^28 : ℝ) :=
  (weighted_tail_integral k (8/5) le_rfl).trans (cutoff_numeric_bound k hk)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCutoff
