import Foundation.RiemannRealOrderUniformCutoff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Coefficient-aware uniform endpoint cancellation for the actual fractional density.
The constants below are chosen before the real order; no common raw-cutoff
pointwise integrable majorant is asserted. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderUniformEndpoint
open RiemannThetaComplexKernel RiemannRealOrderFractionalJets
open RiemannRealOrderFractionalRemainder

private theorem exp_sub_one_bound (s : ℝ) :
    ‖(Real.exp s : ℂ)-1‖ ≤ |s| * Real.exp |s| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (s : ℂ) 1
  simpa only [Finset.sum_range_one,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,
    pow_one,Complex.norm_real,Real.norm_eq_abs,Complex.ofReal_exp] using h

theorem kernel_difference_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ u ∈ Icc (0 : ℝ) 1, ‖kernelComplex (u : ℂ)-kernelComplex 0‖ ≤ C*u := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (kernel_derivative_continuous 1).continuousOn
  let C : ℝ := max M 0
  refine ⟨C,le_max_right _ _,?_⟩
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => kernelComplex (v : ℂ))
      (iteratedDeriv 1 kernelComplex (u : ℂ)) u := by
    have he : RiemannRealOrderCubicDensity.density 0=kernelComplex := by
      funext z
      simp [RiemannRealOrderCubicDensity.density]
    have h := RiemannRealOrderCubicDensity.density_profile_hasDerivAt 0 0 u
    rw [he] at h
    simpa only [iteratedDeriv_zero] using h
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (a := (0 : ℝ)) (b := 1) (fun u _ => (hd u).hasDerivWithinAt)
    (fun u hu => (hM u ⟨hu.1,hu.2.le⟩).trans (le_max_left M 0))
  intro u hu
  simpa only [Complex.ofReal_zero,sub_zero] using hm u hu

theorem endpointDifference_uniform_linear (t : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a : ℝ, 1 ≤ a → ∀ u ∈ Icc (0 : ℝ) 1,
      ‖endpointDifference a t u‖ ≤ C*u := by
  obtain ⟨D,hD,hDK⟩ := kernel_difference_bound
  let K : ℝ := ‖kernelComplex 0‖
  let E : ℝ := Real.exp |t|
  refine ⟨E*D+K*(|t| * E+Real.exp 1),by positivity,?_⟩
  intro a ha u hu
  have hp0 : 0 ≤ u^(2*a) := Real.rpow_nonneg hu.1 _
  have hp1 : u^(2*a) ≤ u := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge' hu.1 hu.2 (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (1 : ℝ) ≤ 2*a)
  have hs : |t*u^(2*a)| ≤ |t| := by
    rw [abs_mul,abs_of_nonneg hp0]
    exact mul_le_of_le_one_right (abs_nonneg t) (hp1.trans hu.2)
  have hEu : ‖(Real.exp (t*u^(2*a)) : ℂ)‖ ≤ E := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans hs)
  have hEs : ‖(Real.exp (t*u^(2*a)) : ℂ)-1‖ ≤ |t| * E*u := by
    calc
      _ ≤ |t*u^(2*a)| * Real.exp |t*u^(2*a)| := exp_sub_one_bound _
      _ ≤ (|t| * u)*E := by
        apply mul_le_mul
        · rw [abs_mul,abs_of_nonneg hp0]
          exact mul_le_mul_of_nonneg_left hp1 (abs_nonneg t)
        · exact Real.exp_le_exp.mpr hs
        · positivity
        · exact mul_nonneg (abs_nonneg t) hu.1
      _ = _ := by ring
  have hEm : ‖(Real.exp (-u) : ℂ)-1‖ ≤ Real.exp 1*u := by
    calc
      _ ≤ |-u| * Real.exp |-u| := exp_sub_one_bound _
      _ ≤ u*Real.exp 1 := by
        rw [abs_neg,abs_of_nonneg hu.1]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.2) hu.1
      _ = _ := by ring
  have he : endpointDifference a t u=
      (Real.exp (t*u^(2*a)) : ℂ)*(kernelComplex (u : ℂ)-kernelComplex 0)+
      ((Real.exp (t*u^(2*a)) : ℂ)-1)*kernelComplex 0-
      kernelComplex 0*((Real.exp (-u) : ℂ)-1) := by
    unfold endpointDifference
    ring
  rw [he]
  calc
    _ ≤ ‖(Real.exp (t*u^(2*a)) : ℂ)*(kernelComplex (u : ℂ)-kernelComplex 0)‖+
        ‖((Real.exp (t*u^(2*a)) : ℂ)-1)*kernelComplex 0‖+
        ‖kernelComplex 0*((Real.exp (-u) : ℂ)-1)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ E*(D*u)+(|t| * E*u)*K+K*(Real.exp 1*u) := by
      simp only [norm_mul]
      exact add_le_add (add_le_add
        (mul_le_mul hEu (hDK u hu) (norm_nonneg _) (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_right hEs (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left hEm (norm_nonneg _))
    _ = _ := by ring

private theorem falling_three_bound (a : ℝ) (ha : 1 ≤ a) (ha5 : a ≤ 5/4) :
    |falling (2*a) 3| ≤ 6*(2*a-2) := by
  have h0 : 0 ≤ 2*a := by linarith
  have h1 : 0 ≤ 2*a-1 := by linarith
  have h2 : 0 ≤ 2*a-2 := by linarith
  have hp : (2*a)*(2*a-1) ≤ (3 : ℝ)*2 :=
    mul_le_mul (by linarith) (by linarith) h1 (by norm_num)
  norm_num only [falling,Finset.prod_range_succ,Finset.prod_range_zero,Nat.cast_zero,
    Nat.cast_one,Nat.cast_ofNat,mul_one,one_mul,sub_zero]
  rw [abs_mul,abs_mul,abs_of_nonneg h0,abs_of_nonneg h1,abs_of_nonneg h2]
  simpa only [show (3 : ℝ)*2=6 by norm_num] using mul_le_mul_of_nonneg_right hp h2

private theorem falling_four_bound (a : ℝ) (ha : 1 ≤ a) (ha5 : a ≤ 5/4) :
    |falling (2*a) 4| ≤ 6*(2*a-2) := by
  rw [falling_succ (2*a) 3,abs_mul]
  have h : |2*a-(3 : ℕ)| ≤ 1 := abs_le.mpr ⟨by norm_num; linarith,by norm_num; linarith⟩
  exact (mul_le_of_le_one_right (abs_nonneg _) h).trans (falling_three_bound a ha ha5)

theorem phase_three_norm_bound (a t u : ℝ) (ha : 1 ≤ a) (ha5 : a ≤ 5/4)
    (hu : 0 < u) :
    ‖phaseJet a t 3 (u : ℂ)‖ ≤ 6*|t| * (2*a-2)*u^(2*a-3) := by
  rw [phaseJet_real a t u 3 hu.le,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hu _)]
  norm_num only [Nat.cast_ofNat]
  calc
    _ ≤ |t| * (6*(2*a-2))*u^(2*a-3) := by
      gcongr
      exact falling_three_bound a ha ha5
    _ = _ := by ring

theorem phase_four_norm_bound (a t u : ℝ) (ha : 1 ≤ a) (ha5 : a ≤ 5/4)
    (hu : 0 < u) :
    ‖phaseJet a t 4 (u : ℂ)‖ ≤ 6*|t| * (2*a-2)*u^(2*a-4) := by
  rw [phaseJet_real a t u 4 hu.le,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hu _)]
  norm_num only [Nat.cast_ofNat]
  calc
    _ ≤ |t| * (6*(2*a-2))*u^(2*a-4) := by
      gcongr
      exact falling_four_bound a ha ha5
    _ = _ := by ring

theorem endpoint_weight_integrable (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => b*u^(b-1)) (Ioo 0 1) :=
  ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr
    (by linarith : -1 < b-1)).const_mul b

theorem endpoint_weight_integral (b : ℝ) (hb : 0 < b) :
    (∫ u : ℝ in Ioo 0 1, b*u^(b-1))=1 := by
  rw [integral_const_mul,← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_rpow (Or.inl (by linarith : -1 < b-1))]
  simp only [sub_add_cancel,Real.one_rpow,Real.zero_rpow hb.ne',sub_zero]
  exact mul_one_div_cancel hb.ne'

theorem singular_fourth_uniform_integral_bound (t : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a : ℝ, 1 < a → a ≤ 5/4 →
      IntegrableOn (fun u : ℝ => phaseJet a t 4 (u : ℂ)*endpointDifference a t u)
        (Ioo 0 1) ∧
      (∫ u : ℝ in Ioo 0 1, ‖phaseJet a t 4 (u : ℂ)*endpointDifference a t u‖) ≤ C := by
  obtain ⟨D,hD,hDu⟩ := endpointDifference_uniform_linear t
  refine ⟨6*|t| * D,by positivity,?_⟩
  intro a ha ha5
  have hb : 0 < 2*a-2 := by linarith
  have hm := (endpoint_weight_integrable (2*a-2) hb).const_mul (6*|t| * D)
  have hc : ContinuousOn (fun u : ℝ => phaseJet a t 4 (u : ℂ)*endpointDifference a t u)
      (Ioo 0 1) := by
    have hp : ContinuousOn (fun u : ℝ => phaseJet a t 4 (u : ℂ)) (Ioo 0 1) := by
      intro u hu
      exact ((phaseJet_hasDerivAt a t 4 (u : ℂ)
        (Complex.mem_slitPlane_iff.mpr (Or.inl hu.1))).comp_ofReal).continuousAt.continuousWithinAt
    exact hp.mul ((endpointDifference_continuousOn a t).mono (fun _ hu => hu.1))
  have hbound : ∀ u ∈ Ioo (0 : ℝ) 1,
      ‖phaseJet a t 4 (u : ℂ)*endpointDifference a t u‖ ≤
        (6*|t| * D)*((2*a-2)*u^((2*a-2)-1)) := by
    intro u hu
    have hr : u^(2*a-4)*u=u^(2*a-3) := by
      calc
        _ = u^(2*a-4)*u^(1 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hu.1]; congr 1; ring
    calc
      _ = ‖phaseJet a t 4 (u : ℂ)‖*‖endpointDifference a t u‖ := norm_mul _ _
      _ ≤ (6*|t| * (2*a-2)*u^(2*a-4))*(D*u) :=
        mul_le_mul (phase_four_norm_bound a t u ha.le ha5 hu.1)
          (hDu a ha.le u ⟨hu.1.le,hu.2.le⟩) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by positivity) hb.le) (Real.rpow_nonneg hu.1.le _))
      _ = _ := by
        rw [show (2*a-2)-1=2*a-3 by ring]
        calc
          _ = (6*|t| * D)*(2*a-2)*(u^(2*a-4)*u) := by ring
          _ = _ := by rw [hr]; ring
  have hi := hm.mono' (hc.aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_mem measurableSet_Ioo).mono fun u hu => hbound u hu)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ u : ℝ in Ioo 0 1, (6*|t| * D)*((2*a-2)*u^((2*a-2)-1)) :=
      integral_mono_ae hi.norm hm
        ((ae_restrict_mem measurableSet_Ioo).mono fun u hu => hbound u hu)
    _ = _ := by rw [integral_const_mul,endpoint_weight_integral (2*a-2) hb,mul_one]

theorem phase_three_integral_norm_bound (a t : ℝ) (ha : 1 < a) (ha5 : a ≤ 5/4) :
    (∫ u : ℝ in Ioo 0 1, ‖phaseJet a t 3 (u : ℂ)‖) ≤ 6*|t| := by
  have hb : 0 < 2*a-2 := by linarith
  have hi := phaseJet_integrable_near a t 3 (by norm_num; linarith) 1 (by norm_num)
  have hm := (endpoint_weight_integrable (2*a-2) hb).const_mul (6*|t|)
  calc
    _ ≤ ∫ u : ℝ in Ioo 0 1, (6*|t|)*((2*a-2)*u^((2*a-2)-1)) := by
      apply integral_mono_ae hi.norm hm
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have h := phase_three_norm_bound a t u ha.le ha5 hu.1
      calc
        _ ≤ 6*|t| * (2*a-2)*u^(2*a-3) := h
        _ = _ := by rw [show (2*a-2)-1=2*a-3 by ring]; ring
    _ = _ := by rw [integral_const_mul,endpoint_weight_integral (2*a-2) hb,mul_one]

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderUniformEndpoint
