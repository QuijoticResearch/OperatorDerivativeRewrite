import Foundation.GaussianFourierJets
import Foundation.FiniteFourierTorusAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Integral-defined Fourier coefficients of the actual periodic Gaussian
series. Absolute convergence justifies every sum/integral interchange. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.GaussianFourierCoefficient
open GaussianFourierJets FiniteFourierTorusAverage
set_option backward.isDefEq.respectTransparency false

def mode (n : ℤ) (y : ℝ) : ℂ := Complex.exp ((Complex.I*(n : ℂ))*(y : ℂ))
def weight (s : ℝ) (n : ℤ) : ℝ := Real.exp (-s*(n : ℝ)^2)
def summand (s : ℝ) (n : ℤ) (y : ℝ) : ℂ :=
  (weight s n : ℂ)*mode n y
def kernel (s y : ℝ) : ℂ := ∑' n : ℤ, summand s n y
def coefficient (f : ℝ → ℂ) (m : ℤ) : ℂ :=
  period⁻¹*(∫ y in (0 : ℝ)..2*Real.pi, f y*mode (-m) y)

theorem mode_norm (n : ℤ) (y : ℝ) : ‖mode n y‖ = 1 := by
  simp [mode, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem mode_add (n m : ℤ) (y : ℝ) : mode (n+m) y = mode n y*mode m y := by
  simp only [mode, Int.cast_add, mul_add, add_mul, Complex.exp_add]

theorem summand_norm (s : ℝ) (n : ℤ) (y : ℝ) :
    ‖summand s n y‖ = weight s n := by
  rw [summand, norm_mul, mode_norm, mul_one, Complex.norm_real]
  exact Real.norm_of_nonneg (Real.exp_pos _).le

theorem summand_summable (s : ℝ) (hs : 0 < s) (y : ℝ) :
    Summable (fun n : ℤ => summand s n y) := by
  apply (bound_summable 0 s hs).of_norm_bounded
  intro n
  simp only [summand_norm, bound, pow_zero, one_mul, weight, le_refl]

theorem summand_conj (s : ℝ) (n : ℤ) (y : ℝ) :
    conj (summand s n y) = summand s (-n) y := by
  have hm : conj (mode n y) = mode (-n) y := by
    apply Complex.ext <;>
      simp [mode, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  have hw : weight s (-n) = weight s n := by simp [weight]
  simp only [summand, map_mul, Complex.conj_ofReal, hm, hw]

theorem kernel_conj (s : ℝ) (hs : 0 < s) (y : ℝ) : conj (kernel s y) = kernel s y := by
  have h := Complex.conjCLE.toContinuousLinearMap.hasSum (summand_summable s hs y).hasSum
  have he : (∑' n : ℤ, summand s (-n) y) = kernel s y :=
    (Equiv.neg ℤ).tsum_eq (fun n => summand s n y)
  change HasSum (fun n : ℤ => conj (summand s n y)) (conj (kernel s y)) at h
  simp only [summand_conj] at h
  exact h.tsum_eq.symm.trans he

theorem kernel_real (s : ℝ) (hs : 0 < s) (y : ℝ) : kernel s y = (jet 0 s y : ℂ) := by
  have h := Complex.reCLM.hasSum (summand_summable s hs y).hasSum
  have ht : (fun n : ℤ => Complex.reCLM (summand s n y)) = fun n => term 0 s n y := by
    funext n
    change ((weight s n : ℂ)*mode n y).re = term 0 s n y
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hm : (mode n y).re = Real.cos ((n : ℝ)*y) := by
      simp [mode, Complex.exp_re, Complex.mul_re, Complex.mul_im]
    rw [hm]
    simp [term, weight]
  rw [ht] at h
  apply Complex.ext
  · exact h.tsum_eq.symm
  · have hh := congrArg Complex.im (kernel_conj s hs y)
    simp only [Complex.conj_im, Complex.ofReal_im] at hh ⊢
    linarith

theorem integral_summand (s : ℝ) (n m : ℤ) :
    (∫ y in (0 : ℝ)..2*Real.pi, summand s n y*mode (-m) y) =
      if n = m then period*(weight s n : ℂ) else 0 := by
  have he : (fun y => summand s n y*mode (-m) y) =
      fun y => (weight s n : ℂ)*mode (n-m) y := by
    funext y
    rw [summand, mul_assoc, ← mode_add]
    rfl
  rw [he, intervalIntegral.integral_const_mul]
  have hi : (∫ y in (0 : ℝ)..2*Real.pi, mode (n-m) y) =
      if n-m = 0 then period else 0 := exponential_integral (n-m)
  rw [hi]
  by_cases h : n = m <;> simp [h, sub_eq_zero, mul_comm]

theorem integral_kernel (s : ℝ) (hs : 0 < s) (m : ℤ) :
    (∫ y in (0 : ℝ)..2*Real.pi, kernel s y*mode (-m) y) =
      period*(weight s m : ℂ) := by
  have hq : Summable (weight s) := by
    convert bound_summable 0 s hs using 1
    funext n
    simp [bound, weight]
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 2*Real.pi) (μ := volume)
    (fun (n : ℤ) (_ : ℝ) => weight s n)
    (fun n => (show Continuous (fun y => summand s n y*mode (-m) y) by
      unfold summand mode
      fun_prop).aestronglyMeasurable)
    (fun n => .of_forall (fun y _ => by simp [norm_mul, summand_norm, mode_norm]))
    (.of_forall (fun y _ => hq)) intervalIntegrable_const
    (.of_forall (fun y _ => ((summand_summable s hs y).hasSum.mul_right (mode (-m) y))))
  change (∫ y in (0 : ℝ)..2*Real.pi, (∑' n : ℤ, summand s n y)*mode (-m) y) = _
  rw [← h.tsum_eq]
  simp only [integral_summand]
  simp

theorem coefficient_kernel (s : ℝ) (hs : 0 < s) (m : ℤ) :
    coefficient (kernel s) m = (weight s m : ℂ) := by
  rw [coefficient, integral_kernel s hs, ← mul_assoc, inv_mul_cancel₀ period_ne_zero, one_mul]

theorem coefficient_jet (s : ℝ) (hs : 0 < s) (m : ℤ) :
    coefficient (fun y => (jet 0 s y : ℂ)) m = (weight s m : ℂ) := by
  have he : (fun y => (jet 0 s y : ℂ)) = kernel s :=
    funext (fun y => (kernel_real s hs y).symm)
  rw [he]
  exact coefficient_kernel s hs m

theorem nonzero_tail (s : ℝ) (hs : 0 < s) (N : ℕ) :
    ∃ m : ℤ, (N : ℤ) < m ∧ coefficient (fun y => (jet 0 s y : ℂ)) m ≠ 0 := by
  refine ⟨(N : ℤ)+1, by omega, ?_⟩
  rw [coefficient_jet s hs]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))

end OperatorDerivativeRewrite.Foundation.GaussianFourierCoefficient
