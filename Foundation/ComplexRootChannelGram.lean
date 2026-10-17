import Foundation.ComplexRootMarkRepresentation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Actual Hermitian covariance of the three centered finite-mark channels. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.ComplexRootChannelGram
open ComplexFourthRootNoise

def gram (a : ℝ) (r s : Fin 3) : ℂ :=
  ∫ k, (noise a k)^(r.val+1)*(starRingEnd ℂ ((noise a k)^(s.val+1))) ∂probability

theorem gram_formula (a : ℝ) (r s : Fin 3) :
    gram a r s = if r = s then ((2*a^2 : ℝ) : ℂ)^(r.val+1) else 0 := by
  fin_cases r <;> fin_cases s <;>
    norm_num [gram, integral_formula, noise, root, map_add, map_sub, map_mul, map_pow] <;>
    push_cast <;> ring_nf <;> norm_num [Complex.I_sq] <;> ring

def channelKernel (a : ℝ) (u : Fin 3 → ℂ) (k : Fin 4) : ℂ :=
  ∑ r : Fin 3, u r*(noise a k)^(r.val+1)

theorem weight_pos (a : ℝ) (ha : a ≠ 0) (r : Fin 3) : 0 < (2*a^2)^(r.val+1) :=
  pow_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero ha)) _

theorem conjugate_weight_identity (a : ℝ) (r : Fin 3) (k : Fin 4) :
    ComplexRootMarkRepresentation.fourthMoment a*starRingEnd ℂ ((noise a k)^(r.val+1)) =
      ((2*a^2 : ℝ) : ℂ)^(r.val+1)*(noise a k)^(3-r.val) := by
  fin_cases r <;> fin_cases k <;>
    norm_num [ComplexRootMarkRepresentation.fourthMoment, noise, root, map_add, map_sub, map_mul, map_pow] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem hermitian_coefficient (a : ℝ) (ha : a ≠ 0) (g : Fin 4 → ℂ) (r : Fin 3) :
    (∫ k, g k*starRingEnd ℂ ((noise a k)^(r.val+1)) ∂probability) =
      ComplexRootMarkRepresentation.coefficient a g r*((2*a^2 : ℝ) : ℂ)^(r.val+1) := by
  have hK := ComplexRootMarkRepresentation.fourthMoment_ne_zero a ha
  have he : ComplexRootMarkRepresentation.fourthMoment a*
      (∫ k, g k*starRingEnd ℂ ((noise a k)^(r.val+1)) ∂probability) =
      ((2*a^2 : ℝ) : ℂ)^(r.val+1)*(∫ k, g k*(noise a k)^(3-r.val) ∂probability) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with k
    calc
      _ = g k*(ComplexRootMarkRepresentation.fourthMoment a*
          starRingEnd ℂ ((noise a k)^(r.val+1))) := by ring
      _ = _ := by rw [conjugate_weight_identity]; ring
  unfold ComplexRootMarkRepresentation.coefficient
  field_simp [hK]
  linear_combination he

theorem sesquilinear_formula (a : ℝ) (u v : Fin 3 → ℂ) :
    (∫ k, channelKernel a u k*starRingEnd ℂ (channelKernel a v k) ∂probability) =
      ∑ r : Fin 3, (u r*starRingEnd ℂ (v r))*((2*a^2 : ℝ) : ℂ)^(r.val+1) := by
  simp only [channelKernel, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  have he (s : Fin 3) :
      (∫ k, (u s*(noise a k)^(s.val+1))*
        (starRingEnd ℂ (v r)*starRingEnd ℂ ((noise a k)^(r.val+1))) ∂probability) =
        (u s*starRingEnd ℂ (v r))*gram a s r := by
    rw [gram, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with k
    ring
  simp_rw [he, gram_formula]
  simp

theorem product_conjugate (z : ℂ) :
    z*starRingEnd ℂ z = ((‖z‖^2 : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply] <;> ring

theorem energy_formula (a : ℝ) (u : Fin 3 → ℂ) :
    (∫ k, ‖channelKernel a u k‖^2 ∂probability) =
      ∑ r : Fin 3, ‖u r‖^2*(2*a^2)^(r.val+1) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [← product_conjugate]
  rw [sesquilinear_formula]
  simp only [product_conjugate, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]

end OperatorDerivativeRewrite.Foundation.ComplexRootChannelGram
