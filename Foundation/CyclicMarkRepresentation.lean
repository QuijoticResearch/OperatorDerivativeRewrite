import Foundation.CyclicRootProbabilityNoise
import Foundation.ComplexRootChannelGram

/-! Exact centered cyclic-character representation on an actual finite probability source. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CyclicMarkRepresentation
open CyclicRootProbabilityNoise
variable (N : ℕ) [NeZero N]

def coefficient (g : ZMod N → ℂ) (j : ZMod N) : ℂ :=
  (ZMod.dft g j)/(N : ℂ)

theorem coefficient_zero (g : ZMod N → ℂ) : coefficient N g 0 = ∫ k, g k ∂probability N := by
  rw [coefficient,ZMod.dft_apply_zero,integral_formula]

theorem representation (g : ZMod N → ℂ) (k : ZMod N) :
    g k = ∑ j : ZMod N, coefficient N g j * ZMod.stdAddChar (j*k) := by
  have he := congrFun ((ZMod.dft (N := N)).symm_apply_apply g) k
  rw [ZMod.invDFT_apply] at he
  simp only [smul_eq_mul,Finset.mul_sum] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [coefficient]
  ring

theorem centered_representation (g : ZMod N → ℂ) (k : ZMod N) :
    g k-(∫ l, g l ∂probability N) =
      ∑ j ∈ Finset.univ.erase (0 : ZMod N), coefficient N g j * ZMod.stdAddChar (j*k) := by
  classical
  have he := Finset.sum_erase_add (Finset.univ : Finset (ZMod N))
    (fun j => coefficient N g j*ZMod.stdAddChar (j*k)) (Finset.mem_univ 0)
  rw [← representation N g k] at he
  simp only [zero_mul,AddChar.map_zero_eq_one,mul_one,coefficient_zero] at he
  linear_combination -he

theorem conjugate_character (j : ZMod N) :
    star (ZMod.stdAddChar j) = ZMod.stdAddChar (-j) := by
  rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

theorem character_gram (j l : ZMod N) :
    (∫ k, ZMod.stdAddChar (j*k)*star (ZMod.stdAddChar (l*k)) ∂probability N) =
      if j = l then 1 else 0 := by
  have hp (k : ZMod N) : ZMod.stdAddChar (j*k)*star (ZMod.stdAddChar (l*k)) =
      ZMod.stdAddChar ((j-l)*k) := by
    rw [conjugate_character,← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hp]
  rw [integral_formula,character_sum]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  by_cases h : j = l <;> simp [sub_eq_zero,h,hN]

def synthesis (u : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ∑ j : ZMod N, u j*ZMod.stdAddChar (j*k)

theorem synthesis_pairing (u v : ZMod N → ℂ) :
    (∫ k, synthesis N u k*starRingEnd ℂ (synthesis N v k) ∂probability N) =
      ∑ j : ZMod N, u j*starRingEnd ℂ (v j) := by
  simp only [synthesis,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
  have he (s : ZMod N) :
      (∫ k, (u s*ZMod.stdAddChar (s*k))*
        (starRingEnd ℂ (v r)*starRingEnd ℂ (ZMod.stdAddChar (r*k))) ∂probability N) =
      (u s*starRingEnd ℂ (v r))*(if s = r then 1 else 0) := by
    rw [← character_gram N s r,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with k
    simp only [starRingEnd_apply]
    ring
  simp_rw [he]
  simp

theorem synthesis_energy (u : ZMod N → ℂ) :
    (∫ k, ‖synthesis N u k‖^2 ∂probability N) = ∑ j : ZMod N, ‖u j‖^2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [← ComplexRootChannelGram.product_conjugate]
  rw [synthesis_pairing]
  simp only [ComplexRootChannelGram.product_conjugate,Complex.ofReal_sum]

end OperatorDerivativeRewrite.Foundation.CyclicMarkRepresentation
