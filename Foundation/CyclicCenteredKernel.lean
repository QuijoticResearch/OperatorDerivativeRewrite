import Foundation.HigherEvenRenewalEnergy

/-! Every nonzero cyclic character is retained; the zero mode is explicitly omitted. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.CyclicCenteredKernel
variable (N : ℕ) [NeZero N]

def kernel (u : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ∑ j ∈ Finset.univ.erase (0 : ZMod N), u j*ZMod.stdAddChar (j*k)

theorem kernel_eq_synthesis (u : ZMod N → ℂ) (k : ZMod N) :
    kernel N u k = CyclicMarkRepresentation.synthesis N (Function.update u 0 0) k := by
  classical
  have he := Finset.sum_erase_add (Finset.univ : Finset (ZMod N))
    (fun j => Function.update u 0 0 j*ZMod.stdAddChar (j*k)) (Finset.mem_univ 0)
  simp only [Function.update_self,zero_mul,add_zero] at he
  rw [CyclicMarkRepresentation.synthesis,← he]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem kernel_mean (u : ZMod N → ℂ) :
    (∫ k, kernel N u k ∂CyclicRootProbabilityNoise.probability N) = 0 := by
  unfold kernel
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_eq_zero
  intro j hj
  rw [integral_const_mul]
  have hj0 : j ≠ 0 := (Finset.mem_erase.mp hj).1
  have hm : (∫ k, ZMod.stdAddChar (j*k) ∂CyclicRootProbabilityNoise.probability N) = 0 := by
    simpa [hj0] using CyclicMarkRepresentation.character_gram N j 0
  rw [hm,mul_zero]

theorem kernel_energy (u : ZMod N → ℂ) :
    (∫ k, ‖kernel N u k‖^2 ∂CyclicRootProbabilityNoise.probability N) =
      ∑ j ∈ Finset.univ.erase (0 : ZMod N), ‖u j‖^2 := by
  classical
  simp_rw [kernel_eq_synthesis]
  rw [CyclicMarkRepresentation.synthesis_energy]
  have he := Finset.sum_erase_add (Finset.univ : Finset (ZMod N))
    (fun j => ‖Function.update u 0 0 j‖^2) (Finset.mem_univ 0)
  simp only [Function.update_self,norm_zero,zero_pow (by decide : 2 ≠ 0),add_zero] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem shifted_kernel_energy (u : ZMod N → ℂ) (c : ℂ) :
    (∫ k, ‖c+kernel N u k‖^2 ∂CyclicRootProbabilityNoise.probability N) =
      ‖c‖^2+∑ j ∈ Finset.univ.erase (0 : ZMod N), ‖u j‖^2 := by
  rw [HigherEvenRenewalEnergy.finite_shift_energy _ _ (kernel_mean N u),kernel_energy]

end OperatorDerivativeRewrite.Foundation.CyclicCenteredKernel
