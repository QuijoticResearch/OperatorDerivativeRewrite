import Foundation.HigherHeatFourierTests

/-! Actual signed-kernel backward Fourier martingales, without a positive pseudo-L2 norm. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatBackwardFourier
open HigherHeatSignedLaws HigherHeatCylinderFourier HigherHeatL2

def transition (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ z : ℝ, f (x+z)*(realKernel m hm t ht z : ℂ)

theorem phase_add (ξ x z : ℝ) : phase ξ (x+z)=phase ξ x*phase ξ z := by
  simp only [phase,add_mul,neg_add_rev,AddChar.map_add_eq_mul]
  simp only [Circle.coe_mul]
  ring

theorem phase_zero (ξ : ℝ) : phase ξ 0=1 := by simp [phase]

theorem transition_scaled_phase (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (a : ℂ) (ξ x : ℝ) :
    transition m hm t ht (fun y => a*phase ξ y) x=a*symbol m t ξ*phase ξ x := by
  have he (z : ℝ) : a*phase ξ (x+z)*(realKernel m hm t ht z : ℂ)=
      (a*phase ξ x)*(phase ξ z*(realKernel m hm t ht z : ℂ)) := by
    rw [phase_add]
    ring
  unfold transition
  simp_rw [he]
  rw [integral_const_mul,kernel_fourier]
  ring

variable {ι : Type*} [Fintype ι]

def fourierTest (a : ι → ℂ) (ξ : ι → ℝ) (x : ℝ) : ℂ := ∑ i, a i*phase (ξ i) x

theorem test_continuous (a : ι → ℂ) (ξ : ι → ℝ) : Continuous (fourierTest a ξ) := by
  unfold fourierTest phase
  fun_prop

theorem test_bound (a : ι → ℂ) (ξ : ι → ℝ) (x : ℝ) :
    ‖fourierTest a ξ x‖ ≤ ∑ i, ‖a i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,phase_norm,mul_one]

theorem transition_test (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (a : ι → ℂ) (ξ : ι → ℝ) (x : ℝ) :
    transition m hm t ht (fourierTest a ξ) x=
      fourierTest (fun i => a i*symbol m t (ξ i)) ξ x := by
  have hi (i : ι) : Integrable (fun z => a i*phase (ξ i) (x+z)*
      (realKernel m hm t ht z : ℂ)) := by
    have h := (kernel_phase_integrable m hm t ht (ξ i)).const_mul (a i*phase (ξ i) x)
    convert h using 1
    funext z
    rw [phase_add]
    ring
  change (∫ z : ℝ, (∑ i, a i*phase (ξ i) (x+z))*(realKernel m hm t ht z : ℂ))=_
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hi
  exact transition_scaled_phase m hm t ht (a i) (ξ i) x

theorem transition_spectral_bound (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (a : ι → ℂ) (ξ : ι → ℝ) (x : ℝ) :
    ‖transition m hm t ht (fourierTest a ξ) x‖ ≤ ∑ i, ‖a i‖ := by
  rw [transition_test]
  apply (test_bound _ _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (symbol_norm_le m t (ξ i))

def backwardCharacter (m : ℕ) (T s : ℝ≥0) (ξ x : ℝ) : ℂ :=
  symbol m (T-s) ξ*phase ξ x

theorem backward_terminal (m : ℕ) (T : ℝ≥0) (ξ x : ℝ) :
    backwardCharacter m T T ξ x=phase ξ x := by
  simp [backwardCharacter,symbol_zero]

theorem backward_initial (m : ℕ) (T : ℝ≥0) (ξ : ℝ) :
    backwardCharacter m T 0 ξ 0=symbol m T ξ := by
  simp [backwardCharacter,phase_zero]

theorem backward_bound (m : ℕ) (T s : ℝ≥0) (ξ x : ℝ) :
    ‖backwardCharacter m T s ξ x‖ ≤ 1 := by
  rw [backwardCharacter,norm_mul,phase_norm,mul_one]
  exact symbol_norm_le m (T-s) ξ

theorem backward_step (m : ℕ) (hm : 0 < m) (T s t : ℝ≥0)
    (hst : s < t) (ht : t ≤ T) (ξ x : ℝ) :
    transition m hm (t-s) (tsub_pos_iff_lt.mpr hst)
      (backwardCharacter m T t ξ) x=backwardCharacter m T s ξ x := by
  change transition m hm (t-s) _ (fun y => symbol m (T-t) ξ*phase ξ y) x=
    symbol m (T-s) ξ*phase ξ x
  rw [transition_scaled_phase]
  have he : (T-t)+(t-s)=T-s := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,NNReal.coe_sub ht,NNReal.coe_sub hst.le,NNReal.coe_sub (hst.le.trans ht)]
    ring
  rw [← symbol_add,he]

end OperatorDerivativeRewrite.Foundation.HigherHeatBackwardFourier
