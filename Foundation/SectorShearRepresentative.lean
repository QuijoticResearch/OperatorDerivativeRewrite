import Foundation.SectorTransferSymmetry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The two-mode transfer test has an actual smooth periodic divergence-free shear representative. -/
noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.SectorShearRepresentative
open SectorTransferSymmetry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def coefficient (k : Wave) (i : Fin 3) : ℂ := Complex.I*(polarization k i : ℂ)
def fourierTerm (k : Wave) (x : Vector) (i : Fin 3) : ℂ :=
  coefficient k i*Complex.exp ((dotWave k x : ℂ)*Complex.I)
def synthesis (x : Vector) (i : Fin 3) : ℂ := ∑ k ∈ modes, fourierTerm k x i
def velocity (x : Vector) : Vector := ![0,-2*Real.sin (x 0),0]

theorem coefficient_imaginary (k : Wave) (i : Fin 3) : (coefficient k i).re = 0 := by
  simp [coefficient,Complex.mul_re]

theorem coefficient_reality (k : Wave) (i : Fin 3) : coefficient (-k) i = conj (coefficient k i) := by
  have hp := congrFun (polarization_odd k) i
  simp only [Pi.neg_apply] at hp
  simp [coefficient,hp]

theorem fourierTerm_real (k : Wave) (x : Vector) (i : Fin 3) :
    (fourierTerm k x i).re = -polarization k i*Real.sin (dotWave k x) := by
  simp [fourierTerm,coefficient,Complex.mul_re,Complex.mul_im]

theorem fourierTerm_imag (k : Wave) (x : Vector) (i : Fin 3) :
    (fourierTerm k x i).im = polarization k i*Real.cos (dotWave k x) := by
  simp [fourierTerm,coefficient,Complex.mul_re,Complex.mul_im]

theorem phase_plus (x : Vector) : dotWave plus x = x 0 := by
  norm_num [dotWave,plus,Fin.sum_univ_succ]

theorem phase_minus (x : Vector) : dotWave (-plus) x = -x 0 := by
  norm_num [dotWave,plus,Fin.sum_univ_succ]

theorem synthesis_two (x : Vector) (i : Fin 3) :
    synthesis x i = fourierTerm plus x i+fourierTerm (-plus) x i := by
  simp [synthesis,modes,plus_ne_neg]

theorem synthesis_eq_velocity (x : Vector) (i : Fin 3) : synthesis x i = (velocity x i : ℂ) := by
  apply Complex.ext
  · rw [synthesis_two,Complex.add_re,fourierTerm_real,fourierTerm_real,
      polarization_plus,polarization_minus,phase_plus,phase_minus]
    fin_cases i <;> simp [velocity,← Complex.ofReal_sin] <;> ring
  · rw [synthesis_two,Complex.add_im,fourierTerm_imag,fourierTerm_imag,
      polarization_plus,polarization_minus,phase_plus,phase_minus]
    fin_cases i <;> simp [velocity] <;> ring

theorem velocity_smooth : ContDiff ℝ ⊤ velocity := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ⊤ (fun _ : Vector => (0 : ℝ))
    fun_prop
  · change ContDiff ℝ ⊤ (fun x : Vector => -2*Real.sin (x 0))
    fun_prop
  · change ContDiff ℝ ⊤ (fun _ : Vector => (0 : ℝ))
    fun_prop

theorem velocity_periodic (i : Fin 3) (x : Vector) :
    velocity (x+Pi.single i (2*Real.pi)) = velocity x := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [velocity,Pi.add_apply,Pi.single_apply,Real.sin_add_two_pi]

def divergence (x : Vector) : ℝ :=
  ∑ i : Fin 3, deriv (fun t : ℝ => velocity (x+t • Pi.single i (1 : ℝ)) i) 0

theorem diagonal_line_constant (x : Vector) (i : Fin 3) :
    (fun t : ℝ => velocity (x+t • Pi.single i (1 : ℝ)) i) = fun _ => velocity x i := by
  funext t
  fin_cases i <;> simp [velocity,Pi.add_apply,Pi.smul_apply,Pi.single_apply]

theorem divergence_zero (x : Vector) : divergence x = 0 := by
  unfold divergence
  simp_rw [diagonal_line_constant]
  simp

theorem along_velocity_constant (x : Vector) :
    (fun t : ℝ => velocity (x+t • velocity x)) = fun _ => velocity x := by
  funext t
  ext i
  fin_cases i <;> simp [velocity,Pi.add_apply,Pi.smul_apply]

theorem advection_zero (x : Vector) :
    deriv (fun t : ℝ => velocity (x+t • velocity x)) 0 = 0 := by
  rw [along_velocity_constant]
  simp

theorem velocity_nonzero : velocity ![Real.pi/2,0,0] ≠ 0 := by
  intro h
  have hh := congrFun h 1
  norm_num [velocity] at hh

theorem physical_transfer_counterexample (s : Wave → Fin 32) :
    (∀ k, dotWave k (polarization k)=0) ∧
    (∀ k, polarization (-k)= -polarization k) ∧
    energy modes polarization=2 ∧
    1/(32 : ℝ)<concentration modes s polarization ∧ rate modes s polarization=0 ∧
    (∀ k, fullTransfer polarization k=0) ∧
    ContDiff ℝ ⊤ velocity ∧ (∀ x, divergence x=0) ∧
    (∀ x i, synthesis x i=(velocity x i : ℂ)) :=
  ⟨transverse,polarization_odd,shear_energy,shear_concentrated s,shear_rate_zero s,
    shear_fullTransfer_zero,velocity_smooth,divergence_zero,synthesis_eq_velocity⟩

end OperatorDerivativeRewrite.Foundation.SectorShearRepresentative
