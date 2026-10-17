import Foundation.ViscousTriadFlow

/-! Decay toward zero differs from contraction between initial states for the
actual viscous retained triad. Equal third amplitudes give an exact contraction;
different third amplitudes permit arbitrarily large distance amplification. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.ViscousTriadSeparation
open ViscousTriadFlow
open SectorTransferSymmetry (Vector)
set_option backward.isDefEq.respectTransparency false

theorem energy_nonneg (x : Vector) : 0 ≤ energy x := by
  unfold energy
  positivity

theorem same_third_energy (ν t : ℝ) (x y : Vector) (hc : x 2=y 2) :
    energy (ViscousTriadFlow.vectorFlow ν t x-ViscousTriadFlow.vectorFlow ν t y)=
      damping (2*ν) t*energy (x-y) := by
  have hs : (Real.cos (angle ν t*y 2))^2+(Real.sin (angle ν t*y 2))^2=1 := by
    linarith [Real.sin_sq_add_cos_sq (angle ν t*y 2)]
  have he : energy (ViscousTriadFlow.vectorFlow ν t x-ViscousTriadFlow.vectorFlow ν t y)=
      2*(damping ν t)^2*((Real.cos (angle ν t*y 2))^2+(Real.sin (angle ν t*y 2))^2)*
        ((x 0-y 0)^2+(x 1-y 1)^2) := by
    simp only [energy,ViscousTriadFlow.vectorFlow_formula,Pi.sub_apply,hc,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    ring
  rw [he,hs,damping_square]
  simp [energy,Pi.sub_apply,hc]
  ring

theorem angle_pos (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) : 0 < angle ν t := by
  have hd : damping (2*ν) t<1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith [mul_pos hν ht]
  simp only [angle,if_neg (ne_of_gt hν)]
  exact div_pos (sub_pos.mpr hd) (by positivity)

def jump (ν t : ℝ) : ℝ := Real.pi/angle ν t

theorem jump_pos (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) : 0 < jump ν t :=
  div_pos Real.pi_pos (angle_pos ν t hν ht)

theorem jump_phase (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    angle ν t*jump ν t=Real.pi := by
  unfold jump
  field_simp [ne_of_gt (angle_pos ν t hν ht)]

def base (A : ℝ) : Vector := ![A,0,0]
def shifted (ν t A : ℝ) : Vector := ![A,0,jump ν t]

theorem base_flow (ν t A : ℝ) :
    ViscousTriadFlow.vectorFlow ν t (base A)=![damping ν t*A,0,0] := by
  simp [ViscousTriadFlow.vectorFlow_formula,base]

theorem shifted_flow (ν t A : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    ViscousTriadFlow.vectorFlow ν t (shifted ν t A)=
      ![-damping ν t*A,0,damping (2*ν) t*jump ν t] := by
  simp [ViscousTriadFlow.vectorFlow_formula,shifted,jump_phase ν t hν ht]

theorem initial_separation (ν t A : ℝ) :
    energy (shifted ν t A-base A)=4*(jump ν t)^2 := by
  simp [energy,shifted,base,Pi.sub_apply]

theorem evolved_separation (ν t A : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    energy (ViscousTriadFlow.vectorFlow ν t (shifted ν t A)-
      ViscousTriadFlow.vectorFlow ν t (base A))=
        8*(damping ν t*A)^2+4*(damping (2*ν) t*jump ν t)^2 := by
  rw [shifted_flow ν t A hν ht,base_flow]
  simp [energy,Pi.sub_apply]
  ring

def amplitude (ν t K : ℝ) : ℝ := jump ν t*(|K|+1)/damping ν t

theorem amplitude_pos (ν t K : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    0 < amplitude ν t K := by
  unfold amplitude damping
  exact div_pos (mul_pos (jump_pos ν t hν ht) (by positivity)) (Real.exp_pos _)

theorem amplitude_damped (ν t K : ℝ) :
    damping ν t*amplitude ν t K=jump ν t*(|K|+1) := by
  unfold amplitude
  field_simp [show damping ν t ≠ 0 from ne_of_gt (Real.exp_pos _)]

theorem arbitrary_amplification (ν t K : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    K*energy (shifted ν t (amplitude ν t K)-base (amplitude ν t K)) <
      energy (ViscousTriadFlow.vectorFlow ν t (shifted ν t (amplitude ν t K))-
        ViscousTriadFlow.vectorFlow ν t (base (amplitude ν t K))) := by
  rw [initial_separation,evolved_separation ν t _ hν ht,amplitude_damped,mul_pow]
  have hj : 0 < (jump ν t)^2 := sq_pos_of_pos (jump_pos ν t hν ht)
  have hk : 0 < 2*(|K|+1)^2-K := by
    nlinarith [abs_nonneg K,le_abs_self K,sq_nonneg (|K|+1)]
  have hp := mul_pos hj hk
  nlinarith [sq_nonneg (damping (2*ν) t*jump ν t)]

/-- No finite squared-energy distance factor controls all pairs, at any positive time. -/
theorem no_uniform_energy_factor (ν t K : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    ¬ (∀ x y : Vector, energy (ViscousTriadFlow.vectorFlow ν t x-
        ViscousTriadFlow.vectorFlow ν t y) ≤ K*energy (x-y)) := by
  intro h
  exact not_le.mpr (arbitrary_amplification ν t K hν ht)
    (h (shifted ν t (amplitude ν t K)) (base (amplitude ν t K)))

def kineticSize (x : Vector) : ℝ := Real.sqrt (energy x)

theorem kineticSize_sq (x : Vector) : (kineticSize x)^2=energy x :=
  Real.sq_sqrt (energy_nonneg x)

theorem no_uniform_size_factor (ν t L : ℝ) (hν : 0 < ν) (ht : 0 < t) (hL : 0 ≤ L) :
    ¬ (∀ x y : Vector, kineticSize (ViscousTriadFlow.vectorFlow ν t x-
        ViscousTriadFlow.vectorFlow ν t y) ≤ L*kineticSize (x-y)) := by
  intro h
  apply no_uniform_energy_factor ν t (L^2) hν ht
  intro x y
  have hs := mul_self_le_mul_self
    (show 0 ≤ kineticSize (ViscousTriadFlow.vectorFlow ν t x-
      ViscousTriadFlow.vectorFlow ν t y) from Real.sqrt_nonneg _) (h x y)
  simpa only [← pow_two,mul_pow,kineticSize_sq] using hs

/-- Both trajectories dissipate while their mutual physical separation grows. -/
theorem expanding_pair_with_dissipation (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    ∃ x y : Vector,
      energy (ViscousTriadFlow.vectorFlow ν t x)<energy x ∧
      energy (ViscousTriadFlow.vectorFlow ν t y)<energy y ∧
      energy (x-y)<energy (ViscousTriadFlow.vectorFlow ν t x-
        ViscousTriadFlow.vectorFlow ν t y) := by
  let A := amplitude ν t 1
  have hA : 0 < A := amplitude_pos ν t 1 hν ht
  have hx : 0 < energy (shifted ν t A) := by
    simp only [energy,shifted,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero]
    nlinarith [sq_pos_of_pos hA,sq_nonneg (jump ν t)]
  have hy : 0 < energy (base A) := by
    simp [energy,base]
    exact sq_pos_of_pos hA
  refine ⟨shifted ν t A,base A,energy_strict ν t hν ht _ hx,
    energy_strict ν t hν ht _ hy,?_⟩
  simpa only [one_mul] using arbitrary_amplification ν t 1 hν ht

end OperatorDerivativeRewrite.Foundation.ViscousTriadSeparation
