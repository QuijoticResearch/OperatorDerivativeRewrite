import Foundation.ParameterizedSectorTriad
import Foundation.SectorTriadRepresentative

/-! The entire three-amplitude signed-transfer family has exact smooth periodic representatives. -/
noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.ParameterizedTriadRepresentative
open SectorTransferSymmetry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def coefficient (a b c : ℝ) (k : Wave) (i : Fin 3) : ℂ :=
  Complex.I*(ParameterizedSectorTriad.polarization a b c k i : ℂ)
def fourierTerm (a b c : ℝ) (k : Wave) (x : Vector) (i : Fin 3) : ℂ :=
  coefficient a b c k i*Complex.exp ((dotWave k x : ℂ)*Complex.I)
def synthesis (a b c : ℝ) (x : Vector) (i : Fin 3) : ℂ :=
  ∑ k ∈ SectorTriadSign.modes, fourierTerm a b c k x i
def velocity (a b c : ℝ) (x : Vector) : Vector :=
  ![2*b*Real.sin (x 1)+2*c*Real.sin (x 0+x 1),
    -2*a*Real.sin (x 0)-2*c*Real.sin (x 0+x 1),0]

theorem coefficient_imaginary (a b c : ℝ) (k : Wave) (i : Fin 3) :
    (coefficient a b c k i).re=0 := by simp [coefficient,Complex.mul_re]

theorem coefficient_reality (a b c : ℝ) (k : Wave) (i : Fin 3) :
    coefficient a b c (-k) i=conj (coefficient a b c k i) := by
  have hp := congrFun (ParameterizedSectorTriad.polarization_odd a b c k) i
  simp only [Pi.neg_apply] at hp
  simp [coefficient,hp]

theorem term_real_mode (a b c : ℝ) (x : Vector) (i : Fin 6) (j : Fin 3) :
    (fourierTerm a b c (SectorTriadSign.mode i) x j).re =
      -ParameterizedSectorTriad.amplitude a b c i j*Real.sin (SectorTriadRepresentative.phases x i) := by
  simp [fourierTerm,coefficient,ParameterizedSectorTriad.polarization_mode,
    SectorTriadRepresentative.phase_mode,Complex.mul_re,Complex.mul_im]

theorem term_imag_mode (a b c : ℝ) (x : Vector) (i : Fin 6) (j : Fin 3) :
    (fourierTerm a b c (SectorTriadSign.mode i) x j).im =
      ParameterizedSectorTriad.amplitude a b c i j*Real.cos (SectorTriadRepresentative.phases x i) := by
  simp [fourierTerm,coefficient,ParameterizedSectorTriad.polarization_mode,
    SectorTriadRepresentative.phase_mode,Complex.mul_re,Complex.mul_im]

theorem synthesis_eq_velocity (a b c : ℝ) (x : Vector) (j : Fin 3) :
    synthesis a b c x j=(velocity a b c x j : ℂ) := by
  have hs : Real.sin (-x 0-x 1)= -Real.sin (x 0+x 1) := by
    rw [show -x 0-x 1= -(x 0+x 1) by ring,Real.sin_neg]
  have hc : Real.cos (-x 0-x 1)=Real.cos (x 0+x 1) := by
    rw [show -x 0-x 1= -(x 0+x 1) by ring,Real.cos_neg]
  unfold synthesis
  rw [SectorTriadRepresentative.sum_modes_complex]
  apply Complex.ext
  · change _ = velocity a b c x j
    fin_cases j <;>
      simp [Fin.sum_univ_succ,Complex.add_re,term_real_mode,ParameterizedSectorTriad.amplitude,
        SectorTriadRepresentative.phases,velocity] <;> ring_nf <;> (try rw [hs]) <;> ring
  · change _ = (0 : ℝ)
    fin_cases j <;>
      simp [Fin.sum_univ_succ,Complex.add_im,term_imag_mode,ParameterizedSectorTriad.amplitude,
        SectorTriadRepresentative.phases,velocity] <;> ring_nf <;> (try rw [hc]) <;> ring

theorem velocity_smooth (a b c : ℝ) : ContDiff ℝ ⊤ (velocity a b c) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ⊤ (fun x : Vector => 2*b*Real.sin (x 1)+2*c*Real.sin (x 0+x 1))
    fun_prop
  · change ContDiff ℝ ⊤ (fun x : Vector => -2*a*Real.sin (x 0)-2*c*Real.sin (x 0+x 1))
    fun_prop
  · change ContDiff ℝ ⊤ (fun _ : Vector => (0 : ℝ))
    fun_prop

theorem velocity_periodic (a b c : ℝ) (i : Fin 3) (x : Vector) :
    velocity a b c (x+Pi.single i (2*Real.pi))=velocity a b c x := by
  have h0 : Real.sin (x 0+2*Real.pi+x 1)=Real.sin (x 0+x 1) := by
    rw [show x 0+2*Real.pi+x 1=x 0+x 1+2*Real.pi by ring,Real.sin_add_two_pi]
  have h1 : Real.sin (x 0+(x 1+2*Real.pi))=Real.sin (x 0+x 1) := by
    rw [← add_assoc,Real.sin_add_two_pi]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [velocity,Pi.add_apply,Pi.single_apply,Real.sin_add_two_pi,h0,h1]

def divergence (a b c : ℝ) (x : Vector) : ℝ :=
  ∑ i : Fin 3, deriv (fun t : ℝ => velocity a b c (x+t • Pi.single i (1 : ℝ)) i) 0

theorem divergence_zero (a b c : ℝ) (x : Vector) : divergence a b c x=0 := by
  have hd0 : HasDerivAt (fun t : ℝ => x 0+t+x 1) 1 0 :=
    ((hasDerivAt_id 0).const_add (x 0)).add_const (x 1)
  have hd1 : HasDerivAt (fun t : ℝ => x 0+(x 1+t)) 1 0 :=
    ((hasDerivAt_id 0).const_add (x 1)).const_add (x 0)
  have h0 : deriv (fun t : ℝ => velocity a b c (x+t • Pi.single (0 : Fin 3) (1 : ℝ)) 0) 0 =
      2*c*Real.cos (x 0+x 1) := by
    simpa [velocity,Pi.add_apply,Pi.smul_apply,Pi.single_apply] using
      ((hd0.sin.const_mul (2*c)).const_add (2*b*Real.sin (x 1))).deriv
  have h1 : deriv (fun t : ℝ => velocity a b c (x+t • Pi.single (1 : Fin 3) (1 : ℝ)) 1) 0 =
      -2*c*Real.cos (x 0+x 1) := by
    have h := ((hd1.sin.const_mul (2*c)).neg.const_add (-2*a*Real.sin (x 0))).deriv
    simpa [velocity,Pi.add_apply,Pi.smul_apply,Pi.single_apply,sub_eq_add_neg] using h
  unfold divergence
  rw [Fin.sum_univ_three,h0,h1]
  simp [velocity] <;> ring

theorem velocity_zero_iff (a b c : ℝ) : (∀ x, velocity a b c x=0) ↔ a=0 ∧ b=0 ∧ c=0 := by
  constructor
  · intro h
    have h0 := congrFun (h ![Real.pi/2,0,0]) 0
    have h1 := congrFun (h ![Real.pi/2,0,0]) 1
    have h2 := congrFun (h ![0,Real.pi/2,0]) 0
    norm_num [velocity] at h0 h1 h2
    constructor
    · linarith
    · constructor <;> linarith
  · rintro ⟨rfl,rfl,rfl⟩ x
    ext i
    fin_cases i <;> simp [velocity]

theorem velocity_nonzero (a b c : ℝ) (he : 0 < ParameterizedSectorTriad.energyValue a b c) :
    ∃ x, velocity a b c x≠0 := by
  by_contra h
  push_neg at h
  have hz := (velocity_zero_iff a b c).mp h
  have hE := (ParameterizedSectorTriad.energy_zero_iff a b c).mpr hz
  linarith

theorem full_mode_transfer (a b c : ℝ) (i : Fin 6) :
    fullTransfer (ParameterizedSectorTriad.polarization a b c) (SectorTriadSign.mode i)=
      ParameterizedSectorTriad.transfers a b c i := by
  rw [SectorTriadRepresentative.fullTransfer_eq_finite SectorTriadSign.modes _
    (ParameterizedSectorTriad.polarization_off a b c)]
  exact ParameterizedSectorTriad.mode_transfer a b c i

theorem open_family_physical (p : Vector) (hp : p∈ParameterizedSectorTriad.negativeRegion) :
    rate SectorTriadSign.modes AngularTriadPartition.sector
      (ParameterizedSectorTriad.polarization (p 0) (p 1) (p 2))<0 ∧
    ContDiff ℝ ⊤ (velocity (p 0) (p 1) (p 2)) ∧
    (∀ x, divergence (p 0) (p 1) (p 2) x=0) ∧
    (∃ x, velocity (p 0) (p 1) (p 2) x≠0) :=
  ⟨ParameterizedSectorTriad.negativeRegion_rate p hp,velocity_smooth _ _ _,
    divergence_zero _ _ _,velocity_nonzero _ _ _ hp.1⟩

end OperatorDerivativeRewrite.Foundation.ParameterizedTriadRepresentative
