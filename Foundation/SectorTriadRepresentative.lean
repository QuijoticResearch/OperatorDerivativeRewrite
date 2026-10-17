import Foundation.SectorTriadSign
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual periodic Fourier representative and full-transfer bridge for the signed triad. -/
noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.SectorTriadRepresentative
open SectorTransferSymmetry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem fullTransfer_eq_finite (K : Finset Wave) (V : Field)
    (hV : ∀ k, k∉K → V k=0) (k : Wave) : fullTransfer V k=transfer K V k := by
  have hout (p : Wave) (hp : p∉K) :
      dotWave (k-p) (V p)*dotVector (V k) (V (k-p))=0 := by simp [hV p hp,dotWave]
  have hinner (p : Wave) : (∑ q ∈ K, triadTerm V k p q)=
      dotWave (k-p) (V p)*dotVector (V k) (V (k-p)) := by
    have he (q : Wave) : p+q=k ↔ q=k-p := by
      constructor
      · intro h
        calc
          q = (p+q)-p := by abel
          _ = k-p := by rw [h]
      · intro h
        rw [h]
        abel
    simp only [triadTerm,he]
    by_cases hq : k-p∈K
    · simp [hq]
    · simp [hq,hV (k-p) hq,dotVector]
  unfold fullTransfer transfer
  rw [tsum_eq_sum (s := K) hout]
  simp_rw [hinner]

theorem fullTransfer_off (K : Finset Wave) (V : Field) (hV : ∀ k, k∉K → V k=0)
    (k : Wave) (hk : k∉K) : fullTransfer V k=0 := by
  simp [fullTransfer,hV k hk,dotVector]

theorem triad_fullTransfer (i : Fin 6) :
    fullTransfer SectorTriadSign.polarization (SectorTriadSign.mode i)=SectorTriadSign.transfers i := by
  rw [fullTransfer_eq_finite SectorTriadSign.modes _ SectorTriadSign.polarization_off]
  exact SectorTriadSign.mode_transfer i

theorem sum_modes_complex (f : Wave → ℂ) :
    (∑ k ∈ SectorTriadSign.modes, f k)=∑ i : Fin 6, f (SectorTriadSign.mode i) := by
  unfold SectorTriadSign.modes
  rw [Finset.sum_image]
  intro i _ j _ h
  exact SectorTriadSign.mode_injective h

def coefficient (k : Wave) (i : Fin 3) : ℂ := Complex.I*(SectorTriadSign.polarization k i : ℂ)
def fourierTerm (k : Wave) (x : Vector) (i : Fin 3) : ℂ :=
  coefficient k i*Complex.exp ((dotWave k x : ℂ)*Complex.I)
def synthesis (x : Vector) (i : Fin 3) : ℂ :=
  ∑ k ∈ SectorTriadSign.modes, fourierTerm k x i
def phases (x : Vector) : Fin 6 → ℝ :=
  ![x 0,x 1,x 0+x 1,-x 0,-x 1,-(x 0+x 1)]
def velocity (x : Vector) : Vector :=
  ![2*Real.sin (x 1)+2*Real.sin (x 0+x 1),-4*Real.sin (x 0)-2*Real.sin (x 0+x 1),0]

theorem coefficient_imaginary (k : Wave) (i : Fin 3) : (coefficient k i).re=0 := by
  simp [coefficient,Complex.mul_re]

theorem coefficient_reality (k : Wave) (i : Fin 3) : coefficient (-k) i=conj (coefficient k i) := by
  have hp := congrFun (SectorTriadSign.polarization_odd k) i
  simp only [Pi.neg_apply] at hp
  simp [coefficient,hp]

theorem phase_mode (x : Vector) (i : Fin 6) : dotWave (SectorTriadSign.mode i) x=phases x i := by
  fin_cases i <;> norm_num [dotWave,SectorTriadSign.mode,phases,Fin.sum_univ_succ] <;> ring

theorem term_real_mode (x : Vector) (i : Fin 6) (j : Fin 3) :
    (fourierTerm (SectorTriadSign.mode i) x j).re =
      -SectorTriadSign.amplitude i j*Real.sin (phases x i) := by
  simp [fourierTerm,coefficient,SectorTriadSign.polarization_mode,phase_mode,Complex.mul_re,Complex.mul_im]

theorem term_imag_mode (x : Vector) (i : Fin 6) (j : Fin 3) :
    (fourierTerm (SectorTriadSign.mode i) x j).im =
      SectorTriadSign.amplitude i j*Real.cos (phases x i) := by
  simp [fourierTerm,coefficient,SectorTriadSign.polarization_mode,phase_mode,Complex.mul_re,Complex.mul_im]

theorem synthesis_eq_velocity (x : Vector) (j : Fin 3) : synthesis x j=(velocity x j : ℂ) := by
  have hs : Real.sin (-x 0-x 1)= -Real.sin (x 0+x 1) := by
    rw [show -x 0-x 1= -(x 0+x 1) by ring,Real.sin_neg]
  have hc : Real.cos (-x 0-x 1)=Real.cos (x 0+x 1) := by
    rw [show -x 0-x 1= -(x 0+x 1) by ring,Real.cos_neg]
  unfold synthesis
  rw [sum_modes_complex]
  apply Complex.ext
  · change _ = velocity x j
    fin_cases j <;>
      simp [Fin.sum_univ_succ,Complex.add_re,term_real_mode,SectorTriadSign.amplitude,
        phases,velocity] <;> ring_nf <;> (try rw [hs]) <;> ring
  · change _ = (0 : ℝ)
    fin_cases j <;>
      simp [Fin.sum_univ_succ,Complex.add_im,term_imag_mode,SectorTriadSign.amplitude,
        phases,velocity] <;> ring_nf <;> (try rw [hc]) <;> ring

theorem velocity_smooth : ContDiff ℝ ⊤ velocity := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ⊤ (fun x : Vector => 2*Real.sin (x 1)+2*Real.sin (x 0+x 1))
    fun_prop
  · change ContDiff ℝ ⊤ (fun x : Vector => -4*Real.sin (x 0)-2*Real.sin (x 0+x 1))
    fun_prop
  · change ContDiff ℝ ⊤ (fun _ : Vector => (0 : ℝ))
    fun_prop

theorem velocity_periodic (i : Fin 3) (x : Vector) :
    velocity (x+Pi.single i (2*Real.pi))=velocity x := by
  have h0 : Real.sin (x 0+2*Real.pi+x 1)=Real.sin (x 0+x 1) := by
    rw [show x 0+2*Real.pi+x 1=x 0+x 1+2*Real.pi by ring,Real.sin_add_two_pi]
  have h1 : Real.sin (x 0+(x 1+2*Real.pi))=Real.sin (x 0+x 1) := by
    rw [← add_assoc,Real.sin_add_two_pi]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [velocity,Pi.add_apply,Pi.single_apply,Real.sin_add_two_pi,h0,h1]

def divergence (x : Vector) : ℝ :=
  ∑ i : Fin 3, deriv (fun t : ℝ => velocity (x+t • Pi.single i (1 : ℝ)) i) 0

theorem divergence_zero (x : Vector) : divergence x=0 := by
  have hd0 : HasDerivAt (fun t : ℝ => x 0+t+x 1) 1 0 :=
    ((hasDerivAt_id 0).const_add (x 0)).add_const (x 1)
  have hd1 : HasDerivAt (fun t : ℝ => x 0+(x 1+t)) 1 0 :=
    ((hasDerivAt_id 0).const_add (x 1)).const_add (x 0)
  have h0 : deriv (fun t : ℝ => velocity (x+t • Pi.single (0 : Fin 3) (1 : ℝ)) 0) 0 =
      2*Real.cos (x 0+x 1) := by
    simpa [velocity,Pi.add_apply,Pi.smul_apply,Pi.single_apply] using
      ((hd0.sin.const_mul 2).const_add (2*Real.sin (x 1))).deriv
  have h1 : deriv (fun t : ℝ => velocity (x+t • Pi.single (1 : Fin 3) (1 : ℝ)) 1) 0 =
      -2*Real.cos (x 0+x 1) := by
    simpa [velocity,Pi.add_apply,Pi.smul_apply,Pi.single_apply] using hd1.sin.deriv
  unfold divergence
  rw [Fin.sum_univ_three]
  rw [h0,h1]
  simp [velocity]

theorem velocity_nonzero : velocity ![Real.pi/2,0,0] ≠ 0 := by
  intro h
  have hh := congrFun h 0
  norm_num [velocity] at hh

theorem signed_transfer_example :
    totalTransfer SectorTriadSign.modes SectorTriadSign.polarization=0 ∧
    sigma SectorTriadSign.modes SectorTriadSign.sector SectorTriadSign.polarization=4/27 ∧
    rate SectorTriadSign.modes SectorTriadSign.sector SectorTriadSign.polarization= -128/149 ∧
    ContDiff ℝ ⊤ velocity ∧ (∀ x, divergence x=0) ∧
    (∀ x i, synthesis x i=(velocity x i : ℂ)) :=
  ⟨SectorTriadSign.totalTransfer_zero,SectorTriadSign.sigma_exact,SectorTriadSign.rate_exact,
    velocity_smooth,divergence_zero,synthesis_eq_velocity⟩

end OperatorDerivativeRewrite.Foundation.SectorTriadRepresentative
