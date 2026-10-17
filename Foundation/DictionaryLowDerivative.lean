import Foundation.DictionaryTriadLocalization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A retained low-direction derivative depends on an unretained high mode,
even at zero retained field. Both Fourier symbols and actual periodic fields are checked. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.DictionaryLowDerivative
open SectorTransferSymmetry DictionaryTriadLocalization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def response (N : ℤ) (c a : ℝ) : Vector :=
  leray (output N) (coefficient low (high N) (a • e2) (c • e3))

theorem response_formula (N : ℤ) (c a : ℝ) : response N c a=(a*c*(N : ℝ)) • e3 := by
  ext i
  fin_cases i <;>
    simp [response,leray,coefficient,dotWave,low,high,output,e2,e3,
      Fin.sum_univ_succ,smul_eq_mul] <;> ring

theorem response_derivative (N : ℤ) (c : ℝ) :
    HasDerivAt (fun a => response N c a 2) (c*(N : ℝ)) 0 := by
  have he : (fun a => response N c a 2)=fun a => a*(c*(N : ℝ)) := by
    funext a
    simp [response_formula,e3,smul_eq_mul]
    ring
  rw [he]
  simpa using (hasDerivAt_id (0 : ℝ)).mul_const (c*(N : ℝ))

theorem cutoff_separation (N : ℤ) (hN : 4 ≤ N) :
    waveSquare low ≤ ((N : ℝ)/2)^2 ∧ ((N : ℝ)/2)^2 < waveSquare (high N) ∧
      ((N : ℝ)/2)^2 < waveSquare (output N) ∧
      ((N : ℝ)/2)^2 < waveSquare (output (-N)) := by
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hl,hh,ho⟩ := low_high_sizes N
  have hm := (low_high_sizes (-N)).2.2
  rw [hl,hh,ho,hm]
  push_cast
  constructor
  · nlinarith [sq_nonneg ((N : ℝ)-2)]
  constructor
  · nlinarith [sq_nonneg ((N : ℝ)-2)]
  constructor <;> nlinarith [sq_nonneg ((N : ℝ)-2)]

def mode (N : ℤ) (i : Fin 4) : Wave := ![low,high N,-low,-high N] i
def amplitude (a c : ℝ) (i : Fin 4) : Vector := ![a • e2,c • e3,-a • e2,-c • e3] i
def fourierTerm (N : ℤ) (a c : ℝ) (i : Fin 4) (x : Vector) (j : Fin 3) : ℂ :=
  (Complex.I*(amplitude a c i j : ℂ))*Complex.exp ((dotWave (mode N i) x : ℂ)*Complex.I)
def synthesis (N : ℤ) (a c : ℝ) (x : Vector) (j : Fin 3) : ℂ :=
  ∑ i : Fin 4, fourierTerm N a c i x j

def lowSynthesis (K : ℝ) (N : ℤ) (a c : ℝ) (x : Vector) (j : Fin 3) : ℂ :=
  ∑ i : Fin 4, if waveSquare (mode N i) ≤ K^2 then fourierTerm N a c i x j else 0

def lowH1Energy (K : ℝ) (N : ℤ) (a c : ℝ) : ℝ :=
  ∑ i : Fin 4, if waveSquare (mode N i) ≤ K^2 then
    (1+waveSquare (mode N i))*dotVector (amplitude a c i) (amplitude a c i) else 0

theorem retained_amplitude_zero (N : ℤ) (hN : 4 ≤ N) (c : ℝ) (i : Fin 4)
    (hi : waveSquare (mode N i) ≤ ((N : ℝ)/2)^2) : amplitude 0 c i=0 := by
  have hh := (cutoff_separation N hN).2.1
  fin_cases i
  · simp [amplitude]
  · exact (not_le.mpr hh hi).elim
  · simp [amplitude]
  · apply False.elim
    apply not_le.mpr hh
    simpa [mode,waveSquare,high,Fin.sum_univ_succ] using hi

theorem lowSynthesis_zero (N : ℤ) (hN : 4 ≤ N) (c : ℝ) :
    lowSynthesis ((N : ℝ)/2) N 0 c=fun _ _ => 0 := by
  funext x j
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs with hs
  · simp [fourierTerm,retained_amplitude_zero N hN c i hs]
  · rfl

theorem lowH1Energy_zero (N : ℤ) (hN : 4 ≤ N) (c : ℝ) :
    lowH1Energy ((N : ℝ)/2) N 0 c=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs with hs
  · simp [retained_amplitude_zero N hN c i hs,dotVector]
  · rfl

/-- No bound proportional only to the retained H1 energy holds at this high background. -/
theorem no_low_only_derivative_bound (N : ℤ) (hN : 4 ≤ N) (c C : ℝ) (hc : c ≠ 0) :
    ¬ |deriv (fun a => response N c a 2) 0| ≤ C*Real.sqrt (lowH1Energy ((N : ℝ)/2) N 0 c) := by
  rw [(response_derivative N c).deriv,lowH1Energy_zero N hN c,Real.sqrt_zero,mul_zero]
  apply not_le.mpr
  apply abs_pos.mpr
  apply mul_ne_zero hc
  exact_mod_cast (show N ≠ 0 by omega)

def velocity (N : ℤ) (a c : ℝ) (x : Vector) : Vector :=
  ![0,-2*a*Real.sin (x 0),-2*c*Real.sin ((N : ℝ)*x 1)]

theorem synthesis_eq_velocity (N : ℤ) (a c : ℝ) (x : Vector) (j : Fin 3) :
    synthesis N a c x j=(velocity N a c x j : ℂ) := by
  apply Complex.ext
  · change (synthesis N a c x j).re=velocity N a c x j
    fin_cases j <;>
      simp [synthesis,fourierTerm,mode,amplitude,low,high,e2,e3,dotWave,velocity,
        Fin.sum_univ_succ,smul_eq_mul,Complex.mul_re,Complex.mul_im,
        Complex.exp_re,Complex.exp_im] <;> ring
  · change (synthesis N a c x j).im=0
    fin_cases j <;>
      simp [synthesis,fourierTerm,mode,amplitude,low,high,e2,e3,dotWave,
        Fin.sum_univ_succ,smul_eq_mul,Complex.mul_re,Complex.mul_im,
        Complex.exp_re,Complex.exp_im] <;> ring

theorem velocity_smooth (N : ℤ) (a c : ℝ) : ContDiff ℝ ⊤ (velocity N a c) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ ⊤ (fun _ : Vector => (0 : ℝ))
    fun_prop
  · change ContDiff ℝ ⊤ (fun x : Vector => -2*a*Real.sin (x 0))
    fun_prop
  · change ContDiff ℝ ⊤ (fun x : Vector => -2*c*Real.sin ((N : ℝ)*x 1))
    fun_prop

theorem velocity_periodic (N : ℤ) (a c : ℝ) (i : Fin 3) (x : Vector) :
    velocity N a c (x+Pi.single i (2*Real.pi))=velocity N a c x := by
  have hn : Real.sin ((N : ℝ)*(x 1+2*Real.pi))=Real.sin ((N : ℝ)*x 1) := by
    rw [mul_add,Real.sin_add_int_mul_two_pi]
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [velocity,Pi.add_apply,Pi.single_apply,Real.sin_add_two_pi,hn]

def axis (i : Fin 3) : Vector := Pi.single i 1

def spatialPartial (u : Vector → Vector) (i j : Fin 3) (x : Vector) : ℝ :=
  deriv (fun t : ℝ => u (x+t • axis i) j) 0

theorem velocity_directional (N : ℤ) (a c : ℝ) (i : Fin 3) (x : Vector) :
    HasDerivAt (fun t : ℝ => velocity N a c (x+t • axis i))
      ![0,(-2*a*Real.cos (x 0))*axis i 0,
        (-2*c*(N : ℝ)*Real.cos ((N : ℝ)*x 1))*axis i 1] 0 := by
  have hd (k : Fin 3) : HasDerivAt (fun t : ℝ => (x+t • axis i) k)
      (axis i k) 0 := by
    simpa [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (axis i k)).const_add (x k)
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j
  · simpa [velocity] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · convert (hd 0).sin.const_mul (-2*a) using 1 <;>
      simp [velocity,Pi.add_apply,Pi.smul_apply,axis,Pi.single_apply] <;> ring
  · convert ((hd 1).const_mul (N : ℝ)).sin.const_mul (-2*c) using 1 <;>
      simp [velocity,Pi.add_apply,Pi.smul_apply,axis,Pi.single_apply] <;> ring

theorem partial_formula (N : ℤ) (a c : ℝ) (i j : Fin 3) (x : Vector) :
    spatialPartial (velocity N a c) i j x=
      ![0,(-2*a*Real.cos (x 0))*axis i 0,
        (-2*c*(N : ℝ)*Real.cos ((N : ℝ)*x 1))*axis i 1] j :=
  (hasDerivAt_pi.mp (velocity_directional N a c i x) j).deriv

def divergence (u : Vector → Vector) (x : Vector) : ℝ := ∑ i : Fin 3, spatialPartial u i i x

theorem velocity_divergence_zero (N : ℤ) (a c : ℝ) (x : Vector) :
    divergence (velocity N a c) x=0 := by
  simp [divergence,partial_formula,Fin.sum_univ_succ,axis,Pi.single_apply]

def advection (N : ℤ) (a c : ℝ) (x : Vector) (j : Fin 3) : ℝ :=
  ∑ i : Fin 3, velocity N a c x i*spatialPartial (velocity N a c) i j x

theorem advection_formula (N : ℤ) (a c : ℝ) (x : Vector) :
    advection N a c x=![0,0,4*a*c*(N : ℝ)*Real.sin (x 0)*Real.cos ((N : ℝ)*x 1)] := by
  ext j
  fin_cases j <;> simp [advection,partial_formula,velocity,Fin.sum_univ_succ,axis,Pi.single_apply] <;> ring

theorem advection_divergence_zero (N : ℤ) (a c : ℝ) (x : Vector) :
    divergence (advection N a c) x=0 := by
  simp [divergence,spatialPartial,advection_formula,Fin.sum_univ_succ,
    Pi.add_apply,Pi.smul_apply,axis,Pi.single_apply]

theorem advection_high_waves (N : ℤ) (a c : ℝ) (x : Vector) :
    advection N a c x=
      (2*a*c*(N : ℝ)*(Real.sin (dotWave (output N) x)+Real.sin (dotWave (output (-N)) x))) • e3 := by
  rw [advection_formula]
  ext j
  fin_cases j <;> simp [dotWave,output,e3,Fin.sum_univ_succ,smul_eq_mul,
    Real.sin_add,Real.sin_sub] <;> ring

theorem leray_output_e3 (N : ℤ) : leray (output N) e3=e3 := by
  apply leray_of_transverse
  simp [dotWave,output,e3,Fin.sum_univ_succ]

def projectedAdvection (N : ℤ) (a c : ℝ) (x : Vector) : Vector :=
  (2*a*c*(N : ℝ)*Real.sin (dotWave (output N) x)) • leray (output N) e3+
    (2*a*c*(N : ℝ)*Real.sin (dotWave (output (-N)) x)) • leray (output (-N)) e3

theorem projectedAdvection_eq (N : ℤ) (a c : ℝ) (x : Vector) :
    projectedAdvection N a c x=advection N a c x := by
  rw [projectedAdvection,advection_high_waves,leray_output_e3,leray_output_e3,← add_smul]
  congr 1
  ring

theorem physical_derivative (N : ℤ) (c : ℝ) (x : Vector) :
    HasDerivAt (fun a => advection N a c x 2)
      (4*c*(N : ℝ)*Real.sin (x 0)*Real.cos ((N : ℝ)*x 1)) 0 := by
  have he : (fun a => advection N a c x 2)=
      fun a => a*(4*c*(N : ℝ)*Real.sin (x 0)*Real.cos ((N : ℝ)*x 1)) := by
    funext a
    simp [advection_formula]
    ring
  rw [he]
  simpa using (hasDerivAt_id (0 : ℝ)).mul_const
    (4*c*(N : ℝ)*Real.sin (x 0)*Real.cos ((N : ℝ)*x 1))

theorem projected_physical_derivative (N : ℤ) (c : ℝ) (x : Vector) :
    HasDerivAt (fun a => projectedAdvection N a c x 2)
      (4*c*(N : ℝ)*Real.sin (x 0)*Real.cos ((N : ℝ)*x 1)) 0 := by
  simpa only [projectedAdvection_eq] using physical_derivative N c x

theorem cosine_frequency_energy (N : ℤ) (hN : N ≠ 0) :
    (∫ y in (0 : ℝ)..2*Real.pi, (Real.cos ((N : ℝ)*y))^2)=Real.pi := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hs : Real.sin ((N : ℝ)*(2*Real.pi))=0 := by
    simpa using Real.sin_add_int_mul_two_pi 0 N
  rw [intervalIntegral.integral_comp_mul_left (fun y : ℝ => (Real.cos y)^2) hn,integral_cos_sq]
  simp [hs,smul_eq_mul]
  field_simp [hn]
  <;> ring

def derivativeEnergy (N : ℤ) (c : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..2*Real.pi, ∫ t in (0 : ℝ)..2*Real.pi,
    ∫ r in (0 : ℝ)..2*Real.pi,
      (deriv (fun a => projectedAdvection N a c ![s,t,r] 2) 0)^2)/(2*Real.pi)^3

theorem derivativeEnergy_formula (N : ℤ) (hN : N ≠ 0) (c : ℝ) :
    derivativeEnergy N c=4*c^2*(N : ℝ)^2 := by
  have hi (s : ℝ) : (∫ t in (0 : ℝ)..2*Real.pi,
      (4*c*(N : ℝ)*Real.sin s*Real.cos ((N : ℝ)*t))^2)=
        16*c^2*(N : ℝ)^2*(Real.sin s)^2*Real.pi := by
    have he : (fun t => (4*c*(N : ℝ)*Real.sin s*Real.cos ((N : ℝ)*t))^2)=
        fun t => (16*c^2*(N : ℝ)^2*(Real.sin s)^2)*(Real.cos ((N : ℝ)*t))^2 := by
      funext t
      ring
    rw [he,intervalIntegral.integral_const_mul,cosine_frequency_energy N hN]
  have ho : (∫ s in (0 : ℝ)..2*Real.pi,
      16*c^2*(N : ℝ)^2*(Real.sin s)^2*Real.pi)=16*c^2*(N : ℝ)^2*Real.pi^2 := by
    have he : (fun s => 16*c^2*(N : ℝ)^2*(Real.sin s)^2*Real.pi)=
        fun s => (16*c^2*(N : ℝ)^2*Real.pi)*(Real.sin s)^2 := by funext s; ring
    rw [he,intervalIntegral.integral_const_mul,integral_sin_sq]
    simp [Real.sin_two_pi]
    ring
  have hd (x : Vector) := (physical_derivative N c x).deriv
  unfold derivativeEnergy
  simp_rw [projectedAdvection_eq,hd]
  change (∫ s in (0 : ℝ)..2*Real.pi, ∫ t in (0 : ℝ)..2*Real.pi,
    ∫ r in (0 : ℝ)..2*Real.pi,
      (4*c*(N : ℝ)*Real.sin s*Real.cos ((N : ℝ)*t))^2)/(2*Real.pi)^3=4*c^2*(N : ℝ)^2
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  simp_rw [intervalIntegral.integral_const_mul,hi]
  rw [ho]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem no_physical_low_only_bound (N : ℤ) (hN : 4 ≤ N) (c C : ℝ) (hc : c ≠ 0) :
    ¬ Real.sqrt (derivativeEnergy N c) ≤ C*Real.sqrt (lowH1Energy ((N : ℝ)/2) N 0 c) := by
  have hn : N ≠ 0 := by omega
  have hnr : (N : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [lowH1Energy_zero N hN c,Real.sqrt_zero,mul_zero]
  apply not_le.mpr
  apply Real.sqrt_pos.mpr
  rw [derivativeEnergy_formula N hn c]
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hc)) (sq_pos_of_ne_zero hnr)

theorem physical_probe_derivative (N : ℤ) (c : ℝ) :
    HasDerivAt (fun a => advection N a c ![Real.pi/2,0,0] 2) (4*c*(N : ℝ)) 0 := by
  have he : (fun a => advection N a c ![Real.pi/2,0,0] 2)=fun a => a*(4*c*(N : ℝ)) := by
    funext a
    simp [advection_formula]
    ring
  rw [he]
  simpa using (hasDerivAt_id (0 : ℝ)).mul_const (4*c*(N : ℝ))

end OperatorDerivativeRewrite.Foundation.DictionaryLowDerivative
