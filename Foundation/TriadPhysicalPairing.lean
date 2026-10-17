import Foundation.DictionaryTriadPhysicalMetric
import Foundation.ViscousTriadSeparation

/-! Direct torus integrals give the full finite velocity Gram matrix and the
physical L2 version of viscous-triad separation. No Parseval theorem is assumed. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.TriadPhysicalPairing
open SectorTransferSymmetry (Vector dotVector)
open ParameterizedTriadRepresentative (velocity)
open DictionaryTriadPhysicalMetric
set_option backward.isDefEq.respectTransparency false

theorem shifted_sin_square_integral (s : ℝ) :
    (∫ t in (0 : ℝ)..2*Real.pi, (Real.sin (s+t))^2)=Real.pi := by
  rw [intervalIntegral.integral_comp_add_left (fun t : ℝ => (Real.sin t)^2) s,integral_sin_sq]
  simp [Real.sin_add_two_pi,Real.cos_add_two_pi]

def integrand (x y : Vector) (s t : ℝ) : ℝ :=
  dotVector (velocity (x 0) (x 1) (x 2) ![s,t,0])
    (velocity (y 0) (y 1) (y 2) ![s,t,0])

theorem integrand_intervalIntegrable (x y : Vector) (s : ℝ) :
    IntervalIntegrable (integrand x y s) volume 0 (2*Real.pi) := by
  change IntervalIntegrable (fun t : ℝ =>
    dotVector (velocity (x 0) (x 1) (x 2) ![s,t,0])
      (velocity (y 0) (y 1) (y 2) ![s,t,0])) volume 0 (2*Real.pi)
  apply Continuous.intervalIntegrable
  unfold dotVector velocity
  fun_prop

theorem integrand_decomp (x y : Vector) (s t : ℝ) :
    integrand x y s t=y 0*integrand x ![1,0,0] s t+
      y 1*integrand x ![0,1,0] s t+y 2*integrand x ![0,0,1] s t := by
  norm_num [integrand,dotVector,velocity,Fin.sum_univ_succ] <;> ring

theorem third_integrand (x : Vector) (s t : ℝ) : integrand x ![0,0,1] s t=
    4*x 1*(Real.sin t*Real.sin (s+t))+(4*x 0*Real.sin s)*Real.sin (s+t)+
      8*x 2*(Real.sin (s+t))^2 := by
  norm_num [integrand,dotVector,velocity,Fin.sum_univ_succ] <;> ring

theorem third_inner_integral (x : Vector) (s : ℝ) :
    (∫ t in (0 : ℝ)..2*Real.pi, integrand x ![0,0,1] s t)=
      4*x 1*Real.pi*Real.cos s+8*x 2*Real.pi := by
  have hi : IntervalIntegrable (fun t => 4*x 1*(Real.sin t*Real.sin (s+t)))
      volume 0 (2*Real.pi) := by apply Continuous.intervalIntegrable; fun_prop
  have hj : IntervalIntegrable (fun t => (4*x 0*Real.sin s)*Real.sin (s+t))
      volume 0 (2*Real.pi) := by apply Continuous.intervalIntegrable; fun_prop
  have hk : IntervalIntegrable (fun t => 8*x 2*(Real.sin (s+t))^2)
      volume 0 (2*Real.pi) := by apply Continuous.intervalIntegrable; fun_prop
  simp_rw [third_integrand]
  rw [intervalIntegral.integral_add (hi.add hj) hk,intervalIntegral.integral_add hi hj,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,sin_shift_product_integral,shifted_sin_integral,
    shifted_sin_square_integral]
  ring

theorem inner_integral_formula (x y : Vector) (s : ℝ) :
    (∫ t in (0 : ℝ)..2*Real.pi, integrand x y s t)=
      (8*Real.pi*x 0*y 0)*(Real.sin s)^2+
      (4*Real.pi*(x 2*y 1+x 1*y 2))*Real.cos s+
      (4*Real.pi*x 1*y 1+8*Real.pi*x 2*y 2) := by
  have he : integrand x y s=fun t => y 0*integrand x ![1,0,0] s t+
      y 1*integrand x ![0,1,0] s t+y 2*integrand x ![0,0,1] s t :=
    funext (integrand_decomp x y s)
  have hi := (integrand_intervalIntegrable x ![1,0,0] s).const_mul (y 0)
  have hj := (integrand_intervalIntegrable x ![0,1,0] s).const_mul (y 1)
  have hk := (integrand_intervalIntegrable x ![0,0,1] s).const_mul (y 2)
  rw [he,intervalIntegral.integral_add (hi.add hj) hk,intervalIntegral.integral_add hi hj,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hf : (∫ t in (0 : ℝ)..2*Real.pi, integrand x ![1,0,0] s t)=
      (2*Real.pi)*(4*x 0*(Real.sin s)^2) := by
    simpa [integrand] using first_inner_integral (x 0) (x 1) (x 2) s
  have hg : (∫ t in (0 : ℝ)..2*Real.pi, integrand x ![0,1,0] s t)=
      4*x 1*Real.pi+(4*x 2*Real.pi)*Real.cos s := by
    simpa [integrand] using second_inner_integral (x 0) (x 1) (x 2) s
  rw [hf,hg,third_inner_integral]
  ring

theorem physicalPair_formula (x y : Vector) :
    physicalPair x y=2*x 0*y 0+2*x 1*y 1+4*x 2*y 2 := by
  change (∫ s in (0 : ℝ)..2*Real.pi, ∫ t in (0 : ℝ)..2*Real.pi,
    integrand x y s t)/(2*Real.pi)^2=_
  simp_rw [inner_integral_formula]
  have hi : IntervalIntegrable (fun s => (8*Real.pi*x 0*y 0)*(Real.sin s)^2)
      volume 0 (2*Real.pi) := by apply Continuous.intervalIntegrable; fun_prop
  have hj : IntervalIntegrable (fun s => (4*Real.pi*(x 2*y 1+x 1*y 2))*Real.cos s)
      volume 0 (2*Real.pi) := by apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add (hi.add hj) intervalIntegrable_const,
    intervalIntegral.integral_add hi hj,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,integral_sin_sq,integral_cos,
    intervalIntegral.integral_const]
  simp [Real.sin_two_pi]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem physicalPair3_formula (x y : Vector) :
    physicalPair3 x y=2*x 0*y 0+2*x 1*y 1+4*x 2*y 2 := by
  rw [physicalPair3_eq,physicalPair_formula]

theorem physicalPair3_eq_kinetic (x y : Vector) :
    physicalPair3 x y=DictionaryTriadPotential.kineticPair x y := by
  rw [physicalPair3_formula,DictionaryTriadPotential.kineticPair_formula]

theorem velocity_difference (x y z : Vector) :
    velocity (x 0) (x 1) (x 2) z-velocity (y 0) (y 1) (y 2) z=
      velocity ((x-y) 0) ((x-y) 1) ((x-y) 2) z := by
  ext i
  fin_cases i <;> simp [velocity,Pi.sub_apply] <;> ring

def physicalSeparation (x y : Vector) : ℝ :=
  (∫ s in (0 : ℝ)..2*Real.pi, ∫ t in (0 : ℝ)..2*Real.pi,
    ∫ r in (0 : ℝ)..2*Real.pi,
      dotVector (velocity (x 0) (x 1) (x 2) ![s,t,r]-velocity (y 0) (y 1) (y 2) ![s,t,r])
        (velocity (x 0) (x 1) (x 2) ![s,t,r]-velocity (y 0) (y 1) (y 2) ![s,t,r]))/
    (2*Real.pi)^3

theorem physicalSeparation_eq (x y : Vector) :
    physicalSeparation x y=ViscousTriadFlow.energy (x-y) := by
  unfold physicalSeparation
  simp_rw [velocity_difference]
  change physicalPair3 (x-y) (x-y)=_
  rw [physicalPair3_formula]
  unfold ViscousTriadFlow.energy
  ring

theorem same_third_physical (ν t : ℝ) (x y : Vector) (hc : x 2=y 2) :
    physicalSeparation (ViscousTriadFlow.vectorFlow ν t x) (ViscousTriadFlow.vectorFlow ν t y)=
      ViscousTriadFlow.damping (2*ν) t*physicalSeparation x y := by
  simp only [physicalSeparation_eq]
  exact ViscousTriadSeparation.same_third_energy ν t x y hc

theorem no_uniform_physical_factor (ν t K : ℝ) (hν : 0 < ν) (ht : 0 < t) :
    ¬ (∀ x y : Vector, physicalSeparation (ViscousTriadFlow.vectorFlow ν t x)
      (ViscousTriadFlow.vectorFlow ν t y) ≤ K*physicalSeparation x y) := by
  simpa only [physicalSeparation_eq] using ViscousTriadSeparation.no_uniform_energy_factor ν t K hν ht

end OperatorDerivativeRewrite.Foundation.TriadPhysicalPairing
