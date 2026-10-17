import Foundation.DictionaryTriadPotential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Direct normalized torus integrals identify the two metric rows needed by
the potential obstruction. No unproved Parseval identity is used. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.DictionaryTriadPhysicalMetric
open SectorTransferSymmetry ParameterizedTriadRepresentative DictionaryTriadPotential
set_option backward.isDefEq.respectTransparency false

theorem shifted_sin_integral (x : ℝ) :
    (∫ y in (0 : ℝ)..2*Real.pi, Real.sin (x+y))=0 := by
  rw [intervalIntegral.integral_comp_add_left Real.sin x,integral_sin]
  simp [Real.cos_add_two_pi]

theorem sin_shift_product_integral (x : ℝ) :
    (∫ y in (0 : ℝ)..2*Real.pi, Real.sin y*Real.sin (x+y))=Real.pi*Real.cos x := by
  have he : (fun y => Real.sin y*Real.sin (x+y)) =
      fun y => Real.sin x*(Real.sin y*Real.cos y)+Real.cos x*(Real.sin y)^2 := by
    funext y
    rw [Real.sin_add]
    ring
  have hi : IntervalIntegrable (fun y => Real.sin x*(Real.sin y*Real.cos y))
      volume 0 (2*Real.pi) := by apply Continuous.intervalIntegrable; fun_prop
  have hj : IntervalIntegrable (fun y => Real.cos x*(Real.sin y)^2)
      volume 0 (2*Real.pi) := by apply Continuous.intervalIntegrable; fun_prop
  rw [he,intervalIntegral.integral_add hi hj,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_sin_mul_cos₁,integral_sin_sq]
  simp [Real.sin_two_pi]
  ring

def physicalPair (x y : Vector) : ℝ :=
  (∫ s in (0 : ℝ)..2*Real.pi, ∫ t in (0 : ℝ)..2*Real.pi,
    dotVector (velocity (x 0) (x 1) (x 2) ![s,t,0])
      (velocity (y 0) (y 1) (y 2) ![s,t,0]))/(2*Real.pi)^2

theorem first_integrand (a b c s t : ℝ) :
    dotVector (velocity a b c ![s,t,0]) (velocity 1 0 0 ![s,t,0])=
      4*a*(Real.sin s)^2+(4*c*Real.sin s)*Real.sin (s+t) := by
  norm_num [dotVector,velocity,Fin.sum_univ_succ] <;> ring

theorem second_integrand (a b c s t : ℝ) :
    dotVector (velocity a b c ![s,t,0]) (velocity 0 1 0 ![s,t,0])=
      4*b*(Real.sin t)^2+4*c*(Real.sin t*Real.sin (s+t)) := by
  norm_num [dotVector,velocity,Fin.sum_univ_succ] <;> ring

theorem first_inner_integral (a b c s : ℝ) :
    (∫ t in (0 : ℝ)..2*Real.pi,
      dotVector (velocity a b c ![s,t,0]) (velocity 1 0 0 ![s,t,0]))=
        (2*Real.pi)*(4*a*(Real.sin s)^2) := by
  simp_rw [first_integrand]
  have hi : IntervalIntegrable (fun t => (4*c*Real.sin s)*Real.sin (s+t))
      volume 0 (2*Real.pi) := by apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add (intervalIntegrable_const) hi,
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,shifted_sin_integral]
  simp

theorem second_inner_integral (a b c s : ℝ) :
    (∫ t in (0 : ℝ)..2*Real.pi,
      dotVector (velocity a b c ![s,t,0]) (velocity 0 1 0 ![s,t,0]))=
        4*b*Real.pi+(4*c*Real.pi)*Real.cos s := by
  simp_rw [second_integrand]
  have hi : IntervalIntegrable (fun t => 4*b*(Real.sin t)^2)
      volume 0 (2*Real.pi) := by apply Continuous.intervalIntegrable; fun_prop
  have hj : IntervalIntegrable (fun t => 4*c*(Real.sin t*Real.sin (s+t)))
      volume 0 (2*Real.pi) := by apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add hi hj,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,integral_sin_sq,sin_shift_product_integral]
  simp [Real.sin_two_pi]
  ring

theorem physicalPair_first (x : Vector) : physicalPair x ![1,0,0]=2*x 0 := by
  change (∫ s in (0 : ℝ)..2*Real.pi, ∫ t in (0 : ℝ)..2*Real.pi,
    dotVector (velocity (x 0) (x 1) (x 2) ![s,t,0])
      (velocity 1 0 0 ![s,t,0]))/(2*Real.pi)^2=2*x 0
  simp_rw [first_inner_integral]
  have he : (fun s => (2*Real.pi)*(4*x 0*(Real.sin s)^2))=
      fun s => ((2*Real.pi)*(4*x 0))*(Real.sin s)^2 := by funext s; ring
  rw [he,intervalIntegral.integral_const_mul,integral_sin_sq]
  simp [Real.sin_two_pi]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem physicalPair_second (x : Vector) : physicalPair x ![0,1,0]=2*x 1 := by
  change (∫ s in (0 : ℝ)..2*Real.pi, ∫ t in (0 : ℝ)..2*Real.pi,
    dotVector (velocity (x 0) (x 1) (x 2) ![s,t,0])
      (velocity 0 1 0 ![s,t,0]))/(2*Real.pi)^2=2*x 1
  simp_rw [second_inner_integral]
  have hi : IntervalIntegrable (fun s => (4*x 2*Real.pi)*Real.cos s)
      volume 0 (2*Real.pi) := by apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_cos]
  simp [Real.sin_two_pi]
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- The obstruction uses the actual normalized physical velocity pairing. -/
theorem no_physical_negative_potential (ν : ℝ) :
    ¬ ∃ Φ : Vector → ℝ,
      (∀ a b c, HasDerivAt (fun x => Φ ![x,b,c])
        (-physicalPair (drift ν ![a,b,c]) ![1,0,0]) a) ∧
      (∀ a b c, HasDerivAt (fun y => Φ ![a,y,c])
        (-physicalPair (drift ν ![a,b,c]) ![0,1,0]) b) := by
  simpa only [physicalPair_first,physicalPair_second,neg_mul] using no_negative_kinetic_potential ν

/-- The normalized physical L2 pairing on the full three-torus. -/
def physicalPair3 (x y : Vector) : ℝ :=
  (∫ s in (0 : ℝ)..2*Real.pi, ∫ t in (0 : ℝ)..2*Real.pi,
    ∫ r in (0 : ℝ)..2*Real.pi,
      dotVector (velocity (x 0) (x 1) (x 2) ![s,t,r])
        (velocity (y 0) (y 1) (y 2) ![s,t,r]))/(2*Real.pi)^3

theorem physicalPair3_eq (x y : Vector) : physicalPair3 x y=physicalPair x y := by
  change (∫ s in (0 : ℝ)..2*Real.pi, ∫ t in (0 : ℝ)..2*Real.pi,
    ∫ r in (0 : ℝ)..2*Real.pi,
      dotVector (velocity (x 0) (x 1) (x 2) ![s,t,0])
        (velocity (y 0) (y 1) (y 2) ![s,t,0]))/(2*Real.pi)^3=physicalPair x y
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  simp_rw [intervalIntegral.integral_const_mul]
  unfold physicalPair
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem no_three_torus_negative_potential (ν : ℝ) :
    ¬ ∃ Φ : Vector → ℝ,
      (∀ a b c, HasDerivAt (fun x => Φ ![x,b,c])
        (-physicalPair3 (drift ν ![a,b,c]) ![1,0,0]) a) ∧
      (∀ a b c, HasDerivAt (fun y => Φ ![a,y,c])
        (-physicalPair3 (drift ν ![a,b,c]) ![0,1,0]) b) := by
  simpa only [physicalPair3_eq] using no_physical_negative_potential ν

end OperatorDerivativeRewrite.Foundation.DictionaryTriadPhysicalMetric
