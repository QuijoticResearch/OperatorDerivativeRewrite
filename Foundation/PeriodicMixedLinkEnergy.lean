import Foundation.PeriodicLocalSpectralSet

/-! A raw local/exterior periodic link split need not make the quadratic
curvature energy factor. This is distinct from a split into orthogonal modes. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicMixedLinkEnergy
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def innerEdge : Edge := (origin,0)
def outerEdge : Edge := (shift (shift (shift origin 1) 1) 1,0)

theorem inner_local : localEdge innerEdge := by decide
theorem outer_not_local : ¬ localEdge outerEdge := by decide

theorem int_inner_norm : (∑ p : Face, (coefficient p innerEdge)^2)=6 := by decide
theorem int_outer_norm : (∑ p : Face, (coefficient p outerEdge)^2)=6 := by decide
theorem int_cross : (∑ p : Face, coefficient p innerEdge*coefficient p outerEdge)=-1 :=
  by decide

def column (e : Edge) : Face → ℝ := incidence (Pi.single e (1 : ℝ))

theorem column_entry (e : Edge) (p : Face) : column e p=(coefficient p e : ℝ) := by
  simp [column,incidence,curl,coefficient,Pi.single_apply,eq_comm]

theorem inner_norm : dotProduct (column innerEdge) (column innerEdge)=6 := by
  simp only [dotProduct,column_entry,← pow_two]
  exact_mod_cast int_inner_norm

theorem outer_norm : dotProduct (column outerEdge) (column outerEdge)=6 := by
  simp only [dotProduct,column_entry,← pow_two]
  exact_mod_cast int_outer_norm

theorem cross : dotProduct (column innerEdge) (column outerEdge)=-1 := by
  simp only [dotProduct,column_entry]
  exact_mod_cast int_cross

def field (s t : ℝ) : Edge → ℝ :=
  s • Pi.single innerEdge (1 : ℝ)+t • Pi.single outerEdge (1 : ℝ)

def energy (s t : ℝ) : ℝ := dotProduct (incidence (field s t)) (incidence (field s t))

theorem incidence_field (s t : ℝ) :
    incidence (field s t)=s • column innerEdge+t • column outerEdge := by
  simp [field,column]

theorem energy_formula (s t : ℝ) : energy s t=6*s^2-2*s*t+6*t^2 := by
  have hcross : dotProduct (column outerEdge) (column innerEdge)=-1 := by
    rw [dotProduct_comm,cross]
  simp only [energy,incidence_field,dotProduct_add,add_dotProduct,
    smul_dotProduct,dotProduct_smul,smul_eq_mul,inner_norm,outer_norm,cross,hcross]
  ring

theorem energy_not_split : energy 1 1 ≠ energy 1 0+energy 0 1 := by
  norm_num [energy_formula]

theorem deriv_first (s t : ℝ) : deriv (fun x => energy x t) s=12*s-2*t := by
  simp_rw [energy_formula]
  have hd : HasDerivAt (fun x : ℝ => 6*x^2-2*x*t+6*t^2) (12*s-2*t) s := by
    have h := (((hasDerivAt_pow 2 s).const_mul 6).sub
      (((hasDerivAt_id s).const_mul 2).mul_const t)).add_const (6*t^2)
    have h' := h.congr_deriv (g' := 12*s-2*t) (by ring)
    apply h'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun x => by
      simp only [Pi.sub_apply,id_eq] <;> ring)
  exact hd.deriv

theorem mixed_partial : deriv (fun t => deriv (fun s => energy s t) 0) 0=-2 := by
  simp_rw [deriv_first]
  have heq : (fun t : ℝ => 12*0-2*t)=-(fun t : ℝ => t*2) := by
    funext t
    change 12*0-2*t=-(t*2)
    ring
  rw [heq]
  simpa using (((hasDerivAt_id (0 : ℝ)).mul_const 2).neg).deriv

theorem gaussian_weight_not_factor :
    Real.exp (-energy 1 1/2) ≠
      Real.exp (-energy 1 0/2)*Real.exp (-energy 0 1/2) := by
  rw [← Real.exp_add]
  intro h
  have he := Real.exp_injective h
  norm_num [energy_formula] at he

end OperatorDerivativeRewrite.Foundation.PeriodicMixedLinkEnergy
