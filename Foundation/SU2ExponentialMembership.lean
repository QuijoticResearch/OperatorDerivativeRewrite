import Foundation.SU2NullPlaquetteWord
import Mathlib.LinearAlgebra.UnitaryGroup

/-! Determinant one from trace and exponential doubling; actual special-unitary membership. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2ExponentialMembership
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open SU2TraceHessianModel SU2MatrixExponentialBridge

theorem trace_square_identity (M : M2) :
    2*Matrix.det M=(Matrix.trace M)^2-Matrix.trace (M^2) := by
  norm_num [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, pow_two]
  ring

theorem doubled_square (A : M2) (ρ : ℝ)
    (hsq : A^2=(-(ρ^2):ℂ) • (1:M2)) :
    (A+A)^2=(-((2*ρ)^2):ℂ) • (1:M2) := by
  rw [← two_smul ℂ A, smul_pow, hsq, smul_smul]
  congr 1
  ring

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem exp_det_of_sq (A : M2) (ρ : ℝ) (ht : Matrix.trace A=0)
    (hsq : A^2=(-(ρ^2):ℂ) • (1:M2)) : Matrix.det (NormedSpace.exp A)=1 := by
  have ht2 : Matrix.trace (A+A)=0 := by rw [Matrix.trace_add, ht, zero_add]
  have he2 : (NormedSpace.exp A)^2=NormedSpace.exp (A+A) := by
    rw [pow_two, Matrix.exp_add_of_commute A A (Commute.refl A)]
  have hh := trace_square_identity (NormedSpace.exp A)
  have htr : Matrix.trace (NormedSpace.exp A)=2*Complex.cos (ρ:ℂ) := exp_trace_of_sq A ρ ht hsq
  have htr2 : Matrix.trace ((NormedSpace.exp A)^2)=2*Complex.cos ((2*ρ:ℝ):ℂ) := by
    rw [he2]
    apply exp_trace_of_sq (A+A) (2*ρ) ht2
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using doubled_square A ρ hsq
  rw [htr, htr2] at hh
  push_cast at hh
  rw [Complex.cos_two_mul] at hh
  linear_combination (1/2:ℂ)*hh

theorem algebraElement_exp_det (v : Fin 3 → ℝ) :
    Matrix.det (NormedSpace.exp (algebraElement v))=1 :=
  exp_det_of_sq _ _ (algebraElement_trace v) (algebraElement_sq_angle v)

theorem algebraElement_smul (t : ℝ) (v : Fin 3 → ℝ) :
    algebraElement (t • v)=t • algebraElement v := by
  ext i j
  simp [algebraElement, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul]
  ring

theorem algebraElement_exp_mem (v : Fin 3 → ℝ) :
    NormedSpace.exp (algebraElement v) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, algebraElement_exp_det v⟩
  exact ⟨algebraElement_exp_unitary_left v, algebraElement_exp_unitary_right v⟩

theorem scaled_algebraElement_exp_mem (t : ℝ) (v : Fin 3 → ℝ) :
    NormedSpace.exp (t • algebraElement v) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [← algebraElement_smul]
  exact algebraElement_exp_mem _

theorem rotation_mem (θ : ℝ) : rotation θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  exact ⟨rotation_unitary θ, rotation_det_one θ⟩

open SU2NullPlaquetteWord

def testLinks (θ t : ℝ) : Fin 4 → M2 :=
  ![rotation θ, NormedSpace.exp (t • tangent 1), NormedSpace.exp (t • (-tangent 0)),
    NormedSpace.exp (t • (tangent 1+tangent 0))]

theorem testLinks_mem (θ t : ℝ) (i : Fin 4) :
    testLinks θ t i ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  fin_cases i
  · exact rotation_mem θ
  · simpa [testLinks, algebraElement, Fin.sum_univ_three] using
      scaled_algebraElement_exp_mem t ![0,1,0]
  · simpa [testLinks, algebraElement, Fin.sum_univ_three] using
      scaled_algebraElement_exp_mem t ![-1,0,0]
  · simpa [testLinks, algebraElement, Fin.sum_univ_three, add_comm] using
      scaled_algebraElement_exp_mem t ![1,1,0]

def testPlaquette (θ t : ℝ) : M2 :=
  plaquette (testLinks θ t 0) (testLinks θ t 1) (testLinks θ t 2) (testLinks θ t 3)

theorem testPlaquette_eq (θ t : ℝ) :
    testPlaquette θ t=rotation θ*threePath (tangent 1) (tangent 0)
      (-(tangent 1+tangent 0)) t := by
  exact plaquette_embedding (rotation θ) (tangent 1) (tangent 0) t

theorem testPlaquette_mem (θ t : ℝ) :
    testPlaquette θ t ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [testPlaquette_eq]
  have hb := testLinks_mem θ t (1:Fin 4)
  have hc : NormedSpace.exp (t • tangent 0) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    simpa [algebraElement, Fin.sum_univ_three] using scaled_algebraElement_exp_mem t ![1,0,0]
  have hd : NormedSpace.exp (t • (-(tangent 1+tangent 0))) ∈
      Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    simpa [algebraElement, Fin.sum_univ_three, neg_add_rev, add_comm] using
      scaled_algebraElement_exp_mem t ![-1,-1,0]
  exact (Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem (rotation_mem θ)
    ((Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem
      ((Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem hb hc) hd)

theorem testPlaquette_zero (θ : ℝ) : testPlaquette θ 0=rotation θ := by
  rw [testPlaquette_eq, null_path_zero, mul_one]

theorem testPlaquette_curvature (θ : ℝ) :
    deriv (deriv (fun t : ℝ => wilson (testPlaquette θ t))) 0= -Real.sin θ/2 := by
  have he : (fun t : ℝ => wilson (testPlaquette θ t))=
      threeAction (rotation θ) (tangent 1) (tangent 0) (-(tangent 1+tangent 0)) := by
    funext t
    rw [testPlaquette_eq]
    rfl
  rw [he, reversed_null_curvature]

theorem testPlaquette_no_quadratic_lower_bound :
    ¬ ∃ K ε : ℝ, 0 ≤ K ∧ 0 < ε ∧ ∀ θ : ℝ, 0 < θ → θ < ε →
      -K*θ^2*4 ≤ deriv (deriv (fun t : ℝ => wilson (testPlaquette θ t))) 0 := by
  simpa only [testPlaquette_curvature, negativeCurvature, reversed_null_curvature] using
    no_direction_normalized_quadratic_lower_bound

end OperatorDerivativeRewrite.Foundation.SU2ExponentialMembership
