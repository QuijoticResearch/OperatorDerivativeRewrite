import Foundation.AffineNavierStokesProfiles

/-! Local pressure-sign calibration using actual derivatives of the affine
Navier--Stokes profiles. No whole-space finite-energy integral is asserted. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.AffineStretchingPressureBalance
open RestrictedEulerRatioCounterexample RestrictedEulerAlignedGrowth
  AffineNavierStokesProfiles
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def gradientMatrix (p a t : ℝ) (x : Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => fderiv ℝ (velocity p a t) x (Pi.single j 1) i

theorem gradientMatrix_eq (p a t : ℝ) (x : Space) : gradientMatrix p a t x=family p a t := by
  ext i j
  simp only [gradientMatrix,velocity_fderiv,ContinuousLinearMap.smul_apply,spatialMap_apply,
    Matrix.mulVec_single_one,Matrix.col_apply,Pi.smul_apply,smul_eq_mul]
  rfl

def omega (p a t : ℝ) (x : Space) : Space := vorticity (gradientMatrix p a t x)
def S (p a t : ℝ) (x : Space) : Matrix (Fin 3) (Fin 3) ℝ := strain (gradientMatrix p a t x)

def density (p a t : ℝ) (x : Space) : ℝ :=
  dotProduct (omega p a t x) ((S p a t x).mulVec (omega p a t x))
def amplification (p a t : ℝ) (x : Space) : ℝ :=
  dotProduct ((S p a t x).mulVec (omega p a t x))
    ((S p a t x).mulVec (omega p a t x))
def pressureContraction (p a t : ℝ) (x : Space) : ℝ :=
  dotProduct (omega p a t x) ((pressureHessian t x).mulVec (omega p a t x))

theorem omega_eq (p a t : ℝ) (x : Space) : omega p a t x=![0,2*scale t*a,0] := by
  rw [omega,gradientMatrix_eq,family,scaled_vorticity]

theorem strain_omega (p a t : ℝ) (x : Space) :
    (S p a t x).mulVec (omega p a t x)=scale t • omega p a t x := by
  simp only [S,omega,gradientMatrix_eq,family]
  exact scaled_alignment p a (scale t)

theorem omega_squared (p a t : ℝ) (x : Space) :
    dotProduct (omega p a t x) (omega p a t x)=4*a^2*(scale t)^2 := by
  rw [omega_eq]
  simp [dotProduct,Fin.sum_univ_succ] <;> ring

theorem density_formula (p a t : ℝ) (x : Space) : density p a t x=4*a^2*(scale t)^3 := by
  rw [density,strain_omega,dotProduct_smul,smul_eq_mul,omega_squared]
  ring

theorem amplification_formula (p a t : ℝ) (x : Space) :
    amplification p a t x=4*a^2*(scale t)^4 := by
  rw [amplification,strain_omega,smul_dotProduct,dotProduct_smul,smul_eq_mul,omega_squared]
  ring

theorem pressure_formula (p a t : ℝ) (x : Space) :
    pressureContraction p a t x=-8*a^2*(scale t)^4 := by
  rw [pressureContraction,pressure_hessian,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_smul,smul_eq_mul,omega_squared]
  ring

theorem density_derivative (p a t : ℝ) (x : Space) (ht : t ≠ 1) :
    HasDerivAt (fun s => density p a s x) (12*a^2*(scale t)^4) t := by
  simp_rw [density_formula]
  have hd := ((scale_derivative t ht).fun_pow 3).const_mul (4*a^2)
  exact hd.congr_deriv (by norm_num; ring)

theorem density_transport_zero (p a t : ℝ) (x : Space) :
    fderiv ℝ (density p a t) x (velocity p a t x)=0 := by
  have he : density p a t=fun _ => 4*a^2*(scale t)^3 := funext (density_formula p a t)
  rw [he]
  simp

theorem minus_pressure_balance (p a t : ℝ) (x : Space) (ht : t ≠ 1) :
    deriv (fun s => density p a s x) t+fderiv ℝ (density p a t) x (velocity p a t x)=
      amplification p a t x-pressureContraction p a t x := by
  rw [(density_derivative p a t x ht).deriv,density_transport_zero,amplification_formula,pressure_formula]
  ring

theorem plus_pressure_fails (p a t : ℝ) (x : Space) (ha : a ≠ 0) (ht : t < 1) :
    deriv (fun s => density p a s x) t+fderiv ℝ (density p a t) x (velocity p a t x) ≠
      amplification p a t x+pressureContraction p a t x := by
  rw [(density_derivative p a t x (by linarith)).deriv,density_transport_zero,
    amplification_formula,pressure_formula]
  have hc : 0 < scale t := inv_pos.mpr (sub_pos.mpr ht)
  have hp : 0 < a^2*(scale t)^4 := mul_pos (sq_pos_of_ne_zero ha) (pow_pos hc 4)
  intro h
  nlinarith

def sourceStrainRHS (A P : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  -(strain A*strain A)-(A-strain A)*(A-strain A)-P+
    ((Matrix.trace (strain A*strain A)+dotProduct (vorticity A) (vorticity A)/2)/3) • 1

theorem skew_trace_identity (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace ((A-strain A)*(A-strain A))=
      -dotProduct (vorticity A) (vorticity A)/2 := by
  simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.sub_apply,strain,
    Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,vorticity,
    dotProduct,smul_eq_mul,Fin.sum_univ_succ] <;> ring

theorem source_trace_general (A P : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.trace (sourceStrainRHS A P)=
      dotProduct (vorticity A) (vorticity A)-Matrix.trace P := by
  simp only [sourceStrainRHS,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_neg,Matrix.trace_smul]
  rw [skew_trace_identity]
  have hI : Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℝ)=3 := by
    norm_num [Matrix.trace,Matrix.diag,Fin.sum_univ_succ]
  rw [hI]
  ring

theorem source_full_pressure_trace :
    Matrix.trace (sourceStrainRHS (matrix 4 (Real.sqrt 10))
      (pressureHessian 0 (0 : Space)))=46 := by
  rw [pressure_hessian]
  rw [source_trace_general]
  norm_num [matrix,vorticity,scale,Matrix.trace,Matrix.diag,dotProduct,Fin.sum_univ_succ] <;>
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (10 : ℝ))]

theorem source_tracefree_pressure_trace :
    Matrix.trace (sourceStrainRHS (matrix 4 (Real.sqrt 10)) 0)=40 := by
  rw [source_trace_general]
  norm_num [matrix,vorticity,dotProduct,Fin.sum_univ_succ] <;>
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (10 : ℝ))]

theorem actual_strain_trace_zero (p a t : ℝ) (x : Space) : Matrix.trace (S p a t x)=0 := by
  rw [S,gradientMatrix_eq,family,strain_smul,matrix_strain]
  simp [Matrix.trace,Matrix.diag,Matrix.diagonal,Fin.sum_univ_succ] <;> ring

theorem actual_strain_trace_derivative (p a t : ℝ) (x : Space) :
    deriv (fun s => Matrix.trace (S p a s x)) t=0 := by
  simp_rw [actual_strain_trace_zero]
  simp

theorem calibration_at_zero (x : Space) :
    deriv (fun t => density 4 (Real.sqrt 10) t x) 0=120 ∧
      amplification 4 (Real.sqrt 10) 0 x=40 ∧ pressureContraction 4 (Real.sqrt 10) 0 x=-80 := by
  rw [(density_derivative 4 (Real.sqrt 10) 0 x (by norm_num)).deriv,
    amplification_formula,pressure_formula]
  norm_num [scale,Real.sq_sqrt]

def traceFree (P : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  P-(Matrix.trace P/3) • 1

theorem pressure_traceFree_zero (t : ℝ) (x : Space) : traceFree (pressureHessian t x)=0 := by
  rw [traceFree,pressure_hessian]
  ext i j
  by_cases h : i=j <;>
    norm_num [h,Matrix.trace,Matrix.diag,Fin.sum_univ_succ,Matrix.one_apply] <;> ring

end OperatorDerivativeRewrite.Foundation.AffineStretchingPressureBalance
