import Foundation.RestrictedEulerRatioCounterexample

/-! A family of exact restricted-Euler trajectories with intermediate-aligned
vorticity. The negative isolated stretching term need not imply damping. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.RestrictedEulerAlignedGrowth
open RestrictedEulerRatioCounterexample
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

def matrix (p a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-p,0,a; 0,1,0; -a,0,p-1]

theorem matrix_trace (p a : ℝ) : Matrix.trace (matrix p a)=0 := by
  simp [matrix,Matrix.trace,Matrix.diag,Fin.sum_univ_succ] <;> ring

theorem matrix_strain (p a : ℝ) :
    strain (matrix p a)=Matrix.diagonal ![-p,1,p-1] := by
  ext i j
  simp only [strain,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [matrix,Matrix.diagonal] <;> ring

theorem strain_smul (c : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    strain (c • A)=c • strain A := by
  ext i j
  simp only [strain,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul]
  ring

theorem flow_smul (c : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    flow (c • A)=c^2 • flow A := by
  ext i j
  simp [flow,Matrix.mul_apply,Matrix.trace,Matrix.diag,Fin.sum_univ_succ] <;> ring

theorem self_similar_profile (p a : ℝ) (ha : a^2=(p-2)*(p+1)) :
    flow (matrix p a)=matrix p a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [flow,matrix,Matrix.mul_apply,Matrix.trace,Matrix.diag,Fin.sum_univ_succ] <;>
    nlinarith [ha]

theorem trace_square (p a : ℝ) (ha : a^2=(p-2)*(p+1)) :
    Matrix.trace (matrix p a*matrix p a)=6 := by
  norm_num [matrix,Matrix.mul_apply,Matrix.trace,Matrix.diag,Fin.sum_univ_succ]
  nlinarith [ha]

theorem scaled_vorticity (p a c : ℝ) :
    vorticity (c • matrix p a)=![0,2*c*a,0] := by
  ext i
  fin_cases i <;> simp [vorticity,matrix] <;> ring

theorem scaled_alignment (p a c : ℝ) :
    (strain (c • matrix p a)).mulVec (vorticity (c • matrix p a))=
      c • vorticity (c • matrix p a) := by
  rw [strain_smul,matrix_strain,scaled_vorticity]
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Matrix.diagonal] <;> ring

def stretching (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  dotProduct (vorticity A) ((strain A).mulVec (vorticity A))/
    dotProduct (vorticity A) (vorticity A)

theorem stretching_scaled (p a c : ℝ) (ha : a ≠ 0) : stretching (c • matrix p a)=c := by
  by_cases hc : c=0
  · simp [hc,stretching,strain,vorticity,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · have hn : dotProduct (vorticity (c • matrix p a)) (vorticity (c • matrix p a)) ≠ 0 := by
      rw [scaled_vorticity]
      simp [dotProduct,Fin.sum_univ_succ,ha,hc]
    rw [stretching,scaled_alignment,dotProduct_smul,smul_eq_mul]
    field_simp

def family (p a t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := scale t • matrix p a

theorem family_component_ode (p a t : ℝ) (ha : a^2=(p-2)*(p+1))
    (ht : t ≠ 1) (i j : Fin 3) :
    HasDerivAt (fun s => family p a s i j) (flow (family p a t) i j) t := by
  have hd := (scale_derivative t ht).mul_const (matrix p a i j)
  simpa [family,flow_smul,self_similar_profile p a ha] using hd

theorem family_stretching (p a t : ℝ) (ha : a ≠ 0) : stretching (family p a t)=scale t :=
  stretching_scaled p a (scale t) ha

theorem family_stretching_derivative (p a t : ℝ) (ha : a ≠ 0) (ht : t ≠ 1) :
    HasDerivAt (fun s => stretching (family p a s)) ((scale t)^2) t := by
  have he : (fun s => stretching (family p a s))=scale := funext (fun s => family_stretching p a s ha)
  rw [he]
  exact scale_derivative t ht

theorem family_stretching_unbounded (p a : ℝ) (ha : a ≠ 0) (M : ℝ) (hM : 0 ≤ M) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ M < stretching (family p a t) := by
  obtain ⟨t,ht₀,ht₁,htM⟩ := scale_unbounded_before_one M hM
  exact ⟨t,ht₀,ht₁,by rwa [family_stretching p a t ha]⟩

theorem vorticity_nonzero (p a : ℝ) (ha : a ≠ 0) : vorticity (matrix p a) ≠ 0 := by
  have hw := scaled_vorticity p a 1
  simp only [one_smul,one_mul,mul_one] at hw
  intro h
  have he := congrFun h 1
  rw [hw] at he
  norm_num at he
  exact ha (by linarith)

theorem sqrt_ten_constraint : (Real.sqrt 10)^2=((4 : ℝ)-2)*(4+1) := by
  rw [Real.sq_sqrt (by norm_num : 0 ≤ (10 : ℝ))]
  norm_num

theorem sqrt_ten_nonzero : Real.sqrt (10 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))

theorem proposed_ratio_exact_ode (t : ℝ) (ht : t ≠ 1) (i j : Fin 3) :
    HasDerivAt (fun s => family 4 (Real.sqrt 10) s i j)
      (flow (family 4 (Real.sqrt 10) t) i j) t :=
  family_component_ode 4 (Real.sqrt 10) t sqrt_ten_constraint ht i j

theorem proposed_ratio_initial_stretching : stretching (matrix 4 (Real.sqrt 10))=1 := by
  simpa using stretching_scaled 4 (Real.sqrt 10) 1 sqrt_ten_nonzero

theorem proposed_ratio_negative_component : -(stretching (matrix 4 (Real.sqrt 10)))^2=-1 := by
  rw [proposed_ratio_initial_stretching]
  norm_num

theorem proposed_ratio_trace_correction :
    Matrix.trace (matrix 4 (Real.sqrt 10)*matrix 4 (Real.sqrt 10))/3=2 := by
  rw [trace_square 4 (Real.sqrt 10) sqrt_ten_constraint]
  norm_num

theorem proposed_ratio_stretching_derivative :
    HasDerivAt (fun t => stretching (family 4 (Real.sqrt 10) t)) 1 0 := by
  simpa [scale] using family_stretching_derivative 4 (Real.sqrt 10) 0 sqrt_ten_nonzero (by norm_num)

theorem proposed_ratio_growth_positive :
    0 < deriv (fun t => stretching (family 4 (Real.sqrt 10) t)) 0 := by
  rw [proposed_ratio_stretching_derivative.deriv]
  norm_num

def strainSquared (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ i, ∑ j, (strain A i j)^2

def normalizedStretching (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  stretching A/Real.sqrt (strainSquared A)

theorem strainSquared_scaled (p a c : ℝ) :
    strainSquared (c • matrix p a)=c^2*(p^2+1+(p-1)^2) := by
  rw [strainSquared,strain_smul,matrix_strain]
  simp [Fin.sum_univ_succ,Matrix.diagonal] <;> ring

theorem proposed_ratio_normalized (c : ℝ) (hc : 0 < c) :
    normalizedStretching (c • matrix 4 (Real.sqrt 10))=1/Real.sqrt 26 := by
  have hs : strainSquared (c • matrix 4 (Real.sqrt 10))=c^2*26 := by
    rw [strainSquared_scaled]
    ring
  rw [normalizedStretching,stretching_scaled _ _ _ sqrt_ten_nonzero,hs,
    Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq_eq_abs,abs_of_pos hc]
  have h26 : Real.sqrt (26 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [ne_of_gt hc,h26]

end OperatorDerivativeRewrite.Foundation.RestrictedEulerAlignedGrowth
