import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! A concrete restricted-Euler matrix trajectory with nonzero vorticity and
strain ratios -3:1:2. This is an ODE diagnostic, not a Navier--Stokes solution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.RestrictedEulerRatioCounterexample

def initial : Matrix (Fin 3) (Fin 3) ℝ := !![-3, 0, 2; 0, 1, 0; -2, 0, 2]

def flow (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  -(A * A) + (Matrix.trace (A * A) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℝ)

def strain (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1/2 : ℝ) • (A + A.transpose)

def vorticity (A : Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ :=
  ![A 2 1 - A 1 2, A 0 2 - A 2 0, A 1 0 - A 0 1]

theorem initial_trace : Matrix.trace initial = 0 := by
  norm_num [initial, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem scaled_flow (c : ℝ) : flow (c • initial) = c^2 • initial := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flow, initial, Matrix.mul_apply, Matrix.trace, Matrix.diag,
      Fin.sum_univ_succ] <;> ring

theorem initial_strain : strain initial = Matrix.diagonal ![-3, 1, 2] := by
  ext i j
  simp only [strain, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> norm_num [initial, Matrix.diagonal]

theorem initial_vorticity : vorticity initial = ![0, 4, 0] := by
  ext i
  fin_cases i <;> norm_num [vorticity, initial]

theorem intermediate_alignment :
    (strain initial).mulVec (vorticity initial) = vorticity initial := by
  rw [initial_strain, initial_vorticity]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.diagonal]

theorem different_strain_ratio :
    strain initial 0 0 ≠ -4 * strain initial 1 1 := by
  rw [initial_strain]
  norm_num [Matrix.diagonal]

def scale (t : ℝ) : ℝ := (1-t)⁻¹

def trajectory (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := scale t • initial

theorem scale_derivative (t : ℝ) (ht : t ≠ 1) : HasDerivAt scale ((scale t)^2) t := by
  have hn : 1-t ≠ 0 := by intro h; apply ht; linarith
  have hd0 : HasDerivAt (fun x : ℝ => 1-x) (-1) t := by
    simpa using HasDerivAt.const_sub 1 (hasDerivAt_id t)
  have hd := (hasDerivAt_inv hn).scomp t hd0
  change HasDerivAt (fun x : ℝ => (1-x)⁻¹) (((1-t)⁻¹)^2) t
  convert hd using 1 <;> simp [inv_pow, smul_eq_mul, Function.comp_def]

/-- The exact component equations of the restricted-Euler ODE. -/
theorem trajectory_component_ode (t : ℝ) (ht : t ≠ 1) (i j : Fin 3) :
    HasDerivAt (fun s => trajectory s i j) (flow (trajectory t) i j) t := by
  have hd := (scale_derivative t ht).mul_const (initial i j)
  simpa [trajectory, scaled_flow] using hd

/-- Throughout the pre-singular interval the intermediate strain eigenvalue
is positive, the ratios stay -3:1:2, and the vorticity is nonzero. -/
theorem trajectory_ratios (t : ℝ) (ht : t < 1) :
    0 < strain (trajectory t) 1 1 ∧
      strain (trajectory t) 0 0 = -3 * strain (trajectory t) 1 1 ∧
      strain (trajectory t) 2 2 = 2 * strain (trajectory t) 1 1 ∧
      vorticity (trajectory t) 1 = 4 * strain (trajectory t) 1 1 ∧
      strain (trajectory t) 0 0 ≠ -4 * strain (trajectory t) 1 1 := by
  have hp : 0 < scale t := inv_pos.mpr (sub_pos.mpr ht)
  simp only [trajectory, strain, Matrix.smul_apply, Matrix.add_apply,
    Matrix.transpose_apply, smul_eq_mul]
  norm_num [vorticity, initial]
  and_intros <;> nlinarith

/-- Positive times below one produce arbitrarily large trajectory scales. -/
theorem scale_unbounded_before_one (M : ℝ) (hM : 0 ≤ M) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ M < scale t := by
  refine ⟨M/(M+1), div_nonneg hM (by positivity), ?_, ?_⟩
  · apply (div_lt_one (by positivity : 0 < M+1)).mpr
    linarith
  · have hn : M+1 ≠ 0 := by positivity
    have he : scale (M/(M+1)) = M+1 := by
      unfold scale
      field_simp
      ring
    rw [he]
    linarith

end OperatorDerivativeRewrite.Foundation.RestrictedEulerRatioCounterexample
