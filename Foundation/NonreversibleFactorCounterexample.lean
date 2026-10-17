import Foundation.SymmetricDefectEnergy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! A stationary three-state Markov factor whose conditional projection increases defect energy. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.NonreversibleFactorCounterexample
set_option backward.isDefEq.respectTransparency false
abbrev Space := EuclideanSpace ℝ (Fin 3)

def kernel : Matrix (Fin 3) (Fin 3) ℝ := !![0,1,0; 1/2,0,1/2; 1/2,0,1/2]

theorem kernel_nonnegative (i j : Fin 3) : 0 ≤ kernel i j := by
  fin_cases i <;> fin_cases j <;> norm_num [kernel]

theorem kernel_rows (i : Fin 3) : ∑ j, kernel i j = 1 := by
  fin_cases i <;> norm_num [kernel, Fin.sum_univ_three]

theorem kernel_columns (j : Fin 3) : ∑ i, kernel i j = 1 := by
  fin_cases j <;> norm_num [kernel, Fin.sum_univ_three]

def transitionLinear : Space →ₗ[ℝ] Space where
  toFun v := WithLp.toLp 2 ![v 1, (v 0+v 2)/2, (v 0+v 2)/2]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

def projectionLinear : Space →ₗ[ℝ] Space where
  toFun v := WithLp.toLp 2 ![v 0, (v 1+v 2)/2, (v 1+v 2)/2]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

theorem transition_apply (v : Space) (i : Fin 3) :
    transitionLinear v i = ![v 1, (v 0+v 2)/2, (v 0+v 2)/2] i := rfl

theorem projection_apply (v : Space) (i : Fin 3) :
    projectionLinear v i = ![v 0, (v 1+v 2)/2, (v 1+v 2)/2] i := rfl

theorem transition_kernel (v : Space) (i : Fin 3) :
    transitionLinear v i = ∑ j, kernel i j * v j := by
  fin_cases i <;> simp [transition_apply, kernel, Fin.sum_univ_three] <;> ring

theorem transition_positive (v : Space) (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ transitionLinear v i := by
  intro i
  rw [transition_kernel]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (kernel_nonnegative i j) (hv j))

theorem transition_preserves_sum (v : Space) :
    ∑ i, transitionLinear v i = ∑ i, v i := by
  simp only [Fin.sum_univ_three, transition_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem norm_square (v : Space) : ‖v‖^2 = v 0^2 + v 1^2 + v 2^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem inner_formula (v w : Space) :
    inner ℝ v w = v 0*w 0 + v 1*w 1 + v 2*w 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, Real.inner_apply]

theorem transition_norm_sq_le (v : Space) : ‖transitionLinear v‖^2 ≤ ‖v‖^2 := by
  rw [norm_square, norm_square]
  simp only [transition_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  nlinarith [sq_nonneg (v 0 - v 2)]

theorem projection_norm_sq_le (v : Space) : ‖projectionLinear v‖^2 ≤ ‖v‖^2 := by
  rw [norm_square, norm_square]
  simp only [projection_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  nlinarith [sq_nonneg (v 1 - v 2)]

theorem transition_norm_le (v : Space) : ‖transitionLinear v‖ ≤ ‖v‖ := by
  nlinarith [transition_norm_sq_le v, norm_nonneg v, norm_nonneg (transitionLinear v)]

theorem projection_norm_le (v : Space) : ‖projectionLinear v‖ ≤ ‖v‖ := by
  nlinarith [projection_norm_sq_le v, norm_nonneg v, norm_nonneg (projectionLinear v)]

def transition : Space →L[ℝ] Space := transitionLinear.mkContinuous 1 (by
  intro v
  simpa only [one_mul] using transition_norm_le v)

def projection : Space →L[ℝ] Space := projectionLinear.mkContinuous 1 (by
  intro v
  simpa only [one_mul] using projection_norm_le v)

theorem projection_idempotent (v : Space) : projection (projection v) = projection v := by
  change projectionLinear (projectionLinear v) = projectionLinear v
  ext i
  fin_cases i <;> simp [projection_apply]

theorem projection_symmetric : projection.toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (projectionLinear v) w = inner ℝ v (projectionLinear w)
  simp only [inner_formula, projection_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem projection_fixed_iff (v : Space) : projection v = v ↔ v 1 = v 2 := by
  constructor
  · intro h
    have h1 := congrArg (fun w : Space => w 1) h
    have h2 := congrArg (fun w : Space => w 2) h
    change (v 1+v 2)/2 = v 1 at h1
    change (v 1+v 2)/2 = v 2 at h2
    linarith
  · intro h
    change projectionLinear v = v
    ext i
    fin_cases i <;> simp [projection_apply, h]

theorem retained_subspace_invariant (v : Space) :
    projection (transition (projection v)) = transition (projection v) := by
  apply (projection_fixed_iff _).mpr
  rfl

theorem projection_residual_pairing (v w : Space) (hw : w 1 = w 2) :
    inner ℝ (v - projection v) w = 0 := by
  rw [inner_sub_left]
  have h : inner ℝ (projection v) w = inner ℝ v (projection w) :=
    projection_symmetric v w
  rw [h, (projection_fixed_iff w).mpr hw, sub_self]

theorem transition_constants (c : ℝ) :
    transition (WithLp.toLp 2 (fun _ : Fin 3 => c)) = WithLp.toLp 2 (fun _ => c) := by
  change transitionLinear (WithLp.toLp 2 (fun _ : Fin 3 => c)) = _
  ext i
  fin_cases i <;> simp [transition_apply]

def pullback (f : Fin 2 → ℝ) : Space := WithLp.toLp 2 ![f 0,f 1,f 1]

def coarseTransition (f : Fin 2 → ℝ) : Fin 2 → ℝ := ![f 1,(f 0+f 1)/2]

theorem transition_pullback (f : Fin 2 → ℝ) :
    transition (pullback f) = pullback (coarseTransition f) := by
  change transitionLinear (pullback f) = _
  ext i
  fin_cases i <;> simp [transition_apply, pullback, coarseTransition]

def μ : Measure (Fin 3) := (1/3 : ℝ≥0∞) • Measure.count

instance μ_probability : IsProbabilityMeasure μ where
  measure_univ := by
    norm_num [μ, Measure.smul_apply, Measure.count_apply_finite]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem uniform_stationary (v : Space) :
    (∫ i, transition v i ∂μ) = ∫ i, v i ∂μ := by
  simp only [μ, integral_smul_measure, integral_count]
  congr 1
  exact transition_preserves_sum v

def energy (v : Space) : ℝ := (‖v‖^2 - inner ℝ (transition v) v)/3

theorem energy_nonnegative (v : Space) : 0 ≤ energy v := by
  have h := SymmetricDefectEnergy.defect_nonnegative 1 (by norm_num) transition
    (fun w => transition_norm_le w) v
  change 0 ≤ inner ℝ ((1 : ℝ)⁻¹ • (v - transition v)) v at h
  simp only [inv_one, one_smul, inner_sub_left, real_inner_self_eq_norm_sq] at h
  exact div_nonneg h (by norm_num)

theorem energy_integral (v : Space) :
    energy v = ∫ i, (v i - transition v i)*v i ∂μ := by
  rw [μ, integral_smul_measure, integral_count]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  rw [Fin.sum_univ_three]
  unfold energy
  rw [norm_square, inner_formula]
  ring

def witness : Space := WithLp.toLp 2 ![2,-1/4,-7/4]

theorem projection_transition_ne :
    projection (transition witness) ≠ transition (projection witness) := by
  intro h
  have h0 := congrArg (fun v : Space => v 0) h
  norm_num [projection, projectionLinear, transition, transitionLinear, witness] at h0

theorem energy_witness : energy witness = 21/8 := by
  norm_num [energy, norm_square, inner_formula, transition, transitionLinear, witness]

theorem energy_projected_witness : energy (projection witness) = 3 := by
  norm_num [energy, norm_square, inner_formula, transition, transitionLinear,
    projection, projectionLinear, witness]

theorem projection_increases_energy : energy witness < energy (projection witness) := by
  rw [energy_witness, energy_projected_witness]
  norm_num

theorem transition_not_symmetric : ¬ transition.toLinearMap.IsSymmetric := by
  intro h
  have ht := h (WithLp.toLp 2 ![1,0,0]) (WithLp.toLp 2 ![0,1,0])
  change inner ℝ (transition (WithLp.toLp 2 ![1,0,0])) (WithLp.toLp 2 ![0,1,0]) =
    inner ℝ (WithLp.toLp 2 ![1,0,0]) (transition (WithLp.toLp 2 ![0,1,0])) at ht
  rw [inner_formula, inner_formula] at ht
  norm_num [transition, transitionLinear] at ht

end OperatorDerivativeRewrite.Foundation.NonreversibleFactorCounterexample
