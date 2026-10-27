import Foundation.FiniteStableGamma
import Foundation.FractionalCurvatureSubordinationObstruction
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Actual Lebesgue-volume correction for the two-mode complex Cauchy Gamma
ellipsoids. Real and imaginary coordinates each carry the same Gram form;
the real Jacobian squares. The two-mode volume ratio is 3, not sqrt(3).
These are fixed-point coefficient ellipsoids, not simultaneous pointwise bounds
at every torus point, integrated-energy ellipsoids, or semigroup contraction. -/
noncomputable section
open MeasureTheory Matrix
namespace OperatorDerivativeRewrite.Foundation.ComplexGammaEllipsoidVolume

def realDouble {ι : Type*} (A : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  Matrix.fromBlocks A 0 0 A

theorem realDouble_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : (realDouble A).det = A.det ^ 2 := by
  rw [realDouble, Matrix.det_fromBlocks_zero₂₁]
  ring

theorem matrix_preimage_volume {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) (s : Set (ι → ℝ)) (hs : MeasurableSet s) :
    volume ((Matrix.toLin' A) ⁻¹' s) = ENNReal.ofReal (|A.det|⁻¹) * volume s := by
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hA
  have he := congrArg (fun μ : Measure (ι → ℝ) => μ s) hm
  rw [Measure.map_apply (LinearMap.continuous_on_pi _).measurable hs] at he
  simpa [abs_inv] using he

theorem realDouble_preimage_volume {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0)
    (s : Set ((ι ⊕ ι) → ℝ)) (hs : MeasurableSet s) :
    volume ((Matrix.toLin' (realDouble A)) ⁻¹' s) =
      ENNReal.ofReal ((A.det ^ 2)⁻¹) * volume s := by
  rw [matrix_preimage_volume _ (by rw [realDouble_det]; exact pow_ne_zero _ hA) _ hs,
    realDouble_det, abs_of_nonneg (sq_nonneg _)]

def factor (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1,1; 0,r]

theorem factor_det (r : ℝ) : (factor r).det = r := by
  simp [factor, Matrix.det_fin_two]

theorem cauchy_two_mode_real_jacobian : (factor (Real.sqrt 3)).det = Real.sqrt 3 :=
  factor_det _

theorem cauchy_two_mode_complex_jacobian :
    (realDouble (factor (Real.sqrt 3))).det = 3 := by
  rw [realDouble_det, factor_det, Real.sq_sqrt (by norm_num)]

theorem cauchy_two_mode_complex_volume
    (s : Set ((Fin 2 ⊕ Fin 2) → ℝ)) (hs : MeasurableSet s) :
    volume ((Matrix.toLin' (realDouble (factor (Real.sqrt 3)))) ⁻¹' s) =
      ENNReal.ofReal (1/3 : ℝ) * volume s := by
  rw [matrix_preimage_volume _ (by rw [cauchy_two_mode_complex_jacobian]; norm_num) _ hs,
    cauchy_two_mode_complex_jacobian]
  norm_num

def coefficients (x : (Fin 2 ⊕ Fin 2) → ℝ) : Fin 2 → ℂ :=
  fun i => ⟨x (Sum.inl i), x (Sum.inr i)⟩

def gram (r : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1,1; 1,1+r^2]

def unitRegion : Set ((Fin 2 ⊕ Fin 2) → ℝ) := {x | ∑ i, x i ^ 2 ≤ 1}

theorem unitRegion_measurable : MeasurableSet unitRegion := by
  apply measurableSet_le
  · fun_prop
  · fun_prop

theorem factor_energy (r : ℝ) (x : (Fin 2 ⊕ Fin 2) → ℝ) :
    (OperatorDerivativeRewrite.Foundation.FiniteStableGamma.ComplexEnergy.energy
      (gram r) (coefficients x)).re =
      ∑ i, (Matrix.toLin' (realDouble (factor r)) x i)^2 := by
  rw [OperatorDerivativeRewrite.Foundation.FiniteStableGamma.ComplexEnergy.energy_re]
  simp [gram, coefficients, realDouble, factor, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fintype.sum_sum_type]
  ring

def complexEllipsoid (r : ℝ) : Set ((Fin 2 ⊕ Fin 2) → ℝ) :=
  {x | (OperatorDerivativeRewrite.Foundation.FiniteStableGamma.ComplexEnergy.energy
      (gram r) (coefficients x)).re ≤ 1}

theorem complexEllipsoid_preimage (r : ℝ) :
    complexEllipsoid r = Matrix.toLin' (realDouble (factor r)) ⁻¹' unitRegion := by
  ext x
  simp only [complexEllipsoid, Set.mem_ofPred_eq, Set.mem_preimage, unitRegion,
    factor_energy]

theorem cauchy_first_ellipsoid_volume : volume (complexEllipsoid 1) = volume unitRegion := by
  rw [complexEllipsoid_preimage, realDouble_preimage_volume _ (by rw [factor_det]; norm_num)
    _ unitRegion_measurable, factor_det]
  norm_num

theorem cauchy_second_ellipsoid_volume :
    volume (complexEllipsoid (Real.sqrt 3)) =
      ENNReal.ofReal (1/3 : ℝ) * volume (complexEllipsoid 1) := by
  rw [complexEllipsoid_preimage, cauchy_two_mode_complex_volume _ unitRegion_measurable,
    cauchy_first_ellipsoid_volume]

theorem unitRegion_contains_ball :
    Metric.closedBall (0 : (Fin 2 ⊕ Fin 2) → ℝ) (1/2) ⊆ unitRegion := by
  intro x hx
  have hn : ‖x‖ ≤ (1/2 : ℝ) := by simpa [dist_zero_right] using hx
  have hb (i) : x i ^ 2 ≤ (1/4 : ℝ) := by
    have hi := (norm_le_pi_norm x i).trans hn
    rw [Real.norm_eq_abs, abs_le] at hi
    nlinarith [hi.1, hi.2]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  simpa [unitRegion, Fintype.sum_sum_type, Fin.sum_univ_two] using hs

theorem unitRegion_subset_ball :
    unitRegion ⊆ Metric.closedBall (0 : (Fin 2 ⊕ Fin 2) → ℝ) 1 := by
  intro x hx
  have hs : ∑ i, x i ^ 2 ≤ 1 := hx
  have hn : ‖x‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (by
    intro i
    have hi := (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)).trans hs
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith)
  simpa [Metric.mem_closedBall, dist_zero_right] using hn

theorem unitRegion_positive : 0 < volume unitRegion :=
  (Metric.measure_closedBall_pos volume (0 : (Fin 2 ⊕ Fin 2) → ℝ) (by norm_num : (0:ℝ)<1/2)).trans_le
    (measure_mono unitRegion_contains_ball)

theorem unitRegion_finite : volume unitRegion < ⊤ :=
  (measure_mono unitRegion_subset_ball).trans_lt measure_closedBall_lt_top

theorem gram_first_actual : gram 1 =
    OperatorDerivativeRewrite.Foundation.FractionalCurvatureSubordinationObstruction.R (1/2) := by
  rw [OperatorDerivativeRewrite.Foundation.FractionalCurvatureSubordinationObstruction.R_half]
  norm_num [gram]

theorem gram_second_actual : gram (Real.sqrt 3) =
    OperatorDerivativeRewrite.Foundation.FractionalCurvatureSubordinationObstruction.P (1/2) := by
  rw [OperatorDerivativeRewrite.Foundation.FractionalCurvatureSubordinationObstruction.P_half]
  norm_num [gram, Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]

theorem cauchy_complex_volume_ratio :
    (volume (complexEllipsoid 1)).toReal /
      (volume (complexEllipsoid (Real.sqrt 3))).toReal = 3 := by
  rw [cauchy_second_ellipsoid_volume, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num), cauchy_first_ellipsoid_volume]
  have hp := ENNReal.toReal_pos (ne_of_gt unitRegion_positive) unitRegion_finite.ne
  field_simp

theorem cauchy_complex_volume_not_real_formula :
    (volume (complexEllipsoid 1)).toReal /
      (volume (complexEllipsoid (Real.sqrt 3))).toReal ≠ Real.sqrt 3 := by
  rw [cauchy_complex_volume_ratio]
  intro h
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

end OperatorDerivativeRewrite.Foundation.ComplexGammaEllipsoidVolume
