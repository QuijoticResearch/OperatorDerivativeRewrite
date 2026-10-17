import Foundation.SparseBlockWilsonAction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds

/-! An explicit normalized Lie-algebra logarithm for the rotation base holonomies. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2ExplicitRotationLog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
open SU2TraceHessianModel SU2MatrixExponentialBridge SparseBlockWilsonAction
open ChristoffelSkewCancellation

def explicitLog (θ : ℝ) : M2 := (2*θ) • tangent 2

theorem explicitLog_diagonal (θ : ℝ) :
    explicitLog θ=Matrix.diagonal ![(θ:ℂ)*Complex.I,-(θ:ℂ)*Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [explicitLog, tangent, generator, generatorZ, Matrix.diagonal] <;> ring

theorem exp_explicitLog (θ : ℝ) : NormedSpace.exp (explicitLog θ)=rotation θ := by
  have hn : Complex.exp (-((θ:ℂ)*Complex.I))=
      Complex.cos (θ:ℂ)-Complex.sin (θ:ℂ)*Complex.I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [explicitLog_diagonal, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.exp_mul_I,
      rotation, generatorZ, hn] <;> ring

theorem explicitLog_as_algebraElement (θ : ℝ) :
    explicitLog θ=algebraElement (Pi.single (2:Fin 3) (2*θ)) :=
  (algebraElement_single (2*θ) 2).symm

theorem explicitLog_trace (θ : ℝ) : Matrix.trace (explicitLog θ)=0 := by
  rw [explicitLog_as_algebraElement]
  exact algebraElement_trace _

theorem explicitLog_skew (θ : ℝ) : (explicitLog θ)ᴴ= -explicitLog θ := by
  rw [explicitLog_as_algebraElement]
  exact algebraElement_skewHermitian _

theorem explicitLog_metric_sq (θ : ℝ) :
    -2*traceReal ((explicitLog θ)^2)=4*θ^2 := by
  rw [explicitLog_as_algebraElement, algebraElement_metric_sq]
  simp [lengthSq, Pi.single_apply]
  ring

theorem inverse_rotation (θ : ℝ) : (rotation θ)⁻¹=rotation (-θ) := by
  rw [← exp_explicitLog, ← Matrix.exp_neg]
  have he : -explicitLog θ=explicitLog (-θ) := by
    unfold explicitLog
    rw [mul_neg, neg_smul]
  rw [he, exp_explicitLog]

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem base_holonomy_has_log (θ : ℝ) (p : Face) (hp : p∈faces) :
    ∃ L : M2, NormedSpace.exp L=evalWord θ 0 (faceWord p) ∧
      Matrix.trace L=0 ∧ Lᴴ= -L ∧ -2*traceReal (L^2) ≤ 4*θ^2 := by
  rcases base_holonomies θ p hp with h | h | h
  · refine ⟨(0:M2), ?_, by simp, by simp, ?_⟩
    · simpa using h.symm
    · simp only [zero_pow (by decide : 2 ≠ 0), traceReal, Matrix.trace_zero, Complex.zero_re, mul_zero]
      positivity
  · refine ⟨explicitLog θ, ?_, explicitLog_trace θ, explicitLog_skew θ, ?_⟩
    · rw [exp_explicitLog, h]
    · rw [explicitLog_metric_sq]
  · refine ⟨explicitLog (-θ), ?_, explicitLog_trace (-θ), explicitLog_skew (-θ), ?_⟩
    · rw [exp_explicitLog, h, inverse_rotation]
    · rw [explicitLog_metric_sq, neg_sq]

def diagonalLog (U : M2) : M2 := Matrix.diagonal (fun i => Complex.log (U i i))

theorem complex_log_exp_imag (s : ℝ) (hs : |s| < Real.pi) :
    Complex.log (Complex.exp ((s:ℂ)*Complex.I))=(s:ℂ)*Complex.I := by
  apply Complex.log_exp <;> norm_num [Complex.mul_im] <;>
    linarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2]

theorem diagonalLog_rotation (θ : ℝ) (hθ : |θ| < Real.pi) :
    diagonalLog (rotation θ)=explicitLog θ := by
  have hp := complex_log_exp_imag θ hθ
  have hn : Complex.log (Complex.exp (-((θ:ℂ)*Complex.I)))= -((θ:ℂ)*Complex.I) := by
    simpa only [abs_neg, Complex.ofReal_neg, neg_mul] using
      complex_log_exp_imag (-θ) (by simpa using hθ)
  rw [← exp_explicitLog θ]
  simp only [explicitLog_diagonal]
  rw [Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonalLog, Matrix.diagonal, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, hp, hn]

theorem base_diagonalLog_metric_bound (θ : ℝ) (hθ : |θ| < Real.pi) (p : Face) (hp : p∈faces) :
    -2*traceReal ((diagonalLog (evalWord θ 0 (faceWord p)))^2) ≤ 4*θ^2 := by
  rcases base_holonomies θ p hp with h | h | h
  · rw [h]
    have hd : diagonalLog (1:M2)=0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [diagonalLog, Matrix.diagonal]
    simp only [hd, zero_pow (by decide : 2 ≠ 0), traceReal, Matrix.trace_zero,
      Complex.zero_re, mul_zero]
    positivity
  · rw [h, diagonalLog_rotation θ hθ, explicitLog_metric_sq]
  · rw [h, inverse_rotation, diagonalLog_rotation (-θ) (by simpa using hθ),
      explicitLog_metric_sq, neg_sq]

def diagonalLogLength (U : M2) : ℝ := Real.sqrt (-2*traceReal ((diagonalLog U)^2))

theorem base_logLength_bound (θ : ℝ) (hθ : |θ| < Real.pi) (p : Face) (hp : p∈faces) :
    diagonalLogLength (evalWord θ 0 (faceWord p)) ≤ 2*|θ| := by
  unfold diagonalLogLength
  calc
    _ ≤ Real.sqrt (4*θ^2) := Real.sqrt_le_sqrt (base_diagonalLog_metric_bound θ hθ p hp)
    _ = 2*|θ| := by
      rw [show 4*θ^2=(2*θ)^2 by ring, Real.sqrt_sq_eq_abs, abs_mul]
      norm_num

theorem base_logLength_strict (θ : ℝ) (ht : 0 < θ) (hθ : θ < Real.pi) (p : Face) (hp : p∈faces) :
    diagonalLogLength (evalWord θ 0 (faceWord p)) < 3*θ := by
  have hh := base_logLength_bound θ (by rwa [abs_of_pos ht]) p hp
  rw [abs_of_pos ht] at hh
  linarith

theorem rational_strict_log_cap (p : Face) (hp : p∈faces) :
    diagonalLogLength (evalWord SparseWilsonCurvature.witnessAngle 0 (faceWord p)) <
      3*SparseWilsonCurvature.witnessAngle := by
  apply base_logLength_strict _ (by norm_num [SparseWilsonCurvature.witnessAngle]) _ p hp
  have hh := Real.pi_gt_three
  norm_num [SparseWilsonCurvature.witnessAngle]
  linarith

end OperatorDerivativeRewrite.Foundation.SU2ExplicitRotationLog
