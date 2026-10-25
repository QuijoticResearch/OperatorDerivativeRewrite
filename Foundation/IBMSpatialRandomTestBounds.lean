import Foundation.IBMSpatialOccupationMeasure
import Foundation.IBMWeakRandomEvaluation

/-! Actual finite spatial actions admit uniform square-integrable random
operator bounds. These bounds are for random spatial testing, not for the
original IBM stochastic integral, whose native L2 escape is preserved. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialRandomTestBounds
open InfiniteGaussian GaussianBrownianQuadraticVariation IBMSpatialBoundedTestOperator
open IBMSpatialCompletedTestLimit IBMSpatialKernelTesting
open IBMFoldedClockQuadraticVariation

theorem quadraticVariation_norm_bound (T : ℝ≥0) (N : ℕ) :
    ‖quadraticVariation (uniformTime T N)‖ ≤ 3*(T:ℝ) := by
  have he := uniform_quadraticVariation_error T N
  have hd : 2*(T:ℝ)^2/(N+1) ≤ 2*(T:ℝ)^2 := by
    apply div_le_self (by positivity)
    exact_mod_cast (show 1 ≤ N+1 by omega)
  have hb : ‖quadraticVariation (uniformTime T N)-(T:ℝ) • gaussianOne‖ ≤ 2*(T:ℝ) := by
    nlinarith [norm_nonneg (quadraticVariation (uniformTime T N)-(T:ℝ) • gaussianOne)]
  have hnorm : ‖(T:ℝ) • gaussianOne‖ = (T:ℝ) := by
    rw [norm_smul,Real.norm_of_nonneg T.coe_nonneg]
    have h1 : ‖(gaussianOne:GaussianL2)‖ = 1 := by
      have hh := GaussianDeterministicGraphCore.gaussianOne_inner_self
      rw [real_inner_self_eq_norm_sq] at hh
      nlinarith [norm_nonneg (gaussianOne:GaussianL2)]
    rw [h1,mul_one]
  have ht := norm_add_le (quadraticVariation (uniformTime T N)-(T:ℝ) • gaussianOne)
    ((T:ℝ) • gaussianOne)
  rw [sub_add_cancel,hnorm] at ht
  linarith

def finitePath (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) : Completed →L[ℝ] ℝ :=
  ({ toFun := fun z => finiteValue (realize z) T N Y
     map_add' := fun z w => by
       unfold finiteValue
       simp only [map_add]
       rw [← Finset.sum_add_distrib]
       exact Finset.sum_congr rfl fun i _ => cellPair_add _ _ _ _
     map_smul' := fun c z => by
       unfold finiteValue
       simp only [map_smul,RingHom.id_apply,smul_eq_mul]
       rw [Finset.mul_sum]
       exact Finset.sum_congr rfl fun i _ => cellPair_smul c _ _ _ } :
      Completed →ₗ[ℝ] ℝ).mkContinuous (foldedSum T N Y) (fun z => by
        change ‖finiteValue (realize z) T N Y‖ ≤ foldedSum T N Y*‖z‖
        simpa only [realize.norm_map,mul_comm] using finiteValue_bound (realize z) T N Y)

theorem finitePath_measurable (T : ℝ≥0) (N : ℕ) (z : Completed) :
    Measurable (fun Y => finitePath T N Y z) := finiteValue_measurable (realize z) T N

theorem finitePath_bound (T : ℝ≥0) (N : ℕ) :
    ∀ᵐ Y ∂gaussianProduct, ∀ z : Completed, ‖finitePath T N Y z‖ ≤
      ‖quadraticVariation (uniformTime T N) Y‖*‖z‖ := by
  filter_upwards [quadraticVariation_coeFn (uniformTime T N) (uniformTime_monotone T N)] with Y hY
  intro z
  have hf := finiteValue_bound (realize z) T N Y
  rw [realize.norm_map] at hf
  have hs := lossValue_nonneg T N Y
  unfold lossValue at hs
  have hle : foldedSum T N Y ≤ rawSum T N Y := by linarith
  have hr : rawSum T N Y = quadraticVariation (uniformTime T N) Y := hY.symm
  change ‖finiteValue (realize z) T N Y‖ ≤ _
  rw [← hr]
  exact hf.trans (by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right
      (hle.trans (le_abs_self (rawSum T N Y))) (norm_nonneg z))

def limitPath (T : ℝ≥0) (Y : SampleSpace) : Completed →L[ℝ] ℝ :=
  (IBMSpatialPathOccupation.pathOperator T Y).comp realize.toContinuousLinearMap

theorem limitPath_measurable (T : ℝ≥0) (z : Completed) :
    Measurable (fun Y => limitPath T Y z) := IBMSpatialPathOccupation.pathValue_measurable (realize z) T

theorem limitPath_bound (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct, ∀ z : Completed, ‖limitPath T Y z‖ ≤ ‖((T:ℝ) • gaussianOne:GaussianL2) Y‖*‖z‖ := by
  filter_upwards [Lp.coeFn_smul (T:ℝ) (gaussianOne:GaussianL2),gaussianOne_coeFn] with Y hs h1
  intro z
  rw [hs,Pi.smul_apply,h1,smul_eq_mul,mul_one,Real.norm_of_nonneg T.coe_nonneg]
  have hb := IBMSpatialPathOccupation.pathValue_bound (realize z) T Y
  rwa [realize.norm_map] at hb

abbrev RandomTests := Lp Completed 2 gaussianProduct

def finiteOperator (T : ℝ≥0) (N : ℕ) : RandomTests →L[ℝ] Values :=
  IBMWeakRandomEvaluation.operator (finitePath T N) (finitePath_measurable T N)
    (quadraticVariation (uniformTime T N)) (finitePath_bound T N)

def limitOperator (T : ℝ≥0) : RandomTests →L[ℝ] Values :=
  IBMWeakRandomEvaluation.operator (limitPath T) (limitPath_measurable T)
    ((T:ℝ) • gaussianOne) (limitPath_bound T)

theorem finite_actual (T : ℝ≥0) (N : ℕ) (u : RandomTests) :
    finiteOperator T N u =ᵐ[gaussianProduct] fun Y => finiteValue (realize (u Y)) T N Y :=
  IBMWeakRandomEvaluation.value_actual (finitePath T N) (finitePath_measurable T N)
    (quadraticVariation (uniformTime T N)) (finitePath_bound T N) u

theorem limit_actual (T : ℝ≥0) (u : RandomTests) :
    limitOperator T u =ᵐ[gaussianProduct] fun Y => IBMSpatialPathOccupation.pathValue (realize (u Y)) T Y :=
  IBMWeakRandomEvaluation.value_actual (limitPath T) (limitPath_measurable T)
    ((T:ℝ) • gaussianOne) (limitPath_bound T) u

theorem finite_norm_bound (T : ℝ≥0) (N : ℕ) (u : RandomTests) :
    ‖finiteOperator T N u‖ ≤ 3*(T:ℝ)*‖u‖ :=
  (IBMWeakRandomEvaluation.value_bound (finitePath T N) (finitePath_measurable T N)
    (quadraticVariation (uniformTime T N)) (finitePath_bound T N) u).trans
    (mul_le_mul_of_nonneg_right (quadraticVariation_norm_bound T N) (norm_nonneg u))

theorem limit_norm_bound (T : ℝ≥0) (u : RandomTests) : ‖limitOperator T u‖ ≤ 3*(T:ℝ)*‖u‖ := by
  have hb := IBMWeakRandomEvaluation.value_bound (limitPath T) (limitPath_measurable T)
    ((T:ℝ) • gaussianOne) (limitPath_bound T) u
  have hn : ‖((T:ℝ) • gaussianOne:GaussianL2)‖ ≤ 3*(T:ℝ) := by
    have ht := (uniform_quadraticVariation_tendsto T).norm
    exact le_of_tendsto ht (Eventually.of_forall (quadraticVariation_norm_bound T))
  exact hb.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg u))

end OperatorDerivativeRewrite.Foundation.IBMSpatialRandomTestBounds
