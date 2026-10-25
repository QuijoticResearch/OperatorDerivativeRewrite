import Foundation.IBMSpatialKernelUniformBound
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Operator.Extend

/-! The literal finite spatial-kernel action on ALL bounded continuous tests.
The inherited test norm is the supremum norm. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialBoundedTestOperator
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMSpatialKernelTesting IBMSpatialClockKernelError IBMSpatialKernelUniformBound

abbrev Tests := BoundedContinuousFunction (ℝ × ℝ) ℝ
abbrev Values := Lp ℝ 1 gaussianProduct

def finiteValue (F : Tests) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (N+1), cellPair F |process (uniformTime T N i.castSucc) Y|
    |process (uniformTime T N i.succ) Y|

theorem finiteValue_measurable (F : Tests) (T : ℝ≥0) (N : ℕ) :
    Measurable (finiteValue F T N) := by
  apply Finset.measurable_fun_sum
  intro i hi
  exact (cellPair_measurable F F.continuous.measurable).comp
    (((process_stronglyMeasurable _).measurable.norm).prodMk
      ((process_stronglyMeasurable _).measurable.norm))

theorem finiteValue_bound (F : Tests) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    ‖finiteValue F T N Y‖ ≤ ‖F‖*IBMFoldedClockQuadraticVariation.foldedSum T N Y := by
  calc
    _ ≤ ∑ i : Fin (N+1), ‖cellPair F |process (uniformTime T N i.castSucc) Y|
        |process (uniformTime T N i.succ) Y|‖ := norm_sum_le _ _
    _ ≤ _ := by
      unfold IBMFoldedClockQuadraticVariation.foldedSum
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => cell_norm_bound F F.continuous.measurable ‖F‖ F.norm_coe_le_norm _ _

theorem finiteValue_integrable (F : Tests) (T : ℝ≥0) (N : ℕ) :
    Integrable (finiteValue F T N) gaussianProduct := by
  apply ((IBMFoldedClockQuadraticVariation.foldedSum_integrable T N).const_mul ‖F‖).mono'
    (finiteValue_measurable F T N).aestronglyMeasurable
  exact ae_of_all _ fun Y => finiteValue_bound F T N Y

def value (F : Tests) (T : ℝ≥0) (N : ℕ) : Values := (finiteValue_integrable F T N).toL1 _

theorem value_actual (F : Tests) (T : ℝ≥0) (N : ℕ) :
    value F T N =ᵐ[gaussianProduct] finiteValue F T N := (finiteValue_integrable F T N).coeFn_toL1

theorem value_norm_bound (F : Tests) (T : ℝ≥0) (N : ℕ) : ‖value F T N‖ ≤ (T:ℝ)*‖F‖ := by
  rw [value,L1.norm_of_fun_eq_integral_norm]
  have hi := integral_mono (finiteValue_integrable F T N).norm
    ((IBMFoldedClockQuadraticVariation.foldedSum_integrable T N).const_mul ‖F‖)
    (finiteValue_bound F T N)
  rw [integral_const_mul] at hi
  have hb := mul_le_mul_of_nonneg_left (folded_mean_le T N) (norm_nonneg F)
  nlinarith

theorem cellPair_add (F G : Tests) (x y : ℝ) :
    cellPair (F+G) x y = cellPair F x y+cellPair G x y := by
  have hF := cell_pair_integrable F F.continuous.measurable ‖F‖ F.norm_coe_le_norm x y
  have hG := cell_pair_integrable G G.continuous.measurable ‖G‖ G.norm_coe_le_norm x y
  unfold cellPair
  have he : (fun z => IBMSpatialIncrementKernel.rectangle (cellSet x y) z*(F z+G z)) =
      fun z => IBMSpatialIncrementKernel.rectangle (cellSet x y) z*F z+
        IBMSpatialIncrementKernel.rectangle (cellSet x y) z*G z := by
    funext z
    change _*(F z+G z) = _
    ring
  simp only [Pi.add_apply]
  rw [he,integral_add hF hG]

theorem cellPair_smul (c : ℝ) (F : Tests) (x y : ℝ) :
    cellPair (c • F) x y = c*cellPair F x y := by
  unfold cellPair
  have he : (fun z => IBMSpatialIncrementKernel.rectangle (cellSet x y) z*(c*F z)) =
      fun z => c*(IBMSpatialIncrementKernel.rectangle (cellSet x y) z*F z) := by
    funext z
    change _*(c*F z) = _
    ring
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [he,integral_const_mul]

theorem value_add (F G : Tests) (T : ℝ≥0) (N : ℕ) : value (F+G) T N = value F T N+value G T N := by
  apply Lp.ext
  filter_upwards [value_actual (F+G) T N,value_actual F T N,value_actual G T N,
    Lp.coeFn_add (value F T N) (value G T N)] with Y ha hf hg hs
  rw [ha,hs,Pi.add_apply,hf,hg]
  unfold finiteValue
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => cellPair_add F G _ _

theorem value_smul (c : ℝ) (F : Tests) (T : ℝ≥0) (N : ℕ) : value (c • F) T N = c • value F T N := by
  apply Lp.ext
  filter_upwards [value_actual (c • F) T N,value_actual F T N,Lp.coeFn_smul c (value F T N)] with Y ha hf hs
  rw [ha,hs,Pi.smul_apply,hf,smul_eq_mul]
  unfold finiteValue
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => cellPair_smul c F _ _

def operator (T : ℝ≥0) (N : ℕ) : Tests →L[ℝ] Values :=
  ({ toFun := fun F => value F T N
     map_add' := fun F G => value_add F G T N
     map_smul' := fun c F => value_smul c F T N } : Tests →ₗ[ℝ] Values).mkContinuous
    (T:ℝ) (fun F => value_norm_bound F T N)

theorem operator_apply (F : Tests) (T : ℝ≥0) (N : ℕ) : operator T N F = value F T N := rfl

theorem operator_norm (T : ℝ≥0) (N : ℕ) : ‖operator T N‖ ≤ (T:ℝ) :=
  (operator T N).opNorm_le_bound T.coe_nonneg (fun F => value_norm_bound F T N)

theorem value_old_action (F : Tests) {K : ℝ≥0} (hF : LipschitzWith K F) (T : ℝ≥0) (N : ℕ) :
    value F T N = IBMSpatialKernelOccupation.action F hF ‖F‖ F.norm_coe_le_norm T N := by
  apply Lp.ext
  filter_upwards [value_actual F T N,IBMSpatialKernelOccupation.action_actual F hF ‖F‖ F.norm_coe_le_norm T N] with Y hv ha
  exact hv.trans ha.symm

end OperatorDerivativeRewrite.Foundation.IBMSpatialBoundedTestOperator
