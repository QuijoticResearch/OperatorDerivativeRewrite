import Foundation.IBMSpatialBoundedTestOperator

/-! Actual endpoint rectangle functional, before any spatial test completion. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialEndpointOperator
open InfiniteGaussian GaussianTimeProcess IBMSpatialBoundedTestOperator
open IBMSpatialKernelTesting IBMSpatialClockKernelError IBMSpatialKernelUniformBound

def endpointValue (F : Tests) (T : ℝ≥0) (Y : SampleSpace) : ℝ :=
  cellPair F 0 |process T Y|

theorem endpointValue_measurable (F : Tests) (T : ℝ≥0) :
    Measurable (endpointValue F T) :=
  (cellPair_measurable F F.continuous.measurable).comp
    (measurable_const.prodMk (process_stronglyMeasurable T).measurable.norm)

theorem endpointValue_bound (F : Tests) (T : ℝ≥0) (Y : SampleSpace) :
    ‖endpointValue F T Y‖ ≤ ‖F‖*(process T Y)^2 := by
  simpa only [endpointValue,sub_zero,sq_abs] using
    cell_norm_bound F F.continuous.measurable ‖F‖ F.norm_coe_le_norm 0 |process T Y|

theorem endpointValue_integrable (F : Tests) (T : ℝ≥0) :
    Integrable (endpointValue F T) gaussianProduct := by
  apply (((process_memLp T 2 (by norm_num)).integrable_sq).const_mul ‖F‖).mono'
    (endpointValue_measurable F T).aestronglyMeasurable
  exact ae_of_all _ fun Y => endpointValue_bound F T Y

def value (F : Tests) (T : ℝ≥0) : Values := (endpointValue_integrable F T).toL1 _

theorem value_actual (F : Tests) (T : ℝ≥0) :
    value F T =ᵐ[gaussianProduct] endpointValue F T := (endpointValue_integrable F T).coeFn_toL1

theorem value_norm_bound (F : Tests) (T : ℝ≥0) : ‖value F T‖ ≤ (T:ℝ)*‖F‖ := by
  rw [value,L1.norm_of_fun_eq_integral_norm]
  have hb := integral_mono (endpointValue_integrable F T).norm
    (((process_memLp T 2 (by norm_num)).integrable_sq).const_mul ‖F‖)
    (endpointValue_bound F T)
  rw [integral_const_mul] at hb
  have hm : (∫ Y, (process T Y)^2 ∂gaussianProduct) = (T:ℝ) := by
    simpa only [pow_two,min_self] using process_product_integral T T
  rw [hm] at hb
  simpa only [mul_comm] using hb

theorem value_add (F G : Tests) (T : ℝ≥0) : value (F+G) T = value F T+value G T := by
  apply Lp.ext
  filter_upwards [value_actual (F+G) T,value_actual F T,value_actual G T,
    Lp.coeFn_add (value F T) (value G T)] with Y ha hf hg hs
  rw [ha,hs,Pi.add_apply,hf,hg]
  exact cellPair_add F G _ _

theorem value_smul (c : ℝ) (F : Tests) (T : ℝ≥0) : value (c • F) T = c • value F T := by
  apply Lp.ext
  filter_upwards [value_actual (c • F) T,value_actual F T,Lp.coeFn_smul c (value F T)] with Y ha hf hs
  rw [ha,hs,Pi.smul_apply,hf,smul_eq_mul]
  exact cellPair_smul c F _ _

def operator (T : ℝ≥0) : Tests →L[ℝ] Values :=
  ({ toFun := fun F => value F T
     map_add' := fun F G => value_add F G T
     map_smul' := fun c F => value_smul c F T } : Tests →ₗ[ℝ] Values).mkContinuous
    (T:ℝ) (fun F => value_norm_bound F T)

theorem operator_apply (T : ℝ≥0) (F : Tests) : operator T F = value F T := rfl

theorem operator_norm (T : ℝ≥0) : ‖operator T‖ ≤ (T:ℝ) :=
  (operator T).opNorm_le_bound T.coe_nonneg (fun F => value_norm_bound F T)

end OperatorDerivativeRewrite.Foundation.IBMSpatialEndpointOperator
