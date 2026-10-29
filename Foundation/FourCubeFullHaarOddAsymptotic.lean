import Foundation.FourCubeFullOddIntegral
import Foundation.FourCubeFullHaarAsymptotic

/-! First-order off-cutoff control and unrestricted full32 odd partition limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullHaarOddAsymptotic
open QuaternionSU2Representation
open FourCubeFullChartOdd FourCubeFullHaarCutoff FourCubeFullHaarGaussianLimit
open FourCubeFullHaarAsymptotic FourCubeFullOddIntegral

private theorem exponential_even_limit :
    Tendsto (fun t : ℝ => Real.exp (-(1/t^2)/4)/|t|^98) (𝓝[≠] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (49 : ℝ) (1/4) (by norm_num)).comp
    FourCubeHaarPartitionAsymptotic.inverse_square_tendsto
  simp only [Real.rpow_ofNat,Function.comp_def] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hp : |t|^(98 : ℕ)=(t^2)^(49 : ℕ) := by
    calc
      _ = (|t|^2)^49 := by rw [← pow_mul]
      _ = _ := by rw [sq_abs]
  rw [div_pow,one_pow,← hp]
  have he : -(1/4 : ℝ)*(1/t^2)=-(1/t^2)/4 := by ring
  rw [he]
  ring

theorem exponential_first_order_limit :
    Tendsto (fun t : ℝ => Real.exp (-(1/t^2)/4)/|t|^97) (𝓝[≠] 0) (𝓝 0) := by
  have ha : Tendsto (fun t : ℝ => |t|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero] using
      ((continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  have h := exponential_even_limit.mul ha
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change Real.exp (-(1/t^2)/4)/|t|^98*|t|=Real.exp (-(1/t^2)/4)/|t|^97
  field_simp [abs_ne_zero.mpr ht]
  <;> ring

/-- Uniform in arbitrary moving boundary parameters; no continuity is assumed of them. -/
theorem outside_first_order_limit (b : ℝ → Fin 3 → SU2) :
    Tendsto (fun t : ℝ => outsidePartition (b t) (1/t^2)/(t*|t|^96))
      (𝓝[≠] 0) (𝓝 0) := by
  apply squeeze_zero_norm' _ exponential_first_order_limit
  apply Filter.Eventually.of_forall
  intro t
  have he : |t*|t|^96|=|t|^97 := by
    rw [abs_mul,abs_pow,abs_abs]
    ring
  rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (outside_nonneg _ _),he]
  exact div_le_div_of_nonneg_right (outside_bound _ _ (by positivity)) (by positivity)

theorem outside_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => (outsidePartition (parameters x y z t) (1/t^2)-
      outsidePartition (parameters x y z (-t)) (1/t^2))/(2*t*|t|^96))
      (𝓝[≠] 0) (𝓝 0) := by
  have h := ((outside_first_order_limit (parameters x y z)).sub
    (outside_first_order_limit (fun t => parameters x y z (-t)))).div_const 2
  simp only [sub_self,zero_div] at h
  apply h.congr'
  filter_upwards with t
  ring

/-- Genuine unrestricted full-Haar odd partition limit, after cutoff and tail proofs. -/
theorem full_partition_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => (FourCubeCompletedHaar.completedPartition (1/t^2) (parameters x y z t)-
      FourCubeCompletedHaar.completedPartition (1/t^2) (parameters x y z (-t)))/(2*t*|t|^96))
      (𝓝[≠] 0) (𝓝 (-(((1784975 : ℝ)/2750517)*x*y*z)*
        (∫ Y : Coordinates,gaussianDensity x y z Y))) := by
  have h := (actual_cutoff_partition_odd_value x y z).add (outside_odd_limit x y z)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards with t
  rw [partition_split,partition_split]
  ring

end OperatorDerivativeRewrite.Foundation.FourCubeFullHaarOddAsymptotic
