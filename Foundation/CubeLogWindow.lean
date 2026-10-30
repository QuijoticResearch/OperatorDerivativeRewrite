import Foundation.CubePolynomialGround
import Foundation.CubeNativeCompression
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Shrinking logarithmic action-window localization of the ACTUAL native Wilson operator. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CubeLogWindow
open CubeSlabGround CubeSlabL2 CubePolynomialGround CubeOperatorLocalization CubeNativeCompression

def window (t : ℝ) : ℝ := 80*t^2*Real.log (1/t)

theorem window_tendsto_zero : Tendsto window (𝓝 (0 : ℝ)) (𝓝 0) := by
  have he : window=(fun t : ℝ => -80*t*(t*Real.log t)) := by
    funext t
    simp only [window,one_div,Real.log_inv]
    ring
  have hc : Continuous window := by
    rw [he]
    exact (continuous_const.mul continuous_id).mul Real.continuous_mul_log
  simpa only [window,zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,zero_mul] using hc.tendsto (0:ℝ)

theorem window_nonnegative (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) : 0 ≤ window t := by
  have hi : 1 ≤ 1/t := (le_div_iff₀ ht).mpr (by simpa using h1)
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg t)) (Real.log_nonneg hi)

private theorem scale_identity (t : ℝ) (ht : 0 < t) : (1/t^2)*t^2=1 := by
  field_simp [ht.ne']

private theorem exp_window (t : ℝ) (ht : 0 < t) :
    Real.exp (-(1/t^2)*window t/2)=t^40 := by
  have hl : Real.log (1/t)= -Real.log t := by rw [one_div,Real.log_inv]
  have he : -(1/t^2)*window t/2=40*Real.log t := by
    rw [window,hl]
    field_simp [ht.ne']
    ring
  rw [he]
  change Real.exp ((40 : ℕ) * Real.log t) = t^40
  rw [Real.exp_nat_mul,Real.exp_log ht]

/-- Quantitative factor for every actual native ground; the normalization is not Gibbs. -/
theorem eigenfactor_window (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (d : GroundData (1/t^2)) :
    Real.exp (-(1/t^2)*window t/2)/d.value ≤ (1/lowerConstant)*t := by
  have hl := eigenvalue_polynomial d t ht h1 (by positivity)
    (le_of_eq (scale_identity t ht))
  rw [exp_window t ht]
  have hd := div_le_div_of_nonneg_left (pow_nonneg ht.le 40)
    (mul_pos lowerConstant_pos (pow_pos ht 39)) hl
  have he : t^40/(lowerConstant*t^39)=(1/lowerConstant)*t := by
    field_simp [lowerConstant_pos.ne',ht.ne']
  exact hd.trans_eq he

/-- Uniform over the full native L2 input space at coupling 1/t^2. -/
theorem input_tail (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (d : GroundData (1/t^2)) (f : StateL2 d) :
    ‖operator d (tailPart d (window t) f)‖ ≤ (1/lowerConstant)*t*‖f‖ :=
  (operator_tailPart_bound d (by positivity) (window t) f).trans
    (mul_le_mul_of_nonneg_right (eigenfactor_window t ht h1 d) (norm_nonneg f))

theorem output_tail (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (d : GroundData (1/t^2)) (f : StateL2 d) :
    ‖tailPart d (window t) (operator d f)‖ ≤ (1/lowerConstant)*t*‖f‖ :=
  (output_tail_bound d (by positivity) (window t) f).trans
    (mul_le_mul_of_nonneg_right (eigenfactor_window t ht h1 d) (norm_nonneg f))

/-- The full actual operator compresses into a shrinking action window with O(t) error. -/
theorem compression (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (d : GroundData (1/t^2)) (f : StateL2 d) :
    ‖operator d f-lowPart d (window t) (operator d (lowPart d (window t) f))‖ ≤
      (2/lowerConstant)*t*‖f‖ := by
  have h := (compression_error d (by positivity) (window t) f).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (eigenfactor_window t ht h1 d) (by norm_num : (0:ℝ) ≤ 2))
      (norm_nonneg f))
  convert h using 1 <;> ring

/-- Native spaces vary with t. The statement is convergence of the actual compression
error norms, uniformly for arbitrary unit-bounded choices in those spaces. -/
theorem compression_tendsto_zero
    (F : (t : ℝ) → StateL2 (ground (1/t^2)))
    (hF : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖F t‖ ≤ 1) :
    Tendsto (fun t : ℝ => ‖operator (ground (1/t^2)) (F t)-
      lowPart (ground (1/t^2)) (window t)
        (operator (ground (1/t^2)) (lowPart (ground (1/t^2)) (window t) (F t)))‖)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : Continuous (fun t : ℝ => (2/lowerConstant)*t) := continuous_const.mul continuous_id
  have hl : Tendsto (fun t : ℝ => (2/lowerConstant)*t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hl
  have hle : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t ≤ 1 :=
    (eventually_le_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hle] with t ht ht1
  have h := compression t ht ht1 (ground (1/t^2)) (F t)
  have h' := mul_le_mul_of_nonneg_left (hF t ht ht1)
    (mul_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) lowerConstant_pos.le) ht.le)
  simpa only [mul_one] using h.trans h'


/-- Quantitative concentration of the actual stationary ground law at the SAME
shrinking window. This law is not replaced by a spatial Gibbs measure. -/
theorem stationary_tail (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (d : GroundData (1/t^2)) :
    d.stationary.real {U | window t ≤ CubeWilsonSlab.spatialAction U} ≤
      ((1/lowerConstant)*t)^2 := by
  have h := CubeGroundMass.action_tail_eigenfactor d (by positivity) (window t)
  have he : Real.exp (-(1/t^2)*window t)/d.value^2 =
      (Real.exp (-(1/t^2)*window t/2)/d.value)^2 := by
    have hx (x : ℝ) : Real.exp x = (Real.exp (x/2))^2 := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    rw [div_pow]
    exact congrArg (fun z : ℝ => z/d.value^2) (hx (-(1/t^2)*window t))
  rw [he] at h
  exact h.trans (pow_le_pow_left₀
    (div_nonneg (Real.exp_pos _).le d.value_pos.le) (eigenfactor_window t ht h1 d) 2)

/-- Convergence of actual stationary tail probabilities, without a common-space
identification or a Gaussian-radius tightness claim. -/
theorem stationary_tail_tendsto_zero :
    Tendsto (fun t : ℝ => (ground (1/t^2)).stationary.real
      {U | window t ≤ CubeWilsonSlab.spatialAction U}) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : Continuous (fun t : ℝ => ((1/lowerConstant)*t)^2) :=
    (continuous_const.mul continuous_id).pow 2
  have hl : Tendsto (fun t : ℝ => ((1/lowerConstant)*t)^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using
      (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) ?_ hl
  have hle : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t ≤ 1 :=
    (eventually_le_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hle] with t ht ht1
  exact stationary_tail t ht ht1 (ground (1/t^2))

end OperatorDerivativeRewrite.Foundation.CubeLogWindow
