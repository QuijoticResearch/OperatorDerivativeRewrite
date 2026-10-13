import Foundation.IBMNegativeSobolevRandom

/-! The spatial Dirac mass at zero belongs to H⁻¹ on the real line. -/
noncomputable section
open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMDeltaBoundary

private theorem weight_memLp_two :
    MemLp (fun x : ℝ => ((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))) 2
      (volume : Measure ℝ) := by
  have hm : AEStronglyMeasurable
      (fun x : ℝ => (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)) volume :=
    (Continuous.rpow_const (by fun_prop)
      (fun x => Or.inl (by positivity))).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  convert integrable_rpow_neg_one_add_norm_sq (E := ℝ)
    (μ := (volume : Measure ℝ)) (r := (2 : ℝ)) (by norm_num) using 1
  ext x
  have hx : 0 ≤ 1 + ‖x‖ ^ 2 := by positivity
  calc
    ((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ)) ^ 2 =
        (1 + ‖x‖ ^ 2) ^ ((-1 / 2 : ℝ) * 2) := by
          rw [← Real.rpow_mul_natCast hx]
          norm_num
    _ = (1 + ‖x‖ ^ 2) ^ (-2 / 2 : ℝ) := by norm_num

/-- The actual Dirac distribution at zero is in complex H⁻¹(ℝ). -/
theorem delta_zero_memHminusOne :
    (TemperedDistribution.delta (0 : ℝ)).MemSobolev (-1) 2 := by
  have hw : MemLp (fun x : ℝ => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ))) 2
      (volume : Measure ℝ) := weight_memLp_two.ofReal
  rw [memSobolev_iff_exists_smulLeftCLM_fourier]
  use hw.toLp _
  rw [TemperedDistribution.fourier_delta_zero]
  ext φ
  simp only [smulLeftCLM_apply_apply, Measure.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hw.coeFn_toLp] with x hx
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), hx]
  simp [smul_eq_mul, mul_comm]

/-- Bundle the origin boundary mass in the concrete H⁻¹ space. -/
def deltaZeroHminusOne : H^{(-1 : ℝ)}(ℝ) :=
  delta_zero_memHminusOne.toBesselPotentialSpace

@[simp] theorem deltaZeroHminusOne_toDistr :
    deltaZeroHminusOne.toDistr = TemperedDistribution.delta (0 : ℝ) := rfl

end OperatorDerivativeRewrite.Foundation.IBMDeltaBoundary
