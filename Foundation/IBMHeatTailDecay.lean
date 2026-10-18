import Foundation.IBMClockOriginMean

/-! Gaussian tail and polynomial decay estimates needed to remove the
actual quartic heat boundary endpoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMHeatTailDecay
open IBMClockGaussianTail IBMClockHeatPotential IBMClockOriginMean IBMClockHeatOccupation

theorem first_tail_moment_integrable {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun x => x*density x) (Ioi r) := by
  have hi := integrableOn_Ioi_deriv_of_nonpos'
    (fun x (_ : x ∈ Ici r) => density_hasDerivAt x)
    (fun x (hx : x ∈ Ioi r) => mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (hr.trans hx.le)) (gaussianPDFReal_nonneg _ _ _)) density_atTop
  convert hi.neg using 1
  funext x
  simp only [Pi.neg_apply, neg_mul, neg_neg]

theorem first_tail_moment {r : ℝ} (hr : 0 ≤ r) :
    (∫ x in Ioi r, x*density x) = density r := by
  have he := integral_Ioi_of_hasDerivAt_of_nonpos'
    (fun x (_ : x ∈ Ici r) => density_hasDerivAt x)
    (fun x (hx : x ∈ Ioi r) => mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (hr.trans hx.le)) (gaussianPDFReal_nonneg _ _ _)) density_atTop
  simp only [neg_mul, integral_neg, zero_sub] at he
  linarith

theorem mills_bound {r : ℝ} (hr : 0 ≤ r) : r*tail r ≤ density r := by
  rw [tail, ← integral_const_mul, ← first_tail_moment hr]
  apply integral_mono_ae (density_integrable.integrableOn.const_mul r)
    (first_tail_moment_integrable hr)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_le_mul_of_nonneg_right hx.le (gaussianPDFReal_nonneg _ _ _)

theorem tail_le_density {r : ℝ} (hr : 1 ≤ r) : tail r ≤ density r := by
  have hm := mills_bound (by linarith : 0 ≤ r)
  have hn := tail_nonneg r
  nlinarith

theorem potential_le_density {T r : ℝ} (hr : 0 ≤ r) :
    potential T r ≤ 4*Real.sqrt T*density (r/Real.sqrt T) := by
  have hn := mul_nonneg hr (tail_nonneg (r/Real.sqrt T))
  unfold potential
  nlinarith

theorem power_density_decay {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun r : ℝ => r^k*density (r/a)) atTop (𝓝 0) := by
  have hb : 0 < 1/(2*a^2) := by positivity
  have he := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hb (k : ℝ)).tendsto_zero_of_tendsto
    (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1/2 : ℝ) < 0)))
  have hd : (fun r : ℝ => r^k*density (r/a)) =
      fun r => (Real.sqrt (2*Real.pi))⁻¹ * (r^(k : ℝ)*Real.exp (-(1/(2*a^2))*r^2)) := by
    funext r
    simp only [density, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Real.rpow_natCast]
    have hx : -(r/a)^2/2 = -(1/(2*a^2))*r^2 := by field_simp
    rw [hx]
    ring
  rw [hd]
  simpa only [mul_zero] using he.const_mul ((Real.sqrt (2*Real.pi))⁻¹)

theorem shifted_power_density_decay {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun r : ℝ => (1+|r|)^k*density (r/a)) atTop (𝓝 0) := by
  have hi := (power_density_decay ha k).const_mul (2^k : ℝ)
  apply squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hi)
  · exact Eventually.of_forall fun r => mul_nonneg (by positivity) (gaussianPDFReal_nonneg _ _ _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    rw [abs_of_nonneg (by linarith : 0 ≤ r)]
    have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1+r) (by linarith : 1+r ≤ 2*r) k
    simpa only [density, mul_pow, mul_assoc] using
      mul_le_mul_of_nonneg_right hp (gaussianPDFReal_nonneg 0 1 (r/a))

end OperatorDerivativeRewrite.Foundation.IBMHeatTailDecay
