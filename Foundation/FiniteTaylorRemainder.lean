import Foundation.FiniteCovarianceHessian
import Foundation.GaussianTaylorRemainder

/-! A genuine multivariate second-order Taylor estimate obtained by actual
one-dimensional differentiation along affine lines. The third derivative is
the derivative of the actual Hessian, never independent prescribed data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteTaylorRemainder
open FiniteCovarianceHessian
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def line (Φ : (ι → ℝ) → ℝ) (x v : ι → ℝ) (s : ℝ) : ℝ := Φ (x + s • v)

def thirdDerivative (Φ : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (hessian Φ) x

def remainder (Φ : (ι → ℝ) → ℝ) (x v : ι → ℝ) : ℝ :=
  Φ (x+v) - Φ x - fderiv ℝ Φ x v - (1/2:ℝ) * hessian Φ x v v

theorem line_contDiff (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 3 Φ) (x v : ι → ℝ) :
    ContDiff ℝ 3 (line Φ x v) :=
  hΦ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

theorem third_line (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 3 Φ)
    (x v : ι → ℝ) (t : ℝ) :
    iteratedDeriv 3 (line Φ x v) t = fderiv ℝ (hessian Φ) (x+t•v) v v v := by
  have hH : ContDiff ℝ 1 (hessian Φ) :=
    (hΦ.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  have hl : HasDerivAt (fun s : ℝ => x+s•v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hd := (((hH.differentiable (by norm_num) (x+t•v)).hasFDerivAt.comp_hasDerivAt t hl).clm_apply
    (hasDerivAt_const t v)).clm_apply (hasDerivAt_const t v)
  have he : deriv (deriv (line Φ x v)) = fun s => hessian Φ (x+s•v) v v :=
    funext fun s => (line_second_hasDerivAt Φ (hΦ.of_le (by norm_num)) x v s).deriv
  simp only [show (3:ℕ)=2+1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero, he]
  simpa using hd.deriv

theorem third_line_bound (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 3 Φ) (M : ℝ≥0)
    (hM : ∀ z v w u, ‖thirdDerivative Φ z v w u‖ ≤ (M:ℝ)*‖v‖*‖w‖*‖u‖) (x v : ι → ℝ) (t : ℝ) :
    ‖iteratedDeriv 3 (line Φ x v) t‖ ≤ (M:ℝ)*‖v‖^3 := by
  rw [third_line Φ hΦ]
  simpa only [thirdDerivative, pow_succ, pow_zero, one_mul, mul_assoc] using hM (x+t•v) v v v

/-- The dimension-free cubic estimate uses the sup norm on the coordinate space. -/
theorem remainder_bound (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 3 Φ) (M : ℝ≥0)
    (hM : ∀ z v w u, ‖thirdDerivative Φ z v w u‖ ≤ (M:ℝ)*‖v‖*‖w‖*‖u‖) (x v : ι → ℝ) :
    ‖remainder Φ x v‖ ≤ ((M:ℝ)/6)*‖v‖^3 := by
  have hr := GaussianTaylorRemainder.remainder_bound (line Φ x v) (line_contDiff Φ hΦ x v)
    ((M:ℝ)*‖v‖^3) (third_line_bound Φ hΦ M hM x v) 0 1
  have hd : deriv (line Φ x v) 0 = fderiv ℝ Φ x v := by
    unfold line
    simpa using (line_hasDerivAt Φ (hΦ.differentiable (by norm_num)) x v 0).deriv
  have hdd : deriv (deriv (line Φ x v)) 0 = hessian Φ x v v := by
    unfold line
    simpa using (line_second_hasDerivAt Φ (hΦ.of_le (by norm_num)) x v 0).deriv
  simpa only [GaussianTaylorRemainder.remainder, hd, hdd, line, zero_smul, one_smul,
    add_zero, sub_zero, mul_one, one_pow, abs_one, remainder, mul_div_assoc, div_mul_eq_mul_div] using hr

theorem remainder_continuous (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 3 Φ) :
    Continuous (fun z : (ι → ℝ) × (ι → ℝ) => remainder Φ z.1 z.2) := by
  have hd : Continuous (fderiv ℝ Φ) := (hΦ.fderiv_right (m := 0) (by norm_num)).continuous
  have hH : Continuous (hessian Φ) :=
    ((hΦ.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  exact (((hΦ.continuous.comp (continuous_fst.add continuous_snd)).sub
    (hΦ.continuous.comp continuous_fst)).sub
    ((hd.comp continuous_fst).clm_apply continuous_snd)).sub
    (continuous_const.mul (((hH.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd))

/-- Explicit second-order identity with the genuine remainder and mixed partials. -/
theorem taylor_identity (Φ : (ι → ℝ) → ℝ) (x v : ι → ℝ) :
    Φ (x+v)-Φ x = (∑ i, v i * partialDerivative Φ i x) +
      (1/2:ℝ)*(∑ i, ∑ j, v i*v j*mixedPartial Φ i j x) + remainder Φ x v := by
  rw [← differential_expansion, ← hessian_expansion]
  unfold remainder
  ring

end OperatorDerivativeRewrite.Foundation.FiniteTaylorRemainder
