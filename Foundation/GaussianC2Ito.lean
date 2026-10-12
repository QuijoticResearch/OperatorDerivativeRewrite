import Foundation.GaussianSmoothIto
import Foundation.RealSteklovApprox
import Foundation.GaussianBoundedApproximation

/-! Brownian Ito for genuine C2 functions with bounded first and second
actual derivatives. No third derivative of the original function is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianC2Ito
open InfiniteGaussian GaussianTimeProcess GaussianLipschitzIntegrands GaussianPredictableFull
open RealSteklovApprox GaussianBoundedApproximation

variable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K0 K1 : ℝ≥0)
  (h0 : ∀ x, ‖deriv f x‖₊ ≤ K0) (h1 : ∀ x, ‖deriv (deriv f) x‖₊ ≤ K1)

def functionLip : LipschitzWith K0 f :=
  lipschitzWith_of_nnnorm_deriv_le (hf.differentiable (by norm_num)) h0

def derivativeLip : LipschitzWith K1 (deriv f) :=
  lipschitzWith_of_nnnorm_deriv_le hf.differentiable_deriv_two h1

include hf in
theorem second_continuous : Continuous (deriv (deriv f)) :=
  (deriv_contDiff_one f hf).continuous_deriv_one

/-- The drift is the actual second derivative, constructed independently of Ito. -/
def curvatureValue (t : ℝ≥0) : GaussianL2 :=
  boundedValue (second_continuous f hf) (fun x => show ‖deriv (deriv f) x‖ ≤ (K1:ℝ) from h1 x) t

theorem curvatureValue_coeFn (t : ℝ≥0) : curvatureValue f hf K1 h1 t =ᵐ[gaussianProduct]
    fun ω => deriv (deriv f) (process t ω) := boundedValue_coeFn _ _ _

/-- Smooth approximants are actual interval averages of the original function. -/
def smoothApprox (n : ℕ) : ℝ → ℝ := average f (width n)

include hf in
theorem smoothApprox_C3 (n : ℕ) : ContDiff ℝ 3 (smoothApprox f n) := approximation_C3 f hf n

def approximateFunctionLip (n : ℕ) : LipschitzWith K0 (smoothApprox f n) :=
  lipschitzWith_of_nnnorm_deriv_le ((smoothApprox_C3 f hf n).differentiable (by norm_num))
    (fun x => show ‖deriv (smoothApprox f n) x‖ ≤ (K0:ℝ) from
      approximation_first_bound f hf K0 (fun x => h0 x) n x)

def approximateDerivativeLip (n : ℕ) : LipschitzWith K1 (deriv (smoothApprox f n)) :=
  lipschitzWith_of_nnnorm_deriv_le
    ((deriv_contDiff_one (smoothApprox f n) ((smoothApprox_C3 f hf n).of_le (by norm_num))).differentiable (by norm_num))
    (fun x => show ‖deriv (deriv (smoothApprox f n)) x‖ ≤ (K1:ℝ) from
      approximation_second_bound f hf K1 (fun x => h1 x) n x)

def curvatureLipConstant (n : ℕ) : ℝ≥0 := ⟨2*(K1:ℝ)/width n, div_nonneg (mul_nonneg (by norm_num) K1.coe_nonneg) (width_pos n).le⟩

def approximateCurvatureLip (n : ℕ) :
    LipschitzWith (curvatureLipConstant K1 n) (deriv (deriv (smoothApprox f n))) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (smoothApprox_C3 f hf n).differentiable_iteratedDeriv 2 (by norm_num)
  · intro x
    exact (show ‖deriv (deriv (deriv (smoothApprox f n))) x‖ ≤ 2*(K1:ℝ)/width n from
      average_third_bound f hf (width_pos n) K1 (fun x => h1 x) x)

theorem terminal_tendsto (t : ℝ≥0) :
    Tendsto (fun n => valueL2 (approximateFunctionLip f hf K0 h0 n) t) atTop
      (𝓝 (valueL2 (functionLip f hf K0 h0) t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => value_uniform_error (approximateFunctionLip f hf K0 h0 n) (functionLip f hf K0 h0)
      (show 0 ≤ (K0:ℝ)*width n from mul_nonneg K0.coe_nonneg (width_pos n).le)
      (average_error_le f (functionLip f hf K0 h0) (width_pos n)) t)
  simpa only [mul_zero] using (width_tendsto.mono_right nhdsWithin_le_nhds).const_mul (K0:ℝ)

include K0 h0 in
theorem stochastic_tendsto (T : ℝ≥0) :
    Tendsto (fun n => itoIntegral (integrand (approximateDerivativeLip f hf K1 h1 n) T)) atTop
      (𝓝 (itoIntegral (integrand (derivativeLip f hf K1 h1) T))) := by
  apply itoIntegral.continuous.continuousAt.tendsto.comp
  apply integrands_tendsto (fun n => deriv (smoothApprox f n)) (fun _ => K1)
    (approximateDerivativeLip f hf K1 h1) (derivativeLip f hf K1 h1)
    (M := (K0:ℝ)) (fun x => h0 x)
    (fun n x => approximation_first_bound f hf K0 (fun x => h0 x) n x)
  intro x
  exact (average_deriv_tendsto f (hf.of_le (by norm_num)) x).comp width_tendsto

theorem curvature_tendsto (t : ℝ≥0) :
    Tendsto (fun n => valueL2 (approximateCurvatureLip f hf K1 h1 n) t) atTop
      (𝓝 (curvatureValue f hf K1 h1 t)) := by
  apply values_tendsto (fun n => deriv (deriv (smoothApprox f n))) (curvatureLipConstant K1)
    (approximateCurvatureLip f hf K1 h1) (second_continuous f hf)
    (fun x => show ‖deriv (deriv f) x‖ ≤ (K1:ℝ) from h1 x)
    (fun n x => approximation_second_bound f hf K1 (fun x => h1 x) n x)
  intro x
  exact (average_second_tendsto f hf x).comp width_tendsto

theorem curvature_integral_tendsto (T : ℝ≥0) :
    IntervalIntegrable (fun t : ℝ => curvatureValue f hf K1 h1 t.toNNReal) volume 0 T ∧
    Tendsto (fun n => ∫ t in 0..(T:ℝ), valueL2 (approximateCurvatureLip f hf K1 h1 n) t.toNNReal)
      atTop (𝓝 (∫ t in 0..(T:ℝ), curvatureValue f hf K1 h1 t.toNNReal)) := by
  apply drift_tendsto _ (fun n => valueL2_continuous _) _ (curvature_tendsto f hf K1 h1) K1
  · intro n t
    exact value_norm_le _ (fun x => approximation_second_bound f hf K1 (fun x => h1 x) n x) t
  · exact fun t => boundedValue_norm_le _ _ t

/-- C2 Brownian Ito, obtained by simultaneous terminal, predictable-field, and
Bochner-drift convergence from independently specified interval averages. -/
theorem c2_ito (T : ℝ≥0) :
    valueL2 (functionLip f hf K0 h0) T - valueL2 (functionLip f hf K0 h0) 0 =
      itoIntegral (integrand (derivativeLip f hf K1 h1) T) +
        (1/2:ℝ) • (∫ t in 0..(T:ℝ), curvatureValue f hf K1 h1 t.toNNReal) := by
  have he (n : ℕ) := GaussianSmoothIto.ito_of_lipschitz_derivatives (smoothApprox f n)
    (smoothApprox_C3 f hf n) (approximateFunctionLip f hf K0 h0 n)
    (approximateDerivativeLip f hf K1 h1 n) (approximateCurvatureLip f hf K1 h1 n)
    (2*(K1:ℝ)/width n) (fun x => by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero, smoothApprox] using
        average_third_bound f hf (width_pos n) K1 (fun x => h1 x) x) T
  have hl := (terminal_tendsto f hf K0 h0 T).sub (terminal_tendsto f hf K0 h0 0)
  have hr := (stochastic_tendsto f hf K0 K1 h0 h1 T).add
    ((curvature_integral_tendsto f hf K1 h1 T).2.const_smul (1/2:ℝ))
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall fun n => (he n).symm))

include K0 h0 in
/-- Almost-everywhere random-variable form, with the actual derivative and
an independently defined, genuinely integrable Gaussian-L2 drift. -/
theorem c2_ito_ae (T : ℝ≥0) :
    (fun ω => f (process T ω)-f 0) =ᵐ[gaussianProduct] fun ω =>
      itoIntegral (integrand (derivativeLip f hf K1 h1) T) ω + (1/2:ℝ) *
        ((∫ t in 0..(T:ℝ), curvatureValue f hf K1 h1 t.toNNReal) : GaussianL2) ω := by
  have he := c2_ito f hf K0 K1 h0 h1 T
  let V : GaussianL2 := ∫ t in 0..(T:ℝ), curvatureValue f hf K1 h1 t.toNNReal
  let U := integrand (derivativeLip f hf K1 h1) T
  rw [GaussianSmoothIto.valueL2_zero] at he
  have he' : valueL2 (functionLip f hf K0 h0) T = f 0 • gaussianOne + itoIntegral U + (1/2:ℝ) • V := by
    linear_combination (norm := module) he
  filter_upwards [valueL2_coeFn (functionLip f hf K0 h0) T,
    Lp.coeFn_add (f 0 • gaussianOne + itoIntegral U) ((1/2:ℝ) • V),
    Lp.coeFn_add (f 0 • gaussianOne) (itoIntegral U), Lp.coeFn_smul (f 0) gaussianOne,
    Lp.coeFn_smul (1/2:ℝ) V, gaussianOne_coeFn] with ω hv ha hb hc hd ho
  have hx := congrArg (fun X : GaussianL2 => X ω) he'
  rw [hv, ha] at hx
  simp only [Pi.add_apply, hb, hc, hd, Pi.smul_apply, ho, smul_eq_mul, mul_one] at hx
  change f (process T ω)-f 0 = itoIntegral U ω + (1/2:ℝ)*V ω
  linarith

end OperatorDerivativeRewrite.Foundation.GaussianC2Ito



