import Foundation.GaussianTimeWeightedSmoothIto
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Actual smooth backward-heat martingales, derived from the verified
Brownian Ito identity. The hypothesis is the explicit differential PDE. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSmoothHeatMartingale
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianLipschitzIntegrands GaussianPredictableFull GaussianPredictableCutoff
open GaussianSmoothConditional GaussianConditionalIto GaussianConditionalClarkOcone
open GaussianSmoothIto GaussianTimeWeightedSmoothIto

variable (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) {K0 K1 K2 : ℝ≥0}
  (h0 : LipschitzWith K0 f) (h1 : LipschitzWith K1 (deriv f))
  (h2 : LipschitzWith K2 (deriv (deriv f)))
  (M : ℝ) (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M)
  (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a)
  (hheat : ∀ t : ℝ, 0 ≤ t → ∀ x : ℝ,
    deriv a t * f x + (1 / 2 : ℝ) * a t * deriv (deriv f) x = 0)

theorem weighted_value_coeFn (T : ℝ≥0) :
    a T • valueL2 h0 T =ᵐ[gaussianProduct] fun ω => a T * f (process T ω) := by
  filter_upwards [Lp.coeFn_smul (a T) (valueL2 h0 T), valueL2_coeFn h0 T] with ω hs hv
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul, hv]

include hheat in
theorem heat_drift_zero (t : ℝ) (ht : 0 ≤ t) :
    deriv a t • valueL2 h0 t.toNNReal +
      (1 / 2 : ℝ) • (a t • valueL2 h2 t.toNNReal) = 0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (deriv a t • valueL2 h0 t.toNNReal)
    ((1 / 2 : ℝ) • (a t • valueL2 h2 t.toNNReal)),
    Lp.coeFn_smul (deriv a t) (valueL2 h0 t.toNNReal),
    Lp.coeFn_smul (1 / 2 : ℝ) (a t • valueL2 h2 t.toNNReal),
    Lp.coeFn_smul (a t) (valueL2 h2 t.toNNReal),
    valueL2_coeFn h0 t.toNNReal, valueL2_coeFn h2 t.toNNReal,
    Lp.coeFn_zero ℝ 2 gaussianProduct] with ω hadd hs1 hs2 hs3 hv1 hv2 hz
  rw [hadd, hz]
  simp only [Pi.add_apply, hs1, hs2, hs3, Pi.smul_apply, smul_eq_mul, hv1, hv2]
  convert hheat t ht (process t.toNNReal ω) using 1 <;> ring

include hf h0 h1 h2 M hM ha hheat in
theorem heat_representation (T : ℝ≥0) :
    a T • valueL2 h0 T - a 0 • valueL2 h0 0 =
      itoIntegral (weightedField a ha.continuous h1 T) := by
  have hi : (∫ t in 0..(T : ℝ), deriv a t • valueL2 h0 t.toNNReal +
      (1 / 2 : ℝ) • (a t • valueL2 h2 t.toNNReal)) = 0 := by
    calc
      _ = ∫ t in 0..(T : ℝ), (0 : GaussianL2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact heat_drift_zero f h0 h2 a hheat t ((uIcc_of_le T.coe_nonneg ▸ ht).1)
      _ = 0 := by simp
  have h := time_weighted_ito_combined f hf h0 h1 h2 M hM a ha T
  simpa only [hi, add_zero] using h

theorem cut_weightedField (S T : ℝ≥0) :
    predictableCut S (weightedField a ha.continuous h1 T) =
      weightedField a ha.continuous h1 (min S T) :=
  cut_predictableField _ _ _ S T

include hf h0 h1 h2 M hM ha hheat in
theorem heat_projection (S T : ℝ≥0) :
    pastProjection S (a T • valueL2 h0 T) = a ((min S T : ℝ≥0) : ℝ) • valueL2 h0 (min S T) := by
  have he (R : ℝ≥0) : a R • valueL2 h0 R =
      a 0 • valueL2 h0 0 + itoIntegral (weightedField a ha.continuous h1 R) := by
    have h := heat_representation f hf h0 h1 h2 M hM a ha hheat R
    linear_combination (norm := module) h
  rw [he T, he (min S T), map_add, pastProjection_integral, cut_weightedField,
    GaussianSmoothIto.valueL2_zero, map_smul, map_smul, pastProjection_one]
  exact ha

include hf h0 h1 h2 M hM ha hheat in
theorem heat_condExp (S T : ℝ≥0) (hST : S ≤ T) :
    gaussianProduct[(fun ω => a T * f (process T ω)) | naturalFiltration S] =ᵐ[gaussianProduct]
      fun ω => a S * f (process S ω) := by
  have hc := pastProjection_ae S (a T • valueL2 h0 T)
  rw [heat_projection f hf h0 h1 h2 M hM a ha hheat, min_eq_left hST] at hc
  exact ((condExp_congr_ae (weighted_value_coeFn f h0 a T)).symm.trans hc.symm).trans
    (weighted_value_coeFn f h0 a S)

include hf h0 h1 h2 M hM ha hheat in
/-- Mathlib's actual martingale predicate on the independently specified
function a(t) f(B_t), not a compensated process supplied as a hypothesis. -/
theorem heat_martingale :
    Martingale (fun (t : ℝ≥0) ω => a t * f (process t ω)) naturalFiltration gaussianProduct := by
  constructor
  · intro t
    exact (h0.continuous.comp_stronglyMeasurable (process_stronglyAdapted t)).const_mul (a t)
  · exact fun S T hST => heat_condExp f hf h0 h1 h2 M hM a ha hheat S T hST

include hf h0 h1 h2 M hM ha hheat in
theorem heat_mean (T : ℝ≥0) :
    a T * (∫ ω, f (process T ω) ∂gaussianProduct) = a 0 * f 0 := by
  have he := congrArg (fun X : GaussianL2 => inner ℝ gaussianOne X)
    (heat_representation f hf h0 h1 h2 M hM a ha hheat T)
  rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    GaussianSmoothIto.valueL2_zero, real_inner_smul_right,
    GaussianDeterministicGraphCore.gaussianOne_inner_self,
    mul_one, gaussianOne_inner_eq_integral, gaussianOne_inner_eq_integral,
    itoIntegral_centered] at he
  have hc : (∫ ω, valueL2 h0 T ω ∂gaussianProduct) =
      ∫ ω, f (process T ω) ∂gaussianProduct := integral_congr_ae (valueL2_coeFn h0 T)
  rw [hc] at he
  linarith

/-- The positive exponential coefficient for backward heat sine and cosine. -/
def expHalf (t : ℝ) : ℝ := Real.exp (t / 2)

theorem expHalf_contDiff : ContDiff ℝ 1 expHalf :=
  Real.contDiff_exp.comp (contDiff_id.div_const 2)

theorem expHalf_deriv (t : ℝ) : deriv expHalf t = expHalf t / 2 := by
  exact (((hasDerivAt_id t).div_const 2).exp).deriv.trans (by simp [expHalf]; ring)

theorem sin_deriv_lipschitz : LipschitzWith 1 (deriv Real.sin) := by
  simpa only [Real.deriv_sin] using Real.lipschitzWith_cos

theorem sin_second_lipschitz : LipschitzWith 1 (deriv (deriv Real.sin)) := by
  intro x y
  simpa only [Real.deriv_sin, Real.deriv_cos, edist_neg_neg] using Real.lipschitzWith_sin x y

theorem cos_deriv_lipschitz : LipschitzWith 1 (deriv Real.cos) := by
  intro x y
  simpa only [Real.deriv_cos, edist_neg_neg] using Real.lipschitzWith_sin x y

theorem cos_second_deriv : deriv (deriv Real.cos) = fun x => -Real.cos x := by
  rw [Real.deriv_cos']
  exact funext fun x => (Real.hasDerivAt_sin x).neg.deriv

theorem cos_second_lipschitz : LipschitzWith 1 (deriv (deriv Real.cos)) := by
  intro x y
  simpa only [cos_second_deriv, edist_neg_neg] using Real.lipschitzWith_cos x y

theorem sin_third_bound (x : ℝ) : ‖iteratedDeriv 3 Real.sin x‖ ≤ 1 := by
  simpa [iteratedDeriv_succ, Real.deriv_sin, Real.deriv_cos', deriv.neg', Real.norm_eq_abs]
    using Real.abs_cos_le_one x

theorem cos_third_bound (x : ℝ) : ‖iteratedDeriv 3 Real.cos x‖ ≤ 1 := by
  simpa [iteratedDeriv_succ, Real.deriv_sin, Real.deriv_cos', deriv.neg', Real.norm_eq_abs]
    using Real.abs_sin_le_one x

theorem sin_heat_equation (t : ℝ) (_ht : 0 ≤ t) (x : ℝ) :
    deriv expHalf t * Real.sin x + (1/2:ℝ)*expHalf t*deriv (deriv Real.sin) x = 0 := by
  rw [expHalf_deriv, Real.deriv_sin, Real.deriv_cos]
  ring

theorem cos_heat_equation (t : ℝ) (_ht : 0 ≤ t) (x : ℝ) :
    deriv expHalf t * Real.cos x + (1/2:ℝ)*expHalf t*deriv (deriv Real.cos) x = 0 := by
  simp only [expHalf_deriv, cos_second_deriv]
  ring

theorem sin_heat_martingale :
    Martingale (fun (t : ℝ≥0) ω => Real.exp ((t:ℝ)/2) * Real.sin (process t ω))
      naturalFiltration gaussianProduct :=
  heat_martingale Real.sin Real.contDiff_sin Real.lipschitzWith_sin
    sin_deriv_lipschitz sin_second_lipschitz 1 sin_third_bound expHalf
    expHalf_contDiff sin_heat_equation

theorem cos_heat_martingale :
    Martingale (fun (t : ℝ≥0) ω => Real.exp ((t:ℝ)/2) * Real.cos (process t ω))
      naturalFiltration gaussianProduct :=
  heat_martingale Real.cos Real.contDiff_cos Real.lipschitzWith_cos
    cos_deriv_lipschitz cos_second_lipschitz 1 cos_third_bound expHalf
    expHalf_contDiff cos_heat_equation

theorem cos_mean (T : ℝ≥0) :
    ∫ ω, Real.cos (process T ω) ∂gaussianProduct = Real.exp (-((T:ℝ)/2)) := by
  have h := heat_mean Real.cos Real.contDiff_cos Real.lipschitzWith_cos
    cos_deriv_lipschitz cos_second_lipschitz 1 cos_third_bound expHalf
    expHalf_contDiff cos_heat_equation T
  simp only [expHalf, zero_div, Real.exp_zero, Real.cos_zero, mul_one] at h
  apply (mul_left_cancel₀ (Real.exp_ne_zero ((T:ℝ)/2)))
  rw [h, ← Real.exp_add]
  simp

end OperatorDerivativeRewrite.Foundation.GaussianSmoothHeatMartingale





