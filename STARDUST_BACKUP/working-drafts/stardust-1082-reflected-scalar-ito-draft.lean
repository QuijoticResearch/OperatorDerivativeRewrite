import Foundation.GaussianC2Ito
import Foundation.ReflectedC2Primitive
import Foundation.BrownianMassLimitIdentification
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
open OperatorDerivativeRewrite.Foundation
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianPredictableFull
open ReflectedC2Primitive GaussianLipschitzIntegrands
namespace DraftReflectedScalarIto
variable (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (K0 K1 : ℝ≥0)
  (h0 : ∀ x, ‖deriv f x‖ ≤ (K0 : ℝ))
  (h1 : ∀ x, ‖deriv (deriv f) x‖ ≤ (K1 : ℝ))

include hf h0 in
theorem bound0 (x : ℝ) : ‖deriv (corrected f) x‖₊ ≤ 2*K0 := by
  exact_mod_cast corrected_deriv_bound (hf.differentiable (by norm_num)) h0 x

include hf h1 in
theorem bound1 (x : ℝ) : ‖deriv (deriv (corrected f)) x‖₊ ≤ K1 := by
  exact_mod_cast corrected_second_deriv_bound hf h1 x

def running (T : ℝ≥0) : fullPredictable :=
  integrand (GaussianC2Ito.derivativeLip (corrected f) (corrected_C2 hf) K1
    (bound1 f hf K1 h1)) T + deriv f 0 • BrownianSignIntegral.predictableField T

def drift (T : ℝ≥0) : GaussianL2 :=
  ∫ t in 0..(T : ℝ), GaussianC2Ito.curvatureValue (corrected f) (corrected_C2 hf) K1
    (bound1 f hf K1 h1) t.toNNReal

include K0 h0 in
theorem reflected_ito_ae (T : ℝ≥0) :
    (fun ω => f |IBMConstructedSources.clockPath ω T|-f 0) =ᵐ[gaussianProduct]
      fun ω => itoIntegral (running f hf K1 h1 T) ω+
        deriv f 0*BrownianMassContinuousLimit.limitPath ω T+
        (1/2 : ℝ)*(drift f hf K1 h1 T) ω := by
  let J := itoIntegral (integrand
    (GaussianC2Ito.derivativeLip (corrected f) (corrected_C2 hf) K1
      (bound1 f hf K1 h1)) T)
  have he : itoIntegral (running f hf K1 h1 T) =
      J+deriv f 0 • BrownianSignIntegral.terminal T := by
    simp only [running, map_add, map_smul]
    rfl
  have hc := GaussianC2Ito.c2_ito_ae (corrected f) (corrected_C2 hf) (2*K0) K1
    (bound0 f hf K0 h0) (bound1 f hf K1 h1) T
  filter_upwards [hc, BrownianMassLimitIdentification.tanaka_ae T,
    IBMConstructedSources.clockPath_coordinate_ae T,
    Lp.coeFn_add J (deriv f 0 • BrownianSignIntegral.terminal T),
    Lp.coeFn_smul (deriv f 0) (BrownianSignIntegral.terminal T)] with ω hc ht hw ha hs
  change corrected f (process T ω)-corrected f 0 = J ω+(1/2 : ℝ)*(drift f hf K1 h1 T) ω at hc
  rw [← hw] at hc
  simp only [corrected, abs_zero, zero_mul, sub_zero] at hc
  rw [he, ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination hc + deriv f 0 * ht
end DraftReflectedScalarIto
