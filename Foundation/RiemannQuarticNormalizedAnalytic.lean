import Foundation.RiemannQuarticCosineNormalization
import Foundation.RiemannQuarticReality
import Mathlib.Analysis.RCLike.Sqrt
/-! Entire and conjugation-compatible normalization of the actual quartic flow. -/
noncomputable section
open Set Metric Complex Filter MeasureTheory
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticNormalizedAnalytic
open RiemannQuarticCosineNormalization RiemannQuarticGaussianPrefactor
open RiemannQuarticSaddleTimes RiemannQuarticSaddleBranch RiemannQuarticFrequencyBranch
open RiemannQuarticSaddleGeometry RiemannQuarticDomain RiemannThetaComplexKernel

def normalizedFlow (t u : ℝ) (z : ℂ) : ℂ := RiemannQuarticFlow.flow t z/gaussianEnvelope t u z

theorem envelope_differentiable (t u : ℝ) : Differentiable ℂ (gaussianEnvelope t u) := by
  apply Differentiable.const_mul
  exact ((differentiable_id.pow 2).div_const _).cexp

theorem normalized_differentiable (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u)
    (hs : phaseSlope t u=0) : Differentiable ℂ (normalizedFlow t u) := by
  exact (RiemannQuarticFlow.flow_differentiable t).div (envelope_differentiable t u)
    (envelope_ne_zero t u ht hu hs)

theorem flow_conj (t : ℝ) (z : ℂ) : RiemannQuarticFlow.flow t (conj z)=conj (RiemannQuarticFlow.flow t z) := by
  rw [RiemannQuarticEvolution.flow_eq_cosine_integral,RiemannQuarticEvolution.flow_eq_cosine_integral,← integral_conj]
  apply integral_congr_ae
  filter_upwards with u
  simp only [map_mul,Complex.conj_ofReal,← Complex.cos_conj]

theorem gaussianFactor_real (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0) :
    gaussianFactor t (u : ℂ)=(Real.sqrt (Real.pi/(-(deriv (phaseSlope t) u)/2)) : ℂ) := by
  have hb : 0 < -(deriv (phaseSlope t) u)/2 := by
    have hn := RiemannQuarticCurvature.stationary_phaseSlope_deriv_neg t u ht hu hs
    linarith
  have hc : (Real.pi : ℂ)/(-(deriv (complexSlope t) (u : ℂ))/2)=
      ((Real.pi/(-(deriv (phaseSlope t) u)/2) : ℝ) : ℂ) := by
    rw [slope_deriv_real t u (by linarith)]
    push_cast
    rfl
  unfold gaussianFactor
  rw [hc,one_div]
  change Complex.sqrt _ = _
  apply Complex.sqrt_of_nonneg
  exact_mod_cast (div_pos Real.pi_pos hb).le

theorem envelope_conj (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0) (z : ℂ) :
    gaussianEnvelope t u (conj z)=conj (gaussianEnvelope t u z) := by
  have hW : saddleWeight t 0 (u : ℂ)=(weighted 0 t 0 u : ℂ) := by
    simp only [saddleWeight,weighted,pow_zero,one_mul,mul_zero,zero_mul,add_zero,kernelComplex_real]
    push_cast
    rfl
  simp only [gaussianEnvelope,hW,gaussianFactor_real t u ht hu hs,
    slope_deriv_real t u (by linarith),map_mul,Complex.conj_ofReal,← Complex.exp_conj,
    map_div₀,map_pow,map_ofNat]

theorem normalized_conj (t u : ℝ) (ht : 0 ≤ t) (hu : 1 ≤ u) (hs : phaseSlope t u=0) (z : ℂ) :
    normalizedFlow t u (conj z)=conj (normalizedFlow t u z) := by
  simp only [normalizedFlow,flow_conj,envelope_conj t u ht hu hs,map_div₀]

end OperatorDerivativeRewrite.Foundation.RiemannQuarticNormalizedAnalytic
