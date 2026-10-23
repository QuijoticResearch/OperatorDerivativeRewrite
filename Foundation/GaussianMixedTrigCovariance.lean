import Foundation.IBMFirstChaosMixedStein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Bilinear nonlinear Gaussian covariances by polarization of the OLD
verified diagonal Stein theorem. All random variables are the original
isonormal embeddings; degenerate source directions remain included. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianMixedTrigCovariance
open InfiniteGaussian IBMFirstChaosMixedStein
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable

theorem polarization_ae (w a b : CoefficientSpace) (φ : ℝ → ℝ) :
    (fun ω => firstChaosEmbedding a ω*firstChaosEmbedding b ω*φ (firstChaosEmbedding w ω))
      =ᵐ[gaussianProduct] (fun ω => ((firstChaosEmbedding (a+b) ω)^2*φ (firstChaosEmbedding w ω)-
        (firstChaosEmbedding (a-b) ω)^2*φ (firstChaosEmbedding w ω))/4) := by
  filter_upwards [Lp.coeFn_add (firstChaosEmbedding a) (firstChaosEmbedding b),
    Lp.coeFn_sub (firstChaosEmbedding a) (firstChaosEmbedding b)] with ω hp hm
  rw [map_add,map_sub,hp,hm]
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem bilinear_integrable (w a b : CoefficientSpace) {φ : ℝ → ℝ} (hc : Continuous φ)
    {A : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) :
    Integrable (fun ω => firstChaosEmbedding a ω*firstChaosEmbedding b ω*
      φ (firstChaosEmbedding w ω)) gaussianProduct :=
  (((second_mixed_integrable w (a+b) hc hA).sub
    (second_mixed_integrable w (a-b) hc hA)).div_const 4).congr
      (polarization_ae w a b φ).symm

/-- The genuine bilinear Stein identity, obtained directly from the existing
actual-source diagonal theorem. No new Gaussian calculus is assumed. -/
theorem bilinear_mixed (w a b : CoefficientSpace) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {A B C : ℝ} (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖deriv φ x‖ ≤ B)
    (hC : ∀ x, ‖deriv (deriv φ) x‖ ≤ C) :
    (∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*φ (firstChaosEmbedding w ω)
      ∂gaussianProduct) =
        inner ℝ a b*(∫ ω, φ (firstChaosEmbedding w ω) ∂gaussianProduct)+
          inner ℝ w a*inner ℝ w b*(∫ ω, deriv (deriv φ) (firstChaosEmbedding w ω)
            ∂gaussianProduct) := by
  rw [integral_congr_ae (polarization_ae w a b φ),integral_div,
    integral_sub (second_mixed_integrable w (a+b) hφ.continuous hA)
      (second_mixed_integrable w (a-b) hφ.continuous hA),
    second_mixed hφ hA hB hC,second_mixed hφ hA hB hC,
    norm_add_sq_real,norm_sub_sq_real,inner_add_right,inner_sub_right]
  ring

def mean (w : CoefficientSpace) : ℝ := ∫ ω, Real.cos (firstChaosEmbedding w ω) ∂gaussianProduct

theorem cosine_deriv_bound (x : ℝ) : ‖deriv Real.cos x‖ ≤ (1 : ℝ) := by
  rw [Real.deriv_cos]
  simpa only [Pi.neg_apply,norm_neg,Real.norm_eq_abs] using Real.abs_sin_le_one x

theorem cosine_second_deriv : deriv (deriv Real.cos) = -Real.cos := by
  have h : deriv Real.cos = fun x => -Real.sin x :=
    funext fun x => (Real.hasDerivAt_cos x).deriv
  rw [h]
  funext x
  exact (Real.hasDerivAt_sin x).neg.deriv

theorem cosine_second_bound (x : ℝ) : ‖deriv (deriv Real.cos) x‖ ≤ (1 : ℝ) := by
  rw [cosine_second_deriv]
  simpa only [Pi.neg_apply,norm_neg,Real.norm_eq_abs] using Real.abs_cos_le_one x

theorem cosine_mixed_integrable (w a b : CoefficientSpace) :
    Integrable (fun ω => firstChaosEmbedding a ω*firstChaosEmbedding b ω*
      Real.cos (firstChaosEmbedding w ω)) gaussianProduct :=
  bilinear_integrable w a b Real.continuous_cos Real.abs_cos_le_one

/-- The covariance correction survives for nonlinear coefficients. -/
theorem cosine_mixed_integral (w a b : CoefficientSpace) :
    (∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
      Real.cos (firstChaosEmbedding w ω) ∂gaussianProduct) =
        (inner ℝ a b-inner ℝ w a*inner ℝ w b)*mean w := by
  have h := bilinear_mixed w a b (φ := Real.cos) (by fun_prop)
    Real.abs_cos_le_one cosine_deriv_bound cosine_second_bound
  rw [cosine_second_deriv] at h
  simp only [Pi.neg_apply,integral_neg] at h
  change _ = (inner ℝ a b-inner ℝ w a*inner ℝ w b)*
    (∫ ω, Real.cos (firstChaosEmbedding w ω) ∂gaussianProduct)
  rw [h]
  ring

theorem mean_bound (w : CoefficientSpace) : |mean w| ≤ 1 := by
  have hi := ((IBMFirstChaosDiagonalStein.bounded_comp_memLp w Real.continuous_cos
    Real.abs_cos_le_one).integrable (by norm_num))
  change ‖∫ ω, Real.cos (firstChaosEmbedding w ω) ∂gaussianProduct‖ ≤ 1
  calc
    _ ≤ ∫ ω, ‖Real.cos (firstChaosEmbedding w ω)‖ ∂gaussianProduct :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _ω : SampleSpace, (1 : ℝ) ∂gaussianProduct :=
      integral_mono hi.norm (integrable_const 1) (fun ω => Real.abs_cos_le_one _)
    _ = 1 := by simp

theorem cosine_mixed_bound (w a b : CoefficientSpace) :
    |∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
      Real.cos (firstChaosEmbedding w ω) ∂gaussianProduct| ≤
        |inner ℝ a b| + |inner ℝ w a| * |inner ℝ w b| := by
  rw [cosine_mixed_integral,abs_mul]
  calc
    _ ≤ |inner ℝ a b-inner ℝ w a*inner ℝ w b| * 1 := by
      exact mul_le_mul_of_nonneg_left (mean_bound w) (abs_nonneg _)
    _ ≤ _ := by
      rw [mul_one]
      simpa only [abs_mul] using abs_sub (inner ℝ a b) (inner ℝ w a*inner ℝ w b)

/-- A quantitative positive lower bound suffices to refute naive
factorization; no characteristic-function differentiation is required. -/
theorem mean_lower (w : CoefficientSpace) : 1-‖w‖^2/2 ≤ mean w := by
  have hsq : (∫ ω, (firstChaosEmbedding w ω)^2 ∂gaussianProduct) = ‖w‖^2 := by
    have h := firstChaosEmbedding.inner_map_map w w
    rw [L2.inner_def] at h
    simpa only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs] using h
  have hi := (Lp.memLp (firstChaosEmbedding w)).integrable_sq
  have hc := ((IBMFirstChaosDiagonalStein.bounded_comp_memLp w Real.continuous_cos
    Real.abs_cos_le_one).integrable (by norm_num))
  have h := integral_mono ((integrable_const (1 : ℝ)).sub (hi.div_const 2)) hc
    (fun ω => Real.one_sub_sq_div_two_le_cos (x := firstChaosEmbedding w ω))
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_const 1) (hi.div_const 2),integral_div,hsq] at h
  simpa [mean] using h

/-- Even one bounded nonlinear Gaussian coefficient invalidates replacing
the mixed expectation by derivative covariance times coefficient mean. -/
theorem naive_factorization_fails (w : CoefficientSpace) (hw : ‖w‖ = 1) :
    (∫ ω, firstChaosEmbedding w ω*firstChaosEmbedding w ω*
      Real.cos (firstChaosEmbedding w ω) ∂gaussianProduct) ≠ inner ℝ w w*mean w := by
  have hp : 0 < mean w := by
    have h := mean_lower w
    rw [hw] at h
    linarith
  rw [cosine_mixed_integral,real_inner_self_eq_norm_sq,hw]
  norm_num
  exact ne_of_lt hp

end OperatorDerivativeRewrite.Foundation.GaussianMixedTrigCovariance
