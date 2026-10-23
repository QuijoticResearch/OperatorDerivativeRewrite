import Foundation.GaussianMixedTrigCovariance

/-! The two nonlinear coefficient factors required by the averaged IBM clock
gradient. A dimension-free bound retains the derivative overlap plus a bounded
value/derivative covariance correction, rather than multiplying expectations. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianCosineProductCovariance
open InfiniteGaussian GaussianMixedTrigCovariance
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable

theorem product_split_ae (w v a b : CoefficientSpace) :
    (fun ω => firstChaosEmbedding a ω*firstChaosEmbedding b ω*
      Real.cos (firstChaosEmbedding w ω)*Real.cos (firstChaosEmbedding v ω))
      =ᵐ[gaussianProduct] (fun ω =>
        (firstChaosEmbedding a ω*firstChaosEmbedding b ω*Real.cos (firstChaosEmbedding (w+v) ω)+
          firstChaosEmbedding a ω*firstChaosEmbedding b ω*
            Real.cos (firstChaosEmbedding (w-v) ω))/2) := by
  filter_upwards [Lp.coeFn_add (firstChaosEmbedding w) (firstChaosEmbedding v),
    Lp.coeFn_sub (firstChaosEmbedding w) (firstChaosEmbedding v)] with ω hp hm
  rw [map_add,map_sub,hp,hm]
  simp only [Pi.add_apply,Pi.sub_apply,Real.cos_add,Real.cos_sub]
  ring

theorem product_integrable (w v a b : CoefficientSpace) :
    Integrable (fun ω => firstChaosEmbedding a ω*firstChaosEmbedding b ω*
      Real.cos (firstChaosEmbedding w ω)*Real.cos (firstChaosEmbedding v ω)) gaussianProduct :=
  (((cosine_mixed_integrable (w+v) a b).add
    (cosine_mixed_integrable (w-v) a b)).div_const 2).congr
      (product_split_ae w v a b).symm

theorem product_integral_split (w v a b : CoefficientSpace) :
    (∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
      Real.cos (firstChaosEmbedding w ω)*Real.cos (firstChaosEmbedding v ω) ∂gaussianProduct) =
        ((∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
          Real.cos (firstChaosEmbedding (w+v) ω) ∂gaussianProduct)+
            ∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
              Real.cos (firstChaosEmbedding (w-v) ω) ∂gaussianProduct)/2 := by
  rw [integral_congr_ae (product_split_ae w v a b),integral_div,
    integral_add (cosine_mixed_integrable (w+v) a b) (cosine_mixed_integrable (w-v) a b)]

/-- Exact mixed covariance for arbitrary original Gaussian directions. -/
theorem product_formula (w v a b : CoefficientSpace) :
    (∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
      Real.cos (firstChaosEmbedding w ω)*Real.cos (firstChaosEmbedding v ω) ∂gaussianProduct) =
        ((inner ℝ a b-inner ℝ (w+v) a*inner ℝ (w+v) b)*mean (w+v)+
          (inner ℝ a b-inner ℝ (w-v) a*inner ℝ (w-v) b)*mean (w-v))/2 := by
  rw [product_integral_split,cosine_mixed_integral,cosine_mixed_integral]

/-- This estimate does not involve the divergent individual derivative
variances. Its four mixed-covariance premises must be proved for actual kernels. -/
theorem product_bound (w v a b : CoefficientSpace) {C : ℝ} (hC : 0 ≤ C)
    (hwa : |inner ℝ w a| ≤ C) (hva : |inner ℝ v a| ≤ C)
    (hwb : |inner ℝ w b| ≤ C) (hvb : |inner ℝ v b| ≤ C) :
    |∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
      Real.cos (firstChaosEmbedding w ω)*Real.cos (firstChaosEmbedding v ω) ∂gaussianProduct| ≤
        |inner ℝ a b| + 4*C^2 := by
  have hb (u : CoefficientSpace) (ha : |inner ℝ u a| ≤ 2*C)
      (hb : |inner ℝ u b| ≤ 2*C) :
      |∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
        Real.cos (firstChaosEmbedding u ω) ∂gaussianProduct| ≤ |inner ℝ a b| + 4*C^2 := by
    have hp : |inner ℝ u a| * |inner ℝ u b| ≤ (2*C)*(2*C) :=
      mul_le_mul ha hb (abs_nonneg _) (by positivity)
    exact (cosine_mixed_bound u a b).trans (by nlinarith)
  have hpa : |inner ℝ (w+v) a| ≤ 2*C := by
    rw [inner_add_left]
    exact (abs_add_le _ _).trans (by linarith)
  have hpb : |inner ℝ (w+v) b| ≤ 2*C := by
    rw [inner_add_left]
    exact (abs_add_le _ _).trans (by linarith)
  have hma : |inner ℝ (w-v) a| ≤ 2*C := by
    rw [inner_sub_left]
    exact (abs_sub _ _).trans (by linarith)
  have hmb : |inner ℝ (w-v) b| ≤ 2*C := by
    rw [inner_sub_left]
    exact (abs_sub _ _).trans (by linarith)
  have hp := hb (w+v) hpa hpb
  have hm := hb (w-v) hma hmb
  rw [product_integral_split,abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (|∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
        Real.cos (firstChaosEmbedding (w+v) ω) ∂gaussianProduct| + 
      |∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
        Real.cos (firstChaosEmbedding (w-v) ω) ∂gaussianProduct|)/2 := by
          exact div_le_div_of_nonneg_right
            (abs_add_le (∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
              Real.cos (firstChaosEmbedding (w+v) ω) ∂gaussianProduct)
                (∫ ω, firstChaosEmbedding a ω*firstChaosEmbedding b ω*
                  Real.cos (firstChaosEmbedding (w-v) ω) ∂gaussianProduct)) (by norm_num)
    _ ≤ _ := by linarith

end OperatorDerivativeRewrite.Foundation.GaussianCosineProductCovariance
