import Foundation.IBMFoldedSmoothQuadraticError

/-! Bounded derivative-square weights preserve the actual vanishing folded
quadratic-variation loss in original clock L1. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFoldedWeightedLoss
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMPhysicalWickTestDomain IBMFoldedClockQuadraticVariation

def weight (g : SchwartzMap ℝ ℝ) (x : ℝ) : ℝ := (deriv g |x|)^2

theorem weight_lipschitz (g : SchwartzMap ℝ ℝ) :
    LipschitzWith (2*firstBound g*secondBound g) (weight g) := by
  have ha : LipschitzWith 1 (abs : ℝ → ℝ) := LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub x y
  change LipschitzWith (2*firstBound g*secondBound g) (fun x : ℝ => (deriv g |x|)^2)
  simpa only [mul_one,Function.comp_def] using
  (GaussianSmoothQuadraticVariation.square_derivative_lipschitz g (g.smooth 2)
    (firstBound g) (secondBound g) (first_derivative_bound g) (second_derivative_bound g)).comp
      ha

theorem weight_bound (g : SchwartzMap ℝ ℝ) (x : ℝ) :
    0 ≤ weight g x ∧ weight g x ≤ (firstBound g:ℝ)^2 := by
  constructor
  · exact sq_nonneg _
  · have hb : ‖deriv g |x|‖ ≤ (firstBound g:ℝ) := first_derivative_bound g |x|
    rw [Real.norm_eq_abs] at hb
    simpa only [← sq,sq_abs,weight] using mul_self_le_mul_self (abs_nonneg _) hb

def value (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (N+1), weight g (process (uniformTime T N i.castSucc) Y)*
    loss (process (uniformTime T N i.castSucc) Y) (process (uniformTime T N i.succ) Y)

theorem value_nonneg (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    0 ≤ value g T N Y := Finset.sum_nonneg fun i _ => mul_nonneg (weight_bound g _).1 (loss_nonneg _ _)

theorem value_bound (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    value g T N Y ≤ (firstBound g:ℝ)^2*lossValue T N Y := by
  rw [lossValue_eq_sum,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (weight_bound g _).2 (loss_nonneg _ _)

theorem value_integrable (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) :
    Integrable (value g T N) gaussianProduct := by
  have hm : Measurable (value g T N) := by
    apply Finset.measurable_fun_sum
    intro i hi
    have hs := (process_stronglyMeasurable (uniformTime T N i.castSucc)).measurable
    have ht := (process_stronglyMeasurable (uniformTime T N i.succ)).measurable
    exact ((weight_lipschitz g).continuous.measurable.comp hs).mul
      (((ht.sub hs).pow_const 2).sub ((ht.norm.sub hs.norm).pow_const 2))
  apply ((lossValue_integrable T N).const_mul ((firstBound g:ℝ)^2)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun Y => by
    rw [Real.norm_of_nonneg (value_nonneg g T N Y)]
    exact value_bound g T N Y

def lossClass (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  (value_integrable g T N).toL1 _

theorem lossClass_actual (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) :
    lossClass g T N =ᵐ[gaussianProduct] value g T N := (value_integrable g T N).coeFn_toL1

theorem lossClass_norm_bound (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (N : ℕ) :
    ‖lossClass g T N‖ ≤ (firstBound g:ℝ)^2*‖IBMFoldedClockQuadraticVariation.lossClass T N‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [lossClass_actual g T N,IBMFoldedClockQuadraticVariation.lossClass_actual T N] with Y hw hl
  rw [hw,hl,Real.norm_of_nonneg (value_nonneg g T N Y),Real.norm_of_nonneg (lossValue_nonneg T N Y)]
  exact value_bound g T N Y

theorem lossClass_tendsto (g : SchwartzMap ℝ ℝ) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (lossClass g T) atTop (𝓝 0) := by
  have ht := ((IBMFoldedClockQuadraticVariation.lossClass_tendsto T hT).norm).const_mul ((firstBound g:ℝ)^2)
  simp only [norm_zero,mul_zero] at ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using squeeze_zero (fun N => norm_nonneg _) (lossClass_norm_bound g T) ht

end OperatorDerivativeRewrite.Foundation.IBMFoldedWeightedLoss
