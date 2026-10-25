import Foundation.IBMSpatialKernelTesting

/-! Actual folded-clock quadratic variation with any fixed bounded Lipschitz
weight, including signed weights. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockWeightedFoldedVariation
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMFoldedClockQuadraticVariation IBMClippedClockStrongLimit

def lossValue (ψ : ℝ → ℝ) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (N+1), ψ (process (uniformTime T N i.castSucc) Y)*
    loss (process (uniformTime T N i.castSucc) Y) (process (uniformTime T N i.succ) Y)

theorem loss_bound (ψ : ℝ → ℝ) (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C)
    (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    ‖lossValue ψ T N Y‖ ≤ C*IBMFoldedClockQuadraticVariation.lossValue T N Y := by
  unfold lossValue
  calc
    _ ≤ ∑ i : Fin (N+1), ‖ψ (process (uniformTime T N i.castSucc) Y)*
      loss (process (uniformTime T N i.castSucc) Y) (process (uniformTime T N i.succ) Y)‖ := norm_sum_le _ _
    _ ≤ _ := by
      rw [IBMFoldedClockQuadraticVariation.lossValue_eq_sum,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,Real.norm_of_nonneg (loss_nonneg _ _)]
      exact mul_le_mul_of_nonneg_right (hC _) (loss_nonneg _ _)

theorem loss_integrable (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ)
    (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) (T : ℝ≥0) (N : ℕ) :
    Integrable (lossValue ψ T N) gaussianProduct := by
  have hm : Measurable (lossValue ψ T N) := by
    apply Finset.measurable_fun_sum
    intro i hi
    have hs := (process_stronglyMeasurable (uniformTime T N i.castSucc)).measurable
    have ht := (process_stronglyMeasurable (uniformTime T N i.succ)).measurable
    exact (hψ.continuous.measurable.comp hs).mul
      (((ht.sub hs).pow_const 2).sub ((ht.norm.sub hs.norm).pow_const 2))
  apply ((IBMFoldedClockQuadraticVariation.lossValue_integrable T N).const_mul C).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun Y => loss_bound ψ C hC T N Y

def lossClass (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ)
    (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) (T : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  (loss_integrable ψ hψ C hC T N).toL1 _

theorem loss_actual (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ)
    (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) (T : ℝ≥0) (N : ℕ) :
    lossClass ψ hψ C hC T N =ᵐ[gaussianProduct] lossValue ψ T N := (loss_integrable ψ hψ C hC T N).coeFn_toL1

theorem loss_norm_bound (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ)
    (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) (T : ℝ≥0) (N : ℕ) :
    ‖lossClass ψ hψ C hC T N‖ ≤ C*‖IBMFoldedClockQuadraticVariation.lossClass T N‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [loss_actual ψ hψ C hC T N,IBMFoldedClockQuadraticVariation.lossClass_actual T N] with Y hw hl
  rw [hw,hl,Real.norm_of_nonneg (lossValue_nonneg T N Y)]
  exact loss_bound ψ C hC T N Y

theorem loss_tendsto (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ)
    (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (lossClass ψ hψ C hC T) atTop (𝓝 0) := by
  have ht := ((IBMFoldedClockQuadraticVariation.lossClass_tendsto T hT).norm).const_mul C
  simp only [norm_zero,mul_zero] at ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using squeeze_zero (fun N => norm_nonneg _) (loss_norm_bound ψ hψ C hC T) ht

def weighted (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ) (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  GaussianLipschitzQuadraticVariation.error hψ T N+GaussianSmoothIto.driftSum hψ T N

def drift (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ) (T : ℝ≥0) : GaussianL2 :=
  ∫ t in 0..(T:ℝ), GaussianLipschitzIntegrands.valueL2 hψ t.toNNReal

theorem weighted_actual (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ) (T : ℝ≥0) (N : ℕ) :
    weighted ψ hψ T N =ᵐ[gaussianProduct] fun Y => ∑ i : Fin (N+1),
      ψ (process (uniformTime T N i.castSucc) Y)*
        (process (uniformTime T N i.succ) Y-process (uniformTime T N i.castSucc) Y)^2 := by
  filter_upwards [Lp.coeFn_add (GaussianLipschitzQuadraticVariation.error hψ T N)
    (GaussianSmoothIto.driftSum hψ T N),GaussianLipschitzQuadraticVariation.error_coeFn hψ T N,
    GaussianSmoothIto.driftSum_coeFn hψ T N] with Y ha he hd
  change weighted ψ hψ T N Y = _ at ha
  rw [ha,Pi.add_apply,he,hd,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem weighted_tendsto (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ) (T : ℝ≥0) :
    Tendsto (weighted ψ hψ T) atTop (𝓝 (drift ψ hψ T)) := by
  have h := (GaussianLipschitzQuadraticVariation.error_tendsto hψ T).add
    (GaussianLipschitzIntegrands.drift_sum_tendsto hψ T)
  unfold weighted drift
  simpa only [zero_add,GaussianSmoothIto.driftSum] using h

def folded (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ)
    (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) (T : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  clockL1 (weighted ψ hψ T N)-lossClass ψ hψ C hC T N

theorem folded_actual (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ)
    (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) (T : ℝ≥0) (N : ℕ) :
    folded ψ hψ C hC T N =ᵐ[gaussianProduct] fun Y => ∑ i : Fin (N+1),
      ψ (process (uniformTime T N i.castSucc) Y)*
        (|process (uniformTime T N i.succ) Y|-|process (uniformTime T N i.castSucc) Y|)^2 := by
  filter_upwards [Lp.coeFn_sub (clockL1 (weighted ψ hψ T N)) (lossClass ψ hψ C hC T N),
    clockL1_actual (weighted ψ hψ T N),weighted_actual ψ hψ T N,loss_actual ψ hψ C hC T N] with Y hs hl hw he
  change folded ψ hψ C hC T N Y = _ at hs
  rw [hs,Pi.sub_apply,hl,hw,he]
  unfold lossValue
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by unfold loss; ring

theorem folded_tendsto (ψ : ℝ → ℝ) {K : ℝ≥0} (hψ : LipschitzWith K ψ)
    (C : ℝ) (hC : ∀ x, ‖ψ x‖ ≤ C) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (folded ψ hψ C hC T) atTop (𝓝 (clockL1 (drift ψ hψ T))) := by
  have h := (clockL1_tendsto _ _ (weighted_tendsto ψ hψ T)).sub (loss_tendsto ψ hψ C hC T hT)
  unfold folded
  simpa only [sub_zero] using h

end OperatorDerivativeRewrite.Foundation.IBMClockWeightedFoldedVariation
