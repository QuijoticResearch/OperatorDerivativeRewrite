import Foundation.IBMMultitimeClockVarianceGraph

/-! Completed actual multitime Fourier source means in the ORIGINAL Gaussian
clock derivative graph. This does not assert intrinsic IBM measurability. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMFourierClockGraph
open InfiniteGaussian GaussianTimeProcess IBMMultitimeClockVarianceGraph

variable {ι : Type*} [Fintype ι] (a : ℕ → ι → ℝ) (β w : ℕ → ℝ)

theorem multitime_clock_graph (hv : Summable (fun k => |w k|))
    (hc : Summable (IBMFourierCylinderSeries.curvatureCost a w)) (r : ι → ℝ≥0) :
    ∃ G : GaussianVectorL2,
      (IBMFourierSourceMeanCalculus.clockMean a β w r, G) ∈
        closedCylindricalDerivative.graph ∧
      G =ᵐ[gaussianProduct] (fun Y => ∑' k,
        (w k * Real.cos (β k)) • dampingGradient (a k) r Y) ∧
      ‖G‖ ≤ (∑' k, IBMFourierCylinderSeries.curvatureCost a w k) *
        ∑ i, Real.sqrt (r i : ℝ) := by
  choose Fn Gn hgraph hFn hGn hGbound using fun k => damping_graph (a k) r
  let vf : ℕ → GaussianL2 := fun k => (w k * Real.cos (β k)) • Fn k
  let vg : ℕ → GaussianVectorL2 := fun k => (w k * Real.cos (β k)) • Gn k
  have hvf (k : ℕ) : ‖vf k‖ ≤ |w k| := by
    have hF : ‖Fn k‖ ≤ 1 := by
      apply le_trans (Lp.norm_le_of_ae_bound (by norm_num : (0 : ℝ) ≤ 1) ?_)
      · simp [measureUnivNNReal]
      · filter_upwards [hFn k] with Y hY
        rw [hY]
        exact IBMFourierClockMeanRegularity.damping_bound
          (IBMFoldedSourceCovariance.variance_nonneg _ _)
    have hcos : |Real.cos (β k)| ≤ 1 := Real.abs_cos_le_one _
    change ‖(w k * Real.cos (β k)) • Fn k‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    have ht := mul_le_mul hcos hF (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [mul_le_mul_of_nonneg_left ht (abs_nonneg (w k))]
  have hvg (k : ℕ) : ‖vg k‖ ≤
      IBMFourierCylinderSeries.curvatureCost a w k * ∑ i, Real.sqrt (r i : ℝ) := by
    change ‖(w k * Real.cos (β k)) • Gn k‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    have hcos : |w k| * |Real.cos (β k)| ≤ |w k| := by
      simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (β k)) (abs_nonneg _)
    have hbase : ‖Gn k‖ ≤ (IBMUniformRidgeNativeBounds.amplitude (a k)) ^ 2 *
        ∑ i, Real.sqrt (r i : ℝ) := by
      have h := varianceCost_bound (a k) r
      nlinarith [hGbound k]
    have ht := mul_le_mul hcos hbase (norm_nonneg _) (abs_nonneg (w k))
    simpa only [IBMFourierCylinderSeries.curvatureCost, mul_assoc] using ht
  have hnf : Summable (fun k => ‖vf k‖) :=
    hv.of_nonneg_of_le (fun _ => norm_nonneg _) hvf
  have hnb := hc.mul_right (∑ i, Real.sqrt (r i : ℝ))
  have hng : Summable (fun k => ‖vg k‖) :=
    hnb.of_nonneg_of_le (fun _ => norm_nonneg _) hvg
  have hpair : ((∑' k, vf k), (∑' k, vg k)) ∈ closedCylindricalDerivative.graph := by
    apply closedCylindricalDerivative_isClosed.mem_of_tendsto
      (hnf.of_norm.hasSum.prodMk hng.of_norm.hasSum)
    exact Eventually.of_forall fun s => closedCylindricalDerivative.graph.sum_mem
      (fun k _ => closedCylindricalDerivative.graph.smul_mem
        (w k * Real.cos (β k)) (hgraph k))
  have hF : (∑' k, vf k) = IBMFourierSourceMeanCalculus.clockMean a β w r := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hnf),
      ae_all_iff.mpr fun k => Lp.coeFn_smul (w k * Real.cos (β k)) (Fn k),
      ae_all_iff.mpr hFn,
      IBMFourierClockMeanRegularity.clockMean_actual a β w r hv] with Y hs hm hf hM
    rw [hs, hM]
    apply tsum_congr
    intro k
    change ((w k * Real.cos (β k)) • Fn k) Y = _
    rw [hm k, Pi.smul_apply, hf k]
    rfl
  refine ⟨∑' k, vg k, ?_, ?_, ?_⟩
  · rwa [hF] at hpair
  · filter_upwards [Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hng),
      ae_all_iff.mpr fun k => Lp.coeFn_smul (w k * Real.cos (β k)) (Gn k),
      ae_all_iff.mpr hGn] with Y hs hm hg
    rw [hs]
    apply tsum_congr
    intro k
    change ((w k * Real.cos (β k)) • Gn k) Y = _
    rw [hm k, Pi.smul_apply, hg k]
  · apply (norm_tsum_le_tsum_norm hng).trans
    have ht := hng.tsum_le_tsum hvg hnb
    simpa only [tsum_mul_right] using ht

theorem multitime_clock_domain (hv : Summable (fun k => |w k|))
    (hc : Summable (IBMFourierCylinderSeries.curvatureCost a w)) (r : ι → ℝ≥0) :
    IBMFourierSourceMeanCalculus.clockMean a β w r ∈ closedCylindricalDerivative.domain := by
  obtain ⟨G, hG, _, _⟩ := multitime_clock_graph a β w hv hc r
  exact LinearPMap.mem_domain_of_mem_graph hG

end OperatorDerivativeRewrite.Foundation.IBMFourierClockGraph
