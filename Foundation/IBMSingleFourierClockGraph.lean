import Foundation.GaussianReflectedDampingGraph
import Foundation.GaussianDeterministicIntegral

/-! The ORIGINAL closed clock graph contains the completed actual one-time
Fourier source mean. The explicit gradient retains the reflected sign. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSingleFourierClockGraph
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess
open GaussianTimeProductL2 GaussianContinuousRigidity GaussianReflectedDampingGraph

def clockGradient (R : ℝ≥0) : GaussianVectorL2 := fieldEmbedding (productTensor (timeVector R) gaussianOne)

theorem clock_graph (R : ℝ≥0) : (wienerL2 R,clockGradient R) ∈ closedCylindricalDerivative.graph :=
  GaussianDeterministicIntegral.firstChaos_closedDerivative_graph (timeVector R)

theorem clockGradient_norm (R : ℝ≥0) : ‖clockGradient R‖ = Real.sqrt (R:ℝ) := by
  have h1 : ‖gaussianOne‖ = 1 := by
    have hi := GaussianDeterministicGraphCore.gaussianOne_inner_self
    rw [real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg gaussianOne]
  rw [clockGradient,fieldEmbedding_tensor,IBMClockAverageCandidate.scalarTensor_norm,
    LinearIsometry.norm_map,h1,one_mul]
  rw [← timeVector_norm_sq R,Real.sqrt_sq (norm_nonneg _)]

variable (a : ℕ → Unit → ℝ) (β w : ℕ → ℝ)

def rate (k : ℕ) : ℝ := (a k ())^2/2

theorem rate_nonneg (k : ℕ) : 0 ≤ rate a k := div_nonneg (sq_nonneg _) (by norm_num)

theorem cost_identity (k : ℕ) :
    |w k| * rate a k = IBMFourierCylinderSeries.curvatureCost a w k/2 := by
  simp only [rate,IBMFourierCylinderSeries.curvatureCost,
    IBMUniformRidgeNativeBounds.amplitude,Finset.univ_unique,Finset.sum_singleton,sq_abs]
  ring

theorem single_clock_graph (hv : Summable (fun k => |w k|))
    (hc : Summable (IBMFourierCylinderSeries.curvatureCost a w)) (R : ℝ≥0) :
    ∃ G : GaussianVectorL2,
      (IBMFourierSourceMeanCalculus.clockMean a β w (fun _ => R),G) ∈ closedCylindricalDerivative.graph ∧
      G =ᵐ[gaussianProduct] (fun Y => ∑' k,
        (w k*Real.cos (β k)*coefficient (rate a k) (process R Y)) • clockGradient R Y) ∧
      ‖G‖ ≤ ((∑' k, IBMFourierCylinderSeries.curvatureCost a w k)/2)*Real.sqrt (R:ℝ) := by
  choose Fn Gn hgraph hFn hGn hGbound using fun k =>
    closed_graph (rate_nonneg a k) (wienerL2 R) (clockGradient R) (clock_graph R)
  let vf : ℕ → GaussianL2 := fun k => (w k*Real.cos (β k)) • Fn k
  let vg : ℕ → GaussianVectorL2 := fun k => (w k*Real.cos (β k)) • Gn k
  have hvf (k : ℕ) : ‖vf k‖ ≤ |w k| := by
    have hF : ‖Fn k‖ ≤ 1 := by
      apply le_trans (Lp.norm_le_of_ae_bound (by norm_num : (0:ℝ) ≤ 1) ?_)
      · simp [measureUnivNNReal]
      · filter_upwards [hFn k] with Y hY
        rw [hY]
        exact value_bound (rate_nonneg a k) _
    have hcos : |Real.cos (β k)| ≤ 1 := Real.abs_cos_le_one _
    change ‖(w k*Real.cos (β k)) • Fn k‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_mul]
    have ht := mul_le_mul hcos hF (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith [mul_le_mul_of_nonneg_left ht (abs_nonneg (w k))]
  have hvg (k : ℕ) : ‖vg k‖ ≤
      (IBMFourierCylinderSeries.curvatureCost a w k/2)*‖clockGradient R‖ := by
    change ‖(w k*Real.cos (β k)) • Gn k‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs,abs_mul]
    have hcos : |w k| * |Real.cos (β k)| ≤ |w k| := by
      simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (β k)) (abs_nonneg (w k))
    have ht := mul_le_mul hcos (hGbound k) (norm_nonneg _) (abs_nonneg _)
    simpa only [← mul_assoc,cost_identity a w] using ht
  have hnf : Summable (fun k => ‖vf k‖) := hv.of_nonneg_of_le (fun _ => norm_nonneg _) hvf
  have hnb := (hc.div_const 2).mul_right ‖clockGradient R‖
  have hng : Summable (fun k => ‖vg k‖) := hnb.of_nonneg_of_le (fun _ => norm_nonneg _) hvg
  have hpair : ((∑' k, vf k),(∑' k, vg k)) ∈ closedCylindricalDerivative.graph := by
    apply closedCylindricalDerivative_isClosed.mem_of_tendsto
      (hnf.of_norm.hasSum.prodMk hng.of_norm.hasSum)
    exact Eventually.of_forall fun s => closedCylindricalDerivative.graph.sum_mem
      (fun k _ => closedCylindricalDerivative.graph.smul_mem (w k*Real.cos (β k)) (hgraph k))
  have hF : (∑' k, vf k) = IBMFourierSourceMeanCalculus.clockMean a β w (fun _ => R) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hnf),
      ae_all_iff.mpr fun k => Lp.coeFn_smul (w k*Real.cos (β k)) (Fn k),
      ae_all_iff.mpr hFn,
      IBMFourierClockMeanRegularity.clockMean_actual a β w (fun _ => R) hv] with Y hs hm hf hM
    rw [hs,hM]
    apply tsum_congr
    intro k
    change ((w k*Real.cos (β k)) • Fn k) Y = _
    rw [hm k,Pi.smul_apply,hf k]
    simp only [smul_eq_mul,IBMFourierClockMeanRegularity.term,
      IBMFourierClockMeanRegularity.damping,IBMFoldedSourceCovariance.variance_expansion,
      Finset.univ_unique,Finset.sum_singleton,min_self,value,rate,process]
    congr 2
    ring
  refine ⟨∑' k, vg k,?_,?_,?_⟩
  · rwa [hF] at hpair
  · filter_upwards [Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hng),
      ae_all_iff.mpr fun k => Lp.coeFn_smul (w k*Real.cos (β k)) (Gn k),
      ae_all_iff.mpr hGn] with Y hs hm hg
    rw [hs]
    apply tsum_congr
    intro k
    change ((w k*Real.cos (β k)) • Gn k) Y = _
    rw [hm k,Pi.smul_apply,hg k,smul_smul]
    rfl
  · apply (norm_tsum_le_tsum_norm hng).trans
    have ht := hng.tsum_le_tsum hvg hnb
    simpa only [tsum_mul_right,tsum_div_const,clockGradient_norm] using ht

theorem single_clock_domain (hv : Summable (fun k => |w k|))
    (hc : Summable (IBMFourierCylinderSeries.curvatureCost a w)) (R : ℝ≥0) :
    IBMFourierSourceMeanCalculus.clockMean a β w (fun _ => R) ∈ closedCylindricalDerivative.domain := by
  obtain ⟨G,hG,_,_⟩ := single_clock_graph a β w hv hc R
  exact LinearPMap.mem_domain_of_mem_graph hG

end OperatorDerivativeRewrite.Foundation.IBMSingleFourierClockGraph
