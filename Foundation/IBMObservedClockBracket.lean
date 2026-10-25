import Foundation.IBMObservedClockOccupation
import Foundation.GaussianFutureTerminalBracket
import Foundation.IBMClippedClockStrongLimit

/-! Actual weighted bracket sums with separate horizon and future observation.
Both surviving interior and shrinking random-boundary fields are controlled. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMObservedClockBracket
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMTerminalBracketWeights IBMObservedClockOccupation

def weightedValue (φ : ℝ × ℝ → ℝ) (H R : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (N+1), (process (uniformTime H N i.succ) Y-process (uniformTime H N i.castSucc) Y)^2*
    φ (process (uniformTime H N i.castSucc) Y,process R Y)

def weightedClass (φ : ℝ × ℝ → ℝ) (hm : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (H R : ℝ≥0) (N : ℕ) : GaussianL2 :=
  GaussianFutureTerminalBracket.error H R N (fun _ => φ) (fun _ => hm) (fun _ => hb)+
    sampledClass φ hm hb H R N

theorem weightedClass_actual (φ : ℝ × ℝ → ℝ) (hm : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (H R : ℝ≥0) (N : ℕ) : weightedClass φ hm hb H R N =ᵐ[gaussianProduct] weightedValue φ H R N := by
  filter_upwards [Lp.coeFn_add
    (GaussianFutureTerminalBracket.error H R N (fun _ => φ) (fun _ => hm) (fun _ => hb))
    (sampledClass φ hm hb H R N),GaussianFutureTerminalBracket.error_actual H R N
    (fun _ => φ) (fun _ => hm) (fun _ => hb),sampledClass_actual φ hm hb H R N] with Y ha he hs
  change weightedClass φ hm hb H R N Y = _ at ha
  rw [ha,Pi.add_apply,he,hs]
  unfold sampledSum weightedValue
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [uniformTime_step]
  ring

theorem weightedValue_memLp (φ : ℝ × ℝ → ℝ) (hm : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (H R : ℝ≥0) (N : ℕ) : MemLp (weightedValue φ H R N) 2 gaussianProduct :=
  (Lp.memLp (weightedClass φ hm hb H R N)).ae_eq (weightedClass_actual φ hm hb H R N)

theorem weightedClass_tendsto (H R : ℝ≥0) (hHR : H < R)
    (φ : ℕ → ℝ × ℝ → ℝ) (hm : ∀ N, Measurable (φ N)) (hb : ∀ N x, ‖φ N x‖ ≤ 1)
    (f : GaussianL2) (hf : Tendsto (fun N => sampledClass (φ N) (hm N) (hb N) H R N) atTop (𝓝 f)) :
    Tendsto (fun N => weightedClass (φ N) (hm N) (hb N) H R N) atTop (𝓝 f) := by
  have he := GaussianFutureTerminalBracket.varying_error_tendsto H R hHR
    (fun N _ => φ N) (fun N _ => hm N) (fun N _ => hb N)
  have h := he.add hf
  simpa only [zero_add,weightedClass] using h

theorem outer_weightedClass_tendsto (H R : ℝ≥0) (hHR : H < R)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N => weightedClass (outerBand (δ N)) (outerBand_measurable (δ N))
      (outerBand_bound (δ N)) H R N) atTop (𝓝 (0:GaussianL2)) :=
  weightedClass_tendsto H R hHR _ _ _ 0 (outer_sampledClass_tendsto H R hHR.le δ hδ)

theorem interior_weightedClass_tendsto (H R : ℝ≥0) (hHR : H < R) :
    Tendsto (weightedClass IBMTerminalBracketWeights.interior interior_measurable interior_bound H R)
      atTop (𝓝 (occupationL2 H R)) := by
  exact weightedClass_tendsto H R hHR (fun _ => IBMTerminalBracketWeights.interior)
    (fun _ => interior_measurable) (fun _ => interior_bound) _ (interior_sampledClass_tendsto H R hHR.le)

theorem weighted_mean (φ : ℝ × ℝ → ℝ) (hm : Measurable φ) (hb : ∀ x, ‖φ x‖ ≤ 1)
    (H R : ℝ≥0) (N : ℕ) :
    (∫ Y, weightedValue φ H R N Y ∂gaussianProduct) =
      inner ℝ gaussianOne (weightedClass φ hm hb H R N) := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [gaussianOne_coeFn,weightedClass_actual φ hm hb H R N] with Y h1 hc
  rw [h1,hc,Real.inner_apply,one_mul]

theorem outer_weighted_mean_tendsto (H R : ℝ≥0) (hHR : H < R)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N => ∫ Y, weightedValue (outerBand (δ N)) H R N Y ∂gaussianProduct) atTop (𝓝 0) := by
  have h := ((innerSL ℝ (gaussianOne:GaussianL2)).continuous.tendsto (0:GaussianL2)).comp
    (outer_weightedClass_tendsto H R hHR δ hδ)
  simp only [map_zero] at h
  exact h.congr' (Eventually.of_forall fun N => (weighted_mean _ (outerBand_measurable (δ N))
    (outerBand_bound (δ N)) H R N).symm)

end OperatorDerivativeRewrite.Foundation.IBMObservedClockBracket
