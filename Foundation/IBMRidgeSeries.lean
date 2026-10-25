import Foundation.IBMRidgeNativeBound
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! A genuine infinite actual-observable IBM testing domain from summable
ridge values and curvature costs. No new probability or normed space is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRidgeSeries
open InfiniteGaussian IBMTimeAveragedObservable IBMJointIntrinsicDerivative
open IBMRidgeNativeSource IBMRidgeNativeLimit IBMRidgeNativeBound IBMCorrectionStein
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _ IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
local instance : Fact ((1:ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
attribute [local irreducible] jointDerivative LinearPMap.adjoint LinearPMap.graph

theorem ridgeObservation_norm_bound {d : ℕ} (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) :
    ‖ridgeObservation g a c τ‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 0) := by
  change ‖jointRealization (ridgeSource g a c τ)‖ ≤ _
  rw [jointRealization.norm_map]
  have hb : ∀ᵐ Y ∂gaussianProduct, ‖ridgeSource g a c τ Y‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (jet g 0) := by
    filter_upwards [ridgeSource_actual g a c τ] with Y hr
    rw [hr]
    exact IBMSchwartzSourceDerivative.observable_bound g a 0 _
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (f:=ridgeSource g a c τ) (by norm_num) hb

variable {d : ℕ → ℕ} (g : ℕ → SchwartzMap ℝ ℝ) (a w : ℕ → ℝ)
  (c : (k : ℕ) → Fin (d k) → ℝ) (τ : (k : ℕ) → Fin (d k) → ℝ≥0)

def valueCost (k : ℕ) : ℝ := |w k| * SchwartzMap.seminorm ℝ 0 0 (jet (g k) 0)

def curvatureCost (k : ℕ) : ℝ :=
  |w k| * SchwartzMap.seminorm ℝ 0 0 (jet (g k) 2)*(∑ j, |c k j|)^2

def term (k : ℕ) : IntrinsicSpace := w k • ridgeObservation (g k) (a k) (c k) (τ k)

def series : IntrinsicSpace := ∑' k, term g a w c τ k

def actualSeries (p : IBMSourceLaws.JointSample) : ℝ :=
  ∑' k, w k*g k (a k+IBMClockCylinderChain.actualValue (c k) (τ k) p)

theorem term_norm_bound (k : ℕ) : ‖term g a w c τ k‖ ≤ valueCost g w k := by
  rw [term,norm_smul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (ridgeObservation_norm_bound (g k) (a k) (c k) (τ k)) (abs_nonneg _)

theorem terms_norm_summable (hv : Summable (valueCost g w)) :
    Summable (fun k => ‖term g a w c τ k‖) :=
  hv.of_nonneg_of_le (fun k => norm_nonneg _) (term_norm_bound g a w c τ)

theorem terms_summable (hv : Summable (valueCost g w)) : Summable (term g a w c τ) :=
  (terms_norm_summable g a w c τ hv).of_norm

theorem series_joint_eq (hv : Summable (valueCost g w)) :
    (series g a w c τ : JointL2) = ∑' k, (term g a w c τ k : JointL2) :=
  (terms_summable g a w c τ hv).map_tsum IntrinsicSpace.subtypeL.toLinearMap.toAddMonoidHom
    IntrinsicSpace.subtypeL.continuous

theorem series_actual (hv : Summable (valueCost g w)) :
    (series g a w c τ : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] actualSeries g a w c τ := by
  have hn : Summable (fun k => ‖(term g a w c τ k : JointL2)‖) := terms_norm_summable g a w c τ hv
  rw [series_joint_eq g a w c τ hv]
  filter_upwards [Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hn),
    ae_all_iff.mpr fun k => Lp.coeFn_smul (w k) (ridgeObservation (g k) (a k) (c k) (τ k) : JointL2),
    ae_all_iff.mpr fun k => ridge_actual (g k) (a k) (c k) (τ k)] with p hs hm hr
  rw [hs]
  apply tsum_congr
  intro k
  change ((w k) • (ridgeObservation (g k) (a k) (c k) (τ k) : JointL2)) p = _
  rw [hm k,Pi.smul_apply]
  change w k*jointRealization (ridgeSource (g k) (a k) (c k) (τ k)) p = _
  rw [hr k]

theorem actualSeries_memLp (hv : Summable (valueCost g w)) :
    MemLp (actualSeries g a w c τ) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (series g a w c τ : JointL2)).ae_eq (series_actual g a w c τ hv)

theorem actual_terms_norm_summable (hv : Summable (valueCost g w))
    (p : IBMSourceLaws.JointSample) :
    Summable (fun k => ‖w k*g k (a k+IBMClockCylinderChain.actualValue (c k) (τ k) p)‖) := by
  apply hv.of_nonneg_of_le (fun k => norm_nonneg _)
  intro k
  rw [norm_mul,Real.norm_eq_abs (w k)]
  have hb := shiftedJet_bound (g k) (a k) 0 (IBMClockCylinderChain.actualValue (c k) (τ k) p)
  exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

theorem series_partial_tendsto (hv : Summable (valueCost g w)) :
    Tendsto (fun n => ∑ k ∈ Finset.range n, term g a w c τ k) atTop (𝓝 (series g a w c τ)) :=
  (terms_summable g a w c τ hv).hasSum.tendsto_sum_nat

theorem native_term_bound (H : ℝ≥0) (N k : ℕ) :
    ‖w k*nativeRidgePairing (g k) (a k) (c k) (τ k) H N‖ ≤ (H:ℝ)*curvatureCost g w c k := by
  rw [norm_mul,Real.norm_eq_abs (w k),Real.norm_eq_abs]
  calc
    _ ≤ |w k| * ((H:ℝ)*SchwartzMap.seminorm ℝ 0 0 (jet (g k) 2)*(∑ j, |c k j|)^2) :=
      mul_le_mul_of_nonneg_left (nativeRidgePairing_bound (g k) (a k) (c k) (τ k) H N) (abs_nonneg _)
    _ = _ := by unfold curvatureCost; ring

theorem series_pairing_identity (hv : Summable (valueCost g w)) (H : ℝ≥0) (N : ℕ) :
    inner ℝ (jointDivergence (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1)))
      (series g a w c τ) = ∑' k, w k*nativeRidgePairing (g k) (a k) (c k) (τ k) H N := by
  let L := innerSL ℝ (jointDivergence (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1)))
  have he := (terms_summable g a w c τ hv).map_tsum L.toLinearMap.toAddMonoidHom L.continuous
  change inner ℝ _ (series g a w c τ) = ∑' k, inner ℝ _ (term g a w c τ k) at he
  simpa only [term,inner_smul_right,nativeRidgePairing] using he

theorem series_native_tendsto (hv : Summable (valueCost g w))
    (hc : Summable (curvatureCost g w c)) (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N : ℕ => inner ℝ
      (jointDivergence (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))) (series g a w c τ))
      atTop (𝓝 (∑' k, w k*ridgeLimit (g k) (a k) (c k) (τ k) H)) := by
  have ht := tendsto_tsum_of_dominated_convergence (hc.mul_left (H:ℝ))
    (fun k => (nativeRidgePairing_tendsto (g k) (a k) (c k) (τ k) H hH).const_mul (w k))
    (Eventually.of_forall fun N k => native_term_bound g a w c τ H N k)
  exact ht.congr' (Eventually.of_forall fun N => (series_pairing_identity g a w c τ hv H N).symm)

theorem limit_series_summable (hc : Summable (curvatureCost g w c)) (H : ℝ≥0) (hH : 0 < H) :
    Summable (fun k => w k*ridgeLimit (g k) (a k) (c k) (τ k) H) := by
  apply (hc.mul_left (H:ℝ)).of_norm_bounded
  intro k
  apply le_of_tendsto ((nativeRidgePairing_tendsto (g k) (a k) (c k) (τ k) H hH).const_mul (w k)).norm
  exact Eventually.of_forall fun N => native_term_bound g a w c τ H N k

theorem series_native_bound (hv : Summable (valueCost g w))
    (hc : Summable (curvatureCost g w c)) (H : ℝ≥0) (N : ℕ) :
    |inner ℝ (jointDivergence (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1)))
      (series g a w c τ)| ≤ (H:ℝ)*∑' k, curvatureCost g w c k := by
  have hn : Summable (fun k => ‖w k*nativeRidgePairing (g k) (a k) (c k) (τ k) H N‖) :=
    (hc.mul_left (H:ℝ)).of_nonneg_of_le (fun k => norm_nonneg _) (native_term_bound g a w c τ H N)
  rw [series_pairing_identity g a w c τ hv H N,← Real.norm_eq_abs]
  calc
    _ ≤ ∑' k, ‖w k*nativeRidgePairing (g k) (a k) (c k) (τ k) H N‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k, (H:ℝ)*curvatureCost g w c k :=
      hn.tsum_le_tsum (native_term_bound g a w c τ H N) (hc.mul_left (H:ℝ))
    _ = _ := hc.tsum_mul_left (H:ℝ)

theorem series_limit_congr {e : ℕ → ℕ}
    (f : ℕ → SchwartzMap ℝ ℝ) (b v : ℕ → ℝ)
    (r : (k : ℕ) → Fin (e k) → ℝ) (σ : (k : ℕ) → Fin (e k) → ℝ≥0)
    (hv : Summable (valueCost g w)) (hc : Summable (curvatureCost g w c))
    (hv' : Summable (valueCost f v)) (hc' : Summable (curvatureCost f v r))
    (H : ℝ≥0) (hH : 0 < H)
    (he : actualSeries g a w c τ =ᵐ[IBMSourceLaws.jointMeasure] actualSeries f b v r σ) :
    (∑' k, w k*ridgeLimit (g k) (a k) (c k) (τ k) H) =
      ∑' k, v k*ridgeLimit (f k) (b k) (r k) (σ k) H := by
  have hs : series g a w c τ = series f b v r σ := by
    apply Subtype.ext
    apply Lp.ext
    exact (series_actual g a w c τ hv).trans (he.trans (series_actual f b v r σ hv').symm)
  have hl := series_native_tendsto g a w c τ hv hc H hH
  have hr := series_native_tendsto f b v r σ hv' hc' H hH
  apply tendsto_nhds_unique hl
  exact hr.congr' (Eventually.of_forall fun N => by rw [hs])

end OperatorDerivativeRewrite.Foundation.IBMRidgeSeries
