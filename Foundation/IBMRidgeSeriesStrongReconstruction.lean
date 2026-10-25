import Foundation.IBMUniformRidgeNativeBounds
import Foundation.IBMRidgeSeries

/-! Strong random native reconstruction on the existing actual Schwartz ridge
series domain. Curvature summability controls clock L2, not intrinsic L2 alone. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMRidgeSeriesStrongReconstruction
open InfiniteGaussian IBMTimeAveragedObservable IBMCorrectionStein
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

theorem second_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    ∀ x, ‖deriv (deriv (shiftedJet g a 0)) x‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 2) := by
  simpa only [shiftedJet_deriv] using shiftedJet_bound g a 2

theorem first_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    ∀ x, ‖deriv (shiftedJet g a 0) x‖ ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 1) := by
  simpa only [shiftedJet_deriv] using shiftedJet_bound g a 1

theorem joint_eq {d : ℕ} (g : SchwartzMap ℝ ℝ) (a : ℝ)
    (c : Fin d → ℝ) (τ : Fin d → ℝ≥0) :
    IBMFiniteRidgeObservation.jointClass c τ (shiftedJet_smooth g a 0).continuous
      (shiftedJet_bound g a 0) =
      (IBMRidgeNativeSource.ridgeObservation g a c τ : JointL2) := by
  apply Lp.ext
  filter_upwards [IBMFiniteRidgeObservation.joint_actual c τ
    (shiftedJet_smooth g a 0).continuous (shiftedJet_bound g a 0),
    IBMRidgeNativeSource.ridge_actual g a c τ] with p hn ho
  exact hn.trans (by simpa only [shiftedJet,jet,IBMFiniteRidgeObservation.value,
    IBMClockCylinderChain.actualValue,IBMRidgeNativeSource.ridgeObservation] using ho.symm)

variable {d : ℕ → ℕ} (g : ℕ → SchwartzMap ℝ ℝ) (a w : ℕ → ℝ)
  (c : (k : ℕ) → Fin (d k) → ℝ) (τ : (k : ℕ) → Fin (d k) → ℝ≥0)

def nativeTerm (H : ℝ≥0) (N k : ℕ) : GaussianL2 :=
  w k • IBMFiniteRidgeNativeReconstruction.native (c k) (τ k)
    (shiftedJet_smooth (g k) (a k) 0) (second_bound (g k) (a k)) H N

def limitTerm (H : ℝ≥0) (k : ℕ) : GaussianL2 :=
  w k • IBMFiniteRidgeNativeReconstruction.reconstruction (c k) (τ k)
    (shiftedJet_smooth (g k) (a k) 0) (second_bound (g k) (a k)) H

def native (H : ℝ≥0) (N : ℕ) : GaussianL2 := ∑' k, nativeTerm g a w c τ H N k
def reconstruction (H : ℝ≥0) : GaussianL2 := ∑' k, limitTerm g a w c τ H k

theorem nativeTerm_bound (H : ℝ≥0) (N k : ℕ) :
    ‖nativeTerm g a w c τ H N k‖ ≤ 3*(H:ℝ)*IBMRidgeSeries.curvatureCost g w c k := by
  rw [nativeTerm,norm_smul,Real.norm_eq_abs]
  have hb := mul_le_mul_of_nonneg_left (IBMUniformRidgeNativeBounds.native_bound
    (c k) (τ k) (shiftedJet_smooth (g k) (a k) 0) (second_bound (g k) (a k)) H N)
    (abs_nonneg (w k))
  simpa only [IBMRidgeSeries.curvatureCost,IBMUniformRidgeNativeBounds.amplitude,
    mul_assoc,mul_left_comm,mul_comm] using hb

theorem term_tendsto (H : ℝ≥0) (hH : 0 < H) (k : ℕ) :
    Tendsto (fun N => nativeTerm g a w c τ H N k) atTop (𝓝 (limitTerm g a w c τ H k)) :=
  (IBMFiniteRidgeNativeReconstruction.native_tendsto (c k) (τ k)
    (shiftedJet_smooth (g k) (a k) 0) (second_bound (g k) (a k)) H hH).const_smul (w k)

theorem native_tendsto (hc : Summable (IBMRidgeSeries.curvatureCost g w c))
    (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (native g a w c τ H) atTop (𝓝 (reconstruction g a w c τ H)) :=
  tendsto_tsum_of_dominated_convergence (hc.mul_left (3*(H:ℝ)))
    (term_tendsto g a w c τ H hH)
    (Eventually.of_forall fun N k => nativeTerm_bound g a w c τ H N k)

theorem term_lower (H : ℝ≥0) (N k : ℕ) :
    IBMClippedClockStrongLimit.clockL1 (nativeTerm g a w c τ H N k) =
      IBMJointRandomGraphIdentity.nativeOperator H N (IBMRidgeSeries.term g a w c τ k : JointL2) := by
  have he := IBMFiniteRidgeNativeReconstruction.native_lower (c k) (τ k)
    (shiftedJet_smooth (g k) (a k) 0) (shiftedJet_bound (g k) (a k) 0)
    (first_bound (g k) (a k)) (second_bound (g k) (a k)) H N
  rw [joint_eq] at he
  apply Lp.ext
  filter_upwards [IBMClippedClockStrongLimit.clockL1_actual (nativeTerm g a w c τ H N k),
    Lp.coeFn_smul (w k) (IBMFiniteRidgeNativeReconstruction.native (c k) (τ k)
      (shiftedJet_smooth (g k) (a k) 0) (second_bound (g k) (a k)) H N),
    IBMClippedClockStrongLimit.clockL1_actual (IBMFiniteRidgeNativeReconstruction.native
      (c k) (τ k) (shiftedJet_smooth (g k) (a k) 0) (second_bound (g k) (a k)) H N),
    Lp.coeFn_smul (w k) (IBMJointRandomGraphIdentity.nativeOperator H N
      (IBMRidgeNativeSource.ridgeObservation (g k) (a k) (c k) (τ k) : JointL2))] with Y hl hs hb ht
  rw [hl]
  change (w k • IBMFiniteRidgeNativeReconstruction.native (c k) (τ k)
    (shiftedJet_smooth (g k) (a k) 0) (second_bound (g k) (a k)) H N) Y = _
  rw [hs,Pi.smul_apply,← hb,he]
  change w k • _ = (IBMJointRandomGraphIdentity.nativeOperator H N
    (w k • (IBMRidgeNativeSource.ridgeObservation (g k) (a k) (c k) (τ k) : JointL2))) Y
  rw [map_smul]
  exact ht.symm

theorem native_terms_summable (hc : Summable (IBMRidgeSeries.curvatureCost g w c))
    (H : ℝ≥0) (N : ℕ) : Summable (nativeTerm g a w c τ H N) :=
  ((hc.mul_left (3*(H:ℝ))).of_nonneg_of_le (fun k => norm_nonneg _)
    (nativeTerm_bound g a w c τ H N)).of_norm

theorem lower_sum (f : ℕ → GaussianL2) (n : ℕ) :
    IBMClippedClockStrongLimit.clockL1 (∑ k ∈ Finset.range n, f k) =
      ∑ k ∈ Finset.range n, IBMClippedClockStrongLimit.clockL1 (f k) := by
  apply Lp.ext
  filter_upwards [IBMClippedClockStrongLimit.clockL1_actual (∑ k ∈ Finset.range n, f k),
    Lp.coeFn_finsetSum (Finset.range n) f,
    Lp.coeFn_finsetSum (Finset.range n) (fun k => IBMClippedClockStrongLimit.clockL1 (f k)),
    ae_all_iff.mpr fun k => IBMClippedClockStrongLimit.clockL1_actual (f k)] with Y hl hs ht hk
  rw [hl,hs,ht]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => (hk k).symm

theorem native_lower (hv : Summable (IBMRidgeSeries.valueCost g w))
    (hc : Summable (IBMRidgeSeries.curvatureCost g w c)) (H : ℝ≥0) (N : ℕ) :
    IBMClippedClockStrongLimit.clockL1 (native g a w c τ H N) =
      IBMJointRandomGraphIdentity.nativeOperator H N (IBMRidgeSeries.series g a w c τ : JointL2) := by
  have h₁ := IBMClippedClockStrongLimit.clockL1_tendsto _ _
    (native_terms_summable g a w c τ hc H N).hasSum.tendsto_sum_nat
  have h₂ := ((IBMJointRandomGraphIdentity.nativeOperator H N).comp
    IntrinsicSpace.subtypeL).continuous.tendsto (IBMRidgeSeries.series g a w c τ)
      |>.comp (IBMRidgeSeries.series_partial_tendsto g a w c τ hv)
  apply tendsto_nhds_unique h₁
  apply h₂.congr'
  exact Eventually.of_forall fun n => by
    change IBMJointRandomGraphIdentity.nativeOperator H N
      (IntrinsicSpace.subtypeL (∑ k ∈ Finset.range n, IBMRidgeSeries.term g a w c τ k)) =
      IBMClippedClockStrongLimit.clockL1 (∑ k ∈ Finset.range n, nativeTerm g a w c τ H N k)
    rw [lower_sum]
    simp only [map_sum]
    exact Finset.sum_congr rfl fun k _ => (term_lower g a w c τ H N k).symm

theorem source_native_tendsto (hv : Summable (IBMRidgeSeries.valueCost g w))
    (hc : Summable (IBMRidgeSeries.curvatureCost g w c)) (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => IBMJointRandomGraphIdentity.nativeOperator H N
      (IBMRidgeSeries.series g a w c τ : JointL2)) atTop
        (𝓝 (IBMClippedClockStrongLimit.clockL1 (reconstruction g a w c τ H))) :=
  (IBMClippedClockStrongLimit.clockL1_tendsto _ _
    (native_tendsto g a w c τ hc H hH)).congr'
      (Eventually.of_forall fun N => native_lower g a w c τ hv hc H N)

theorem native_bound (hc : Summable (IBMRidgeSeries.curvatureCost g w c))
    (H : ℝ≥0) (N : ℕ) : ‖native g a w c τ H N‖ ≤
      3*(H:ℝ)*∑' k, IBMRidgeSeries.curvatureCost g w c k := by
  have hn : Summable (fun k => ‖nativeTerm g a w c τ H N k‖) :=
    (hc.mul_left (3*(H:ℝ))).of_nonneg_of_le (fun _ => norm_nonneg _)
      (nativeTerm_bound g a w c τ H N)
  calc
    _ ≤ ∑' k, ‖nativeTerm g a w c τ H N k‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k, 3*(H:ℝ)*IBMRidgeSeries.curvatureCost g w c k :=
      hn.tsum_le_tsum (nativeTerm_bound g a w c τ H N) (hc.mul_left _)
    _ = _ := tsum_mul_left

theorem reconstruction_bound (hc : Summable (IBMRidgeSeries.curvatureCost g w c))
    (H : ℝ≥0) (hH : 0 < H) : ‖reconstruction g a w c τ H‖ ≤
      3*(H:ℝ)*∑' k, IBMRidgeSeries.curvatureCost g w c k :=
  le_of_tendsto (native_tendsto g a w c τ hc H hH).norm
    (Eventually.of_forall fun N => native_bound g a w c τ hc H N)

theorem clockL1_injective : Function.Injective IBMClippedClockStrongLimit.clockL1 := by
  intro u v he
  apply Lp.ext
  exact (IBMClippedClockStrongLimit.clockL1_actual u).symm.trans
    (he ▸ IBMClippedClockStrongLimit.clockL1_actual v)

theorem reconstruction_congr
    {d' : ℕ → ℕ} (g' : ℕ → SchwartzMap ℝ ℝ) (a' w' : ℕ → ℝ)
    (c' : (k : ℕ) → Fin (d' k) → ℝ) (τ' : (k : ℕ) → Fin (d' k) → ℝ≥0)
    (hv : Summable (IBMRidgeSeries.valueCost g w))
    (hc : Summable (IBMRidgeSeries.curvatureCost g w c))
    (hv' : Summable (IBMRidgeSeries.valueCost g' w'))
    (hc' : Summable (IBMRidgeSeries.curvatureCost g' w' c'))
    (H : ℝ≥0) (hH : 0 < H)
    (he : IBMRidgeSeries.actualSeries g a w c τ =ᵐ[IBMSourceLaws.jointMeasure]
      IBMRidgeSeries.actualSeries g' a' w' c' τ') :
    reconstruction g a w c τ H = reconstruction g' a' w' c' τ' H := by
  have hj : (IBMRidgeSeries.series g a w c τ : JointL2) =
      (IBMRidgeSeries.series g' a' w' c' τ' : JointL2) := by
    apply Lp.ext
    exact (IBMRidgeSeries.series_actual g a w c τ hv).trans
      (he.trans (IBMRidgeSeries.series_actual g' a' w' c' τ' hv').symm)
  apply clockL1_injective
  have ht := source_native_tendsto g a w c τ hv hc H hH
  rw [hj] at ht
  exact tendsto_nhds_unique ht (source_native_tendsto g' a' w' c' τ' hv' hc' H hH)

theorem native_expectation (hv : Summable (IBMRidgeSeries.valueCost g w))
    (hc : Summable (IBMRidgeSeries.curvatureCost g w c)) (H : ℝ≥0) (N : ℕ) :
    L1.integralCLM (IBMClippedClockStrongLimit.clockL1 (native g a w c τ H N)) =
      inner ℝ (IBMJointIntrinsicDerivative.jointDivergence
        (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))) (IBMRidgeSeries.series g a w c τ) := by
  rw [native_lower g a w c τ hv hc H N]
  change L1.integralCLM (IBMJointRandomContraction.jointOperator
    (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1))
    (IBMRidgeSeries.series g a w c τ : JointL2)) = _
  rw [IBMJointRandomContraction.joint_expectation,IBMRawGridSecondChaos.native_grid_value]
  exact (IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right
    (IBMRidgeSeries.series g a w c τ)
    (jointRealization (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1)))).symm

theorem reconstruction_expectation (hv : Summable (IBMRidgeSeries.valueCost g w))
    (hc : Summable (IBMRidgeSeries.curvatureCost g w c)) (H : ℝ≥0) (hH : 0 < H) :
    L1.integralCLM (IBMClippedClockStrongLimit.clockL1 (reconstruction g a w c τ H)) =
      ∑' k, w k*IBMRidgeNativeLimit.ridgeLimit (g k) (a k) (c k) (τ k) H := by
  have ht := (L1.integralCLM (μ := gaussianProduct) (E := ℝ)).continuous.tendsto _
    |>.comp (IBMClippedClockStrongLimit.clockL1_tendsto _ _
      (native_tendsto g a w c τ hc H hH))
  have hs := ht.congr' (Eventually.of_forall fun N => native_expectation g a w c τ hv hc H N)
  exact tendsto_nhds_unique hs (IBMRidgeSeries.series_native_tendsto g a w c τ hv hc H hH)

end OperatorDerivativeRewrite.Foundation.IBMRidgeSeriesStrongReconstruction
