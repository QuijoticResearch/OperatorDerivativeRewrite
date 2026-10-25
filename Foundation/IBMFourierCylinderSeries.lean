import Foundation.IBMFourierRidgeCoefficients
import Foundation.IBMRidgeSeriesStrongReconstruction
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Actual multivariate Fourier cylinders and their strong random native action.
No claim of arbitrary C2 representation or density in an operator domain is made. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFourierCylinderSeries
open InfiniteGaussian IBMTimeAveragedObservable IBMFourierRidgeCoefficients
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe

variable {ι : Type*} [Fintype ι] (a : ℕ → ι → ℝ) (r : ι → ℝ≥0) (β w : ℕ → ℝ)

def valueTerm (k : ℕ) (x : ι → ℝ) : ℝ := w k*mode (β k) (∑ i, a k i*x i)
def value (x : ι → ℝ) : ℝ := ∑' k, valueTerm a β w k x

theorem valueTerm_bound (k : ℕ) (x : ι → ℝ) : ‖valueTerm a β w k x‖ ≤ |w k| := by
  rw [valueTerm,norm_mul,Real.norm_eq_abs]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (mode_bound (β k) _) (abs_nonneg _)

theorem value_uniform (hv : Summable (fun k => |w k|)) :
    TendstoUniformly (fun n x => ∑ k ∈ Finset.range n, valueTerm a β w k x)
      (value a β w) atTop :=
  tendstoUniformly_tsum_nat hv (valueTerm_bound a β w)

theorem value_continuous (hv : Summable (fun k => |w k|)) : Continuous (value a β w) := by
  apply continuous_tsum (fun k => ?_) hv (valueTerm_bound a β w)
  unfold valueTerm mode
  fun_prop

def term (k : ℕ) : IntrinsicSpace :=
  w k • IBMFiniteRidgeObservation.observation (a k) r (mode_smooth (β k)).continuous (mode_bound (β k))

def observation : IntrinsicSpace := ∑' k, term a r β w k

theorem term_bound (k : ℕ) : ‖term a r β w k‖ ≤ |w k| := by
  rw [term,norm_smul,Real.norm_eq_abs]
  have hn : ‖(IBMFiniteRidgeObservation.observation (a k) r
      (mode_smooth (β k)).continuous (mode_bound (β k)) : JointL2)‖ ≤ 1 := by
    apply le_trans (Lp.norm_le_of_ae_bound (by norm_num : (0:ℝ) ≤ 1) ?_)
    · simp [measureUnivNNReal]
    · filter_upwards [IBMFiniteRidgeObservation.joint_actual (a k) r
        (mode_smooth (β k)).continuous (mode_bound (β k))] with p hp
      change ‖IBMFiniteRidgeObservation.jointClass (a k) r
        (mode_smooth (β k)).continuous (mode_bound (β k)) p‖ ≤ 1
      rw [hp]
      exact mode_bound _ _
  exact (mul_le_mul_of_nonneg_left hn (abs_nonneg _)).trans_eq (mul_one _)

theorem terms_summable (hv : Summable (fun k => |w k|)) : Summable (term a r β w) :=
  (hv.of_nonneg_of_le (fun _ => norm_nonneg _) (term_bound a r β w)).of_norm

theorem observation_actual (hv : Summable (fun k => |w k|)) :
    (observation a r β w : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => value a β w (fun i => IBMConstructedSources.ibmValue (r i) p) := by
  have hn : Summable (fun k => ‖(term a r β w k : JointL2)‖) :=
    hv.of_nonneg_of_le (fun _ => norm_nonneg _) (term_bound a r β w)
  have he := (terms_summable a r β w hv).map_tsum
    IntrinsicSpace.subtypeL.toLinearMap.toAddMonoidHom IntrinsicSpace.subtypeL.continuous
  change (observation a r β w : JointL2) = ∑' k, (term a r β w k : JointL2) at he
  rw [he]
  filter_upwards [Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hn),
    ae_all_iff.mpr fun k => Lp.coeFn_smul (w k)
      (IBMFiniteRidgeObservation.observation (a k) r
        (mode_smooth (β k)).continuous (mode_bound (β k)) : JointL2),
    ae_all_iff.mpr fun k => IBMFiniteRidgeObservation.joint_actual (a k) r
      (mode_smooth (β k)).continuous (mode_bound (β k))] with p hs hm hp
  rw [hs]
  apply tsum_congr
  intro k
  change (w k • IBMFiniteRidgeObservation.jointClass (a k) r
    (mode_smooth (β k)).continuous (mode_bound (β k))) p = _
  have hm' := hm k
  change (w k • IBMFiniteRidgeObservation.jointClass (a k) r
    (mode_smooth (β k)).continuous (mode_bound (β k))) p =
      w k * IBMFiniteRidgeObservation.jointClass (a k) r
        (mode_smooth (β k)).continuous (mode_bound (β k)) p at hm'
  rw [hm',hp k]
  rfl

def curvatureCost (k : ℕ) : ℝ := |w k| *(IBMUniformRidgeNativeBounds.amplitude (a k))^2

def nativeTerm (H : ℝ≥0) (N k : ℕ) : GaussianL2 :=
  w k • IBMFiniteRidgeNativeReconstruction.native (a k) r
    (mode_smooth (β k)) (mode_second_bound (β k)) H N

def limitTerm (H : ℝ≥0) (k : ℕ) : GaussianL2 :=
  w k • IBMFiniteRidgeNativeReconstruction.reconstruction (a k) r
    (mode_smooth (β k)) (mode_second_bound (β k)) H

def native (H : ℝ≥0) (N : ℕ) : GaussianL2 := ∑' k, nativeTerm a r β w H N k
def reconstruction (H : ℝ≥0) : GaussianL2 := ∑' k, limitTerm a r β w H k

theorem nativeTerm_bound (H : ℝ≥0) (N k : ℕ) :
    ‖nativeTerm a r β w H N k‖ ≤ 3*(H:ℝ)*curvatureCost a w k := by
  rw [nativeTerm,norm_smul,Real.norm_eq_abs]
  have hb := mul_le_mul_of_nonneg_left (IBMUniformRidgeNativeBounds.native_bound
    (a k) r (mode_smooth (β k)) (mode_second_bound (β k)) H N) (abs_nonneg (w k))
  simpa only [curvatureCost,mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using hb

theorem native_tendsto (hc : Summable (curvatureCost a w)) (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (native a r β w H) atTop (𝓝 (reconstruction a r β w H)) :=
  tendsto_tsum_of_dominated_convergence (hc.mul_left (3*(H:ℝ)))
    (fun k => (IBMFiniteRidgeNativeReconstruction.native_tendsto (a k) r
      (mode_smooth (β k)) (mode_second_bound (β k)) H hH).const_smul (w k))
    (Eventually.of_forall fun N k => nativeTerm_bound a r β w H N k)

theorem limitTerm_actual (H : ℝ≥0) (k : ℕ) : limitTerm a r β w H k =ᵐ[gaussianProduct]
    fun Y => -(w k/2)*Real.cos (β k)*
      Real.exp (-‖IBMFiniteRidgeObservation.direction (a k) r Y‖^2/2)*
        IBMFiniteRidgeQuadraticTesting.limitValue (a k) r H Y := by
  filter_upwards [Lp.coeFn_smul (w k) (IBMFiniteRidgeNativeReconstruction.reconstruction
    (a k) r (mode_smooth (β k)) (mode_second_bound (β k)) H),
    IBMFiniteRidgeNativeReconstruction.reconstruction_actual (a k) r
      (mode_smooth (β k)) (mode_second_bound (β k)) H] with Y hs hl
  change (w k • IBMFiniteRidgeNativeReconstruction.reconstruction (a k) r
    (mode_smooth (β k)) (mode_second_bound (β k)) H) Y = _
  rw [hs,Pi.smul_apply,hl,coefficient_formula]
  simp only [smul_eq_mul]
  ring

theorem lower_smul (b : ℝ) (u : GaussianL2) :
    IBMClippedClockStrongLimit.clockL1 (b • u) = b • IBMClippedClockStrongLimit.clockL1 u := by
  apply Lp.ext
  filter_upwards [IBMClippedClockStrongLimit.clockL1_actual (b • u),
    Lp.coeFn_smul b u,Lp.coeFn_smul b (IBMClippedClockStrongLimit.clockL1 u),
    IBMClippedClockStrongLimit.clockL1_actual u] with Y hl hs ht hu
  rw [hl,hs,ht,Pi.smul_apply,Pi.smul_apply,hu]

theorem term_lower (H : ℝ≥0) (N k : ℕ) :
    IBMClippedClockStrongLimit.clockL1 (nativeTerm a r β w H N k) =
      IBMJointRandomGraphIdentity.nativeOperator H N (term a r β w k : JointL2) := by
  rw [nativeTerm,lower_smul,IBMFiniteRidgeNativeReconstruction.native_lower
    (a k) r (mode_smooth (β k)) (mode_bound (β k))
    (mode_first_bound (β k)) (mode_second_bound (β k))]
  change w k • _ = IBMJointRandomGraphIdentity.nativeOperator H N
    (w k • IBMFiniteRidgeObservation.jointClass (a k) r
      (mode_smooth (β k)).continuous (mode_bound (β k)))
  rw [map_smul]

theorem native_lower (hv : Summable (fun k => |w k|))
    (hc : Summable (curvatureCost a w)) (H : ℝ≥0) (N : ℕ) :
    IBMClippedClockStrongLimit.clockL1 (native a r β w H N) =
      IBMJointRandomGraphIdentity.nativeOperator H N (observation a r β w : JointL2) := by
  have hn : Summable (nativeTerm a r β w H N) :=
    ((hc.mul_left (3*(H:ℝ))).of_nonneg_of_le (fun _ => norm_nonneg _)
      (nativeTerm_bound a r β w H N)).of_norm
  have h₁ := IBMClippedClockStrongLimit.clockL1_tendsto _ _ hn.hasSum.tendsto_sum_nat
  have h₂ := ((IBMJointRandomGraphIdentity.nativeOperator H N).comp
    IntrinsicSpace.subtypeL).continuous.tendsto (observation a r β w)
      |>.comp (terms_summable a r β w hv).hasSum.tendsto_sum_nat
  apply tendsto_nhds_unique h₁
  apply h₂.congr'
  exact Eventually.of_forall fun n => by
    change IBMJointRandomGraphIdentity.nativeOperator H N
      (IntrinsicSpace.subtypeL (∑ k ∈ Finset.range n, term a r β w k)) =
      IBMClippedClockStrongLimit.clockL1 (∑ k ∈ Finset.range n, nativeTerm a r β w H N k)
    rw [IBMRidgeSeriesStrongReconstruction.lower_sum]
    simp only [map_sum]
    exact Finset.sum_congr rfl fun k _ => (term_lower a r β w H N k).symm

theorem source_native_tendsto (hv : Summable (fun k => |w k|))
    (hc : Summable (curvatureCost a w)) (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => IBMJointRandomGraphIdentity.nativeOperator H N
      (observation a r β w : JointL2)) atTop
        (𝓝 (IBMClippedClockStrongLimit.clockL1 (reconstruction a r β w H))) :=
  (IBMClippedClockStrongLimit.clockL1_tendsto _ _
    (native_tendsto a r β w hc H hH)).congr'
      (Eventually.of_forall fun N => native_lower a r β w hv hc H N)

theorem limitTerm_bound (H : ℝ≥0) (hH : 0 < H) (k : ℕ) :
    ‖limitTerm a r β w H k‖ ≤ 3*(H:ℝ)*curvatureCost a w k :=
  le_of_tendsto ((IBMFiniteRidgeNativeReconstruction.native_tendsto (a k) r
    (mode_smooth (β k)) (mode_second_bound (β k)) H hH).const_smul (w k)).norm
      (Eventually.of_forall fun N => nativeTerm_bound a r β w H N k)

theorem reconstruction_actual (hc : Summable (curvatureCost a w))
    (H : ℝ≥0) (hH : 0 < H) : reconstruction a r β w H =ᵐ[gaussianProduct]
    fun Y => ∑' k, -(w k/2)*Real.cos (β k)*
      Real.exp (-‖IBMFiniteRidgeObservation.direction (a k) r Y‖^2/2)*
        IBMFiniteRidgeQuadraticTesting.limitValue (a k) r H Y := by
  have hn : Summable (fun k => ‖limitTerm a r β w H k‖) :=
    (hc.mul_left (3*(H:ℝ))).of_nonneg_of_le (fun _ => norm_nonneg _)
      (limitTerm_bound a r β w H hH)
  filter_upwards [Lp.coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hn),
    ae_all_iff.mpr fun k => limitTerm_actual a r β w H k] with Y hs hk
  change (∑' k, limitTerm a r β w H k) Y = _
  rw [hs]
  exact tsum_congr hk

theorem native_bound (hc : Summable (curvatureCost a w)) (H : ℝ≥0) (N : ℕ) :
    ‖native a r β w H N‖ ≤ 3*(H:ℝ)*∑' k, curvatureCost a w k := by
  have hn : Summable (fun k => ‖nativeTerm a r β w H N k‖) :=
    (hc.mul_left (3*(H:ℝ))).of_nonneg_of_le (fun _ => norm_nonneg _)
      (nativeTerm_bound a r β w H N)
  calc
    _ ≤ ∑' k, ‖nativeTerm a r β w H N k‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k, 3*(H:ℝ)*curvatureCost a w k :=
      hn.tsum_le_tsum (nativeTerm_bound a r β w H N) (hc.mul_left _)
    _ = _ := tsum_mul_left

theorem reconstruction_congr (a' : ℕ → ι → ℝ) (r' : ι → ℝ≥0) (β' w' : ℕ → ℝ)
    (hv : Summable (fun k => |w k|)) (hc : Summable (curvatureCost a w))
    (hv' : Summable (fun k => |w' k|)) (hc' : Summable (curvatureCost a' w'))
    (H : ℝ≥0) (hH : 0 < H)
    (he : (fun p => value a β w (fun i => IBMConstructedSources.ibmValue (r i) p))
      =ᵐ[IBMSourceLaws.jointMeasure]
      (fun p => value a' β' w' (fun i => IBMConstructedSources.ibmValue (r' i) p))) :
    reconstruction a r β w H = reconstruction a' r' β' w' H := by
  have hj : (observation a r β w : JointL2) = (observation a' r' β' w' : JointL2) := by
    apply Lp.ext
    exact (observation_actual a r β w hv).trans (he.trans (observation_actual a' r' β' w' hv').symm)
  apply IBMRidgeSeriesStrongReconstruction.clockL1_injective
  have ht := source_native_tendsto a r β w hv hc H hH
  rw [hj] at ht
  exact tendsto_nhds_unique ht (source_native_tendsto a' r' β' w' hv' hc' H hH)

end OperatorDerivativeRewrite.Foundation.IBMFourierCylinderSeries
