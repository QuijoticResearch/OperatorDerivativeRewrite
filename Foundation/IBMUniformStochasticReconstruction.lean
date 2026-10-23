import Foundation.IBMCompletedBoundedAssociativity
import Foundation.IBMClockWeakChain
import Mathlib.Topology.UniformSpace.Dini
/-! Locally uniform actual stochastic reconstruction, uniform over causal horizons,
and convergence in the ORIGINAL native divergence graph norm. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology DirectSum
namespace OperatorDerivativeRewrite.Foundation.IBMUniformStochasticReconstruction
open IBMTimeAveragedObservable IBMFixedStochasticFamily IBMMultichannelCompletion
open IBMCompletedCoordinates IBMCompletedTimeCutoff IBMObservedTerminalMartingale
attribute [local instance] componentAdd componentGroup componentModule componentZeroDec
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : DecidableEq basisSet := Classical.decEq _
set_option backward.isDefEq.respectTransparency false

def lift (f : IntrinsicSpace) : Completed fixedFamily := fixedHilbertEquiv.symm (remainder f)

def partialInput (s : Finset basisSet) (f : IntrinsicSpace) : Completed fixedFamily :=
  ∑ i ∈ s, embed fixedFamily (DirectSum.lof ℝ basisSet _ i (coefficient f i • integrand i))

theorem lift_continuous : Continuous lift := by
  apply fixedHilbertEquiv.symm.continuous.comp
  exact (continuous_subtype_val.sub
    ((IBMIntrinsicRightGerm.rightPast 0).starProjection.continuous.comp continuous_subtype_val)).subtype_mk _

theorem coefficient_continuous (i : basisSet) : Continuous (fun f : IntrinsicSpace => coefficient f i) := by
  simp only [coefficient_pairing]
  exact continuous_const.inner continuous_subtype_val

def gap (s : Finset basisSet) (f : IntrinsicSpace) : ℝ :=
  ‖remainder f‖^2-∑ i ∈ s, (coefficient f i)^2

theorem partial_actual (s : Finset basisSet) (f : IntrinsicSpace) :
    completedIntegral fixedFamily (partialInput s f)=
      (∑ i ∈ s, coefficient f i • basis i : remainderSpace) := by
  simp only [partialInput,map_sum,completedIntegral_embed,rawIntegral_single,map_smul]
  change _ = remainderSpace.subtypeL (∑ i ∈ s, coefficient f i • basis i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  exact congrArg (fun v : JointL2 => coefficient f i • v) (integral_integrand i)

theorem error_sq (s : Finset basisSet) (f : IntrinsicSpace) :
    ‖partialInput s f-lift f‖^2=gap s f := by
  have he : ‖(∑ i ∈ s, coefficient f i • basis i : remainderSpace)-remainder f‖^2=gap s f := by
    rw [norm_sub_sq_real]
    have hn := basis.orthonormal.inner_sum (coefficient f) (coefficient f) s
    rw [real_inner_self_eq_norm_sq] at hn
    have hi : inner ℝ (∑ i ∈ s, coefficient f i • basis i) (remainder f)=
        ∑ i ∈ s, (coefficient f i)^2 := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = coefficient f i * inner ℝ (basis i) (remainder f) :=
          real_inner_smul_left (basis i) (remainder f) (coefficient f i)
        _ = _ := by
          rw [← HilbertBasis.repr_apply_apply]
          change coefficient f i * coefficient f i=(coefficient f i)^2
          ring
    simp only [conj_trivial,← pow_two] at hn
    rw [hn,hi]
    unfold gap
    ring
  rw [← (completedIntegral fixedFamily).norm_map,map_sub,partial_actual,
    show completedIntegral fixedFamily (lift f)=(remainder f : JointL2) from fixed_reconstruction f]
  change ‖((∑ i ∈ s, coefficient f i • basis i : remainderSpace) : JointL2)-
    (remainder f : JointL2)‖^2=gap s f
  exact he

theorem gap_continuous (s : Finset basisSet) : Continuous (gap s) := by
  have hc : Continuous (fun f : IntrinsicSpace => remainder f) := by
    exact (continuous_subtype_val.sub
      ((IBMIntrinsicRightGerm.rightPast 0).starProjection.continuous.comp continuous_subtype_val)).subtype_mk _
  exact (hc.norm.pow 2).sub (continuous_finsetSum s (fun i _ => (coefficient_continuous i).pow 2))

theorem gap_antitone (f : IntrinsicSpace) : Antitone (fun s => gap s f) := by
  intro s t hst
  exact sub_le_sub_left (Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => sq_nonneg _)) _

theorem gap_tendsto (f : IntrinsicSpace) : Tendsto (fun s => gap s f) atTop (𝓝 0) := by
  have hc : Tendsto (fun s : Finset basisSet => ∑ i ∈ s, (coefficient f i)^2)
      atTop (𝓝 (‖remainder f‖^2)) := coefficient_energy f
  simpa only [gap,sub_self] using
    (tendsto_const_nhds : Tendsto (fun _ : Finset basisSet => ‖remainder f‖^2) atTop _).sub hc

theorem gap_uniform {α : Type*} [TopologicalSpace α] (u : α → IntrinsicSpace)
    (hu : Continuous u) {K : Set α} (hK : IsCompact K) :
    TendstoUniformlyOn (fun s t => gap s (u t)) (fun _ => 0) atTop K :=
  Antitone.tendstoUniformlyOn_of_forall_tendsto hK
    (fun s => ((gap_continuous s).comp hu).continuousOn)
    (fun t _ => gap_antitone (u t)) continuousOn_const (fun t _ => gap_tendsto (u t))

theorem uniform_input {α : Type*} [TopologicalSpace α] (u : α → IntrinsicSpace)
    (hu : Continuous u) {K : Set α} (hK : IsCompact K) :
    ∀ ε > (0 : ℝ), ∀ᶠ s : Finset basisSet in atTop,
      ∀ t ∈ K, ‖partialInput s (u t)-lift (u t)‖<ε := by
  intro ε hε
  have hg := (Metric.tendstoUniformlyOn_iff.mp (gap_uniform u hu hK)) (ε^2) (sq_pos_of_pos hε)
  filter_upwards [hg] with s hs
  intro t ht
  have hb := hs t ht
  rw [dist_zero_left,Real.norm_eq_abs] at hb
  have hn := error_sq s (u t)
  have hnon : 0 ≤ gap s (u t) := hn ▸ sq_nonneg _
  rw [abs_of_nonneg hnon] at hb
  nlinarith [norm_nonneg (partialInput s (u t)-lift (u t))]

theorem lift_actual (f : IntrinsicSpace) :
    completedIntegral fixedFamily (lift f)=(f : JointL2)-channelClass (f : JointL2) 0 :=
  fixed_reconstruction f

theorem stopped_error (s : Finset basisSet) (r : ℝ≥0) (f : IntrinsicSpace) :
    ‖stop r (partialInput s f)-stop r (lift f)‖ ≤ ‖partialInput s f-lift f‖ := by
  rw [← map_sub]
  exact stop_norm r _

theorem uniform_stopped {α : Type*} [TopologicalSpace α] (u : α → IntrinsicSpace)
    (hu : Continuous u) {K : Set α} (hK : IsCompact K) :
    ∀ ε > (0 : ℝ), ∀ᶠ s : Finset basisSet in atTop,
      ∀ t ∈ K, ∀ r : ℝ≥0, ‖stop r (partialInput s (u t))-stop r (lift (u t))‖<ε := by
  intro ε hε
  filter_upwards [uniform_input u hu hK ε hε] with s hs
  exact fun t ht r => (stopped_error s r (u t)).trans_lt (hs t ht)

def stoppedActual (s : Finset basisSet) (r : ℝ≥0) (f : IntrinsicSpace) : JointL2 :=
  ∑ i ∈ s, IBMFullPredictableIntegral.integral (fixedFamily i)
    (IBMPredictableTimeCutoff.cutoff (fixedFamily i) r (coefficient f i • integrand i))

theorem stoppedActual_eq (s : Finset basisSet) (r : ℝ≥0) (f : IntrinsicSpace) :
    stoppedActual s r f=completedIntegral fixedFamily (stop r (partialInput s f)) := by
  simp only [partialInput,map_sum,stopped_single,completedIntegral_embed,rawIntegral_single,stoppedActual]

theorem stoppedActual_past (s : Finset basisSet) (r : ℝ≥0) (f : IntrinsicSpace) :
    stoppedActual s r f ∈ IBMIntrinsicRightGerm.rightPast r := by
  rw [stoppedActual_eq,stop_integral]
  exact Submodule.starProjection_apply_mem _ _

theorem stopped_lift_actual (r : ℝ≥0) (f : IntrinsicSpace) :
    completedIntegral fixedFamily (stop r (lift f))=
      channelClass (f : JointL2) r-channelClass (f : JointL2) 0 := by
  rw [stop_integral,lift_actual]
  change (IBMIntrinsicRightGerm.rightPast r).starProjection
    ((f : JointL2)-channelClass (f : JointL2) 0)=_
  rw [map_sub]
  have h0 : (IBMIntrinsicRightGerm.rightPast r).starProjection (channelClass (f : JointL2) 0)=
      channelClass (f : JointL2) 0 :=
    Submodule.starProjection_eq_self_iff.mpr
      (IBMRightGermFiltration.rightPast_mono (zero_le : (0 : ℝ≥0) ≤ r)
        (Submodule.starProjection_apply_mem _ _))
  rw [h0]
  rfl

theorem uniform_actual {α : Type*} [TopologicalSpace α] (u : α → IntrinsicSpace)
    (hu : Continuous u) {K : Set α} (hK : IsCompact K) :
    ∀ ε > (0 : ℝ), ∀ᶠ s : Finset basisSet in atTop,
      ∀ t ∈ K, ∀ r : ℝ≥0, ‖stoppedActual s r (u t)-
        (channelClass (u t : JointL2) r-channelClass (u t : JointL2) 0)‖<ε := by
  intro ε hε
  filter_upwards [uniform_stopped u hu hK ε hε] with s hs
  intro t ht r
  rw [stoppedActual_eq,← stopped_lift_actual,← map_sub,(completedIntegral fixedFamily).norm_map]
  exact hs t ht r

theorem actual_IBM_uniform (T : ℝ≥0) :
    ∀ ε > (0 : ℝ), ∀ᶠ s : Finset basisSet in atTop,
      ∀ t ∈ Icc 0 T, ‖stoppedActual s t (intrinsicCurve t)-(intrinsicCurve t : JointL2)‖<ε := by
  intro ε hε
  filter_upwards [uniform_actual intrinsicCurve intrinsicCurve_continuous isCompact_Icc ε hε] with s hs
  intro t ht
  have hb := hs t ht t
  have hT : channelClass (intrinsicCurve t : JointL2) t=(intrinsicCurve t : JointL2) :=
    terminal_class _ (IBMDeterministicRangeObstruction.observed_mem_past t) le_rfl
  have h0 : channelClass (intrinsicCurve t : JointL2) 0=0 :=
    IBMObservedInitialGerm.initial_channel_zero t
  rw [hT,h0,sub_zero] at hb
  exact hb

def nonlinear (φ : IBMClockWeakChain.TestFunction) (t : ℝ≥0) : IntrinsicSpace :=
  ⟨IBMClockWeakChain.value φ (intrinsicCurve t : JointL2),
    IBMIntrinsicChainRule.composition_observable (intrinsicCurve t) _ φ.value
      (IBMClockWeakChain.continuous_value φ) (IBMClockWeakChain.value_ae φ _)⟩

theorem nonlinear_ae (φ : IBMClockWeakChain.TestFunction) (t : ℝ≥0) :
    (nonlinear φ t : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => φ.value (IBMConstructedSources.ibmValue t ω) :=
  (IBMClockWeakChain.value_ae φ _).trans
    ((joint_point_actual_ae t).fun_comp φ.value)

theorem nonlinear_continuous (φ : IBMClockWeakChain.TestFunction) : Continuous (nonlinear φ) :=
  ((IBMClockWeakChain.value_L2_lipschitz φ).continuous.comp
    (continuous_subtype_val.comp intrinsicCurve_continuous)).subtype_mk _

theorem nonlinear_past (φ : IBMClockWeakChain.TestFunction) (t : ℝ≥0) :
    (nonlinear φ t : JointL2) ∈ IBMNaturalFiltrationObstruction.past t :=
  ((IBMClockWeakChain.continuous_value φ).stronglyMeasurable.comp_measurable
    (IBMNaturalFiltrationObstruction.point_stronglyAdapted t).measurable).aestronglyMeasurable.congr
      (nonlinear_ae φ t).symm

theorem nonlinear_uniform (φ : IBMClockWeakChain.TestFunction) (T : ℝ≥0) :
    ∀ ε > (0 : ℝ), ∀ᶠ s : Finset basisSet in atTop,
      ∀ t ∈ Icc 0 T, ‖stoppedActual s t (nonlinear φ t)-
        ((nonlinear φ t : JointL2)-channelClass (nonlinear φ t : JointL2) 0)‖<ε := by
  intro ε hε
  filter_upwards [uniform_actual (nonlinear φ) (nonlinear_continuous φ) isCompact_Icc ε hε] with s hs
  intro t ht
  have hb := hs t ht t
  rw [terminal_class _ (nonlinear_past φ t) le_rfl] at hb
  exact hb

theorem native_error (s : Finset basisSet) (f : IntrinsicSpace) :
    ‖IBMCompletedNativeCalculus.transfer fixedFamily (partialInput s f)-
      IBMCompletedNativeCalculus.transfer fixedFamily (lift f)‖ ≤ 2*‖partialInput s f-lift f‖ := by
  rw [← map_sub]
  have hb := IBMCompletedNativeCalculus.transfer_bound fixedFamily (partialInput s f-lift f)
  nlinarith [norm_nonneg (IBMCompletedNativeCalculus.transfer fixedFamily (partialInput s f-lift f)),
    norm_nonneg (partialInput s f-lift f),sq_nonneg (‖partialInput s f-lift f‖)]

attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative

def nativeGraphDistance (V W : IBMJointIntrinsicDerivative.jointDivergence.domain) : ℝ :=
  ‖(V : IBMJointIntrinsicDerivative.JointFieldSpace)-(W : IBMJointIntrinsicDerivative.JointFieldSpace)‖+
    ‖IBMJointIntrinsicDerivative.jointDivergence V-IBMJointIntrinsicDerivative.jointDivergence W‖

theorem native_graph_distance (z w : Completed fixedFamily) :
    nativeGraphDistance (IBMCompletedNativeCalculus.nativeTest fixedFamily z)
      (IBMCompletedNativeCalculus.nativeTest fixedFamily w) ≤ 3*‖z-w‖ := by
  have hd : IBMJointIntrinsicDerivative.jointDivergence
      (IBMCompletedNativeCalculus.nativeTest fixedFamily z)=IBMCompletedNativeCalculus.observable fixedFamily z :=
    IBMCompletedNativeCalculus.transfer_divergence fixedFamily z
  have he : IBMJointIntrinsicDerivative.jointDivergence
      (IBMCompletedNativeCalculus.nativeTest fixedFamily w)=IBMCompletedNativeCalculus.observable fixedFamily w :=
    IBMCompletedNativeCalculus.transfer_divergence fixedFamily w
  unfold nativeGraphDistance
  rw [hd,he]
  change ‖IBMCompletedNativeCalculus.transfer fixedFamily z-IBMCompletedNativeCalculus.transfer fixedFamily w‖+
    ‖completedIntegral fixedFamily z-completedIntegral fixedFamily w‖ ≤ _
  have hJ : ‖completedIntegral fixedFamily z-completedIntegral fixedFamily w‖=‖z-w‖ :=
    (congrArg Norm.norm ((completedIntegral fixedFamily).map_sub z w).symm).trans
      ((completedIntegral fixedFamily).norm_map (z-w))
  have hT : ‖IBMCompletedNativeCalculus.transfer fixedFamily z-
      IBMCompletedNativeCalculus.transfer fixedFamily w‖=
      ‖IBMCompletedNativeCalculus.transfer fixedFamily (z-w)‖ :=
    congrArg Norm.norm ((IBMCompletedNativeCalculus.transfer fixedFamily).map_sub z w).symm
  have hb := IBMCompletedNativeCalculus.transfer_bound fixedFamily (z-w)
  have hb' : ‖IBMCompletedNativeCalculus.transfer fixedFamily (z-w)‖ ≤ 2*‖z-w‖ := by
    nlinarith [norm_nonneg (IBMCompletedNativeCalculus.transfer fixedFamily (z-w)),norm_nonneg (z-w),sq_nonneg ‖z-w‖]
  exact (add_le_add (hT.le.trans hb') hJ.le).trans_eq (by ring)

theorem uniform_native_graph {α : Type*} [TopologicalSpace α] (u : α → IntrinsicSpace)
    (hu : Continuous u) {K : Set α} (hK : IsCompact K) :
    ∀ ε > (0 : ℝ), ∀ᶠ s : Finset basisSet in atTop, ∀ t ∈ K, ∀ r : ℝ≥0,
      nativeGraphDistance
        (IBMCompletedNativeCalculus.nativeTest fixedFamily (stop r (partialInput s (u t))))
        (IBMCompletedNativeCalculus.nativeTest fixedFamily (stop r (lift (u t))))<ε := by
  intro ε hε
  filter_upwards [uniform_stopped u hu hK (ε/3) (by positivity)] with s hs
  intro t ht r
  have hb := native_graph_distance (stop r (partialInput s (u t))) (stop r (lift (u t)))
  have hh := hs t ht r
  linarith

end OperatorDerivativeRewrite.Foundation.IBMUniformStochasticReconstruction
-- Norm convergence above does not assert a samplewise supremum topology.
