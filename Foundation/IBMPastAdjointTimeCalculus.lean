import Foundation.IBMAverageNativeTimeObstruction
import Mathlib.Analysis.Normed.Operator.NormedSpace
/-! Ordinary-time differentiation of actual IBM averages in the dual of the
original adjoint graph, and in the dual of the maximal adjoint on each FIXED raw
observed past. Endpoint differentiation uses only left time increments.
The dual limit has an actual joint-law pairing but no original native-field
representative at positive times. Native left-slope norms escape to infinity.
These are adjoint-test-dual identities, not a physical-time Ito or Clark--Ocone
formula, a new predictable driver, or an enlargement of the original domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPastAdjointTimeCalculus
open OperatorDerivativeRewrite.Foundation
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMRampSimpsonNativeAverage
open IBMIntrinsicGraphDual
attribute [local irreducible] IBMJointIntrinsicDerivative.jointDerivative
  IBMIntrinsicGraphDual.weakDerivative IBMIntrinsicGraphDual.embed
  IBMRampSimpsonNativeAverage.averageGradient
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
local instance : NormedAddCommGroup (StrongDual ℝ Tests) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := Tests) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ (StrongDual ℝ Tests) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := Tests) (F := ℝ) (σ₁₂ := RingHom.id ℝ)

theorem average_graphDual_hasDerivAt {T : ℝ} (hT : 0 < T) :
    HasDerivAt (fun t : ℝ => embed (averageGradient t.toNNReal))
      (pointDerivative T.toNNReal) T := by
  have hc : HasFDerivAt (fun f : IntrinsicSpace => weakDerivative f) weakDerivative
      (intrinsicAverage (T.toNNReal:ℝ)) := weakDerivative.hasFDerivAt
  have h := HasFDerivAt.comp_hasDerivAt
    (f := fun t : ℝ => intrinsicAverage (t.toNNReal:ℝ))
    (l := fun f : IntrinsicSpace => weakDerivative f) (l' := weakDerivative) T hc
    (IBMAverageNativeTimeObstruction.actual_average_hasDerivAt hT)
  simpa only [Function.comp_def, ← averageGradient_embed, pointDerivative] using h

theorem actual_adjoint_time_pairing {T : ℝ} (hT : 0 < T)
    (v : jointDivergence.domain) :
    HasDerivAt (fun t : ℝ => embed (averageGradient t.toNNReal) (testOf v))
      (∫ ω, IBMConstructedSources.ibmValue T.toNNReal ω *
        ((jointDivergence v : IntrinsicSpace) : JointL2) ω ∂IBMSourceLaws.jointMeasure) T := by
  have hc : HasFDerivAt (fun L : StrongDual ℝ Tests => L (testOf v))
      (ContinuousLinearMap.apply ℝ ℝ (testOf v)) (embed (averageGradient T.toNNReal)) :=
    (ContinuousLinearMap.apply ℝ ℝ (testOf v)).hasFDerivAt
  have h := HasFDerivAt.comp_hasDerivAt
    (f := fun t : ℝ => embed (averageGradient t.toNNReal))
    (l := fun L : StrongDual ℝ Tests => L (testOf v))
    (l' := ContinuousLinearMap.apply ℝ ℝ (testOf v)) T hc (average_graphDual_hasDerivAt hT)
  simpa only [Function.comp_def, ContinuousLinearMap.apply_apply,
    point_actual_pairing] using h

theorem dual_slope_convergence {T : ℝ} (hT : 0 < T) (e : ℕ → ℝ)
    (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => embed ((e n)⁻¹ •
      (averageGradient (T+e n).toNNReal-averageGradient T.toNNReal))) atTop
      (𝓝 (pointDerivative T.toNNReal)) := by
  have h := (average_graphDual_hasDerivAt hT).tendsto_slope_zero_right.comp
    (tendsto_nhdsWithin_iff.mpr ⟨he0,Eventually.of_forall he⟩)
  simpa only [Function.comp_def, map_smul, map_sub] using h

open IBMPastIntrinsicOperators
local instance (H : ℝ≥0) : CompleteSpace (pastSpace H) :=
  (pastSpace_closed H).completeSpace_coe

theorem past_adjoint_average_pairing (H : ℝ≥0) (v : (pastDivergence H).domain)
    (t : ℝ) (ht : t ≤ H) :
    inner ℝ (v : JointFieldSpace) (averageGradient t.toNNReal) =
      inner ℝ ((pastDivergence H v : pastSpace H) : IntrinsicSpace)
        (intrinsicAverage (t.toNNReal:ℝ)) := by
  let a : pastSpace H := ⟨intrinsicAverage (t.toNNReal:ℝ), by
    change (intrinsicAverage (t.toNNReal:ℝ) : JointL2) ∈ IBMNaturalFiltrationObstruction.past H
    rw [← nativeAverage_eq_intrinsicAverage]
    exact IBMPastAverageCore.nativeAverage_mem_past
      (Real.toNNReal_le_iff_le_coe.mpr ht)⟩
  have ha : a ∈ (pastDerivative H).domain := average_mem_joint_domain t.toNNReal
  have h := IBMPastIntrinsicOperators.integration_by_parts H v ⟨a,ha⟩
  have hd : pastDerivative H ⟨a,ha⟩ = averageGradient t.toNNReal := by
    unfold averageGradient
    rfl
  rw [hd] at h
  change inner ℝ ((pastDivergence H v : pastSpace H) : IntrinsicSpace)
    (intrinsicAverage (t.toNNReal:ℝ)) =
      inner ℝ (v : JointFieldSpace) (averageGradient t.toNNReal) at h
  exact h.symm

theorem past_adjoint_left_time_derivative (H : ℝ≥0) (v : (pastDivergence H).domain)
    {T : ℝ} (hT : 0 < T) (hTH : T ≤ H) :
    HasDerivWithinAt (fun t : ℝ => inner ℝ (v : JointFieldSpace) (averageGradient t.toNNReal))
      (inner ℝ ((pastDivergence H v : pastSpace H) : IntrinsicSpace)
        (intrinsicCurve T.toNNReal)) (Set.Iic (H:ℝ)) T := by
  have h := (innerSL ℝ ((pastDivergence H v : pastSpace H) : IntrinsicSpace)).hasFDerivAt.comp_hasDerivAt T
    (IBMAverageNativeTimeObstruction.actual_average_hasDerivAt hT)
  apply h.hasDerivWithinAt.congr
  · intro t ht
    exact past_adjoint_average_pairing H v t ht
  · exact past_adjoint_average_pairing H v T hTH

attribute [local irreducible] IBMPastIntrinsicOperators.pastDerivative
  IBMPastIntrinsicOperators.pastSpace

abbrev PastTests (H : ℝ≥0) := ClosedOperatorGraphDualDerivative.Tests
  (E := pastSpace H) (F := JointFieldSpace) (pastDerivative H) (pastDerivative_dense H)


local instance (H : ℝ≥0) : NormedAddCommGroup (PastTests H) :=
  ClosedSubmodule.normedAddCommGroup (𝕜 := ℝ) (E := WithLp 2 (JointFieldSpace × pastSpace H))
    (ClosedOperatorEnergyResolvent.graphSpace (E := JointFieldSpace) (F := pastSpace H)
      (pastDivergence H) (pastDivergence_closed H))
local instance (H : ℝ≥0) : NormedSpace ℝ (PastTests H) :=
  ClosedSubmodule.normedSpace (𝕜 := ℝ) (R := ℝ) (E := WithLp 2 (JointFieldSpace × pastSpace H))
    (ClosedOperatorEnergyResolvent.graphSpace (E := JointFieldSpace) (F := pastSpace H)
      (pastDivergence H) (pastDivergence_closed H))

local instance (H : ℝ≥0) : NormedAddCommGroup (StrongDual ℝ (PastTests H)) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PastTests H) (F := ℝ) (σ₁₂ := RingHom.id ℝ)
local instance (H : ℝ≥0) : NormedSpace ℝ (StrongDual ℝ (PastTests H)) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PastTests H) (F := ℝ) (σ₁₂ := RingHom.id ℝ)

def pastEmbed (H : ℝ≥0) :=
  ClosedOperatorGraphDualDerivative.embed (E := pastSpace H) (F := JointFieldSpace)
    (pastDerivative H) (pastDerivative_dense H)

def pastWeak (H : ℝ≥0) :=
  (ClosedOperatorGraphDualDerivative.derivative (E := pastSpace H) (F := JointFieldSpace)
    (pastDerivative H) (pastDerivative_dense H)).comp
    (pastSpace H).orthogonalProjectionOnto

attribute [local irreducible] pastEmbed pastWeak
  ClosedOperatorGraphDualDerivative.embed ClosedOperatorGraphDualDerivative.derivative

def pastAverage (H : ℝ≥0) (t : ℝ) (ht : t ≤ H) : pastSpace H :=
  ⟨intrinsicAverage (t.toNNReal:ℝ), by
    unfold pastSpace
    change (intrinsicAverage (t.toNNReal:ℝ) : JointL2) ∈ IBMNaturalFiltrationObstruction.past H
    rw [← nativeAverage_eq_intrinsicAverage]
    exact IBMPastAverageCore.nativeAverage_mem_past (Real.toNNReal_le_iff_le_coe.mpr ht)⟩

theorem pastAverage_domain (H : ℝ≥0) (t : ℝ) (ht : t ≤ H) :
    pastAverage H t ht ∈ (pastDerivative H).domain := by
  unfold pastDerivative pastAverage
  exact average_mem_joint_domain t.toNNReal

theorem pastAverage_gradient (H : ℝ≥0) (t : ℝ) (ht : t ≤ H) :
    pastDerivative H ⟨pastAverage H t ht,pastAverage_domain H t ht⟩ = averageGradient t.toNNReal := by
  unfold pastDerivative averageGradient pastAverage
  rfl

theorem pastAverage_projection (H : ℝ≥0) (t : ℝ) (ht : t ≤ H) :
    (pastSpace H).orthogonalProjectionOnto (intrinsicAverage (t.toNNReal:ℝ)) = pastAverage H t ht :=
  (pastSpace H).orthogonalProjectionOnto_mem_subspace_eq_self (pastAverage H t ht)

theorem past_average_graph (H : ℝ≥0) (t : ℝ) (ht : t ≤ H) :
    pastEmbed H (averageGradient t.toNNReal) = pastWeak H (intrinsicAverage (t.toNNReal:ℝ)) := by
  have h := ClosedOperatorGraphDualDerivative.graph_agreement (E := pastSpace H) (F := JointFieldSpace)
    (pastDerivative H) (pastDerivative_dense H)
    ((pastDerivative H).mem_graph ⟨pastAverage H t ht,pastAverage_domain H t ht⟩)
  have he := congrArg
    (ClosedOperatorGraphDualDerivative.embed (E := pastSpace H) (F := JointFieldSpace)
      (pastDerivative H) (pastDerivative_dense H)) (pastAverage_gradient H t ht).symm
  have hp := congrArg
    (ClosedOperatorGraphDualDerivative.derivative (E := pastSpace H) (F := JointFieldSpace)
      (pastDerivative H) (pastDerivative_dense H)) (pastAverage_projection H t ht).symm
  unfold pastWeak pastEmbed
  exact he.trans (h.trans hp)


theorem full_past_dual_time_derivative (H : ℝ≥0) {T : ℝ} (hT : 0 < T) (hTH : T ≤ H) :
    HasDerivWithinAt (fun t : ℝ => pastEmbed H (averageGradient t.toNNReal))
      (pastWeak H (intrinsicCurve T.toNNReal)) (Set.Iic (H:ℝ)) T := by
  have h := HasFDerivAt.comp_hasDerivAt
    (f := fun t : ℝ => intrinsicAverage (t.toNNReal:ℝ))
    (l := fun f : IntrinsicSpace => pastWeak H f) (l' := pastWeak H) T
    (pastWeak H).hasFDerivAt (IBMAverageNativeTimeObstruction.actual_average_hasDerivAt hT)
  apply h.hasDerivWithinAt.congr
  · intro t ht
    exact past_average_graph H t ht
  · exact past_average_graph H T hTH

def pastPoint (H T : ℝ≥0) (hTH : T ≤ H) : pastSpace H :=
  ⟨intrinsicCurve T, by
    unfold pastSpace
    exact IBMPastAverageCore.point_mem_past hTH⟩

theorem pastPoint_projection (H T : ℝ≥0) (hTH : T ≤ H) :
    (pastSpace H).orthogonalProjectionOnto (intrinsicCurve T) = pastPoint H T hTH :=
  (pastSpace H).orthogonalProjectionOnto_mem_subspace_eq_self (pastPoint H T hTH)

theorem past_point_not_native (H T : ℝ≥0) (hT : 0 < T) (hTH : T ≤ H) :
    ¬ ∃ V : JointFieldSpace, pastEmbed H V = pastWeak H (intrinsicCurve T) := by
  rintro ⟨V,hV⟩
  unfold pastEmbed pastWeak at hV
  have hp := congrArg
    (ClosedOperatorGraphDualDerivative.derivative (E := pastSpace H) (F := JointFieldSpace)
      (pastDerivative H) (pastDerivative_dense H)) (pastPoint_projection H T hTH)
  have hm := (ClosedOperatorGraphDualDerivative.representable_iff_domain
    (E := pastSpace H) (F := JointFieldSpace)
    (pastDerivative H) (pastDerivative_closed H) (pastDerivative_dense H)
    (pastPoint H T hTH)).mp ⟨V,hV.trans hp⟩
  have hx : intrinsicCurve T ∈ jointDerivative.domain := by
    unfold pastDerivative pastPoint at hm
    exact hm
  exact IBMPointClockDomainObstruction.actual_point_not_joint_domain T hT hx

def pastTestOf (H : ℝ≥0) (v : (pastDivergence H).domain) :=
  ClosedOperatorGraphDualDerivative.testOf (E := pastSpace H) (F := JointFieldSpace)
    (pastDerivative H) (pastDerivative_dense H) v

theorem past_test_pairing (H : ℝ≥0) (f : IntrinsicSpace) (v : (pastDivergence H).domain) :
    pastWeak H f (pastTestOf H v) =
      inner ℝ f ((pastDivergence H v : pastSpace H) : IntrinsicSpace) := by
  have h := ClosedOperatorGraphDualDerivative.derivative_original_test
    (E := pastSpace H) (F := JointFieldSpace) (pastDerivative H) (pastDerivative_dense H)
    ((pastSpace H).orthogonalProjectionOnto f) v
  have hp := (pastSpace H).inner_orthogonalProjectionOnto_eq_of_mem_right (pastDivergence H v) f
  unfold pastWeak pastTestOf
  exact h.trans hp

theorem past_point_actual_pairing (H T : ℝ≥0) (v : (pastDivergence H).domain) :
    pastWeak H (intrinsicCurve T) (pastTestOf H v) =
      ∫ ω, IBMConstructedSources.ibmValue T ω *
        (((pastDivergence H v : pastSpace H) : IntrinsicSpace) : JointL2) ω
          ∂IBMSourceLaws.jointMeasure := by
  rw [past_test_pairing H (intrinsicCurve T) v]
  change inner ℝ (intrinsicCurve T : JointL2)
    (((pastDivergence H v : pastSpace H) : IntrinsicSpace) : JointL2) = _
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [joint_point_actual_ae T] with ω hω
  change (intrinsicCurve T : JointL2) ω = IBMConstructedSources.ibmValue T ω at hω
  rw [hω, Real.inner_apply]

theorem past_slope_graph (H : ℝ≥0) (T e : ℝ) (hTH : T ≤ H) (he : e ≤ 0) :
    pastEmbed H (e⁻¹ • (averageGradient (T+e).toNNReal-averageGradient T.toNNReal)) =
      e⁻¹ • (pastWeak H (intrinsicAverage ((T+e).toNNReal:ℝ))-
        pastWeak H (intrinsicAverage (T.toNNReal:ℝ))) := by
  have h1 := past_average_graph H (T+e) (by linarith)
  have h0 := past_average_graph H T hTH
  have hx := congrArg₂ (fun x y : StrongDual ℝ (PastTests H) => e⁻¹ • (x-y)) h1 h0
  exact ((pastEmbed H).map_smul e⁻¹ _).trans
    ((congrArg (fun x => e⁻¹ • x) ((pastEmbed H).map_sub _ _)).trans hx)

theorem past_left_slope_convergence (H : ℝ≥0) {T : ℝ} (hT : 0 < T) (hTH : T ≤ H)
    (e : ℕ → ℝ) (he : ∀ n, e n < 0) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => pastEmbed H ((e n)⁻¹ •
      (averageGradient (T+e n).toNNReal-averageGradient T.toNNReal))) atTop
      (𝓝 (pastWeak H (intrinsicCurve T.toNNReal))) := by
  have hd := HasFDerivAt.comp_hasDerivAt
    (f := fun t : ℝ => intrinsicAverage (t.toNNReal:ℝ))
    (l := fun f : IntrinsicSpace => pastWeak H f) (l' := pastWeak H) T
    (pastWeak H).hasFDerivAt (IBMAverageNativeTimeObstruction.actual_average_hasDerivAt hT)
  have hs := hd.tendsto_slope_zero_left.comp
    (tendsto_nhdsWithin_iff.mpr ⟨he0,Eventually.of_forall he⟩)
  apply hs.congr'
  exact Eventually.of_forall fun n => (past_slope_graph H T (e n) hTH (he n).le).symm

theorem native_left_slope_escape {T : ℝ} (hT : 0 < T) (e : ℕ → ℝ)
    (he : ∀ n, e n < 0) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ‖(e n)⁻¹ •
      (averageGradient (T+e n).toNNReal-averageGradient T.toNNReal)‖) atTop atTop := by
  have hm (t : ℝ) : (intrinsicAverage (t.toNNReal:ℝ),averageGradient t.toNNReal) ∈
      jointDerivative.graph := by
    unfold averageGradient
    exact jointDerivative.mem_graph ⟨_,average_mem_joint_domain t.toNNReal⟩
  have hs := (IBMAverageNativeTimeObstruction.actual_average_hasDerivAt hT).tendsto_slope_zero_left.comp
    (tendsto_nhdsWithin_iff.mpr ⟨he0,Eventually.of_forall he⟩)
  exact ClosedOperatorEscapeEnergy.output_norm_tendsto_atTop jointDerivative
    jointDerivative_closed jointDerivative_dense
    (fun n => jointDerivative.graph.smul_mem (e n)⁻¹
      (jointDerivative.graph.sub_mem (hm (T+e n)) (hm T))) hs
    (IBMPointClockDomainObstruction.actual_point_not_joint_domain T.toNNReal
      (Real.toNNReal_pos.mpr hT))

end OperatorDerivativeRewrite.Foundation.IBMPastAdjointTimeCalculus
