import Foundation.IBMPastSourceRepresentation

/-! Identification of nested observable projections with actual IBM conditional
expectation, and native divergence approximation in that actual L2 topology. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPastConditionalDivergence
open IBMTimeAveragedObservable IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMPastIntrinsicOperators IBMPastDivergenceClosure
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.ibmValue IBMConstructedSources.clockPath
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
local instance (T : ℝ≥0) : CompleteSpace (pastSpace T) :=
  (pastSpace_closed T).completeSpace_coe

def projectJoint (T : ℝ≥0) : JointL2 →L[ℝ] pastSpace T :=
  (pastSpace T).orthogonalProjectionOnto.comp IntrinsicSpace.orthogonalProjectionOnto

theorem projection_eq_condExp (T : ℝ≥0) (f : JointL2) :
    ((projectJoint T f).val : JointL2) =
      (condExpL2 ℝ ℝ (IBMNaturalFiltrationObstruction.naturalFiltration.le T) f : JointL2) := by
  let : CompleteSpace (IBMNaturalFiltrationObstruction.past T) :=
    (IBMNaturalFiltrationObstruction.past_closed T).completeSpace_coe
  change ((projectJoint T f).val : JointL2) =
    (IBMNaturalFiltrationObstruction.past T).starProjection f
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (show ((projectJoint T f).val : JointL2) ∈ IBMNaturalFiltrationObstruction.past T from
      (projectJoint T f).property)
  intro w hw
  let wi : IntrinsicSpace := ⟨w, IBMPastCoreDensity.past_le_intrinsic T hw⟩
  let wp : pastSpace T := ⟨wi, hw⟩
  have hp := (pastSpace T).inner_orthogonalProjectionOnto_eq_of_mem_right wp
    (IntrinsicSpace.orthogonalProjectionOnto f)
  have hi := IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right wi f
  have he : inner ℝ ((projectJoint T f).val : JointL2) w = inner ℝ f w := hp.trans hi
  rw [inner_sub_left, he, sub_self]

theorem projection_ae_condExp (T : ℝ≥0) (f : JointL2) :
    ((projectJoint T f).val : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      IBMSourceLaws.jointMeasure[f | IBMNaturalFiltrationObstruction.naturalFiltration T] := by
  rw [projection_eq_condExp]
  simpa only [Lp.toLp_coeFn] using (Lp.memLp f).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) (IBMNaturalFiltrationObstruction.naturalFiltration.le T)

set_option maxHeartbeats 800000 in
-- Graph witnesses carry the actual source adjoints and nested L2 inclusions.
/-- Every maximal past integrand is approximated by genuine source pairs,
with the conditional expectation of their SUM converging strongly in actual L2. -/
theorem full_graph_actual_condExp (T : ℝ≥0) (u : (pastDivergence T).domain) :
    ∃ (a : ℕ → sourceDerivative.adjoint.domain) (b : ℕ → clockDerivative.adjoint.domain),
      Tendsto (fun n => pairField (a n) (b n)) atTop (𝓝 (u : JointFieldSpace)) ∧
      Tendsto (fun n => (condExpL2 ℝ ℝ
        (IBMNaturalFiltrationObstruction.naturalFiltration.le T)
        (sourceDerivative.adjoint (a n) + clockDerivative.adjoint (b n)) : JointL2))
        atTop (𝓝 ((pastDivergence T u).val : JointL2)) := by
  obtain ⟨a, b, ha, hb⟩ := full_native_graph_approximation T u
  let embed : pastSpace T →L[ℝ] JointL2 :=
    IntrinsicSpace.subtypeL.comp (pastSpace T).subtypeL
  have ht := (embed.continuous.tendsto (pastDivergence T u)).comp hb
  refine ⟨a, b, ha, ht.congr' (Eventually.of_forall fun n => ?_)⟩
  exact projection_eq_condExp T _

set_option maxHeartbeats 800000 in
-- Closed graph membership retains native pair-domain witnesses and actual L2 inclusions.
theorem strong_graph_actual_condExp (T : ℝ≥0)
    (a : ℕ → sourceDerivative.adjoint.domain) (b : ℕ → clockDerivative.adjoint.domain)
    (u : JointFieldSpace) (v : pastSpace T)
    (hu : Tendsto (fun n => pairField (a n) (b n)) atTop (𝓝 u))
    (hv : Tendsto (fun n => (condExpL2 ℝ ℝ
      (IBMNaturalFiltrationObstruction.naturalFiltration.le T)
      (sourceDerivative.adjoint (a n) + clockDerivative.adjoint (b n)) : JointL2))
      atTop (𝓝 (v.val : JointL2))) :
    ∃ h : u ∈ (pastDivergence T).domain, pastDivergence T ⟨u, h⟩ = v := by
  have hp : Tendsto (fun n => projectJoint T
      (sourceDerivative.adjoint (a n) + clockDerivative.adjoint (b n))) atTop (𝓝 v) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have ht := tendsto_iff_norm_sub_tendsto_zero.mp hv
    apply ht.congr' (Eventually.of_forall fun n => ?_)
    have he := projection_eq_condExp T
      (sourceDerivative.adjoint (a n) + clockDerivative.adjoint (b n))
    rw [← he]
    rfl
  have hg : (u, v) ∈ (pastDivergence T).graph := by
    apply (pastDivergence_closed T).mem_of_tendsto (hu.prodMk_nhds hp)
    apply Eventually.of_forall
    intro n
    have hn := LinearPMap.le_graph_of_le (nativePair_le T)
      ((nativePair T).mem_graph
        ⟨pairField (a n) (b n), IBMIntrinsicDivergenceClosure.pair_mem (a n) (b n)⟩)
    have he : nativePair T
        ⟨pairField (a n) (b n), IBMIntrinsicDivergenceClosure.pair_mem (a n) (b n)⟩ =
          projectJoint T (sourceDerivative.adjoint (a n) + clockDerivative.adjoint (b n)) := by
      change (pastSpace T).orthogonalProjectionOnto
        (IBMIntrinsicDivergenceClosure.ambientPairOperator _) = _
      rw [IBMIntrinsicDivergenceClosure.pair_value]
      rfl
    rw [he] at hn
    exact hn
  have h := LinearPMap.mem_domain_of_mem_graph hg
  exact ⟨h, ((pastDivergence T).image_iff h).mpr hg |>.symm⟩

end OperatorDerivativeRewrite.Foundation.IBMPastConditionalDivergence
