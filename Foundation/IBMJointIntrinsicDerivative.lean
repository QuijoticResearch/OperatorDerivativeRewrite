import Foundation.IBMIntrinsicOperators

/-! The actual two-channel intrinsic IBM derivative with its full intersection
domain and Hilbert adjoint. Channel zero is scenery; channel one is clock. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMJointIntrinsicDerivative
open InfiniteGaussian IBMTimeAveragedObservable IBMFiniteAverageCore IBMIntrinsicCoreDensity
open IBMIntrinsicOperators
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable IBMConstructedSources.clockPath_measurable).completeSpace_coe

abbrev JointFieldSpace := PiLp 2 (fun _ : Fin 2 => FieldSpace)

def jointDerivative : IntrinsicSpace →ₗ.[ℝ] JointFieldSpace where
  domain := intrinsicSource.domain ⊓ intrinsicClock.domain
  toFun := {
    toFun := fun f => WithLp.toLp 2 ![intrinsicSource ⟨f.val, f.property.1⟩,
      intrinsicClock ⟨f.val, f.property.2⟩]
    map_add' f g := by
      apply PiLp.ext
      intro i
      fin_cases i
      · change intrinsicSource (⟨f.val, f.property.1⟩ + ⟨g.val, g.property.1⟩) = _
        exact intrinsicSource.map_add _ _
      · change intrinsicClock (⟨f.val, f.property.2⟩ + ⟨g.val, g.property.2⟩) = _
        exact intrinsicClock.map_add _ _
    map_smul' c f := by
      apply PiLp.ext
      intro i
      fin_cases i
      · change intrinsicSource (c • ⟨f.val, f.property.1⟩) = _
        exact intrinsicSource.map_smul c _
      · change intrinsicClock (c • ⟨f.val, f.property.2⟩) = _
        exact intrinsicClock.map_smul c _ }

theorem joint_domain_iff (f : IntrinsicSpace) :
    f ∈ jointDerivative.domain ↔ (f : JointL2) ∈ intrinsicCore := by
  change (f ∈ intrinsicSource.domain ∧ f ∈ intrinsicClock.domain) ↔ _
  rw [mem_intrinsicCore_iff]
  change (_ ∧ _) ↔ (f.val ∈ IntrinsicSpace ∧ _ ∧ _)
  exact ⟨fun h => ⟨f.property, h.2, h.1⟩, fun h => ⟨h.2.2, h.2.1⟩⟩

theorem joint_graph_iff (f : IntrinsicSpace) (g : JointFieldSpace) :
    (f, g) ∈ jointDerivative.graph ↔
      (f, g 0) ∈ intrinsicSource.graph ∧ (f, g 1) ∈ intrinsicClock.graph := by
  constructor
  · intro h
    obtain ⟨u, hu, hv⟩ := jointDerivative.mem_graph_iff.mp h
    change (u : IntrinsicSpace) = f at hu
    change jointDerivative u = g at hv
    subst f
    constructor
    · exact intrinsicSource.mem_graph_iff.mpr ⟨⟨u.val, u.property.1⟩, rfl, congrArg (fun v => v 0) hv⟩
    · exact intrinsicClock.mem_graph_iff.mpr ⟨⟨u.val, u.property.2⟩, rfl, congrArg (fun v => v 1) hv⟩
  · rintro ⟨hs, hc⟩
    have hfs := LinearPMap.mem_domain_of_mem_graph hs
    have hfc := LinearPMap.mem_domain_of_mem_graph hc
    refine jointDerivative.mem_graph_iff.mpr ⟨⟨f, hfs, hfc⟩, rfl, ?_⟩
    apply PiLp.ext
    intro i
    fin_cases i
    · exact ((intrinsicSource.image_iff hfs).mpr hs).symm
    · exact ((intrinsicClock.image_iff hfc).mpr hc).symm

theorem jointDerivative_closed : jointDerivative.IsClosed := by
  have he : (jointDerivative.graph : Set (IntrinsicSpace × JointFieldSpace)) =
      (fun z : IntrinsicSpace × JointFieldSpace => (z.1, z.2 0)) ⁻¹'
          (intrinsicSource.graph : Set (IntrinsicSpace × FieldSpace)) ∩
        (fun z : IntrinsicSpace × JointFieldSpace => (z.1, z.2 1)) ⁻¹'
          (intrinsicClock.graph : Set (IntrinsicSpace × FieldSpace)) := by
    ext z
    exact joint_graph_iff z.1 z.2
  change IsClosed (jointDerivative.graph : Set (IntrinsicSpace × JointFieldSpace))
  rw [he]
  exact (intrinsicSource_closed.preimage (continuous_fst.prodMk
    ((continuous_apply 0).comp ((PiLp.continuous_ofLp (p := 2)
      (fun _ : Fin 2 => FieldSpace)).comp continuous_snd)))).inter
    (intrinsicClock_closed.preimage (continuous_fst.prodMk
    ((continuous_apply 1).comp ((PiLp.continuous_ofLp (p := 2)
      (fun _ : Fin 2 => FieldSpace)).comp continuous_snd))))

theorem jointDerivative_dense : Dense (jointDerivative.domain : Set IntrinsicSpace) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  simp only [Submodule.mem_orthogonal']
  intro g hg
  apply Subtype.ext
  apply intrinsic_annihilator_zero (g : JointL2) _ g.property
  rw [Submodule.mem_orthogonal']
  intro f hf
  let fi : IntrinsicSpace := ⟨f, ((mem_intrinsicCore_iff f).mp hf).1⟩
  exact hg fi ((joint_domain_iff fi).mpr hf)

/-- Genuine intrinsic divergence, with its naturally determined adjoint domain. -/
abbrev jointDivergence := jointDerivative.adjoint

def pairField (a b : FieldSpace) : JointFieldSpace := WithLp.toLp 2 ![a, b]

theorem joint_adjoint_pair (a : intrinsicSource.adjoint.domain) (b : intrinsicClock.adjoint.domain) :
    ∃ hp : pairField a b ∈ jointDivergence.domain,
      jointDivergence ⟨pairField a b, hp⟩ = intrinsicSource.adjoint a + intrinsicClock.adjoint b := by
  let P := intrinsicSource.adjoint a + intrinsicClock.adjoint b
  have hpair (f : jointDerivative.domain) :
      inner ℝ P (f : IntrinsicSpace) = inner ℝ (pairField a b) (jointDerivative f) := by
    have hs := intrinsicSource.adjoint_isFormalAdjoint intrinsicSource_dense a ⟨f.val, f.property.1⟩
    have hc := intrinsicClock.adjoint_isFormalAdjoint intrinsicClock_dense b ⟨f.val, f.property.2⟩
    simpa [P, inner_add_left, pairField, jointDerivative, PiLp.inner_apply, Fin.sum_univ_two] using
      congrArg₂ (fun x y : ℝ => x + y) hs hc
  have hp : pairField a b ∈ jointDivergence.domain :=
    (mem_adjoint_domain_iff_representable jointDerivative jointDerivative_dense _).mpr ⟨P, hpair⟩
  exact ⟨hp, jointDerivative.adjoint_apply_eq jointDerivative_dense _ hpair⟩

/-- The manuscript's projected-sum formula on the LIFTED AMBIENT divergence
domain. No equality with the full intrinsic adjoint domain is assumed. -/
theorem ambient_pair_divergence (a : sourceDerivative.adjoint.domain) (b : clockDerivative.adjoint.domain) :
    ∃ hp : pairField a b ∈ jointDivergence.domain,
      jointDivergence ⟨pairField a b, hp⟩ =
        IntrinsicSpace.orthogonalProjectionOnto (sourceDerivative.adjoint a + clockDerivative.adjoint b) := by
  obtain ⟨hp, hv⟩ := joint_adjoint_pair
    ⟨(a : FieldSpace), source_source_divergence_mem a⟩
    ⟨(b : FieldSpace), clock_source_divergence_mem b⟩
  refine ⟨hp, ?_⟩
  rw [hv, intrinsic_source_divergence_value, intrinsic_clock_divergence_value, map_add]

/-- The projected divergence is precisely conditional expectation onto the
actual IBM-generated sigma algebra, on the ambient source-divergence domain. -/
theorem ambient_pair_conditional_divergence
    (a : sourceDerivative.adjoint.domain) (b : clockDerivative.adjoint.domain) :
    ∃ hp : pairField a b ∈ jointDivergence.domain,
      jointDivergence ⟨pairField a b, hp⟩ =
        IBMConditionalObservable.observableProjection IBMConstructedSources.sceneryPath
          IBMConstructedSources.clockPath IBMConstructedSources.sceneryPath_measurable
          IBMConstructedSources.clockPath_measurable
          (sourceDerivative.adjoint a + clockDerivative.adjoint b) := by
  simpa only [IBMConditionalObservable.observableProjection, condExpL2,
    IBMTimeAveragedObservable.IntrinsicSpace, IBMConditionalObservable.observableSpace] using
    ambient_pair_divergence a b

theorem ambient_pair_duality (a : sourceDerivative.adjoint.domain) (b : clockDerivative.adjoint.domain)
    (f : jointDerivative.domain) :
    inner ℝ (IntrinsicSpace.orthogonalProjectionOnto
      (sourceDerivative.adjoint a + clockDerivative.adjoint b)) (f : IntrinsicSpace) =
        inner ℝ (pairField a b) (jointDerivative f) := by
  obtain ⟨hp, hv⟩ := ambient_pair_divergence a b
  rw [← hv]
  exact jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense ⟨_, hp⟩ f

end OperatorDerivativeRewrite.Foundation.IBMJointIntrinsicDerivative
