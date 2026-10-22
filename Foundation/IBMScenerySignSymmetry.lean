import Foundation.IBMClockSignSymmetry
import Foundation.IBMRightGermCovarianceAdjoint
import Foundation.GaussianPredictableStep

/-! Global scenery-sign symmetry on the actual joint IBM probability space.
The raw observation past is preserved as a space, not fixed pointwise. -/
noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMScenerySignSymmetry
open InfiniteGaussian GaussianSampleReflection IBMConstructedSources
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction
set_option backward.isDefEq.respectTransparency false
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable

theorem sceneryBase_reflect (r : ℝ) :
    (fun ω => IBMSourceLaws.sceneryBase r (reflect ω)) =ᵐ[gaussianProduct]
      fun ω => -IBMSourceLaws.sceneryBase r ω :=
  firstChaos_reflect_ae (SeparableHilbertEmbedding.hilbertEmbedding
    FractionalSpectralKernel.SpectralSpace
      (FractionalSpectralGeometry.normalized (1/2) (by norm_num) (by norm_num) r))

theorem scenery_reflect_coordinate (r : ℝ) :
    (fun ω => sceneryPath (reflect ω) r) =ᵐ[gaussianProduct] fun ω => -sceneryPath ω r := by
  filter_upwards [reflect_preserving.quasiMeasurePreserving.ae_eq_comp
    (sceneryPath_coordinate_ae r), sceneryBase_reflect r, sceneryPath_coordinate_ae r]
      with ω hc hb ho
  exact hc.trans (hb.trans (congrArg Neg.neg ho.symm))

theorem scenery_reflect_simultaneous :
    ∀ᵐ ω ∂gaussianProduct, ∀ r : ℝ, sceneryPath (reflect ω) r = -sceneryPath ω r := by
  have hs : ∀ᵐ ω ∂gaussianProduct, ∀ n : ℕ,
      sceneryPath (reflect ω) (denseSeq ℝ n) = -sceneryPath ω (denseSeq ℝ n) :=
    ae_all_iff.mpr fun n => scenery_reflect_coordinate _
  filter_upwards [hs] with ω hω
  have he : (fun r => sceneryPath (reflect ω) r) = fun r => -sceneryPath ω r := by
    apply Continuous.ext_on (denseRange_denseSeq ℝ)
      (sceneryPath (reflect ω)).continuous (sceneryPath ω).continuous.neg
    rintro r ⟨n, rfl⟩
    exact hω n
  exact fun r => congrFun he r

def reflectScenery (ω : IBMSourceLaws.JointSample) : IBMSourceLaws.JointSample :=
  (reflect ω.1, ω.2)

theorem preserving :
    MeasurePreserving reflectScenery IBMSourceLaws.jointMeasure IBMSourceLaws.jointMeasure :=
  reflect_preserving.prod (MeasurePreserving.id gaussianProduct)

theorem involutive : Function.Involutive reflectScenery := by
  intro ω
  apply Prod.ext
  · funext n
    change -(-ω.1 n) = ω.1 n
    exact neg_neg _
  · rfl

theorem ibm_reflect_simultaneous : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
    ∀ t : ℝ≥0, ibmValue t (reflectScenery ω) = -ibmValue t ω := by
  have hs := (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae
    scenery_reflect_simultaneous
  filter_upwards [hs] with ω hω t
  exact hω |clockPath ω.2 t|

def action : JointL2 →ₗᵢ[ℝ] JointL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ reflectScenery preserving

theorem action_ae (f : JointL2) : action f =ᵐ[IBMSourceLaws.jointMeasure]
    fun ω => f (reflectScenery ω) := Lp.coeFn_compMeasurePreserving f preserving

theorem action_involutive (f : JointL2) : action (action f) = f := by
  apply Lp.ext
  filter_upwards [action_ae (action f), preserving.quasiMeasurePreserving.ae_eq_comp
    (action_ae f)] with ω h₁ h₂
  exact h₁.trans (h₂.trans (congrArg f (involutive ω)))

theorem action_self_adjoint (f g : JointL2) : inner ℝ (action f) g = inner ℝ f (action g) := by
  have h := action.inner_map_map f (action g)
  rwa [action_involutive] at h

theorem action_mem_past (s : ℝ≥0) (f : JointL2) (hf : f ∈ past s) : action f ∈ past s := by
  change AEStronglyMeasurable[naturalFiltration s] f IBMSourceLaws.jointMeasure at hf
  obtain ⟨g, hg, he⟩ := (GaussianPredictableStep.measurable_natural_iff_exists_pastCoefficient
    (fun t => (point_stronglyMeasurable t).measurable) s (hf.mk f)).mp
      hf.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[IBMSourceLaws.jointMeasure]
      GaussianPredictableStep.pastCoefficient ibmValue s g :=
    hf.ae_eq_mk.trans (EventuallyEq.of_eq he)
  have hm : StronglyMeasurable[naturalFiltration s]
      (GaussianPredictableStep.pastCoefficient ibmValue s (fun p => g (-p))) := by
    apply Measurable.stronglyMeasurable
    apply (GaussianPredictableStep.measurable_natural_iff_exists_pastCoefficient
      (fun t => (point_stronglyMeasurable t).measurable) s _).mpr
    exact ⟨_, hg.comp measurable_neg, rfl⟩
  apply hm.aestronglyMeasurable.congr
  filter_upwards [action_ae f, preserving.quasiMeasurePreserving.ae_eq_comp hfg,
    ibm_reflect_simultaneous] with ω ha hc hi
  simp only [Function.comp_def] at hc
  rw [ha, hc]
  apply congrArg g
  funext t
  exact (hi t).symm

theorem projection_fixed (K : Submodule ℝ JointL2) [K.HasOrthogonalProjection]
    (hK : ∀ f ∈ K, action f ∈ K) (f : JointL2) (hf : action f = f) :
    action (K.starProjection f) = K.starProjection f := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hK _ (K.starProjection_apply_mem f))
  intro g hg
  calc
    inner ℝ (f - action (K.starProjection f)) g =
        inner ℝ (action (f - K.starProjection f)) g := by rw [map_sub, hf]
    _ = inner ℝ (f - K.starProjection f) (action g) := action_self_adjoint _ _
    _ = 0 := K.starProjection_inner_eq_zero f (action g) (hK g hg)

theorem clockQuadratic_fixed (t : ℝ≥0) : action (IBMEvenClockProjection.clockQuadratic t) =
    IBMEvenClockProjection.clockQuadratic t := by
  let q := (GaussianTimeSpaceHermite.brownianCore t 2 : GaussianL2)
  apply Lp.ext
  filter_upwards [action_ae (IBMClockConditionalCorrection.clockLift q),
    preserving.quasiMeasurePreserving.ae_eq_comp (IBMClockConditionalCorrection.clockLift_coeFn q),
    IBMClockConditionalCorrection.clockLift_coeFn q] with ω ha hc ho
  exact ha.trans (hc.trans ho.symm)

theorem original_fixed (t : ℝ≥0) :
    action (IBMIntrinsicQuadraticMartingale.valueClass t : JointL2) =
      (IBMIntrinsicQuadraticMartingale.valueClass t : JointL2) := by
  exact projection_fixed (past t) (action_mem_past t)
    (IBMEvenClockProjection.clockQuadratic t) (clockQuadratic_fixed t)

theorem action_mem_rightPast (t : ℝ≥0) (f : JointL2) (hf : f ∈ IBMIntrinsicRightGerm.rightPast t) :
    action f ∈ IBMIntrinsicRightGerm.rightPast t := by
  have hle : (IBMIntrinsicRightGerm.rightPast t).map action.toLinearMap ≤
      IBMIntrinsicRightGerm.rightPast t := by
    conv_rhs => rw [IBMIntrinsicRightGerm.rightPast_eq_iInf]
    apply le_iInf
    intro u g hg
    obtain ⟨f, hf, rfl⟩ := hg
    exact action_mem_past u.val f ((IBMIntrinsicRightGerm.rightPast_le_past u.property) hf)
  exact hle ⟨f, hf, rfl⟩

theorem rightLimit_fixed (t : ℝ≥0) : action (IBMIntrinsicRightGerm.rightLimitClass t) =
    IBMIntrinsicRightGerm.rightLimitClass t :=
  projection_fixed (IBMIntrinsicRightGerm.rightPast t) (action_mem_rightPast t)
    (IBMIntrinsicQuadraticMartingale.valueClass (t + 1) : JointL2) (original_fixed (t + 1))

end OperatorDerivativeRewrite.Foundation.IBMScenerySignSymmetry
