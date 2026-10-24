import Foundation.IBMSchwartzHybridTime
import Foundation.BochnerL2RepresentativeFubini

/-! Actual centered Schwartz time averages are divergences of the physical-time
Bochner integral of the SAME explicit source/native heat-clock fields.
No strong derivative-domain membership of the point observables is assumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzNativeAverage
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMJointIntrinsicDerivative IBMSchwartzHybridReconstruction IBMSchwartzHybridTime
open IBMSchwartzHeatDerivative IBMClockOverlapEnergy
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
attribute [local irreducible] integrand centered heatMean
  IBMSchwartzHalfHolderHeat.curve GaussianBoundedHeatDerivative.mean

def observable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : IntrinsicSpace :=
  ∫ t, centered g a t.toNNReal ∂window T

def field (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : JointFieldSpace :=
  ∫ t, integrand g a t.toNNReal ∂window T

theorem observable_coe (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    (observable g a T : JointL2) =
      ∫ t, (centered g a t.toNNReal : JointL2) ∂window T :=
  (IntrinsicSpace.subtypeL.integral_comp_comm (centered_integrable g a T)).symm

theorem reconstruction (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∃ hi : field g a T ∈ jointDivergence.domain,
      jointDivergence ⟨field g a T,hi⟩ = observable g a T := by
  let S := jointDivergence.graph
  let : IsClosed (S : Set (JointFieldSpace × IntrinsicSpace)) :=
    jointDerivative.adjoint_isClosed jointDerivative_dense
  let z : ℝ → JointFieldSpace × IntrinsicSpace :=
    fun t => (integrand g a t.toNNReal,centered g a t.toNNReal)
  have hz : Integrable z (window T) :=
    (integrand_integrable g a T).prodMk (centered_integrable g a T)
  have ha : ∀ᵐ t ∂window T, z t ∈ S := ae_of_all _ fun t => by
    obtain ⟨hi,hv⟩ := IBMSchwartzHybridReconstruction.reconstruction g a t.toNNReal
    exact jointDivergence.mem_graph_iff.mpr ⟨⟨_,hi⟩,rfl,hv⟩
  have hq : S.mkQL (∫ t, z t ∂window T) = 0 := by
    rw [← S.mkQL.integral_comp_comm hz]
    apply integral_eq_zero_of_ae
    filter_upwards [ha] with t ht
    exact (Submodule.Quotient.mk_eq_zero S).mpr ht
  have hm := (Submodule.Quotient.mk_eq_zero S).mp hq
  have he : (∫ t, z t ∂window T) = (field g a T,observable g a T) := by
    exact integral_pair (integrand_integrable g a T) (centered_integrable g a T)
  rw [he] at hm
  have hi := LinearPMap.mem_domain_of_mem_graph hm
  exact ⟨hi,((jointDivergence.image_iff hi).mpr hm).symm⟩

def raw (g : SchwartzMap ℝ ℝ) (a : ℝ) (z : ℝ × IBMSourceLaws.JointSample) : ℝ :=
  g (a+IBMConstructedSources.ibmValue z.1.toNNReal z.2) -
    inner ℝ gaussianOne (heatMean g a 0 z.1.toNNReal)

theorem raw_measurable (g : SchwartzMap ℝ ℝ) (a : ℝ) : Measurable (raw g a) := by
  have hp : Measurable (fun z : ℝ × IBMSourceLaws.JointSample => (z.1.toNNReal,z.2)) :=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
  have hb := IBMConstructedSources.ibmValue_jointly_measurable.comp hp
  have hm : Continuous (fun t : ℝ => inner ℝ gaussianOne (heatMean g a 0 t.toNNReal)) :=
    continuous_const.inner ((initial_continuous g a).comp continuous_real_toNNReal)
  exact (g.continuous.measurable.comp (measurable_const.add hb)).sub
    (hm.measurable.comp measurable_fst)

theorem centered_raw (g : SchwartzMap ℝ ℝ) (a : ℝ) (t : ℝ) :
    (centered g a t.toNNReal : JointL2) =ᵐ[IBMSourceLaws.jointMeasure]
      fun p => raw g a (t,p) := by
  simpa only [raw,global_mean] using centered_actual g a t.toNNReal

theorem raw_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Integrable (raw g a) ((window T).prod IBMSourceLaws.jointMeasure) := by
  apply BochnerL2RepresentativeFubini.representative_integrable
    (fun t => (centered g a t.toNNReal : JointL2))
    (IntrinsicSpace.subtypeL.integrable_comp (centered_integrable g a T))
    (raw g a) (raw_measurable g a).aestronglyMeasurable
  exact ae_of_all _ (centered_raw g a)

theorem observable_actual (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    (observable g a T : JointL2) =ᵐ[IBMSourceLaws.jointMeasure] fun p =>
      ∫ t, g (a+IBMConstructedSources.ibmValue t.toNNReal p) -
        (∫ q, g (a+IBMConstructedSources.ibmValue t.toNNReal q)
          ∂IBMSourceLaws.jointMeasure) ∂window T := by
  rw [observable_coe]
  have h := BochnerL2RepresentativeFubini.integral_coeFn_ae
    (fun t => (centered g a t.toNNReal : JointL2))
    (IntrinsicSpace.subtypeL.integrable_comp (centered_integrable g a T))
    (raw g a) (raw_measurable g a).aestronglyMeasurable (ae_of_all _ (centered_raw g a))
  simpa only [raw,global_mean] using h

theorem duality (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (F : jointDerivative.domain) :
    inner ℝ (observable g a T) (F : IntrinsicSpace) =
      inner ℝ (field g a T) (jointDerivative F) := by
  obtain ⟨hi,hv⟩ := reconstruction g a T
  have h := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense
    ⟨field g a T,hi⟩ F
  rw [hv] at h
  exact h

end OperatorDerivativeRewrite.Foundation.IBMSchwartzNativeAverage
