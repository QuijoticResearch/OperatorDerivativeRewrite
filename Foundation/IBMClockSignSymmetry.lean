import Foundation.GaussianSampleReflection
import Foundation.IBMConstructedSources

/-! Global clock-sign symmetry of the actual continuous IBM realization.
Coordinate null sets are made simultaneous using continuous paths. -/
noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMClockSignSymmetry
open InfiniteGaussian GaussianSampleReflection IBMConstructedSources
set_option backward.isDefEq.respectTransparency false
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable

theorem process_reflect_ae (t : ℝ≥0) :
    (fun ω => GaussianTimeProcess.process t (reflect ω)) =ᵐ[gaussianProduct]
      fun ω => -GaussianTimeProcess.process t ω :=
  firstChaos_reflect_ae (SeparableHilbertEmbedding.hilbertEmbedding
    GaussianTimeHilbert.TimeHilbert (GaussianTimeHilbert.timeVector t))

theorem clock_reflect_coordinate (t : ℝ≥0) :
    (fun ω => clockPath (reflect ω) t) =ᵐ[gaussianProduct] fun ω => -clockPath ω t := by
  filter_upwards [reflect_preserving.quasiMeasurePreserving.ae_eq_comp
    (clockPath_coordinate_ae t), process_reflect_ae t, clockPath_coordinate_ae t]
    with ω hc hp ho
  exact hc.trans (hp.trans (congrArg Neg.neg ho.symm))

theorem clock_reflect_simultaneous :
    ∀ᵐ ω ∂gaussianProduct, ∀ t : ℝ≥0, clockPath (reflect ω) t = -clockPath ω t := by
  have hs : ∀ᵐ ω ∂gaussianProduct, ∀ n : ℕ,
      clockPath (reflect ω) (denseSeq ℝ≥0 n) = -clockPath ω (denseSeq ℝ≥0 n) :=
    ae_all_iff.mpr fun n => clock_reflect_coordinate _
  filter_upwards [hs] with ω hω
  have he : (fun t => clockPath (reflect ω) t) = fun t => -clockPath ω t := by
    apply Continuous.ext_on (denseRange_denseSeq ℝ≥0)
      (clockPath (reflect ω)).continuous (clockPath ω).continuous.neg
    rintro t ⟨n, rfl⟩
    exact hω n
  exact fun t => congrFun he t

def reflectClock (ω : IBMSourceLaws.JointSample) : IBMSourceLaws.JointSample :=
  (ω.1, reflect ω.2)

theorem reflectClock_preserving :
    MeasurePreserving reflectClock IBMSourceLaws.jointMeasure IBMSourceLaws.jointMeasure :=
  (MeasurePreserving.id gaussianProduct).prod reflect_preserving

theorem ibm_reflect_simultaneous : ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
    ∀ t : ℝ≥0, ibmValue t (reflectClock ω) = ibmValue t ω := by
  have hs := (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae
      clock_reflect_simultaneous
  filter_upwards [hs] with ω hω
  intro t
  change sceneryPath ω.1 |clockPath (reflect ω.2) t| = sceneryPath ω.1 |clockPath ω.2 t|
  rw [hω t, abs_neg]

end OperatorDerivativeRewrite.Foundation.IBMClockSignSymmetry
