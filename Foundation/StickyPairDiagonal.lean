import Foundation.StickyPairMarginals
import Foundation.BrownianStickyBoundaryAtom

/-! Nontrivial coupling: Gaussian coordinate marginals coexist with positive diagonal mass. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StickyPairDiagonal
open InfiniteGaussian IBMConstructedSources StickyPairPaths StickyPairSampling StickyPairMarginals
open BrownianMassRandomTimeChange
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath

def oneTimeLaw (κ t : ℝ≥0) : Measure (ℝ × ℝ) :=
  sourceMeasure.map (fun w => (leftPath κ w t,rightPath κ w t))

theorem evaluation_measurable (κ t : ℝ≥0) :
    Measurable (fun w => (leftPath κ w t,rightPath κ w t)) :=
  ((ContinuousMap.measurable_eval t).comp (left_measurable κ)).prodMk
    ((ContinuousMap.measurable_eval t).comp (right_measurable κ))

instance oneTimeLaw_probability (κ t : ℝ≥0) : IsProbabilityMeasure (oneTimeLaw κ t) := by
  unfold oneTimeLaw
  infer_instance

theorem oneTimeLaw_eq_evaluation (κ t : ℝ≥0) :
    oneTimeLaw κ t=(pathLaw κ).map (fun f => f t) := by
  rw [pathLaw,Measure.map_map (ContinuousMap.measurable_eval t) (pair_measurable κ)]
  rfl

theorem coincidence_probability (κ t : ℝ≥0) :
    sourceMeasure {w | leftPath κ w t=rightPath κ w t}=
      gaussianProduct {w | changedPath κ w t=0} := by
  have hp : MeasurePreserving (Prod.fst : Sample → SampleSpace)
      sourceMeasure gaussianProduct := measurePreserving_fst
  have he : {w | leftPath κ w t=rightPath κ w t} =ᵐ[sourceMeasure]
      {w | changedPath κ w.1 t=0} := by
    filter_upwards [hp.quasiMeasurePreserving.ae source_zero] with w hw
    apply propext
    change (leftPath κ w t=rightPath κ w t) ↔ changedPath κ w.1 t=0
    rw [coincidence]
    simp [separationPath,centeredPath,changedPath,hw]
  rw [measure_congr he]
  have hZ : MeasurableSet {w | changedPath κ w t=0} :=
    measurableSet_eq_fun (changedPath_coordinate_measurable κ t) measurable_const
  have h := congrArg (fun μ : Measure SampleSpace => μ {w | changedPath κ w t=0}) hp.map_eq
  rw [Measure.map_apply hp.measurable hZ] at h
  exact h

theorem diagonal_probability (κ t : ℝ≥0) :
    oneTimeLaw κ t (diagonal ℝ)=gaussianProduct {w | changedPath κ w t=0} := by
  rw [oneTimeLaw,Measure.map_apply (evaluation_measurable κ t) measurableSet_diagonal]
  exact coincidence_probability κ t

theorem gaussian_product_diagonal_zero (t : ℝ≥0) (ht : 0 < t) :
    ((gaussianReal 0 t).prod (gaussianReal 0 t)) (diagonal ℝ)=0 := by
  letI : NullSingletonClass (gaussianReal 0 t) := nullSingletonClass_gaussianReal (ne_of_gt ht)
  rw [Measure.prod_apply measurableSet_diagonal]
  have he (x : ℝ) : Prod.mk x ⁻¹' diagonal ℝ={x} := by
    ext y
    simp [mem_diagonal_iff,eq_comm]
  simp_rw [he,measure_singleton]
  exact lintegral_zero

theorem exists_nonproduct_coupling (κ T : ℝ≥0) (hκ : 0 < κ) (hT : 0 < T) :
    ∃ s : ℝ≥0, 0 < s ∧ s ≤ T ∧
      0 < oneTimeLaw κ s (diagonal ℝ) ∧
      oneTimeLaw κ s ≠ (gaussianReal 0 s).prod (gaussianReal 0 s) := by
  obtain ⟨s,hs,hsT,hp⟩ := BrownianStickyBoundaryAtom.exists_boundary_atom κ T hκ hT
  refine ⟨s,hs,hsT,?_,?_⟩
  · rwa [diagonal_probability]
  · intro he
    have hz := congrArg (fun μ : Measure (ℝ × ℝ) => μ (diagonal ℝ)) he
    rw [diagonal_probability,gaussian_product_diagonal_zero s hs] at hz
    rw [hz] at hp
    exact (lt_irrefl 0) hp

end OperatorDerivativeRewrite.Foundation.StickyPairDiagonal
