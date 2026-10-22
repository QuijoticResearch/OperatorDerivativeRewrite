import Foundation.IBMPastCylinderClosure

/-! Zero-time recovery removes positivity restrictions from past cylinders. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPastEndpointCore
open InfiniteGaussian IBMTimeAveragedObservable IBMPastAverageCore
set_option backward.isDefEq.respectTransparency false

theorem randomSource_zero : IBMRandomTimeHilbert.randomSourceL2 0 = 0 := by
  apply Lp.ext
  filter_upwards [(IBMRandomTimeHilbert.randomSourceClass_memLp 0).coeFn_toLp,
    GaussianTimeProcess.process_zero_ae,
    Lp.coeFn_zero InfiniteGaussian.GaussianL2 2 InfiniteGaussian.gaussianProduct]
    with ω hu hy hz
  change IBMRandomTimeHilbert.randomSourceL2 0 ω = IBMRandomTimeHilbert.randomSourceClass 0 ω at hu
  rw [hu, hz, Pi.zero_apply]
  have hn := IBMRandomTimeHilbert.randomSourceClass_norm_sq 0 ω
  rw [hy, abs_zero] at hn
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (IBMRandomTimeHilbert.randomSourceClass 0 ω)])

theorem point_mem_closure {t : ℝ} {T : ℝ≥0} (ht : 0 ≤ t) (hT : t ≤ T) :
    jointRealization (IBMRandomTimeHilbert.randomSourceL2 t.toNNReal) ∈
      (pastCore T).topologicalClosure := by
  rcases ht.eq_or_lt with he | hp
  · subst t
    simpa only [Real.toNNReal_zero, randomSource_zero, map_zero] using
      (pastCore T).topologicalClosure.zero_mem
  · exact point_mem_past_core_closure hp hT

theorem point_cylinder_closure {I : Type*} [Fintype I] (T : ℝ≥0) (w t : I → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hT : ∀ i, t i ≤ T)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : JointL2, F ∈ (pastCore T).topologicalClosure ∧
      F =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        φ (∑ i, w i * IBMConstructedSources.ibmValue (t i).toNNReal ω) := by
  classical
  let q : JointL2 := ∑ i,
    w i • jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i).toNNReal)
  have hq : q ∈ (pastCore T).topologicalClosure :=
    (pastCore T).topologicalClosure.sum_mem (fun i _ =>
      (pastCore T).topologicalClosure.smul_mem (w i) (point_mem_closure (ht i) (hT i)))
  have hqa : q =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      ∑ i, w i * IBMConstructedSources.ibmValue (t i).toNNReal ω := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
        w i • jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i).toNNReal)),
      ae_all_iff.mpr (fun i => Lp.coeFn_smul (w i)
        (jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i).toNNReal))),
      ae_all_iff.mpr (fun i => joint_point_actual_ae (t i).toNNReal)] with ω hs hm hp
    change (∑ i, w i • jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i).toNNReal)) ω = _
    rw [hs]
    simp only [Finset.sum_apply, hm, Pi.smul_apply, smul_eq_mul, hp]
  obtain ⟨F, hf, ha⟩ := IBMPastCylinderClosure.bounded_chain_closure T q hq φ dφ hd hc A B hA hB
  refine ⟨F, hf, ?_⟩
  filter_upwards [ha, hqa] with ω h1 h2
  rw [h1, h2]

end OperatorDerivativeRewrite.Foundation.IBMPastEndpointCore
