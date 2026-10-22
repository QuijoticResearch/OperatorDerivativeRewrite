import Foundation.IBMPastAverageCore

/-! Genuine finite-past IBM cylinder approximation in the joint derivative core. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPastCylinderClosure
open IBMTimeAveragedObservable IBMPastAverageCore
set_option backward.isDefEq.respectTransparency false

theorem bounded_chain_closure (T : ℝ≥0) (f : JointL2) (hf : f ∈ (pastCore T).topologicalClosure)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : JointL2, F ∈ (pastCore T).topologicalClosure ∧
      F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ (f ω) := by
  classical
  have hh : f ∈ closure ((pastCore T) : Set JointL2) := hf
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hh
  choose Fn hFn hFa using fun n => bounded_chain_past T (u n) (hu n) φ dφ hd hc A B hA hB
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hB0 : 0 ≤ B := (norm_nonneg (dφ 0)).trans (hB 0)
  have hlip : LipschitzWith ⟨B, hB0⟩ φ :=
    lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt) (fun x => by
      change ‖deriv φ x‖ ≤ B
      rw [(hd x).deriv]
      exact hB x)
  have hm : MemLp (fun ω => φ (f ω)) 2 IBMSourceLaws.jointMeasure :=
    MemLp.of_bound (hφ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) A
      (ae_of_all _ fun ω => hA _)
  let F : JointL2 := hm.toLp _
  have hF : F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ (f ω) := hm.coeFn_toLp
  have hconv : Tendsto Fn atTop (𝓝 F) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hb (n : ℕ) : ‖Fn n - F‖ ≤ B * ‖u n - f‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [hFa n, hF, Lp.coeFn_sub (Fn n) F, Lp.coeFn_sub (u n) f]
        with ω h1 h2 h3 h4
      simp only [h3, Pi.sub_apply, h1, h2, h4]
      exact hlip.norm_sub_le _ _
    apply squeeze_zero (fun n => norm_nonneg _) hb
    simpa using tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp ht)
  exact ⟨F, (pastCore T).isClosed_topologicalClosure.mem_of_tendsto hconv
    (Eventually.of_forall fun n => (pastCore T).le_topologicalClosure (hFn n)), hF⟩

theorem point_cylinder_closure {I : Type*} [Fintype I] (T : ℝ≥0) (w t : I → ℝ)
    (ht : ∀ i, 0 < t i) (hT : ∀ i, t i ≤ T)
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
      (pastCore T).topologicalClosure.smul_mem (w i) (point_mem_past_core_closure (ht i) (hT i)))
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
  obtain ⟨F, hf, ha⟩ := bounded_chain_closure T q hq φ dφ hd hc A B hA hB
  refine ⟨F, hf, ?_⟩
  filter_upwards [ha, hqa] with ω h1 h2
  rw [h1, h2]

end OperatorDerivativeRewrite.Foundation.IBMPastCylinderClosure
