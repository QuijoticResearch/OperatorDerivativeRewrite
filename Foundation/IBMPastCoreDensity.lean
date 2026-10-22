import Foundation.IBMPastWeightedLaws
import Foundation.GaussianGeneratedDensity

/-! Dense actual IBM finite-past derivative domains, including zero horizon. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPastCoreDensity
open InfiniteGaussian IBMTimeAveragedObservable IBMPastAverageCore IBMFiniteWeightedLaws
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.ibmValue IBMConstructedSources.clockPath

abbrev PastTime (T : ℝ≥0) := Set.Iic T

def pastFamily (T : ℝ≥0) (ω : IBMSourceLaws.JointSample) (t : PastTime T) : ℝ :=
  IBMConstructedSources.ibmValue (t.val : ℝ).toNNReal ω

@[instance_reducible]
def pastSigma (T : ℝ≥0) : MeasurableSpace IBMSourceLaws.JointSample :=
  MeasurableSpace.comap (pastFamily T) inferInstance

theorem pastFamily_measurable (T : ℝ≥0) : Measurable (pastFamily T) := by
  apply Measurable.of_eval
  intro t
  exact IBMConstructedSources.ibmValue_jointly_measurable.comp
    (measurable_const.prodMk measurable_id)

theorem natural_eq_pastSigma (T : ℝ≥0) :
    IBMNaturalFiltrationObstruction.naturalFiltration T = pastSigma T := by
  have he : pastFamily T = fun ω (j : Set.Iic T) =>
      IBMConstructedSources.ibmValue j.val ω := by
    funext ω j
    change IBMConstructedSources.ibmValue (j.val : ℝ).toNNReal ω = _
    rw [Real.toNNReal_coe]
  change IBMNaturalFiltrationObstruction.naturalFiltration T =
    MeasurableSpace.comap (pastFamily T) inferInstance
  rw [he]
  exact Filtration.natural_eq_comap IBMConstructedSources.ibmValue
    IBMNaturalFiltrationObstruction.point_stronglyMeasurable T

theorem annihilator_past_cylinder (T : ℝ≥0) (H : JointL2) (hH : H ∈ (pastCore T)ᗮ)
    (s : Finset (PastTime T)) (S : Set (s → ℝ)) (hS : MeasurableSet S) :
    (∫ ω in (pastFamily T) ⁻¹' cylinder s S, H ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  let t : s → ℝ := fun i => (i.val.val : ℝ)
  have ht : ∀ i, 0 ≤ t i := fun i => i.val.val.property
  have hSE : MeasurableSet ((fun x : EuclideanSpace ℝ s => x.ofLp) ⁻¹' S) :=
    hS.preimage (PiLp.continuous_ofLp (p := 2) (fun _ : s => ℝ)).measurable
  change (∫ ω in pointObservation t ⁻¹' ((fun x : EuclideanSpace ℝ s => x.ofLp) ⁻¹' S),
    H ω ∂IBMSourceLaws.jointMeasure) = 0
  exact IBMPastWeightedLaws.annihilator_finite_event T H hH t ht
    (fun i => i.val.property) _ hSE

theorem annihilator_past_measurable_zero (T : ℝ≥0) (H : JointL2) (hH : H ∈ (pastCore T)ᗮ)
    (hmH : AEStronglyMeasurable[pastSigma T] H IBMSourceLaws.jointMeasure) : H = 0 := by
  have hi : Integrable H IBMSourceLaws.jointMeasure := (Lp.memLp H).integrable (by simp)
  have hu : (∫ ω, H ω ∂IBMSourceLaws.jointMeasure) = 0 := by
    simpa [cylinder] using annihilator_past_cylinder T H hH ∅ Set.univ MeasurableSet.univ
  have hall : ∀ A : Set (PastTime T → ℝ), MeasurableSet A →
      (∫ ω in (pastFamily T) ⁻¹' A, H ω ∂IBMSourceLaws.jointMeasure) = 0 := by
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => (∫ ω in (pastFamily T) ⁻¹' A, H ω ∂IBMSourceLaws.jointMeasure) = 0)
      (generateFrom_measurableCylinders (α := fun _ : PastTime T => ℝ)).symm
      isPiSystem_measurableCylinders (by simp) ?_ ?_ ?_
    · intro A hA
      obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders A).mp hA
      exact annihilator_past_cylinder T H hH s S hS
    · intro A hA hz
      rw [Set.preimage_compl, setIntegral_compl (hA.preimage (pastFamily_measurable T)) hi,
        hu, hz, sub_self]
    · intro A hd hm hz
      rw [Set.preimage_iUnion, integral_iUnion (fun n => (hm n).preimage (pastFamily_measurable T))
        (hd.mono fun i j hij => hij.preimage _) hi.integrableOn]
      simp only [hz, tsum_zero]
  have hz : H =ᵐ[IBMSourceLaws.jointMeasure] (0 : IBMSourceLaws.JointSample → ℝ) :=
    Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' ℝ (pastFamily_measurable T).comap_le H
      (by norm_num) (by simp) (fun _ _ _ => hi.integrableOn)
      (by rintro A ⟨S, hS, rfl⟩ _; exact hall S hS) hmH
  exact Lp.ext (hz.trans (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := IBMSourceLaws.jointMeasure)).symm)

theorem past_annihilator_zero (T : ℝ≥0) (H : JointL2)
    (hH : H ∈ (pastCore T)ᗮ) (hp : H ∈ IBMNaturalFiltrationObstruction.past T) : H = 0 := by
  apply annihilator_past_measurable_zero T H hH
  change AEStronglyMeasurable[IBMNaturalFiltrationObstruction.naturalFiltration T]
    H IBMSourceLaws.jointMeasure at hp
  rwa [natural_eq_pastSigma] at hp

theorem core_closure_eq_past (T : ℝ≥0) :
    (pastCore T).topologicalClosure = IBMNaturalFiltrationObstruction.past T := by
  have hle := closure_le_past T
  have hz : (pastCore T).topologicalClosureᗮ ⊓ IBMNaturalFiltrationObstruction.past T = ⊥ := by
    apply eq_bot_iff.mpr
    rintro H ⟨hH, hp⟩
    apply past_annihilator_zero T H _ hp
    rwa [Submodule.orthogonal_closure] at hH
  have he := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle
  simpa only [hz, sup_bot_eq] using he

theorem past_le_intrinsic (T : ℝ≥0) : IBMNaturalFiltrationObstruction.past T ≤ IntrinsicSpace := by
  rw [← core_closure_eq_past T]
  apply Submodule.topologicalClosure_minimal
  · intro f hf
    exact ((IBMFiniteAverageCore.mem_intrinsicCore_iff f).mp hf.1).1
  · exact IBMConditionalObservable.observableSpace_isClosed _ _
      IBMConstructedSources.sceneryPath_measurable IBMConstructedSources.clockPath_measurable

theorem past_core_approximation (T : ℝ≥0) (f : IBMNaturalFiltrationObstruction.past T) :
    ∃ u : ℕ → pastCore T,
      Tendsto (fun n => (u n : JointL2)) atTop (𝓝 (f : JointL2)) := by
  have hf : (f : JointL2) ∈ closure (pastCore T : Set JointL2) := by
    change (f : JointL2) ∈ (pastCore T).topologicalClosure
    rw [core_closure_eq_past]
    exact f.property
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hf
  exact ⟨fun n => ⟨u n, hu n⟩, ht⟩

theorem conditional_core_approximation (T : ℝ≥0) (f : JointL2) :
    ∃ u : ℕ → pastCore T,
      Tendsto (fun n => (u n : JointL2)) atTop
        (𝓝 (condExpL2 ℝ ℝ (IBMNaturalFiltrationObstruction.naturalFiltration.le T) f : JointL2)) :=
  past_core_approximation T
    (condExpL2 ℝ ℝ (IBMNaturalFiltrationObstruction.naturalFiltration.le T) f)

end OperatorDerivativeRewrite.Foundation.IBMPastCoreDensity
