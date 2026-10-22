import Foundation.IBMPredictableLpDictionary
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.PiSystem

/-! Density in the full actual raw-predictable L2 space, including the zero origin. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableDictionaryDensity
open IBMPredictableRectangles IBMPredictableFiniteIntegral IBMPredictableLpDictionary
open IBMJointPredictableEnergyMeasure IBMTimeAveragedObservable
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
local instance (F : JointL2) : IsFiniteMeasure (predictableMeasure F) := finite_measure F

def domain (F : JointL2) : Submodule ℝ (PredictableL2 F) :=
  (dictionary F).range.topologicalClosure

theorem orthogonal_ring_integral (F : JointL2) (f : PredictableL2 F)
    (hf : f ∈ (domain F)ᗮ) {E : Set Space} (hE : E ∈ elementaryRing) :
    (∫ p in E, f p ∂predictableMeasure F) = 0 := by
  have hm : indicatorConstLp 2 (elementary_predictable hE) (measure_ne_top _ _) (1 : ℝ) ∈
      domain F := (dictionary F).range.le_topologicalClosure (indicator_in_range F hE)
  have hi := Submodule.inner_right_of_mem_orthogonal hm hf
  exact (L2.inner_indicatorConstLp_one (𝕜 := ℝ)
    (elementary_predictable hE) (measure_ne_top _ _) f).symm.trans hi

theorem orthogonal_zero_on_rectangle (F : JointL2) (f : PredictableL2 F)
    (hf : f ∈ (domain F)ᗮ) (T : ℝ≥0) :
    f =ᵐ[(predictableMeasure F).restrict (rect 0 T univ)] (fun _ => (0 : ℝ)) := by
  have hU : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration 0]
      (univ : Set IBMSourceLaws.JointSample) := @MeasurableSet.univ _ _
  have hR : rect 0 T univ ∈ elementaryRing := subset_supClosure (rect_mem 0 T univ hU)
  have hi : Integrable f ((predictableMeasure F).restrict (rect 0 T univ)) :=
    (Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) |>.restrict
  have hv : ((predictableMeasure F).restrict (rect 0 T univ)).withDensityᵥ f = 0 := by
    apply VectorMeasure.ext_of_generateFrom generators
    · intro E hE
      have hm : MeasurableSet E := by
        change MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration.predictable] E
        rw [← predictable_generation]
        exact MeasurableSpace.measurableSet_generateFrom hE
      rw [withDensityᵥ_apply hi hm, VectorMeasure.zero_apply, Measure.restrict_restrict hm]
      rcases hE with hE | ⟨A, _hA, rfl⟩
      · exact orthogonal_ring_integral F f hf (elementary_isSetRing.inter_mem hE hR)
      · have he : ({0} ×ˢ A) ∩ rect 0 T univ = ∅ := by
          exact (ring_disjoint_origin hR A).symm.eq_bot
        rw [he, Measure.restrict_empty]
        exact integral_zero_measure _
    · exact predictable_generation.symm
    · intro E hE H hH _hne
      exact generators_inter hE hH
    · rw [withDensityᵥ_apply hi MeasurableSet.univ, VectorMeasure.zero_apply, Measure.restrict_univ]
      exact orthogonal_ring_integral F f hf hR
  apply hi.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ _)
  simpa only [withDensityᵥ_zero] using hv

theorem orthogonal_zero (F : JointL2) (f : PredictableL2 F)
    (hf : f ∈ (domain F)ᗮ) : f = 0 := by
  have hU : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration 0]
      (univ : Set IBMSourceLaws.JointSample) := @MeasurableSet.univ _ _
  have hz : ∀ᵐ p ∂predictableMeasure F, p ∉ origin univ :=
    measure_eq_zero_iff_ae_notMem.mp (predictableMeasure_origin F univ hU)
  have hall : ∀ᵐ p ∂predictableMeasure F, ∀ n : ℕ,
      p ∈ rect 0 n univ → f p = 0 :=
    ae_all_iff.mpr fun n => (ae_restrict_iff' (rect_predictable 0 n univ hU)).mp
      (orthogonal_zero_on_rectangle F f hf n)
  apply Lp.ext
  filter_upwards [hz, hall, Lp.coeFn_zero ℝ 2 (predictableMeasure F)] with p hp hn hzero
  rw [hzero]
  have ht : 0 < p.1 := pos_iff_ne_zero.mpr fun he => hp ⟨he, mem_univ _⟩
  obtain ⟨n, hn'⟩ := exists_nat_ge p.1
  exact hn n ⟨⟨ht, hn'⟩, mem_univ _⟩

theorem domain_eq_top (F : JointL2) : domain F = ⊤ := by
  letI : (domain F).HasOrthogonalProjection := by unfold domain; infer_instance
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro f hf
  change f = 0
  exact orthogonal_zero F f hf

theorem dictionary_dense (F : JointL2) : DenseRange (dictionary F) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr (domain_eq_top F)

end OperatorDerivativeRewrite.Foundation.IBMPredictableDictionaryDensity
