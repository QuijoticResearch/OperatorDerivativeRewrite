import Foundation.BrownianBoundedStrongMarkov
import Mathlib.MeasureTheory.Measure.Continuity

/-! Localization removes the deterministic bound from the whole-path restart
law for actual, everywhere finite NNReal-valued stopping times. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianFiniteStrongMarkov
open InfiniteGaussian BrownianMassClockStoppingTime BrownianBoundedRestartProcess
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IBMConstructedSources.clockPath
variable (τ : SampleSpace → ℝ≥0)
  (hτ : IsStoppingTime augmentedPast (fun ω => (τ ω : WithTop ℝ≥0)))

def truncate (N : ℕ) (ω : SampleSpace) : ℝ≥0 := min (τ ω) N

include hτ in
theorem truncate_stopping (N : ℕ) :
    IsStoppingTime augmentedPast (fun ω => (truncate τ N ω : WithTop ℝ≥0)) := by
  simpa only [truncate,WithTop.coe_min] using hτ.min_const (N : ℝ≥0)

theorem localized_measurable (A : Set SampleSpace)
    (hA : MeasurableSet[hτ.measurableSpace] A) (N : ℕ) :
    MeasurableSet[(truncate_stopping τ hτ N).measurableSpace]
      (A ∩ {ω | τ ω ≤ N}) := by
  have hm := (hτ.measurableSet_inter_le_const_iff A (N : ℝ≥0)).mp
    (hA.inter (hτ.measurableSet_le' N))
  simpa only [truncate,WithTop.coe_min,WithTop.coe_le_coe] using hm

theorem localized_path_eq (N : ℕ) (ω : SampleSpace) (hω : τ ω ≤ N) :
    path (truncate τ N) ω = path τ ω := by
  ext t
  simp only [path,truncate,min_eq_left hω,ContinuousMap.coe_mk]

theorem localized_event (A : Set SampleSpace)
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (B : Set C(ℝ≥0, ℝ)) (hB : MeasurableSet B) (N : ℕ) :
    gaussianProduct ((A ∩ {ω | τ ω ≤ N}) ∩ path τ ⁻¹' B) =
      gaussianProduct (A ∩ {ω | τ ω ≤ N}) *
        gaussianProduct.map IBMConstructedSources.clockPath B := by
  have hi := BrownianBoundedStrongMarkov.path_independent (truncate τ N)
    (truncate_stopping τ hτ N) N (fun ω => min_le_right _ _)
  have he := (hi.symm.indepSet_of_measurableSet (localized_measurable τ hτ A hA N)
    (show MeasurableSet[MeasurableSpace.comap (path (truncate τ N)) inferInstance]
      (path (truncate τ N) ⁻¹' B) from ⟨B,hB,rfl⟩)).measure_inter_eq_mul
  have hl := congrArg (fun ν : Measure C(ℝ≥0, ℝ) => ν B)
    (BrownianBoundedStrongMarkov.path_law (truncate τ N) (truncate_stopping τ hτ N)
      N (fun ω => min_le_right _ _))
  rw [Measure.map_apply (path_measurable _ (truncate_stopping τ hτ N)) hB] at hl
  have hs : (A ∩ {ω | τ ω ≤ N}) ∩ path τ ⁻¹' B =
      (A ∩ {ω | τ ω ≤ N}) ∩ path (truncate τ N) ⁻¹' B := by
    ext ω
    by_cases hω : τ ω ≤ N
    · simp only [Set.mem_inter_iff,Set.mem_setOf_eq,Set.mem_preimage,
        localized_path_eq τ N ω hω]
    · simp [hω]
  rw [hs,he,hl]

theorem localized_union (A : Set SampleSpace) :
    (⋃ N : ℕ, A ∩ {ω | τ ω ≤ N}) = A := by
  ext ω
  simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_setOf_eq]
  exact ⟨fun ⟨_,hA,_⟩ => hA,fun hA => ⟨Nat.ceil (τ ω),hA,Nat.le_ceil _⟩⟩

theorem event_law (A : Set SampleSpace)
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (B : Set C(ℝ≥0, ℝ)) (hB : MeasurableSet B) :
    gaussianProduct (A ∩ path τ ⁻¹' B) =
      gaussianProduct A * gaussianProduct.map IBMConstructedSources.clockPath B := by
  have hm : Monotone (fun N : ℕ => A ∩ {ω | τ ω ≤ N}) := by
    intro i j hij ω hω
    refine ⟨hω.1,?_⟩
    change τ ω ≤ (j : ℝ≥0)
    exact hω.2.trans (Nat.cast_le.mpr hij)
  have hmB : Monotone (fun N : ℕ => (A ∩ {ω | τ ω ≤ N}) ∩ path τ ⁻¹' B) :=
    fun i j hij ω hω => ⟨hm hij hω.1,hω.2⟩
  calc
    gaussianProduct (A ∩ path τ ⁻¹' B) =
        gaussianProduct (⋃ N : ℕ, (A ∩ {ω | τ ω ≤ N}) ∩ path τ ⁻¹' B) := by
      rw [← Set.iUnion_inter,localized_union]
    _ = ⨆ N : ℕ, gaussianProduct ((A ∩ {ω | τ ω ≤ N}) ∩ path τ ⁻¹' B) :=
      hmB.measure_iUnion
    _ = ⨆ N : ℕ, gaussianProduct (A ∩ {ω | τ ω ≤ N}) *
        gaussianProduct.map IBMConstructedSources.clockPath B := by
      congr 1
      funext N
      exact localized_event τ hτ A hA B hB N
    _ = (⨆ N : ℕ, gaussianProduct (A ∩ {ω | τ ω ≤ N})) *
        gaussianProduct.map IBMConstructedSources.clockPath B := (ENNReal.iSup_mul _ _).symm
    _ = gaussianProduct A * gaussianProduct.map IBMConstructedSources.clockPath B := by
      rw [← hm.measure_iUnion,localized_union]

include hτ in
theorem path_law : gaussianProduct.map (path τ) =
    gaussianProduct.map IBMConstructedSources.clockPath := by
  ext B hB
  rw [Measure.map_apply (path_measurable τ hτ) hB]
  simpa only [Set.univ_inter,measure_univ,one_mul] using event_law τ hτ univ .univ B hB

theorem path_independent :
    Indep (MeasurableSpace.comap (path τ) inferInstance) hτ.measurableSpace
      gaussianProduct := by
  apply (indep_iff_forall_indepSet gaussianProduct).mpr
  intro S A hS hA
  obtain ⟨B,hB,rfl⟩ := hS
  apply (indepSet_iff_measure_inter_eq_mul ((path_measurable τ hτ) hB)
    (hτ.measurableSpace_le A hA) gaussianProduct).mpr
  have hl := congrArg (fun ν : Measure C(ℝ≥0, ℝ) => ν B) (path_law τ hτ)
  rw [Measure.map_apply (path_measurable τ hτ) hB] at hl
  rw [inter_comm,event_law τ hτ A hA B hB,hl,mul_comm]

end OperatorDerivativeRewrite.Foundation.BrownianFiniteStrongMarkov
