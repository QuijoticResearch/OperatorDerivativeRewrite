import Foundation.IBMCompletedSignedCovarianceIntegral
import Foundation.IBMFixedStochasticFamily
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.InnerProductSpace.Completion

/-! The genuine signed-energy null quotient and Hilbert completion of random IBM channels. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology DirectSum
namespace OperatorDerivativeRewrite.Foundation.IBMMultichannelCompletion
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableLpDictionary
open IBMFullPredictableIntegral IBMPredictableCovarianceMeasure IBMCompletedSignedCovarianceIntegral
variable {ι : Type*} [DecidableEq ι] (F : ι → JointL2)
local instance componentAdd : ∀ i, AddCommMonoid (PredictableL2 (F i)) := fun _ => inferInstance
local instance componentGroup : ∀ i, AddCommGroup (PredictableL2 (F i)) := fun _ => inferInstance
local instance componentModule : ∀ i, Module ℝ (PredictableL2 (F i)) := fun _ => inferInstance
local instance componentZeroDec : ∀ i, (x : PredictableL2 (F i)) → Decidable (x ≠ 0) :=
  fun _ _ => Classical.propDecidable _

abbrev Raw := ⨁ i, PredictableL2 (F i)

def rawIntegral : Raw F →ₗ[ℝ] JointL2 :=
  DirectSum.toModule ℝ ι JointL2 (fun i => (integral (F i)).toLinearMap)

theorem rawIntegral_single (i : ι) (H : PredictableL2 (F i)) :
    rawIntegral F (DirectSum.lof ℝ ι (fun i => PredictableL2 (F i)) i H) = integral (F i) H := by
  simp only [rawIntegral, DirectSum.toModule_lof]
  rfl

theorem rawIntegral_sum (u : Raw F) :
    rawIntegral F u = ∑ i ∈ u.support, integral (F i) (u i) := by
  classical
  change DFinsupp.sumAddHom (fun i => (integral (F i)).toLinearMap.toAddMonoidHom) u = _
  rw [DFinsupp.sumAddHom_apply]
  rfl

def gram (u v : Raw F) : ℝ :=
  ∑ i ∈ u.support, ∑ j ∈ v.support,
    ∫ᵛ p, u i p * v j p ∂<•covariance (F i) (F j)

theorem gram_actual (u v : Raw F) : gram F u v = inner ℝ (rawIntegral F u) (rawIntegral F v) := by
  classical
  rw [rawIntegral_sum, rawIntegral_sum, sum_inner]
  simp only [inner_sum, gram, actual_completed_signed_identity]

theorem gram_nonneg (u : Raw F) : 0 ≤ gram F u u := by
  rw [gram_actual, real_inner_self_eq_norm_sq]
  positivity

abbrev Null := LinearMap.ker (rawIntegral F)
abbrev EnergyQuotient := Raw F ⧸ Null F

def quotientRange : EnergyQuotient F ≃ₗ[ℝ] LinearMap.range (rawIntegral F) :=
  (rawIntegral F).quotKerEquivRange

def quotientIntegral : EnergyQuotient F →ₗ[ℝ] JointL2 :=
  (LinearMap.range (rawIntegral F)).subtype.comp (quotientRange F).toLinearMap

theorem quotientIntegral_injective : Function.Injective (quotientIntegral F) :=
  Subtype.val_injective.comp (quotientRange F).injective

instance quotientNorm : NormedAddCommGroup (EnergyQuotient F) :=
  NormedAddCommGroup.induced _ _ (quotientIntegral F) (quotientIntegral_injective F)
instance quotientNormedSpace : NormedSpace ℝ (EnergyQuotient F) :=
  NormedSpace.induced ℝ _ _ (quotientIntegral F)
instance quotientInner : InnerProductSpace ℝ (EnergyQuotient F) :=
  InnerProductSpace.induced (quotientIntegral F)

theorem quotientIntegral_mk (u : Raw F) :
    quotientIntegral F (Submodule.Quotient.mk u) = rawIntegral F u :=
  (rawIntegral F).quotKerEquivRange_apply_mk u

theorem null_iff_zero_energy (u : Raw F) : u ∈ Null F ↔ gram F u u = 0 := by
  rw [gram_actual, real_inner_self_eq_norm_sq]
  change rawIntegral F u = 0 ↔ ‖rawIntegral F u‖^2 = 0
  simp

theorem quotient_gram (u v : Raw F) :
    inner ℝ (Submodule.Quotient.mk u : EnergyQuotient F) (Submodule.Quotient.mk v) = gram F u v := by
  change inner ℝ (quotientIntegral F _) (quotientIntegral F _) = _
  rw [quotientIntegral_mk, quotientIntegral_mk, gram_actual]

abbrev Completed := UniformSpace.Completion (EnergyQuotient F)

def completedIntegral : Completed F →ₗᵢ[ℝ] JointL2 :=
  (quotientIntegral F).extendOfIsometry
    (show DenseRange ((UniformSpace.Completion.toComplₗᵢ : EnergyQuotient F →ₗᵢ[ℝ] Completed F).toLinearMap) from
      UniformSpace.Completion.denseRange_coe)
    (fun q => by
      change ‖quotientIntegral F q‖ = ‖(q : Completed F)‖
      rw [UniformSpace.Completion.norm_coe]
      rfl)

theorem completedIntegral_coe (q : EnergyQuotient F) :
    completedIntegral F q = quotientIntegral F q := LinearMap.extendOfIsometry_eq _ _ _ q

def embed : Raw F →ₗ[ℝ] Completed F :=
  (UniformSpace.Completion.toComplₗᵢ : EnergyQuotient F →ₗᵢ[ℝ] Completed F).toLinearMap.comp
    (Null F).mkQ

theorem completedIntegral_embed (u : Raw F) : completedIntegral F (embed F u) = rawIntegral F u := by
  exact (completedIntegral_coe F _).trans (quotientIntegral_mk F u)

theorem embed_dense : DenseRange (embed F) :=
  UniformSpace.Completion.denseRange_coe.comp (Submodule.mkQ_surjective (Null F)).denseRange
    (UniformSpace.Completion.toComplₗᵢ : EnergyQuotient F →ₗᵢ[ℝ] Completed F).continuous

theorem completed_energy (u : Raw F) : ‖embed F u‖^2 = gram F u u := by
  rw [← (completedIntegral F).norm_map, completedIntegral_embed, gram_actual,
    real_inner_self_eq_norm_sq]

theorem embed_eq_iff (u v : Raw F) : embed F u = embed F v ↔ gram F (u-v) (u-v) = 0 := by
  rw [← completed_energy, map_sub]
  simp only [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

theorem completed_range_closed : IsClosed (Set.range (completedIntegral F)) :=
  (completedIntegral F).isometry.isClosedEmbedding.isClosed_range

theorem completed_range : LinearMap.range (completedIntegral F).toLinearMap =
    (LinearMap.range (rawIntegral F)).topologicalClosure := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    refine UniformSpace.Completion.induction_on z ?_ ?_
    · exact (Submodule.isClosed_topologicalClosure _).preimage (completedIntegral F).continuous
    · intro q
      obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective (Null F) q
      change completedIntegral F (↑(Submodule.Quotient.mk u : EnergyQuotient F)) ∈
        (LinearMap.range (rawIntegral F)).topologicalClosure
      rw [completedIntegral_coe, quotientIntegral_mk]
      exact (LinearMap.range (rawIntegral F)).le_topologicalClosure ⟨u, rfl⟩
  · apply Submodule.topologicalClosure_minimal
    · rintro x ⟨u, rfl⟩
      exact ⟨embed F u, completedIntegral_embed F u⟩
    · exact completed_range_closed F

theorem raw_mem_remainder (u : Raw F) : rawIntegral F u ∈ IBMFixedStochasticFamily.remainderSpace := by
  classical
  rw [rawIntegral_sum]
  apply IBMFixedStochasticFamily.remainderSpace.sum_mem
  intro i _
  exact (IBMTerminalSelfRepresentation.all_channels_range_iff _).mp ⟨F i, u i, rfl⟩

theorem completed_mem_remainder (z : Completed F) :
    completedIntegral F z ∈ IBMFixedStochasticFamily.remainderSpace := by
  have hr : (LinearMap.range (rawIntegral F)).topologicalClosure ≤
      IBMFixedStochasticFamily.remainderSpace := by
    apply Submodule.topologicalClosure_minimal
    · rintro x ⟨u, rfl⟩
      exact raw_mem_remainder F u
    · exact IBMFixedStochasticFamily.remainderSpace_closed
  exact hr ((completed_range F).le ⟨z, rfl⟩)

def fixedFamily (i : IBMFixedStochasticFamily.basisSet) : JointL2 :=
  (IBMFixedStochasticFamily.terminal i : JointL2)

local instance : DecidableEq IBMFixedStochasticFamily.basisSet := Classical.decEq _

theorem fixed_range : LinearMap.range (completedIntegral fixedFamily).toLinearMap =
    IBMFixedStochasticFamily.remainderSpace := by
  apply le_antisymm
  · rintro x ⟨z, rfl⟩
    exact completed_mem_remainder fixedFamily z
  · intro x hx
    let f : IntrinsicSpace := ⟨x, hx.1⟩
    have hz : IBMObservedTerminalMartingale.channelClass (f : JointL2) 0 = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff (IBMIntrinsicRightGerm.rightPast 0)).mpr hx.2
    have hs := IBMFixedStochasticFamily.stochastic_reconstruction f
    rw [hz, sub_zero] at hs
    apply (completed_range_closed fixedFamily).mem_of_tendsto hs
    apply Eventually.of_forall
    intro s
    refine ⟨∑ i ∈ s, embed fixedFamily (DirectSum.lof ℝ _ _ i
      (IBMFixedStochasticFamily.coefficient f i • IBMFixedStochasticFamily.integrand i)), ?_⟩
    simp only [map_sum, completedIntegral_embed]
    apply Finset.sum_congr rfl
    intro i _
    exact rawIntegral_single fixedFamily i _

def fixedOutput : Completed fixedFamily →ₗᵢ[ℝ] IBMFixedStochasticFamily.remainderSpace where
  toLinearMap := (completedIntegral fixedFamily).toLinearMap.codRestrict _
    (completed_mem_remainder fixedFamily)
  norm_map' z := (completedIntegral fixedFamily).norm_map z

theorem fixedOutput_surjective : Function.Surjective fixedOutput := by
  intro x
  obtain ⟨z, hz⟩ := (fixed_range.ge x.property)
  exact ⟨z, Subtype.ext hz⟩

def fixedHilbertEquiv : Completed fixedFamily ≃ₗᵢ[ℝ] IBMFixedStochasticFamily.remainderSpace :=
  LinearIsometryEquiv.ofSurjective fixedOutput fixedOutput_surjective

theorem fixed_reconstruction (f : IntrinsicSpace) :
    completedIntegral fixedFamily (fixedHilbertEquiv.symm (IBMFixedStochasticFamily.remainder f)) =
      (f : JointL2)-IBMObservedTerminalMartingale.channelClass (f : JointL2) 0 :=
  congrArg Subtype.val (fixedHilbertEquiv.apply_symm_apply (IBMFixedStochasticFamily.remainder f))

theorem completedIntegral_unique (J : Completed F →ₗᵢ[ℝ] JointL2)
    (hJ : ∀ u, J (embed F u) = rawIntegral F u) : J = completedIntegral F := by
  apply LinearIsometry.ext
  intro z
  exact (embed_dense F).induction_on z (isClosed_eq J.continuous (completedIntegral F).continuous)
    (fun u => (hJ u).trans (completedIntegral_embed F u).symm)

def finiteEnergy (s : Finset ι) (H : ∀ i, PredictableL2 (F i)) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, ∫ᵛ p, H i p*H j p ∂<•covariance (F i) (F j)

omit [DecidableEq ι] in
theorem finiteEnergy_actual (s : Finset ι) (H : ∀ i, PredictableL2 (F i)) :
    finiteEnergy F s H = ‖∑ i ∈ s, integral (F i) (H i)‖^2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum, finiteEnergy, actual_completed_signed_identity]

theorem completed_partial_energy (s : Finset ι) (H : ∀ i, PredictableL2 (F i)) :
    ‖∑ i ∈ s, embed F (DirectSum.lof ℝ ι _ i (H i))‖^2 = finiteEnergy F s H := by
  rw [← (completedIntegral F).norm_map, finiteEnergy_actual]
  simp only [map_sum, completedIntegral_embed, rawIntegral_single]

theorem series_iff_energy_tails (H : ∀ i, PredictableL2 (F i)) :
    Summable (fun i => embed F (DirectSum.lof ℝ ι _ i (H i))) ↔
      ∀ ε > (0 : ℝ), ∃ s : Finset ι, ∀ t, Disjoint t s → finiteEnergy F t H < ε^2 := by
  rw [summable_iff_vanishing_norm]
  constructor
  · intro h ε hε
    obtain ⟨s, hs⟩ := h ε hε
    refine ⟨s, fun t ht => ?_⟩
    rw [← completed_partial_energy]
    have hn := hs t ht
    nlinarith [norm_nonneg (∑ i ∈ t, embed F (DirectSum.lof ℝ ι _ i (H i)))]
  · intro h ε hε
    obtain ⟨s, hs⟩ := h ε hε
    refine ⟨s, fun t ht => ?_⟩
    have hn := hs t ht
    rw [← completed_partial_energy] at hn
    nlinarith [norm_nonneg (∑ i ∈ t, embed F (DirectSum.lof ℝ ι _ i (H i)))]

theorem series_realization (H : ∀ i, PredictableL2 (F i))
    (hH : ∀ ε > (0 : ℝ), ∃ s : Finset ι, ∀ t, Disjoint t s → finiteEnergy F t H < ε^2) :
    ∃ z : Completed F,
      HasSum (fun i => embed F (DirectSum.lof ℝ ι _ i (H i))) z ∧
      HasSum (fun i => integral (F i) (H i)) (completedIntegral F z) := by
  obtain ⟨z, hz⟩ := (series_iff_energy_tails F H).mpr hH
  refine ⟨z, hz, ?_⟩
  have hm := hz.mapL (completedIntegral F).toContinuousLinearMap
  change HasSum (fun i => completedIntegral F (embed F (DirectSum.lof ℝ ι _ i (H i))))
    (completedIntegral F z) at hm
  simpa only [completedIntegral_embed, rawIntegral_single] using hm

end OperatorDerivativeRewrite.Foundation.IBMMultichannelCompletion
