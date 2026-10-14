import Foundation.GaussianDivergenceRecovery

/-! Closed gradient range and the full source Hodge decomposition, constructed
from the actual derivative/divergence graphs and bounded potential recovery. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.GaussianSourceHodge
open InfiniteGaussian GaussianNumberSectors GaussianDivergenceRecovery

def gradientRange : Submodule ℝ GaussianVectorL2 :=
  closedCylindricalDerivative.graph.map (LinearMap.snd ℝ GaussianL2 GaussianVectorL2)

theorem mem_gradientRange_iff (v : GaussianVectorL2) :
    v ∈ gradientRange ↔ ∃ f : GaussianL2, (f,v) ∈ closedCylindricalDerivative.graph := by
  constructor
  · rintro ⟨⟨f,g⟩,hf,rfl⟩
    exact ⟨f,hf⟩
  · rintro ⟨f,hf⟩
    exact ⟨(f,v),hf,rfl⟩

theorem gradientRange_recovery_characterization (v : GaussianVectorL2) :
    v ∈ gradientRange ↔ (recoveryOperator.adjoint v,v) ∈ closedCylindricalDerivative.graph := by
  constructor
  · intro hv
    obtain ⟨f,hf⟩ := (mem_gradientRange_iff v).mp hv
    have hz : (projection 0 f,(0 : GaussianVectorL2)) ∈ closedCylindricalDerivative.graph := by
      rw [projection_zero]
      exact closedDerivative_constant_graph _
    have hs := closedCylindricalDerivative.graph.sub_mem hf hz
    change (f-projection 0 f,v-0) ∈ closedCylindricalDerivative.graph at hs
    rw [sub_zero, ← recovery_adjoint_derivative hf] at hs
    exact hs
  · intro hv
    exact (mem_gradientRange_iff v).mpr ⟨_,hv⟩

theorem gradientRange_isClosed : IsClosed (gradientRange : Set GaussianVectorL2) := by
  have he : (gradientRange : Set GaussianVectorL2) =
      {v | (recoveryOperator.adjoint v,v) ∈ closedCylindricalDerivative.graph} := by
    ext v
    exact gradientRange_recovery_characterization v
  rw [he]
  exact closedCylindricalDerivative_isClosed.preimage
    (recoveryOperator.adjoint.prod (ContinuousLinearMap.id ℝ GaussianVectorL2)).continuous

instance gradientRange_complete : CompleteSpace gradientRange :=
  gradientRange_isClosed.completeSpace_coe

theorem gradientRange_orthogonal_iff_divergence_zero (v : GaussianVectorL2) :
    v ∈ gradientRangeᗮ ↔ (v,0) ∈ hilbertDivergence.graph := by
  constructor
  · intro hv
    change (v,0) ∈ closedCylindricalDerivative.adjoint.graph
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint closedCylindricalDerivative_dense_domain]
    apply (Submodule.mem_adjoint_iff _ _).mpr
    intro f g hf
    rw [inner_zero_right, sub_zero]
    exact (gradientRange.mem_orthogonal v).mp hv g ((mem_gradientRange_iff g).mpr ⟨f,hf⟩)
  · intro hv
    apply (gradientRange.mem_orthogonal v).mpr
    intro g hg
    obtain ⟨f,hf⟩ := (mem_gradientRange_iff g).mp hg
    simpa only [inner_zero_right] using GaussianNumberSectors.graph_duality hf hv

def gradientProjection : GaussianVectorL2 →L[ℝ] GaussianVectorL2 := gradientRange.starProjection

theorem gradientProjection_mem (v : GaussianVectorL2) : gradientProjection v ∈ gradientRange :=
  gradientRange.starProjection_apply_mem v

theorem residual_divergence_zero (v : GaussianVectorL2) :
    (v-gradientProjection v,0) ∈ hilbertDivergence.graph := by
  apply (gradientRange_orthogonal_iff_divergence_zero _).mp
  apply (gradientRange.mem_orthogonal' _).mpr
  intro g hg
  exact gradientRange.starProjection_inner_eq_zero v g hg

theorem recovery_adjoint_kernel_zero (v : GaussianVectorL2)
    (hv : (v,0) ∈ hilbertDivergence.graph) : recoveryOperator.adjoint v = 0 := by
  apply ext_inner_right ℝ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ v (recovery f) = inner ℝ (0 : GaussianL2) f
  rw [recovery_orthogonal_kernel f v hv, inner_zero_left]

/-- Every field has a centered potential in the full derivative domain;
its derivative is the actual orthogonal gradient component. -/
theorem potential_gradient_graph (v : GaussianVectorL2) :
    (recoveryOperator.adjoint v, gradientProjection v) ∈ closedCylindricalDerivative.graph := by
  have hp := (gradientRange_recovery_characterization _).mp (gradientProjection_mem v)
  have hz := recovery_adjoint_kernel_zero _ (residual_divergence_zero v)
  rw [map_sub] at hz
  have he := sub_eq_zero.mp hz
  rw [← he] at hp
  exact hp

end OperatorDerivativeRewrite.Foundation.GaussianSourceHodge
