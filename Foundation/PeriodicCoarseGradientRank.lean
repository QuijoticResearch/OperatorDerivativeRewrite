import Foundation.PeriodicCoarseClosedClasses

/-! Native rank fifteen of the actual coarse periodic gradient. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseGradientRank
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarseCurlCoordinates PeriodicCoarseClosedReconstruction
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

theorem character_pair (T U : Finset Direction) :
    dotProduct (character T) (character U) = if T = U then 16 else 0 := by
  unfold dotProduct character
  exact_mod_cast int_character_pair T U

theorem character_linearIndependent : LinearIndependent ℝ character := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc T
  have h := congrArg (fun f => dotProduct f (character T)) hc
  rw [sum_dotProduct] at h
  simp only [smul_dotProduct, character_pair, smul_eq_mul, zero_dotProduct,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  linarith

theorem vertex_card : Fintype.card CoarseVertex = 16 := by decide
theorem subset_card : Fintype.card (Finset Direction) = 16 := by decide

def vertexBasis : Module.Basis (Finset Direction) ℝ (CoarseVertex → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ character_linearIndependent (by
    rw [subset_card, Module.finrank_fintype_fun_eq_card, vertex_card])

theorem vertexBasis_apply (T : Finset Direction) : vertexBasis T = character T := by
  rw [vertexBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

abbrev GradientLabel := {T : Finset Direction // T.Nonempty}
theorem gradientLabel_card : Fintype.card GradientLabel = 15 := by decide
def gradientMode (T : GradientLabel) : Field := ∑ i ∈ T.val, mode (T.val,i)

theorem gradientMode_coordinate (T S : GradientLabel) :
    coefficient (S.val,pivot S.val) (gradientMode T) = if T = S then 1 else 0 := by
  rw [gradientMode, coefficient_mode_sum]
  by_cases h : T = S
  · subst S
    simp [pivot_mem T.val T.property]
  · have hn : T.val ≠ S.val := fun he => h (Subtype.ext he)
    simp [hn, h]

theorem gradientMode_linearIndependent : LinearIndependent ℝ gradientMode := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc S
  have h := congrArg (coefficient (S.val,pivot S.val)) hc
  simp only [map_sum, map_smul, gradientMode_coordinate, smul_eq_mul, map_zero,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

theorem gradientMode_mem_range (T : GradientLabel) : gradientMode T ∈ LinearMap.range coarseGradient := by
  refine ⟨(-1/2 : ℝ) • character T.val, ?_⟩
  rw [map_smul, gradient_character, smul_smul]
  norm_num
  rfl

theorem gradient_range_span :
    LinearMap.range coarseGradient = Submodule.span ℝ (Set.range gradientMode) := by
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    have hs : (∑ T : Finset Direction, vertexBasis.repr φ T • character T) = φ := by
      simpa only [vertexBasis_apply] using vertexBasis.sum_repr φ
    rw [← hs, map_sum]
    apply Submodule.sum_mem
    intro T _
    rw [map_smul]
    apply Submodule.smul_mem
    rw [gradient_character]
    apply Submodule.smul_mem
    by_cases hn : T.Nonempty
    · exact Submodule.subset_span ⟨⟨T,hn⟩, rfl⟩
    · have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [hT]
  · apply Submodule.span_le.mpr
    rintro _ ⟨T, rfl⟩
    exact gradientMode_mem_range T

theorem gradient_range_finrank : Module.finrank ℝ (LinearMap.range coarseGradient) = 15 := by
  rw [gradient_range_span, finrank_span_eq_card gradientMode_linearIndependent]
  exact gradientLabel_card

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseGradientRank
