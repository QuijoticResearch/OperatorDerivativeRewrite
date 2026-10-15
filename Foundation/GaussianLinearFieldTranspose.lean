import Foundation.GaussianLinearFieldDivergenceCompletion
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Completed Gaussian linear-field transposition is the actual Hodge reflection. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianLinearFieldTranspose
open InfiniteGaussian GaussianSourceHodge GaussianQuadraticSourceHodge GaussianLinearFieldDivergenceCompletion

def transpose : GaussianVectorL2 ≃ₗᵢ[ℝ] GaussianVectorL2 := gradientRange.reflection

theorem transpose_apply (v : GaussianVectorL2) : transpose v=2 • gradientProjection v-v := rfl

theorem transpose_rank (a b : CoefficientSpace) :
    transpose (scalarTensor a (firstChaosEmbedding b))=scalarTensor b (firstChaosEmbedding a) := by
  rw [transpose_apply,linear_rank_gradientProjection,mixedSource]
  module

theorem transpose_involution (v : GaussianVectorL2) : transpose (transpose v)=v :=
  gradientRange.reflection_reflection v

theorem transpose_norm (v : GaussianVectorL2) : ‖transpose v‖=‖v‖ := transpose.norm_map v

theorem transpose_pairing (v w : GaussianVectorL2) : inner ℝ (transpose v) w=inner ℝ v (transpose w) := by
  have h := transpose.inner_map_map v (transpose w)
  simpa only [transpose_involution] using h

theorem transpose_mem {v : GaussianVectorL2} (hv : v∈linearGaussianFields) : transpose v∈linearGaussianFields := by
  have hs : linearFieldCore≤linearGaussianFields.comap transpose.toLinearEquiv.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,b,rfl⟩
    change transpose (scalarTensor a (firstChaosEmbedding b))∈linearGaussianFields
    rw [transpose_rank]
    exact linear_rank_mem b a
  exact (linearFieldCore.topologicalClosure_minimal hs
    ((Submodule.isClosed_topologicalClosure _).preimage transpose.continuous)) hv

theorem transpose_matrix_coefficient (a b : CoefficientSpace) (v : GaussianVectorL2) :
    inner ℝ (scalarTensor a (firstChaosEmbedding b)) (transpose v)=
      inner ℝ (scalarTensor b (firstChaosEmbedding a)) v := by
  rw [← transpose_pairing,transpose_rank]

theorem symmetricPart_eq (v : GaussianVectorL2) :
    (1/2 : ℝ) • (v+transpose v)=gradientProjection v := by
  rw [transpose_apply]
  module

theorem antisymmetricPart_eq (v : GaussianVectorL2) :
    (1/2 : ℝ) • (v-transpose v)=v-gradientProjection v := by
  rw [transpose_apply]
  module

theorem transpose_fix_iff (v : GaussianVectorL2) : transpose v=v ↔ v∈gradientRange :=
  Submodule.reflection_eq_self_iff v

theorem transpose_neg_iff (v : GaussianVectorL2) : transpose v=-v ↔ gradientProjection v=0 := by
  rw [transpose_apply]
  constructor
  · intro h
    have hz : (2 : ℝ) • gradientProjection v=0 := by
      simpa only [neg_add_cancel,two_smul,two_nsmul] using (sub_eq_iff_eq_add.mp h)
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro h
    simp [h]

theorem completed_kernel_antisymmetric {v : GaussianVectorL2} (hv : v∈linearGaussianFields) :
    completedDivergence v=0 ↔ transpose v=-v := by
  rw [completed_kernel_iff hv,transpose_neg_iff]

theorem transpose_divergence {v : GaussianVectorL2} (hv : v∈linearGaussianFields) :
    completedDivergence (transpose v)=completedDivergence v := by
  have hg := hilbertDivergence.graph.sub_mem (full_divergence_graph hv)
    (hilbertDivergence.graph.smul_mem (2 : ℝ) (residual_divergence_zero v))
  have he : v-(2 : ℝ) • (v-gradientProjection v)=transpose v := by rw [transpose_apply]; module
  change (v-(2 : ℝ) • (v-gradientProjection v),completedDivergence v-(2 : ℝ) • 0)∈_ at hg
  rw [he,smul_zero,sub_zero] at hg
  exact hilbertDivergence.mem_graph_snd_inj (full_divergence_graph (transpose_mem hv)) hg rfl

end OperatorDerivativeRewrite.Foundation.GaussianLinearFieldTranspose


