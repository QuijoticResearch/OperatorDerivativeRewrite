import Foundation.GaussianJointRecoveryIntertwining
import Foundation.GaussianPotentialPredictionRank

/-! Actual full divergence and completed quadratic Hodge geometry on closed linear Gaussian fields. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianLinearFieldDivergenceCompletion
open InfiniteGaussian GaussianNumberSectors GaussianDivergenceRecovery GaussianSourceHodge
open GaussianQuadraticSourceHodge GaussianInverseNumberPotential GaussianPotentialPredictionRank
open GaussianJointRecoveryIntertwining

def linearFieldCore : Submodule ℝ GaussianVectorL2 :=
  Submodule.span ℝ {v | ∃ a b : CoefficientSpace, v=scalarTensor a (firstChaosEmbedding b)}

def linearGaussianFields : Submodule ℝ GaussianVectorL2 := linearFieldCore.topologicalClosure

theorem mixedTarget_mem_sector_two (a b : CoefficientSpace) : mixedTarget a b∈sector 2 := by
  have hc := (exists_divergence_iff_centered (mixedTarget a b)).mp ⟨_,mixed_divergence_graph a b⟩
  have hr := recovery_graph (mixedTarget a b)
  rw [projection_zero,hc,zero_smul,sub_zero,recovery_mixed] at hr
  have hd := mixed_derivative_graph a b
  have he : scalarTensor a (firstChaosEmbedding b)+scalarTensor b (firstChaosEmbedding a)=
      (2 : ℝ) • mixedSource a b := by rw [mixedSource,smul_smul]; norm_num
  rw [he] at hd
  apply (mem_sector 2 _).mpr
  refine ⟨(2 : ℝ) • mixedSource a b,hd,?_⟩
  exact hilbertDivergence.graph.smul_mem (2 : ℝ) hr

theorem adjoint_linear_rank (a b : CoefficientSpace) :
    recoveryOperator.adjoint (scalarTensor a (firstChaosEmbedding b))=(1/2 : ℝ) • mixedTarget a b := by
  rw [adjoint_divergence_potential (mixed_divergence_graph a b)]
  have he := potential_sector 2 ⟨_,mixedTarget_mem_sector_two a b⟩
  simpa only [Nat.cast_ofNat,one_div] using he

def completedDivergence : GaussianVectorL2 →L[ℝ] GaussianL2 := (2 : ℝ) • recoveryOperator.adjoint

theorem completedDivergence_rank (a b : CoefficientSpace) :
    completedDivergence (scalarTensor a (firstChaosEmbedding b))=mixedTarget a b := by
  change (2 : ℝ) • recoveryOperator.adjoint (scalarTensor a (firstChaosEmbedding b))=_
  rw [adjoint_linear_rank,smul_smul]
  norm_num

theorem full_divergence_graph {v : GaussianVectorL2} (hv : v∈linearGaussianFields) :
    (v,completedDivergence v)∈hilbertDivergence.graph := by
  let L := (ContinuousLinearMap.id ℝ GaussianVectorL2).prod completedDivergence
  have hs : linearFieldCore≤hilbertDivergence.graph.comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro v ⟨a,b,rfl⟩
    change (scalarTensor a (firstChaosEmbedding b),completedDivergence (scalarTensor a (firstChaosEmbedding b)))∈hilbertDivergence.graph
    rw [completedDivergence_rank]
    exact mixed_divergence_graph a b
  have hc := linearFieldCore.topologicalClosure_minimal hs (hilbertDivergence_isClosed.preimage L.continuous)
  exact hc hv

theorem completedDivergence_mem_sector_two {v : GaussianVectorL2} (hv : v∈linearGaussianFields) :
    completedDivergence v∈sector 2 := by
  have hs : linearFieldCore≤(sector 2).comap completedDivergence.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro v ⟨a,b,rfl⟩
    change completedDivergence (scalarTensor a (firstChaosEmbedding b))∈sector 2
    rw [completedDivergence_rank]
    exact mixedTarget_mem_sector_two a b
  exact (linearFieldCore.topologicalClosure_minimal hs
    ((sector_isClosed 2).preimage completedDivergence.continuous)) hv

theorem completed_derivative_graph (v : GaussianVectorL2) :
    (completedDivergence v,(2 : ℝ) • gradientProjection v)∈closedCylindricalDerivative.graph := by
  exact closedCylindricalDerivative.graph.smul_mem (2 : ℝ) (potential_gradient_graph v)

theorem completed_recovery {v : GaussianVectorL2} (hv : v∈linearGaussianFields) :
    recovery (completedDivergence v)=gradientProjection v :=
  recovery_divergence_gradientProjection _ _ (full_divergence_graph hv)

theorem completed_energy {v : GaussianVectorL2} (hv : v∈linearGaussianFields) :
    ‖completedDivergence v‖^2=2*‖gradientProjection v‖^2 := by
  have hr := full_divergence_graph hv
  have hs := hilbertDivergence.graph.sub_mem hr (residual_divergence_zero v)
  have he : v-(v-gradientProjection v)=gradientProjection v := by module
  change (v-(v-gradientProjection v),completedDivergence v-0)∈_ at hs
  rw [he,sub_zero] at hs
  have hi := GaussianNumberSectors.graph_duality (completed_derivative_graph v) hs
  rw [real_inner_smul_left,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hi
  exact hi.symm

theorem completed_norm_bound {v : GaussianVectorL2} (hv : v∈linearGaussianFields) :
    ‖completedDivergence v‖≤Real.sqrt 2*‖v‖ := by
  have he := completed_energy hv
  have hp := gradientRange.norm_starProjection_apply_le v
  change ‖gradientProjection v‖≤‖v‖ at hp
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤Real.sqrt 2*‖v‖)).mp
  rw [mul_pow,hs,he]
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hp) (by norm_num)

theorem completed_kernel_iff {v : GaussianVectorL2} (hv : v∈linearGaussianFields) :
    completedDivergence v=0 ↔ gradientProjection v=0 := by
  rw [← norm_eq_zero,← sq_eq_zero_iff,completed_energy hv]
  constructor
  · intro hz
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (by linarith : ‖gradientProjection v‖^2=0))
  · intro hz
    simp [hz]

theorem linear_rank_mem (a b : CoefficientSpace) : scalarTensor a (firstChaosEmbedding b)∈linearGaussianFields :=
  linearFieldCore.le_topologicalClosure (Submodule.subset_span ⟨a,b,rfl⟩)

theorem completed_series_graph (v : ℕ → GaussianVectorL2) (hv : ∀ n,v n∈linearGaussianFields)
    {V : GaussianVectorL2} (hs : HasSum v V) :
    (V,completedDivergence V)∈hilbertDivergence.graph ∧ HasSum (fun n => completedDivergence (v n)) (completedDivergence V) := by
  have hm : V∈linearGaussianFields :=
    (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hs
      (Eventually.of_forall fun s => linearGaussianFields.sum_mem (fun n hn => hv n))
  exact ⟨full_divergence_graph hm,completedDivergence.hasSum hs⟩

end OperatorDerivativeRewrite.Foundation.GaussianLinearFieldDivergenceCompletion
