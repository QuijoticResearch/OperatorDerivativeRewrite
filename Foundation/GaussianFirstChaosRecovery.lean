import Foundation.GaussianDivergenceRecovery
import Foundation.IBMCubicFirstChaos

/-! Canonical source-divergence recovery is an isometry on the first chaos.
Inverse number weighting cannot remove a first-chaos L2 obstruction. -/
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.GaussianFirstChaosRecovery
open InfiniteGaussian GaussianNumberSectors GaussianTimeSpaceHermite IBMCubicFirstChaos
open GaussianDivergenceRecovery GaussianTimeFieldNorm

theorem firstChaos_derivative_graph (h : CoefficientSpace) :
    (firstChaosEmbedding h, scalarTensor h gaussianOne) ∈ closedCylindricalDerivative.graph := by
  have hg := closedCylindricalDerivative_core_graph (wick h 1)
  have hd : polynomialDerivative (wick h 1)=scalarTensor h gaussianOne := by
    simpa only [wick,core_zero,Nat.cast_zero,zero_add,one_smul] using core_derivative h (‖h‖^2) 0
  rw [wick_one_eq_embedding,hd] at hg
  exact hg

theorem firstChaos_divergence_graph (h : CoefficientSpace) :
    (scalarTensor h gaussianOne,firstChaosEmbedding h) ∈ hilbertDivergence.graph := by
  have hg := LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (cylindricalDivergence_rank_graph (wick h 0) h)
  rw [← wick_raising h 0] at hg
  have h0 : (wick h 0 : GaussianL2)=gaussianOne := core_zero h (‖h‖^2)
  rw [h0,wick_one_eq_embedding] at hg
  exact hg

theorem recovery_firstChaos (h : CoefficientSpace) :
    recovery (firstChaosEmbedding h)=scalarTensor h gaussianOne := by
  let f := firstChaosEmbedding h
  let u := scalarTensor h gaussianOne
  have hc : inner ℝ gaussianOne f=0 := by
    change inner ℝ gaussianOne (firstChaosEmbedding h)=0
    rw [← wick_one_eq_embedding]
    exact wick_centered h 0
  have hr := recovery_graph f
  rw [projection_zero,hc,zero_smul,sub_zero] at hr
  have hz : (recovery f-u,0) ∈ hilbertDivergence.graph := by
    simpa only [Prod.mk_sub_mk,f,u,sub_self] using
      hilbertDivergence.graph.sub_mem hr (firstChaos_divergence_graph h)
  have hR := recovery_orthogonal_kernel f (recovery f-u) hz
  have hU := GaussianNumberSectors.graph_duality (firstChaos_derivative_graph h) hz
  rw [inner_zero_right] at hU
  have hU' : inner ℝ (recovery f-u) u=0 := (real_inner_comm u (recovery f-u)).trans hU
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  change inner ℝ (recovery f-u) (recovery f-u)=0
  rw [inner_sub_right,hR,hU',sub_self]

theorem recovery_firstChaos_norm (h : CoefficientSpace) :
    ‖recovery (firstChaosEmbedding h)‖=‖firstChaosEmbedding h‖ := by
  rw [recovery_firstChaos,firstChaosEmbedding.norm_map]
  have hn : ‖scalarTensor h gaussianOne‖^2=‖h‖^2 := by
    rw [← real_inner_self_eq_norm_sq,scalarTensor_pair_inner,
      GaussianDeterministicGraphCore.gaussianOne_inner_self,
      one_mul,real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg (scalarTensor h gaussianOne),norm_nonneg h]

/-- Non-Cauchy behavior of first-chaos source classes survives recovery
exactly, not just as an upper-bound comparison. -/
theorem recovery_firstChaos_distance (h k : CoefficientSpace) :
    ‖recovery (firstChaosEmbedding h)-recovery (firstChaosEmbedding k)‖ =
      ‖firstChaosEmbedding h-firstChaosEmbedding k‖ := by
  calc
    _ = ‖recovery (firstChaosEmbedding (h-k))‖ := by
      rw [map_sub]
      change ‖recoveryOperator (firstChaosEmbedding h)-recoveryOperator (firstChaosEmbedding k)‖ =
        ‖recoveryOperator (firstChaosEmbedding h-firstChaosEmbedding k)‖
      rw [map_sub]
    _ = ‖firstChaosEmbedding (h-k)‖ := recovery_firstChaos_norm _
    _ = _ := by rw [map_sub]

/-- The first-chaos energy of any target is a lower bound on the full
primitive energy. Higher-chaos inverse weighting cannot cancel this term. -/
theorem recovery_norm_sq_ge_firstProjection (f : GaussianL2) :
    ‖projection 1 f‖^2 ≤ ‖recovery f‖^2 := by
  have hs := recovery_inverse_energy_hasSum f
  have hh := hs.summable.sum_le_tsum ({1} : Finset ℕ)
    (fun n _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (sq_nonneg ‖projection n f‖))
  simpa only [Finset.sum_singleton,Nat.cast_one,inv_one,one_mul,hs.tsum_eq] using hh

end OperatorDerivativeRewrite.Foundation.GaussianFirstChaosRecovery
