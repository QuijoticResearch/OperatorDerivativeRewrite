import Foundation.SPDEObservationRecoveryCompactness

/-! One continuous Brownian observation channel already has infinite source multiplicity. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.BrownianHistoryRecoveryCompactness
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection GaussianDivergenceRecovery
open GaussianTimeHilbert GaussianTimeDivergence GaussianTimeFieldNorm SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

def pastDirections (t : ℝ≥0) : Set.Iic t → CoefficientSpace :=
  fun s => hilbertEmbedding TimeHilbert (timeVector s)

def geometricTime (t : ℝ≥0) (n : ℕ) : ℝ≥0 := t*(1/2 : ℝ≥0)^n

theorem geometricTime_antitone (t : ℝ≥0) : Antitone (geometricTime t) := by
  intro n m hnm
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num : (0 : ℝ≥0)≤1/2) (by norm_num : (1/2 : ℝ≥0)≤1) hnm)
    (by positivity)

theorem geometricTime_le (t : ℝ≥0) (n : ℕ) : geometricTime t n≤t := by
  simpa [geometricTime] using geometricTime_antitone t (Nat.zero_le n)

theorem geometric_gap_pos (t : ℝ≥0) (ht : 0<t) (n : ℕ) :
    0<(geometricTime t n : ℝ)-(geometricTime t (n+1) : ℝ) := by
  simp only [geometricTime,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,pow_succ]
  norm_num
  have hp : 0<(t : ℝ)*(1/2 : ℝ)^n := by positivity
  nlinarith

def incrementUnit (t : ℝ≥0) (n : ℕ) : CoefficientSpace :=
  (Real.sqrt ((geometricTime t n : ℝ)-(geometricTime t (n+1) : ℝ)))⁻¹ •
    incrementDirection (geometricTime t (n+1)) (geometricTime t n)

theorem geometric_increments_orthogonal (t : ℝ≥0) (n m : ℕ) (hnm : n<m) :
    inner ℝ (incrementDirection (geometricTime t (n+1)) (geometricTime t n))
      (incrementDirection (geometricTime t (m+1)) (geometricTime t m))=0 := by
  have hn := geometricTime_antitone t (Nat.le_succ n)
  have hm := geometricTime_antitone t (Nat.le_succ m)
  have hgap := geometricTime_antitone t (show n+1≤m by omega)
  rw [real_inner_comm,incrementDirection,incrementDirection,(hilbertEmbedding TimeHilbert).inner_map_map,
    ← timeVector_sub _ _ hm,← timeVector_sub _ _ hn]
  exact timeVector_increments_orthogonal _ _ _ _ hm hgap hn

theorem incrementUnit_orthonormal (t : ℝ≥0) (ht : 0<t) : Orthonormal ℝ (incrementUnit t) := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [incrementUnit,real_inner_smul_left,real_inner_smul_right]
  by_cases hnm : n=m
  · subst m
    rw [if_pos rfl,real_inner_self_eq_norm_sq,
      incrementDirection_norm_sq _ _ (geometricTime_antitone t (Nat.le_succ n))]
    have hp := geometric_gap_pos t ht n
    have hs := Real.sq_sqrt hp.le
    have hz : Real.sqrt ((geometricTime t n : ℝ)-(geometricTime t (n+1) : ℝ))≠0 :=
      ne_of_gt (Real.sqrt_pos.mpr hp)
    field_simp
    nlinarith
  · rw [if_neg hnm]
    have ho : inner ℝ (incrementDirection (geometricTime t (n+1)) (geometricTime t n))
        (incrementDirection (geometricTime t (m+1)) (geometricTime t m))=0 := by
      rcases lt_or_gt_of_ne hnm with hl | hl
      · exact geometric_increments_orthogonal t n m hl
      · rw [real_inner_comm]
        exact geometric_increments_orthogonal t m n hl
    rw [ho,mul_zero,mul_zero]

theorem incrementUnit_mem (t : ℝ≥0) (n : ℕ) : incrementUnit t n∈sourceSpan (pastDirections t) := by
  apply (sourceSpan (pastDirections t)).smul_mem
  have hn := geometricTime_antitone t (Nat.le_succ n)
  rw [incrementDirection,← timeVector_sub _ _ hn,map_sub]
  apply (sourceSpan (pastDirections t)).sub_mem
  · exact (Submodule.span ℝ (Set.range (pastDirections t))).le_topologicalClosure
      (Submodule.subset_span ⟨⟨geometricTime t n,geometricTime_le t n⟩,rfl⟩)
  · exact (Submodule.span ℝ (Set.range (pastDirections t))).le_topologicalClosure
      (Submodule.subset_span ⟨⟨geometricTime t (n+1),geometricTime_le t (n+1)⟩,rfl⟩)

def historySourceEmbedding (t : ℝ≥0) (ht : 0<t) : CoefficientSpace →ₗᵢ[ℝ] CoefficientSpace :=
  (incrementUnit_orthonormal t ht).orthogonalFamily.linearIsometry

theorem historySourceEmbedding_hasSum (t : ℝ≥0) (ht : 0<t) (c : CoefficientSpace) :
    HasSum (fun n => c n • incrementUnit t n) (historySourceEmbedding t ht c) := by
  simpa only [historySourceEmbedding,LinearIsometry.toSpanSingleton_apply] using
    (incrementUnit_orthonormal t ht).orthogonalFamily.hasSum_linearIsometry c

theorem historySourceEmbedding_mem (t : ℝ≥0) (ht : 0<t) (c : CoefficientSpace) :
    historySourceEmbedding t ht c∈sourceSpan (pastDirections t) := by
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (historySourceEmbedding_hasSum t ht c)
  exact Eventually.of_forall fun s => (sourceSpan (pastDirections t)).sum_mem
    (fun n hn => (sourceSpan (pastDirections t)).smul_mem _ (incrementUnit_mem t n))

theorem positive_history_recovery_noncompact (t : ℝ≥0) (ht : 0<t) :
    ¬ IsCompactOperator (recoveryOperator.comp (conditionalProjection (pastDirections t))) :=
  SPDEObservationRecoveryCompactness.infinite_observed_source_noncompact (pastDirections t)
    (historySourceEmbedding t ht) (historySourceEmbedding_mem t ht)

theorem zero_history_recovery_zero : recoveryOperator.comp (conditionalProjection (pastDirections 0))=0 := by
  have hz (s : Set.Iic (0 : ℝ≥0)) : pastDirections 0 s=0 := by
    have hs : (s : ℝ≥0)=0 := le_antisymm s.property (by positivity)
    simp [pastDirections,hs,timeVector_zero]
  apply ContinuousLinearMap.ext
  intro f
  change recovery (conditionalProjection (pastDirections 0) f)=0
  rw [GaussianConditionalCompactness.zero_family_projection _ hz,recovery_smul,
    GaussianOneObservationRecoveryCompactness.recovery_vacuum_zero,smul_zero]

theorem brownian_history_recovery_compact_iff (t : ℝ≥0) :
    IsCompactOperator (recoveryOperator.comp (conditionalProjection (pastDirections t))) ↔ t=0 := by
  constructor
  · intro hc
    by_contra ht
    exact positive_history_recovery_noncompact t (lt_of_le_of_ne (by positivity) (Ne.symm ht)) hc
  · intro ht
    subst t
    rw [zero_history_recovery_zero]
    change IsCompactOperator (0 : GaussianL2 → GaussianVectorL2)
    exact isCompactOperator_zero

end OperatorDerivativeRewrite.Foundation.BrownianHistoryRecoveryCompactness
