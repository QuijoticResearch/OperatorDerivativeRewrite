import Foundation.PoissonRecoveryCompactness
import Foundation.PoissonWeightedScalarGeometry
import Foundation.GaussianWickRecoveryPrediction

/-! One-coordinate conditional recovery is compact although conditional projection is not. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianOneObservationRecoveryCompactness
open InfiniteGaussian GaussianTimeSpaceHermite GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianConditionalCompactness GaussianWickRecoveryPrediction GaussianSingleObservationPrediction
open PoissonDifferenceOperators PoissonCharlierHilbertBasis

private theorem poisson_coefficient_basis (n m : ℕ) :
    PoissonDivergenceRecovery.coefficient 1 (by norm_num) (normalized 1 (by norm_num) n) m=
      if m=n then 1 else 0 := by
  exact (orthonormal_iff_ite.mp (normalized_orthonormal 1 (by norm_num))) m n

theorem poisson_recovery_normalized_zero :
    PoissonDivergenceRecovery.recovery 1 (by norm_num) (normalized 1 (by norm_num) 0)=0 := by
  unfold PoissonDivergenceRecovery.recovery
  have he (n : ℕ) : PoissonDivergenceRecovery.inverseCoefficient 1 (by norm_num) (normalized 1 (by norm_num) 0) n=0 := by
    rw [PoissonDivergenceRecovery.inverseCoefficient,poisson_coefficient_basis]
    simp
  simp only [he,zero_smul,tsum_zero]

theorem poisson_recovery_normalized_succ (k : ℕ) :
    PoissonDivergenceRecovery.recovery 1 (by norm_num) (normalized 1 (by norm_num) (k+1))=
      (Real.sqrt (k+1 : ℝ))⁻¹ • PoissonDivergenceRecovery.normalizedField 1 (by norm_num) k := by
  have he (n : ℕ) : PoissonDivergenceRecovery.inverseCoefficient 1 (by norm_num)
      (normalized 1 (by norm_num) (k+1)) n • PoissonDivergenceRecovery.normalizedField 1 (by norm_num) n=
        if n=k then (Real.sqrt (k+1 : ℝ))⁻¹ • PoissonDivergenceRecovery.normalizedField 1 (by norm_num) k else 0 := by
    rw [PoissonDivergenceRecovery.inverseCoefficient,poisson_coefficient_basis]
    by_cases hn : n=k
    · subst n; simp
    · simp [hn,show n+1≠k+1 by omega]
  have hs := (PoissonDivergenceRecovery.recovery_summable 1 (by norm_num) (normalized 1 (by norm_num) (k+1))).hasSum
  change HasSum _ (PoissonDivergenceRecovery.recovery 1 (by norm_num) (normalized 1 (by norm_num) (k+1))) at hs
  simp_rw [he] at hs
  exact hs.unique (hasSum_ite_eq k _)

theorem terminalEmbedding_single (u : CoefficientSpace) (hu : ‖u‖^2=1) (n : ℕ) :
    terminalEmbedding u hu (lp.single 2 n (1 : ℝ))=normalizedWick u n := by
  simp only [terminalEmbedding,OrthogonalFamily.linearIsometry_apply_single,LinearIsometry.toSpanSingleton_apply,one_smul]

theorem terminal_adjoint_normalized (u : CoefficientSpace) (hu : ‖u‖^2=1) (n : ℕ) :
    (terminalEmbedding u hu).toContinuousLinearMap.adjoint (normalizedWick u n)=lp.single 2 n (1 : ℝ) := by
  have he := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (terminalEmbedding u hu).toContinuousLinearMap).mp
    (terminalEmbedding u hu).norm_map
  rw [← terminalEmbedding_single u hu n]
  change ((terminalEmbedding u hu).toContinuousLinearMap.adjoint.comp (terminalEmbedding u hu).toContinuousLinearMap)
    (lp.single 2 n (1 : ℝ))=_
  rw [he]
  rfl

def poissonInput (u : CoefficientSpace) (hu : ‖u‖^2=1) : GaussianL2 →L[ℝ] ScalarL2 1 :=
  (basis 1 (by norm_num)).repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    (terminalEmbedding u hu).toContinuousLinearMap.adjoint

def poissonOutput (u : CoefficientSpace) (hu : ‖u‖^2=1) : FieldL2 1 →L[ℝ] GaussianL2 :=
  (terminalEmbedding u hu).toContinuousLinearMap.comp
    ((basis 1 (by norm_num)).repr.toLinearIsometry.toContinuousLinearMap.comp
      (PoissonWeightedScalarGeometry.weightedScalarEquiv 1 (by norm_num)).toLinearIsometry.toContinuousLinearMap)

def transferredRecovery (u : CoefficientSpace) (hu : ‖u‖^2=1) : GaussianL2 →L[ℝ] GaussianVectorL2 :=
  (scalarTensor u).comp ((poissonOutput u hu).comp
    ((PoissonDivergenceRecovery.recoveryOperator 1 (by norm_num)).comp (poissonInput u hu)))

theorem transferredRecovery_compact (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    IsCompactOperator (transferredRecovery u hu) :=
  ((PoissonRecoveryCompactness.recovery_compact 1 (by norm_num)).comp_clm (poissonInput u hu)).clm_comp
    ((scalarTensor u).comp (poissonOutput u hu))

theorem poissonInput_normalized (u : CoefficientSpace) (hu : ‖u‖^2=1) (n : ℕ) :
    poissonInput u hu (normalizedWick u n)=normalized 1 (by norm_num) n := by
  rw [poissonInput,ContinuousLinearMap.comp_apply,terminal_adjoint_normalized]
  exact (basis 1 (by norm_num)).repr_symm_single n |>.trans (basis_apply 1 (by norm_num) n)

theorem poissonOutput_normalizedField (u : CoefficientSpace) (hu : ‖u‖^2=1) (n : ℕ) :
    poissonOutput u hu (PoissonDivergenceRecovery.normalizedField 1 (by norm_num) n)=normalizedWick u n := by
  rw [poissonOutput,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]
  change terminalEmbedding u hu ((basis 1 (by norm_num)).repr
    (PoissonWeightedScalarGeometry.weightedScalarEquiv 1 (by norm_num)
      (PoissonDivergenceRecovery.normalizedField 1 (by norm_num) n)))=_
  rw [PoissonWeightedScalarGeometry.equiv_normalizedField,← basis_apply 1 (by norm_num) n,
    HilbertBasis.repr_self,terminalEmbedding_single]

theorem recovery_vacuum_zero : GaussianDivergenceRecovery.recovery gaussianOne=0 := by
  have hg := GaussianDivergenceRecovery.recovery_graph gaussianOne
  rw [GaussianNumberSectors.projection_zero,GaussianDeterministicGraphCore.gaussianOne_inner_self,one_smul,sub_self] at hg
  have hi := GaussianDivergenceRecovery.recovery_orthogonal_kernel gaussianOne _ hg
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp hi

theorem transferredRecovery_normalized (u : CoefficientSpace) (hu : ‖u‖^2=1) (n : ℕ) :
    transferredRecovery u hu (normalizedWick u n)=GaussianDivergenceRecovery.recovery (normalizedWick u n) := by
  rw [transferredRecovery,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply,poissonInput_normalized]
  change scalarTensor u (poissonOutput u hu (PoissonDivergenceRecovery.recovery 1 (by norm_num)
    (normalized 1 (by norm_num) n)))=_
  cases n with
  | zero =>
    rw [poisson_recovery_normalized_zero,map_zero,map_zero]
    simp only [normalizedWick,wick,core_zero,Nat.factorial_zero,Nat.cast_one,Real.sqrt_one,inv_one,one_smul]
    exact recovery_vacuum_zero.symm
  | succ n =>
    rw [poisson_recovery_normalized_succ,map_smul,poissonOutput_normalizedField,map_smul]
    simp only [normalizedWick]
    rw [GaussianDivergenceRecovery.recovery_smul,recovery_wick,map_smul,smul_smul]
    have he : (Real.sqrt ((n+1).factorial : ℝ))⁻¹=
        (Real.sqrt (n+1 : ℝ))⁻¹*(Real.sqrt (n.factorial : ℝ))⁻¹ := by
      rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Real.sqrt_mul (by positivity),mul_inv]
    rw [he]

theorem transferredRecovery_on_terminal (u : CoefficientSpace) (hu : ‖u‖^2=1)
    (f : GaussianL2) (hf : f∈singleGenerated u) :
    transferredRecovery u hu f=GaussianDivergenceRecovery.recovery f := by
  let L := transferredRecovery u hu-GaussianDivergenceRecovery.recoveryOperator
  have hs : wickSpan u≤L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    change L (wick u n)=0
    have ht : L (normalizedWick u n)=0 := by
      change transferredRecovery u hu (normalizedWick u n)-GaussianDivergenceRecovery.recovery (normalizedWick u n)=0
      rw [transferredRecovery_normalized,sub_self]
    rw [normalizedWick,map_smul] at ht
    exact (smul_eq_zero.mp ht).resolve_left (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by positivity))))
  have hc := (wickSpan u).topologicalClosure_minimal hs L.isClosed_ker
  rw [wickSpan_closure] at hc
  have he := hc hf
  change transferredRecovery u hu f-GaussianDivergenceRecovery.recovery f=0 at he
  exact sub_eq_zero.mp he

theorem terminal_adjoint_conditional (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) :
    (terminalEmbedding u hu).toContinuousLinearMap.adjoint (conditionalProjection (fun _ : Unit => u) f)=
      (terminalEmbedding u hu).toContinuousLinearMap.adjoint f := by
  have hm : u∈sourceSpan (fun _ : Unit => u) :=
    (Submodule.span ℝ (Set.range (fun _ : Unit => u))).le_topologicalClosure (Submodule.subset_span ⟨(),rfl⟩)
  apply ext_inner_right ℝ
  intro c
  rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]
  have he := (generated (fun _ : Unit => u)).inner_starProjection_left_eq_right f (terminalEmbedding u hu c)
  change inner ℝ (conditionalProjection (fun _ : Unit => u) f) (terminalEmbedding u hu c)=
    inner ℝ f (conditionalProjection (fun _ : Unit => u) (terminalEmbedding u hu c)) at he
  rw [conditional_fixes_terminalEmbedding _ u hu hm] at he
  exact he

theorem transferredRecovery_conditional (u : CoefficientSpace) (hu : ‖u‖^2=1) (f : GaussianL2) :
    transferredRecovery u hu (conditionalProjection (fun _ : Unit => u) f)=transferredRecovery u hu f := by
  simp only [transferredRecovery,poissonInput,ContinuousLinearMap.comp_apply,terminal_adjoint_conditional]

theorem transferredRecovery_eq_conditional_recovery (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    transferredRecovery u hu=GaussianDivergenceRecovery.recoveryOperator.comp (conditionalProjection (fun _ : Unit => u)) := by
  apply ContinuousLinearMap.ext
  intro f
  change transferredRecovery u hu f=GaussianDivergenceRecovery.recovery (conditionalProjection (fun _ : Unit => u) f)
  rw [← transferredRecovery_conditional u hu f]
  exact transferredRecovery_on_terminal u hu _ ((generated (fun _ : Unit => u)).starProjection_apply_mem f)

theorem single_observation_recovery_compact (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    IsCompactOperator (GaussianDivergenceRecovery.recoveryOperator.comp (conditionalProjection (fun _ : Unit => u))) := by
  rw [← transferredRecovery_eq_conditional_recovery u hu]
  exact transferredRecovery_compact u hu

theorem compact_recovery_noncompact_projection (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    IsCompactOperator (GaussianDivergenceRecovery.recoveryOperator.comp (conditionalProjection (fun _ : Unit => u))) ∧
      ¬ IsCompactOperator (conditionalProjection (fun _ : Unit => u)) := by
  refine ⟨single_observation_recovery_compact u hu,nonzero_observation_noncompact _ () ?_⟩
  intro hz
  rw [hz,norm_zero] at hu
  norm_num at hu
end OperatorDerivativeRewrite.Foundation.GaussianOneObservationRecoveryCompactness


