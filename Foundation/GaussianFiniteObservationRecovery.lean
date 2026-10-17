import Foundation.GaussianRecoverySpectralCompactness
import Foundation.GaussianRecoveryCompactApproximationGap
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite source dimension, rather than number of observation labels, controls
compact Gaussian recovery. Finite Hermite ranges are constructed explicitly. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianFiniteObservationRecovery
open InfiniteGaussian FiniteGaussian GaussianNumberSectors GaussianConditionalGraph
open GaussianWickConditionalProjection GaussianDivergenceRecovery
open GaussianRecoverySpectralCompactness GaussianRecoveryCompactnessObstruction

def boundedHermiteSpace {J : Type*} [Fintype J]
    (v : J → CoefficientSpace) (n : ℕ) : Submodule ℝ GaussianL2 :=
  Submodule.span ℝ (Set.range (fun a : J → Fin (n + 1) =>
    isonormalCylinderL2 v (tensorHermitePolynomial (fun j => (a j : ℕ)))))

instance boundedHermiteSpace_finite {J : Type*} [Fintype J]
    (v : J → CoefficientSpace) (n : ℕ) : FiniteDimensional ℝ (boundedHermiteSpace v n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- An explicit finite upper bound; the exact homogeneous dimension can be smaller. -/
theorem boundedHermiteSpace_dimension {J : Type*} [Fintype J]
    (v : J → CoefficientSpace) (n : ℕ) :
    Module.finrank ℝ (boundedHermiteSpace v n) ≤ (n+1)^(Fintype.card J) := by
  classical
  have h := finrank_range_le_card (R := ℝ) (fun a : J → Fin (n+1) =>
    isonormalCylinderL2 v (tensorHermitePolynomial (fun j => (a j : ℕ))))
  simpa only [Fintype.card_fun, Fintype.card_fin, Set.finrank, boundedHermiteSpace] using h

theorem tensor_mem_bounded {J : Type*} [Fintype J]
    (v : J → CoefficientSpace) (n : ℕ) (a : J → ℕ) (ha : ∑ j, a j = n) :
    isonormalCylinderL2 v (tensorHermitePolynomial a) ∈ boundedHermiteSpace v n := by
  classical
  have hb (j : J) : a j < n + 1 := by
    have h := Finset.single_le_sum (fun i _ => Nat.zero_le (a i)) (Finset.mem_univ j)
    omega
  exact Submodule.subset_span ⟨(fun j => ⟨a j, hb j⟩), rfl⟩

theorem orthonormal_projection_polynomial_mem {J : Type*} [Fintype J]
    (v : J → CoefficientSpace) (hv : Orthonormal ℝ v) (n : ℕ) (p : MvPolynomial J ℝ) :
    projection n (isonormalCylinderL2 v p) ∈ boundedHermiteSpace v n := by
  classical
  let L := (projection n).toLinearMap.comp (familyPolynomialEmbedding v)
  have hs : Submodule.span ℝ (Set.range (tensorHermitePolynomial (ι := J))) ≤
      (boundedHermiteSpace v n).comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change projection n (isonormalCylinderL2 v (tensorHermitePolynomial a)) ∈
      boundedHermiteSpace v n
    rw [projection_of_sector ⟨_, orthonormal_tensor_mem_sector v hv a⟩]
    split_ifs with ha
    · exact tensor_mem_bounded v n a ha.symm
    · exact (boundedHermiteSpace v n).zero_mem
  rw [tensorHermitePolynomial_span] at hs
  exact hs (Submodule.mem_top (x := p))

theorem substituted_projection_mem {I J : Type*} [Fintype I] [Fintype J]
    (h : I → CoefficientSpace) (v : J → CoefficientSpace) (hv : Orthonormal ℝ v)
    (c : I → J → ℝ) (hc : ∀ i, ∑ j, c i j • v j = h i)
    (n : ℕ) (p : MvPolynomial I ℝ) :
    projection n (isonormalCylinderL2 h p) ∈ boundedHermiteSpace v n := by
  have he := isonormalCylinderL2_linear_substitution v c p
  rw [show (fun i => ∑ j, c i j • v j) = h from funext hc] at he
  rw [he]
  exact orthonormal_projection_polynomial_mem v hv n _

theorem observed_projection_bounded {I : Type*} (h : I → CoefficientSpace)
    [FiniteDimensional ℝ (sourceSpan h)] (n : ℕ) (f : GaussianL2) :
    projection n (conditionalProjection h f) ∈ boundedHermiteSpace
      (fun j => ((stdOrthonormalBasis ℝ (sourceSpan h)) j : CoefficientSpace)) n := by
  classical
  let S := sourceSpan h
  let b := stdOrthonormalBasis ℝ S
  let v : Fin (Module.finrank ℝ S) → CoefficientSpace := fun j => (b j : CoefficientSpace)
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    exact (orthonormal_iff_ite.mp b.orthonormal) i j
  have hs : (familyPolynomialEmbedding h).range ≤
      (boundedHermiteSpace v n).comap (projection n).toLinearMap := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨s, p, rfl⟩ := MvPolynomial.exists_finset_rename p
    rw [familyPolynomial_rename]
    let h' : s → S := fun i => ⟨h i, (Submodule.span ℝ (Set.range h)).le_topologicalClosure
      (Submodule.subset_span ⟨i.val, rfl⟩)⟩
    let c : s → Fin (Module.finrank ℝ S) → ℝ := fun i j => inner ℝ (b j) (h' i)
    have hc (i : s) : ∑ j, c i j • v j = h i := by
      have he := congrArg (fun x : S => (x : CoefficientSpace)) (b.sum_repr' (h' i))
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using he
    exact substituted_projection_mem (fun i : s => h i) v hv c hc n p
  have hcl := (familyPolynomialEmbedding h).range.topologicalClosure_minimal hs
    ((Submodule.closed_of_finiteDimensional (boundedHermiteSpace v n)).preimage
      (projection n).continuous)
  rw [familyPolynomial_closure] at hcl
  exact hcl ((generated h).starProjection_apply_mem f)

theorem observed_chaos_block_compact {I : Type*} (h : I → CoefficientSpace)
    [FiniteDimensional ℝ (sourceSpan h)] (n : ℕ) :
    IsCompactOperator ((projection n).comp (conditionalProjection h)) := by
  let S := boundedHermiteSpace
    (fun j => ((stdOrthonormalBasis ℝ (sourceSpan h)) j : CoefficientSpace)) n
  let T := (projection n).comp (conditionalProjection h)
  let U := T.codRestrict S (observed_projection_bounded h n)
  letI : FiniteDimensional ℝ S := boundedHermiteSpace_finite _ _
  have hc := isCompactOperator_of_locallyCompactSpace_dom U
  have he : S.subtypeL.comp U = T := by rfl
  change IsCompactOperator T
  rw [← he]
  exact hc.clm_comp S.subtypeL

theorem finite_source_recovery_compact {I : Type*} (h : I → CoefficientSpace)
    [FiniteDimensional ℝ (sourceSpan h)] :
    IsCompactOperator (recoveryOperator.comp (conditionalProjection h)) :=
  (recovery_composition_compact_iff _).mpr (fun n _ => observed_chaos_block_compact h n)

theorem compact_recovery_source_finite {I : Type*} (h : I → CoefficientSpace)
    (hc : IsCompactOperator (recoveryOperator.comp (conditionalProjection h))) :
    FiniteDimensional ℝ (sourceSpan h) := by
  let U : sourceSpan h →ₗᵢ[ℝ] GaussianL2 := firstChaosEmbedding.comp (sourceSpan h).subtypeₗᵢ
  let V : sourceSpan h →ₗᵢ[ℝ] GaussianVectorL2 := vacuumEmbedding.comp (sourceSpan h).subtypeₗᵢ
  have he : V.toContinuousLinearMap.adjoint.comp
      ((recoveryOperator.comp (conditionalProjection h)).comp U.toContinuousLinearMap) =
      ContinuousLinearMap.id ℝ (sourceSpan h) := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℝ
    intro y
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.id_apply]
    change inner ℝ (recovery (conditionalProjection h (firstChaosEmbedding x)))
      (vacuumEmbedding y) = inner ℝ x y
    rw [conditional_firstChaos_projection]
    have hx : sourceProjection h (x : CoefficientSpace) = x :=
      (sourceSpan h).starProjection_eq_self_iff.mpr x.property
    rw [hx]
    change inner ℝ (vacuumEmbedding x) (vacuumEmbedding y) = inner ℝ x y
    rw [vacuumEmbedding.inner_map_map]
    rfl
  have hi := (hc.comp_clm U.toContinuousLinearMap).clm_comp V.toContinuousLinearMap.adjoint
  change IsCompactOperator (V.toContinuousLinearMap.adjoint.comp
    ((recoveryOperator.comp (conditionalProjection h)).comp U.toContinuousLinearMap)) at hi
  rw [he] at hi
  exact isCompactOperator_id_iff_finiteDimensional.mp hi

/-- Exact classification, allowing arbitrary observation index sets. -/
theorem recovery_compact_iff_finite_source {I : Type*} (h : I → CoefficientSpace) :
    IsCompactOperator (recoveryOperator.comp (conditionalProjection h)) ↔
      FiniteDimensional ℝ (sourceSpan h) := by
  constructor
  · exact compact_recovery_source_finite h
  · intro hs
    letI := hs
    exact finite_source_recovery_compact h

/-- Every finite family has compact full recovery, including singular covariance. -/
theorem finite_observations_recovery_compact {I : Type*} [Finite I]
    (h : I → CoefficientSpace) :
    IsCompactOperator (recoveryOperator.comp (conditionalProjection h)) := by
  let S := Submodule.span ℝ (Set.range h)
  letI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range h)
  have he : sourceSpan h = S := (Submodule.closed_of_finiteDimensional S).submodule_topologicalClosure_eq
  haveI : FiniteDimensional ℝ (sourceSpan h) := by rw [he]; infer_instance
  exact finite_source_recovery_compact h

end OperatorDerivativeRewrite.Foundation.GaussianFiniteObservationRecovery
