import Foundation.GaussianWickPredictionBound
import Foundation.GaussianWickContinuity
import Mathlib.Topology.Algebra.MvPolynomial

/-! Exact Wick prediction from arbitrary actual Gaussian observation families. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianWickConditionalProjection
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeFieldNorm GaussianNumberSectors
open GaussianConditionalGraph GaussianWickPredictionBound IBMCubicFirstChaos

theorem wick_pairing_recursion {I : Type*} [Fintype I] (h : I → CoefficientSpace)
    (u : CoefficientSpace) (n : ℕ) (p : MvPolynomial I ℝ) :
    inner ℝ (wick u (n+1) : GaussianL2) (familyPolynomialEmbedding h p)=
      ∑ i, inner ℝ u (h i)*inner ℝ (wick u n : GaussianL2)
        (familyPolynomialEmbedding h (MvPolynomial.pderiv i p)) := by
  have hi := polynomialDerivative_rank_pairing (cylinderCore h p) (wick u n) u
  rw [cylinder_gradient_expansion,← wick_raising] at hi
  change inner ℝ (∑ i, scalarTensor (h i) (cylinderCore h (MvPolynomial.pderiv i p)))
    (scalarTensor u (wick u n))=inner ℝ (familyPolynomialEmbedding h p) (wick u (n+1)) at hi
  simp only [sum_inner,scalarTensor_pair_inner] at hi
  calc
    _ = ∑ i, inner ℝ u (h i)*inner ℝ (wick u n : GaussianL2)
        (cylinderCore h (MvPolynomial.pderiv i p) : GaussianL2) := by
      simpa only [real_inner_comm,mul_comm] using hi.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rfl

theorem wick_pairing_eq_of_covariances {I : Type*} [Fintype I] (h : I → CoefficientSpace)
    (u v : CoefficientSpace) (hc : ∀ i, inner ℝ u (h i)=inner ℝ v (h i))
    (n : ℕ) (p : MvPolynomial I ℝ) :
    inner ℝ (wick u n : GaussianL2) (familyPolynomialEmbedding h p)=
      inner ℝ (wick v n : GaussianL2) (familyPolynomialEmbedding h p) := by
  induction n generalizing p with
  | zero => simp only [wick,core_zero]
  | succ n ih =>
    rw [wick_pairing_recursion,wick_pairing_recursion]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc i,ih]

theorem wick_family_pairing_eq {I : Type*} (h : I → CoefficientSpace) (u v : CoefficientSpace)
    (hc : ∀ i, inner ℝ u (h i)=inner ℝ v (h i)) (n : ℕ) (p : MvPolynomial I ℝ) :
    inner ℝ (wick u n : GaussianL2) (familyPolynomialEmbedding h p)=
      inner ℝ (wick v n : GaussianL2) (familyPolynomialEmbedding h p) := by
  obtain ⟨s,p,rfl⟩ := MvPolynomial.exists_finset_rename p
  rw [familyPolynomial_rename]
  exact wick_pairing_eq_of_covariances (fun i : s => h i) u v (fun i => hc i) n p

theorem conditional_wick_eq_of_covariances {I : Type*} (h : I → CoefficientSpace)
    (u v : CoefficientSpace) (hc : ∀ i, inner ℝ u (h i)=inner ℝ v (h i)) (n : ℕ) :
    conditionalProjection h (wick u n)=conditionalProjection h (wick v n) := by
  let r : GaussianL2 := (wick u n : GaussianL2)-(wick v n : GaussianL2)
  have hs : (familyPolynomialEmbedding h).range ≤ (innerSL ℝ r).ker := by
    rintro _ ⟨p,rfl⟩
    change inner ℝ ((wick u n : GaussianL2)-(wick v n : GaussianL2)) (familyPolynomialEmbedding h p)=0
    rw [inner_sub_left,wick_family_pairing_eq h u v hc n p,sub_self]
  have hcl := (familyPolynomialEmbedding h).range.topologicalClosure_minimal hs
    (innerSL ℝ r).isClosed_ker
  rw [familyPolynomial_closure] at hcl
  have ho : r ∈ (generated h)ᗮ := by
    apply (generated h).mem_orthogonal r |>.mpr
    intro f hf
    have hi := hcl hf
    change inner ℝ r f=0 at hi
    simpa only [real_inner_comm] using hi
  have hz : conditionalProjection h r=0 := by
    exact (generated h).eq_starProjection_of_mem_orthogonal (generated h).zero_mem
      (by simpa only [sub_zero] using ho)
  change conditionalProjection h ((wick u n : GaussianL2)-(wick v n : GaussianL2))=0 at hz
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

def sourceSpan {I : Type*} (h : I → CoefficientSpace) : Submodule ℝ CoefficientSpace :=
  (Submodule.span ℝ (Set.range h)).topologicalClosure

instance sourceSpan_complete {I : Type*} (h : I → CoefficientSpace) : CompleteSpace (sourceSpan h) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def sourceProjection {I : Type*} (h : I → CoefficientSpace) : CoefficientSpace →L[ℝ] CoefficientSpace :=
  (sourceSpan h).starProjection

theorem sourceProjection_pairing {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) (i : I) :
    inner ℝ (sourceProjection h u) (h i)=inner ℝ u (h i) := by
  have hm : h i ∈ sourceSpan h :=
    (Submodule.span ℝ (Set.range h)).le_topologicalClosure (Submodule.subset_span ⟨i,rfl⟩)
  have he := (sourceSpan h).starProjection_inner_eq_zero u (h i) hm
  rw [inner_sub_left] at he
  change inner ℝ ((sourceSpan h).starProjection u) (h i)=inner ℝ u (h i)
  linarith

theorem firstChaos_mem_generated_of_sourceSpan {I : Type*} (h : I → CoefficientSpace)
    (v : CoefficientSpace) (hv : v ∈ sourceSpan h) : firstChaosEmbedding v ∈ generated h := by
  let S := (generated h).comap firstChaosEmbedding.toLinearMap
  have hs : Submodule.span ℝ (Set.range h) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change firstChaosEmbedding (h i) ∈ generated h
    rw [← wick_one_eq_embedding]
    exact observed_wick_mem h i 1
  have hc : IsClosed (S : Set CoefficientSpace) :=
    (generated_isClosed h).preimage firstChaosEmbedding.continuous
  exact (Submodule.span ℝ (Set.range h)).topologicalClosure_minimal hs hc hv

theorem wick_mem_generated_of_firstChaos {I : Type*} (h : I → CoefficientSpace) (v : CoefficientSpace)
    (hv : firstChaosEmbedding v ∈ generated h) (n : ℕ) : (wick v n : GaussianL2) ∈ generated h := by
  have hx : AEStronglyMeasurable[MeasurableSpace.comap (firstChaosFamily h) inferInstance]
      (firstChaosEmbedding v) gaussianProduct := hv
  have hc : Continuous (fun x : ℝ => value n x (‖v‖^2)) := by
    exact (MvPolynomial.continuous_eval (polynomial (‖v‖^2) n)).comp (continuous_pi fun _ => continuous_id)
  exact (hc.comp_aestronglyMeasurable hx).congr (core_coeFn v (‖v‖^2) n).symm

theorem wick_mem_generated_of_sourceSpan {I : Type*} (h : I → CoefficientSpace)
    (v : CoefficientSpace) (hv : v ∈ sourceSpan h) (n : ℕ) : (wick v n : GaussianL2) ∈ generated h :=
  wick_mem_generated_of_firstChaos h v (firstChaos_mem_generated_of_sourceSpan h v hv) n

theorem conditional_wick_projection {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) (n : ℕ) :
    conditionalProjection h (wick u n)=(wick (sourceProjection h u) n : GaussianL2) := by
  rw [conditional_wick_eq_of_covariances h u (sourceProjection h u)
    (fun i => (sourceProjection_pairing h u i).symm) n]
  apply Submodule.starProjection_eq_self_iff.mpr
  exact wick_mem_generated_of_sourceSpan h _ ((sourceSpan h).starProjection_apply_mem u) n

theorem conditional_firstChaos_projection {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) :
    conditionalProjection h (firstChaosEmbedding u)=firstChaosEmbedding (sourceProjection h u) := by
  rw [← wick_one_eq_embedding,conditional_wick_projection,wick_one_eq_embedding]

theorem conditional_wick_energy {I : Type*} (h : I → CoefficientSpace) (u : CoefficientSpace) (n : ℕ) :
    ‖conditionalProjection h (wick u n)‖^2=(n.factorial : ℝ)*(‖sourceProjection h u‖^2)^n := by
  rw [conditional_wick_projection,GaussianWickContinuity.wick_norm_sq]

theorem conditional_wick_energy_from_linear {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (n : ℕ) :
    ‖conditionalProjection h (wick u n)‖^2=
      (n.factorial : ℝ)*(‖conditionalProjection h (firstChaosEmbedding u)‖^2)^n := by
  rw [conditional_wick_energy,conditional_firstChaos_projection,LinearIsometry.norm_map]

namespace Fractional

theorem forecast_energy_exact (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1) (t : ℝ≥0) (n : ℕ) :
    ‖GaussianWickPredictionBound.Fractional.forecast H hH0 hH1 t n‖^2=
      (n.factorial : ℝ)*(‖FractionalPredictionObstruction.forecast H hH0 hH1 t‖^2)^n := by
  simpa only [GaussianWickPredictionBound.Fractional.forecast,FractionalWickCovariance.cylinder,
    FractionalPredictionObstruction.forecast,FractionalGaussianProcess.value] using
      conditional_wick_energy_from_linear (FractionalPredictionObstruction.pastDirections H hH0 hH1 t)
        (FractionalGaussianProcess.direction H hH0 hH1 1) n

end Fractional
end OperatorDerivativeRewrite.Foundation.GaussianWickConditionalProjection
