import Foundation.GaussianChaosCylinders

/-! Homogeneous chaos differentiation in every genuine Hilbert component. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianChaosLowering
open InfiniteGaussian FiniteGaussian GaussianNumberSectors
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def component (k : CoefficientSpace) : GaussianVectorL2 →L[ℝ] GaussianL2 :=
  (innerSL ℝ k).compLpL 2 gaussianProduct

theorem component_scalarTensor (k h : CoefficientSpace) (f : GaussianL2) :
    component k (scalarTensor h f) = inner ℝ k h • f := by
  apply Lp.ext
  filter_upwards [(innerSL ℝ k).coeFn_compLp (scalarTensor h f), scalarTensor_coeFn h f,
    Lp.coeFn_smul (inner ℝ k h) f] with ω hc ht hs
  change (innerSL ℝ k).compLp (scalarTensor h f) ω = _
  rw [hc, ht, hs]
  simp only [innerSL_apply_apply, real_inner_smul_right, Pi.smul_apply, smul_eq_mul]
  ring

theorem tensor_derivative_component_mem (s : Finset ℕ) (α : s → ℕ) (k : CoefficientSpace) :
    component k (finiteVectorPullback s (gradientPolynomialL2 (tensorHermitePolynomial α))) ∈
      sector ((∑ i, α i) - 1) := by
  classical
  rw [gradientPolynomialL2, finiteVectorPullback_polynomial]
  change component k (∑ i : s, scalarTensor (lp.single 2 i.val (1 : ℝ))
    (coordinatePolynomialDomain s (MvPolynomial.pderiv i (tensorHermitePolynomial α)))) ∈ _
  rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [component_scalarTensor]
  apply Submodule.smul_mem
  change finitePullback s (productPolynomialEmbedding
    (MvPolynomial.pderiv i (tensorHermitePolynomial α))) ∈ _
  by_cases hi : α i = 0
  · rw [tensorHermitePolynomial_lowering_zero α i hi, map_zero, map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hi
    rw [tensorHermitePolynomial_lowering α i m hm, map_smul, map_smul]
    apply Submodule.smul_mem
    change finitePullback s (productPolynomialL2 (tensorHermitePolynomial (Function.update α i m))) ∈ _
    rw [tensorHermitePolynomial_L2]
    have he : (∑ j, Function.update α i m j) = (∑ j, α j) - 1 := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
      have hh := Finset.sum_erase_add Finset.univ α (Finset.mem_univ i)
      omega
    rw [← he]
    exact finiteHermite_mem_sector s _

theorem projectedGradient_zero (f : GaussianL2) : projectedGradient 0 f = 0 := by
  have he := projectedGradient_energy 0 f
  simp only [Nat.cast_zero, zero_mul] at he
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (projectedGradient 0 f)])

theorem projectedGradient_finiteHermite (n : ℕ) (s : Finset ℕ) (α : s → ℕ) :
    projectedGradient n (finitePullback s (tensorHermite α)) =
      if n = ∑ i, α i then finiteVectorPullback s (gradientPolynomialL2 (tensorHermitePolynomial α))
      else 0 := by
  classical
  have hp := projection_of_sector (n := n) ⟨_, finiteHermite_mem_sector s α⟩
  have hd := (projectedGradient_graph n (finitePullback s (tensorHermite α))).1
  rw [hp] at hd
  split_ifs with hn
  · rw [if_pos hn] at hd
    have hg := closedCylindricalDerivative_core_graph
      (coordinatePolynomialDomain s (tensorHermitePolynomial α))
    rw [coordinatePolynomialDomain_derivative_lift] at hg
    change (finitePullback s (productPolynomialL2 (tensorHermitePolynomial α)), _) ∈ _ at hg
    rw [tensorHermitePolynomial_L2] at hg
    exact closedCylindricalDerivative.mem_graph_snd_inj hd hg rfl
  · rw [if_neg hn] at hd
    exact closedCylindricalDerivative.mem_graph_snd_inj hd closedCylindricalDerivative.graph.zero_mem rfl

theorem component_projectedGradient_mem (n : ℕ) (k : CoefficientSpace) (f : GaussianL2) :
    component k (projectedGradient n f) ∈ sector (n - 1) := by
  let L := (component k).comp (projectedGradient n)
  let S := (sector (n - 1)).comap L.toLinearMap
  have hc : IsClosed (S : Set GaussianL2) := (sector_isClosed _).preimage L.continuous
  have hf (s : Finset ℕ) (g : ScalarGaussianL2 s) : finitePullback s g ∈ S := by
    have hs : Submodule.span ℝ (Set.range (tensorHermite (ι := s))) ≤
        S.comap (finitePullback s).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨α, rfl⟩
      change component k (projectedGradient n (finitePullback s (tensorHermite α))) ∈ sector (n - 1)
      rw [projectedGradient_finiteHermite]
      split_ifs with hn
      · rw [hn]
        exact tensor_derivative_component_mem s α k
      · rw [map_zero]
        exact Submodule.zero_mem _
    exact (closure_minimal hs (hc.preimage (finitePullback s).continuous)) (tensorHermite_dense_span g)
  have hd : Dense (S : Set GaussianL2) := polynomialCylinders_dense.mono (by
    intro g hg
    obtain ⟨s, p, rfl⟩ := Set.mem_iUnion.mp hg
    exact hf s (productPolynomialL2 p))
  change f ∈ S
  have hh := hd f
  rw [hc.closure_eq] at hh
  exact hh

theorem component_derivative_intertwining (n : ℕ) (k : CoefficientSpace)
    {f : GaussianL2} {g : GaussianVectorL2} (hf : (f, g) ∈ closedCylindricalDerivative.graph) :
    component k (projectedGradient (n + 1) f) = projection n (component k g) := by
  let L := (projection n).comp (component k)
  have hs := (projectedGradient_hasSum hf).map L.toAddMonoidHom L.continuous
  change HasSum (fun m => L (projectedGradient m f)) (L g) at hs
  have he (m : ℕ) : L (projectedGradient m f) =
      if m = n + 1 then component k (projectedGradient (n + 1) f) else 0 := by
    by_cases hm : m = 0
    · simp [hm, L, projectedGradient_zero]
    · change projection n (component k (projectedGradient m f)) = _
      rw [projection_of_sector ⟨_, component_projectedGradient_mem m k f⟩]
      by_cases hmn : m = n + 1
      · subst m
        simp
      · have hne : n ≠ m - 1 := by omega
        simp only [hne, hmn, ↓reduceIte]
  have ht : HasSum (fun m => if m = n + 1 then component k (projectedGradient (n + 1) f) else 0)
      (projection n (component k g)) := by
    change HasSum _ (L g)
    simpa only [he] using hs
  exact (hasSum_ite_eq (n + 1) (component k (projectedGradient (n + 1) f))).unique ht

def projectionDomain (n : ℕ) (f : GaussianL2) : closedCylindricalDerivative.domain :=
  ⟨projection n f, LinearPMap.mem_domain_iff.mpr ⟨_, (projectedGradient_graph n f).1⟩⟩

theorem derivative_projection_value (n : ℕ) (f : GaussianL2) :
    closedCylindricalDerivative (projectionDomain n f) = projectedGradient n f :=
  closedCylindricalDerivative.mem_graph_snd_inj
    (closedCylindricalDerivative.mem_graph (projectionDomain n f)) (projectedGradient_graph n f).1 rfl

/-- Exact closed-operator lowering, tested against EVERY Hilbert direction.
No finite-coordinate support is imposed on either the function or direction. -/
theorem closedDerivative_projection_component (n : ℕ) (k : CoefficientSpace)
    (f : closedCylindricalDerivative.domain) :
    component k (closedCylindricalDerivative (projectionDomain (n + 1) f)) =
      projection n (component k (closedCylindricalDerivative f)) := by
  rw [derivative_projection_value]
  exact component_derivative_intertwining n k (closedCylindricalDerivative.mem_graph f)

end OperatorDerivativeRewrite.Foundation.GaussianChaosLowering
