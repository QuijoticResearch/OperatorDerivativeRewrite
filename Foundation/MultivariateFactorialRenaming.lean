import Foundation.MultivariateFactorialDomain
import Mathlib.Algebra.MvPolynomial.Rename

/-! Isometric coordinate embeddings and compatible derivatives on complete factorial domains. -/
noncomputable section
open Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MultivariateFactorialRenaming
open MultivariateFactorialDomain
variable {ι κ ν : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

def atom (e : ι ↪ κ) (d : ι →₀ ℕ) : H κ := lp.single 1 (d.embDomain e) (1 : ℝ)

omit [DecidableEq ι] in
theorem atom_norm (e : ι ↪ κ) (d : ι →₀ ℕ) : ‖atom e d‖ ≤ 1 := by
  rw [atom, lp.norm_single (by norm_num : (0 : ℝ≥0∞)<1)]
  norm_num

def renameOperator (e : ι ↪ κ) : H ι →L[ℝ] H κ :=
  L1BoundedSynthesis.synthesis (atom e) (atom_norm e)

theorem renaming_single (e : ι ↪ κ) (d : ι →₀ ℕ) (c : ℝ) :
    renameOperator e (lp.single 1 d c) = c • atom e d :=
  L1BoundedSynthesis.synthesis_single _ _ _ _

omit [DecidableEq ι] in
theorem renaming_coordinate (e : ι ↪ κ) (u : H ι) (d : ι →₀ ℕ) :
    renameOperator e u (d.embDomain e) = u d := by
  let L := lp.evalCLM ℝ (fun _ : κ →₀ ℕ => ℝ) 1 (d.embDomain e)
  have he := L.map_tsum (L1BoundedSynthesis.terms_summable (atom e) (atom_norm e) u)
  change L (L1BoundedSynthesis.synthesis (atom e) (atom_norm e) u) = _
  rw [L1BoundedSynthesis.synthesis_apply, he, tsum_eq_single d]
  · change (u d • (lp.single 1 (d.embDomain e) (1 : ℝ) : H κ)) (d.embDomain e) = u d
    simp
  · intro j hj
    change (u j • atom e j) (d.embDomain e) = 0
    have hne : d.embDomain e ≠ j.embDomain e :=
      fun h => hj ((Finsupp.embDomain_injective e h).symm)
    simp [atom, lp.single_apply, hne]

omit [DecidableEq ι] in
theorem renaming_norm_le (e : ι ↪ κ) : ‖renameOperator e‖ ≤ 1 :=
  L1BoundedSynthesis.synthesis_norm (atom e) (atom_norm e)

omit [DecidableEq ι] in
theorem renaming_norm (e : ι ↪ κ) (u : H ι) : ‖renameOperator e u‖ = ‖u‖ := by
  apply le_antisymm
  · simpa only [one_mul] using (renameOperator e).le_of_opNorm_le (renaming_norm_le e) u
  · have hs : Summable (fun j : κ →₀ ℕ => ‖renameOperator e u j‖) := by
      simpa using (renameOperator e u).property.summable
    have he := tsum_comp_le_tsum_of_inj hs (fun j => norm_nonneg (renameOperator e u j))
      (Finsupp.embDomain_injective e (M := ℕ))
    have hu : ‖u‖ = ∑' d : ι →₀ ℕ, ‖u d‖ := by
      simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) u
    have hv : ‖renameOperator e u‖ = ∑' j : κ →₀ ℕ, ‖renameOperator e u j‖ := by
      simpa using lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) (renameOperator e u)
    rw [hu, hv]
    simpa only [Function.comp_def, renaming_coordinate] using he

def isometricRenaming (e : ι ↪ κ) : H ι →ₗᵢ[ℝ] H κ where
  toLinearMap := (renameOperator e).toLinearMap
  norm_map' := renaming_norm e

omit [DecidableEq ι] [DecidableEq κ] in
theorem degree_embDomain (e : ι ↪ κ) (d : ι →₀ ℕ) : (d.embDomain e).degree = d.degree := by
  simp only [Finsupp.degree_apply, Finsupp.support_embDomain, Finset.sum_map,
    Finsupp.embDomain_apply_self]

omit [DecidableEq ι] in
theorem renaming_polynomial (e : ι ↪ κ) (P : MvPolynomial ι ℝ) :
    renameOperator e (polynomial P) = polynomial (MvPolynomial.rename e P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [polynomial_monomial, renaming_single, MvPolynomial.rename_monomial,
      ← Finsupp.embDomain_eq_mapDomain e, polynomial_monomial, degree_embDomain]
    change ((d.degree.factorial : ℝ)*c) • (lp.single 1 (d.embDomain e) (1 : ℝ) : H κ) =
      lp.single 1 (d.embDomain e) ((d.degree.factorial : ℝ)*c)
    rw [← lp.single_smul]
    simp only [smul_eq_mul, mul_one]
  | add P Q hP hQ =>
    change renameOperator e (polynomialMap (P + Q)) = polynomialMap (MvPolynomial.rename e (P + Q))
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (·+·) hP hQ

omit [DecidableEq ι] in
theorem renaming_comp (e : ι ↪ κ) (f : κ ↪ ν) :
    (renameOperator f).comp (renameOperator e) = renameOperator (e.trans f) := by
  classical
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext P
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, renaming_polynomial,
    MvPolynomial.rename_rename]
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
theorem polynomialDerivative_rename (e : ι ↪ κ) (v : κ → ℝ) (P : MvPolynomial ι ℝ) :
    polynomialDerivative v (MvPolynomial.rename e P) =
      MvPolynomial.rename e (polynomialDerivative (fun i => v (e i)) P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [MvPolynomial.rename_monomial, ← Finsupp.embDomain_eq_mapDomain e,
      polynomialDerivative_monomial, polynomialDerivative_monomial, map_sum]
    simp only [Finsupp.support_embDomain, Finset.sum_map, Finsupp.embDomain_apply_self,
      MvPolynomial.rename_monomial, ← Finsupp.embDomain_eq_mapDomain e,
      Finsupp.embDomain_tsub, Finsupp.embDomain_single]
  | add P Q hP hQ =>
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (·+·) hP hQ

theorem derivative_rename (e : ι ↪ κ) (v : κ → ℝ) (hv : ∀ i, |v i| ≤ 1) :
    (derivative v hv).comp (renameOperator e) = (renameOperator e).comp
      (derivative (fun i => v (e i)) (fun i => hv (e i))) := by
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer
    (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  funext P
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, renaming_polynomial,
    derivative_polynomial, polynomialDerivative_rename]

end OperatorDerivativeRewrite.Foundation.MultivariateFactorialRenaming
