import Foundation.HigherHeatPolynomialRefinement
import Mathlib.LinearAlgebra.Pi

/-! Polynomial pullback by finite real linear maps, with genuine evaluation identities. -/
noncomputable section
open scoped BigOperators
namespace OperatorDerivativeRewrite.Foundation.PolynomialLinearSubstitution
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

open Classical in
def linearVariable (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (i : κ) : MvPolynomial ι ℝ :=
  ∑ j, MvPolynomial.C (L (Pi.single j 1) i) * MvPolynomial.X j

omit [Fintype κ] in
theorem eval_variable (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (i : κ) (x : ι → ℝ) :
    MvPolynomial.eval x (linearVariable L i) = L x i := by
  classical
  have hx : (∑ j, x j • (Pi.single j 1 : ι → ℝ)) = x := by
    ext k
    simp [Pi.single_apply]
  have he := congrArg (fun y : ι → ℝ => L y i) hx
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  rw [linearVariable, map_sum]
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact (Finset.sum_congr rfl (fun j _ => mul_comm _ _)).trans he

def pullback (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial ι ℝ :=
  MvPolynomial.aeval (linearVariable L)

omit [Fintype κ] in
theorem eval_pullback (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (P : MvPolynomial κ ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (pullback L P) = MvPolynomial.eval (L x) P := by
  have he : (MvPolynomial.aeval x).comp (pullback L) = MvPolynomial.aeval (L x) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, pullback, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact eval_variable L i x
  exact DFunLike.congr_fun he P

theorem pullback_id (P : MvPolynomial ι ℝ) : pullback (LinearMap.id (R := ℝ)) P = P := by
  apply MvPolynomial.funext
  intro x
  rw [eval_pullback]
  rfl

omit [Fintype ν] in
theorem pullback_comp (L : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (M : (κ → ℝ) →ₗ[ℝ] (ν → ℝ)) (P : MvPolynomial ν ℝ) :
    pullback L (pullback M P) = pullback (M.comp L) P := by
  apply MvPolynomial.funext
  intro x
  rw [eval_pullback, eval_pullback, eval_pullback]
  rfl

def equivalence (L : (ι → ℝ) ≃ₗ[ℝ] (κ → ℝ)) : MvPolynomial κ ℝ ≃ₐ[ℝ] MvPolynomial ι ℝ :=
  { pullback L.toLinearMap with
    invFun := pullback L.symm.toLinearMap
    left_inv := by
      intro P
      apply MvPolynomial.funext
      intro x
      change MvPolynomial.eval x (pullback L.symm.toLinearMap (pullback L.toLinearMap P)) = _
      rw [eval_pullback, eval_pullback]
      exact congrArg (fun y : κ → ℝ => MvPolynomial.eval y P) (L.apply_symm_apply x)
    right_inv := by
      intro P
      apply MvPolynomial.funext
      intro x
      change MvPolynomial.eval x (pullback L.toLinearMap (pullback L.symm.toLinearMap P)) = _
      rw [eval_pullback, eval_pullback]
      exact congrArg (fun y : ι → ℝ => MvPolynomial.eval y P) (L.symm_apply_apply x) }

theorem equivalence_apply (L : (ι → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (P : MvPolynomial κ ℝ) :
    equivalence L P = pullback L.toLinearMap P := rfl

theorem equivalence_symm_apply (L : (ι → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (P : MvPolynomial ι ℝ) :
    (equivalence L).symm P = pullback L.symm.toLinearMap P := rfl

end OperatorDerivativeRewrite.Foundation.PolynomialLinearSubstitution
