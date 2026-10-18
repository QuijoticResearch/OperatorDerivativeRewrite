import Foundation.MultivariateFactorialSubstitution
import Foundation.HigherHeatAnalyticCylinderDomain

/-! Actual bounded directional derivatives restricted to the complete common cylinder domain. -/
noncomputable section
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCommonDerivative
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatAnalyticCylinderDomain
open MultivariateFactorialDomain MultivariateFactorialRenaming MultivariateFactorialSubstitution
open Classical

theorem derivative_rename {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ↪ κ) (v : κ → ℝ) (hv : ∀ j, |v j| ≤ 1) (P : MvPolynomial ι ℝ) :
    derivative v hv (renameOperator e (polynomial P)) =
      renameOperator e (polynomial (polynomialDerivative (fun i => v (e i)) P)) := by
  rw [renaming_polynomial, derivative_polynomial]
  rw [← polynomialSubstitution_one e, polynomialDerivative_substitution]
  simp only [one_mul]
  rw [polynomialSubstitution_one, renaming_polynomial]

def gridDerivative (n : ℕ) (w : Fin (size n) → ℝ) : Test n →ₗ[ℝ] Test n :=
  (coordinates n).toLinearMap.comp
    ((polynomialDerivative w).toLinearMap.comp (coordinates n).symm.toLinearMap)

theorem derivative_embedding (v : Time → ℝ) (hv : ∀ i, |v i| ≤ 1) (n : ℕ) (P : Test n) :
    derivative v hv (embedding (cylinderOf n P)) =
      embedding (cylinderOf n (gridDerivative n (fun i => v (timeEmbedding n i)) P)) := by
  simp only [embedding_apply, gridEmbedding_apply, encode_apply]
  rw [derivative_rename]
  simp only [gridDerivative, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.symm_apply_apply]
  rfl

theorem derivative_mem (v : Time → ℝ) (hv : ∀ i, |v i| ≤ 1) (u : Domain) :
    derivative v hv u.val ∈ commonClosure := by
  refine core_dense.induction_on u ?_ ?_
  · exact commonClosure_closed.preimage (by fun_prop)
  · intro F
    induction F using DirectLimit.induction with
    | _ n P =>
      change derivative v hv (embedding (cylinderOf n P)) ∈ commonClosure
      rw [derivative_embedding]
      exact embedding.range.le_topologicalClosure ⟨_, rfl⟩

def operator (v : Time → ℝ) (hv : ∀ i, |v i| ≤ 1) : Domain →L[ℝ] Domain :=
  ((derivative v hv).comp commonClosure.subtypeL).codRestrict commonClosure (derivative_mem v hv)

theorem operator_apply (v : Time → ℝ) (hv : ∀ i, |v i| ≤ 1) (u : Domain) :
    (operator v hv u).val = derivative v hv u.val := rfl

theorem operator_bound (v : Time → ℝ) (hv : ∀ i, |v i| ≤ 1) (u : Domain) :
    ‖operator v hv u‖ ≤ ‖u‖ := by
  change ‖derivative v hv u.val‖ ≤ ‖u.val‖
  simpa only [one_mul] using (derivative v hv).le_of_opNorm_le (derivative_norm v hv) u.val

theorem operator_norm (v : Time → ℝ) (hv : ∀ i, |v i| ≤ 1) : ‖operator v hv‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => by simpa only [one_mul] using operator_bound v hv u)

theorem operator_core (v : Time → ℝ) (hv : ∀ i, |v i| ≤ 1) (n : ℕ) (P : Test n) :
    operator v hv (core (cylinderOf n P)) =
      core (cylinderOf n (gridDerivative n (fun i => v (timeEmbedding n i)) P)) := by
  apply Subtype.ext
  exact derivative_embedding v hv n P

theorem operator_pow_bound (v : Time → ℝ) (hv : ∀ i, |v i| ≤ 1) (r : ℕ) (u : Domain) :
    ‖((operator v hv)^r) u‖ ≤ ‖u‖ := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
    rw [pow_succ']
    exact (operator_bound v hv (((operator v hv)^r) u)).trans ih

theorem operator_pow_core (v : Time → ℝ) (hv : ∀ i, |v i| ≤ 1) (r n : ℕ) (P : Test n) :
    ((operator v hv)^r) (core (cylinderOf n P)) =
      core (cylinderOf n ((gridDerivative n (fun i => v (timeEmbedding n i)))^[r] P)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [pow_succ']
    change operator v hv (((operator v hv)^r) (core (cylinderOf n P))) = _
    rw [ih, operator_core, Function.iterate_succ_apply']

end OperatorDerivativeRewrite.Foundation.HigherHeatCommonDerivative
