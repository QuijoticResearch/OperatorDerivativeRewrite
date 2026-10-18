import Foundation.PolynomialLinearSubstitution
import Foundation.HigherHeatPolynomialPathDomain
import Foundation.MultivariateFactorialRenaming

/-! Common analytic cylinder domains and their precise time-topology boundary. -/
noncomputable section
open scoped BigOperators NNReal ENNReal Topology

namespace OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialCoordinates
open HigherHeatPolynomialCylinders HigherHeatPositionVariation HigherHeatGridDoubling
open HigherHeatPolynomialPathDomain HigherHeatCylinderFourier
open PolynomialLinearSubstitution

def coordinates (n : ℕ) : Test n ≃ₐ[ℝ] Test n := equivalence (cumulativeEquiv (size n))

theorem eval_coordinates (n : ℕ) (P : Test n) (x : Fin (size n) → ℝ) :
    MvPolynomial.eval x (coordinates n P) = MvPolynomial.eval (cumulativeEquiv (size n) x) P :=
  eval_pullback _ _ _

theorem eval_inverse (n : ℕ) (P : Test n) (x : Fin (size n) → ℝ) :
    MvPolynomial.eval x ((coordinates n).symm P) =
      MvPolynomial.eval ((cumulativeEquiv (size n)).symm x) P :=
  eval_pullback _ _ _

theorem coordinates_X (n : ℕ) (i : Fin (size n)) :
    coordinates n (MvPolynomial.X i) = positionPolynomial n i := by
  apply MvPolynomial.funext
  intro x
  rw [eval_coordinates, MvPolynomial.eval_X, cumulativeEquiv_apply, cumulative_apply]
  simp only [positionPolynomial, map_sum, MvPolynomial.eval_X]

def oldEmbedding (n : ℕ) : Fin (size n) ↪ Fin (size (n+1)) where
  toFun := oddIndex
  inj' := by
    intro i j he
    apply Fin.ext
    have hh := congrArg Fin.val he
    dsimp [oddIndex] at hh
    omega

theorem step_coordinates (n : ℕ) (P : Test n) :
    step n (coordinates n P) =
      coordinates (n+1) (MvPolynomial.rename (oldEmbedding n) P) := by
  apply MvPolynomial.funext
  intro x
  have hleft : MvPolynomial.eval x (step n (coordinates n P)) =
      MvPolynomial.eval (cumulativeEquiv (size n)
        (HigherHeatPolynomialRefinement.coarsen (@pairBlock (size n)) x)) P :=
    (HigherHeatPolynomialRefinement.eval_pullback (@pairBlock (size n)) (coordinates n P) x).trans
      (eval_coordinates n P (HigherHeatPolynomialRefinement.coarsen (@pairBlock (size n)) x))
  have hmid := congrArg (fun y => MvPolynomial.eval y P) (cumulative_coarsen (size n) x)
  have hright : MvPolynomial.eval x (coordinates (n+1) (MvPolynomial.rename (oldEmbedding n) P)) =
      MvPolynomial.eval (oldPositions (cumulativeEquiv (size (n+1)) x)) P := by
    exact (eval_coordinates (n+1) (MvPolynomial.rename (oldEmbedding n) P) x).trans
      (MvPolynomial.eval_rename (oldEmbedding n) (cumulativeEquiv (size (n+1)) x) P)
  exact hleft.trans (hmid.trans hright.symm)

theorem inverse_step (n : ℕ) (P : Test n) :
    (coordinates (n+1)).symm (step n P) =
      MvPolynomial.rename (oldEmbedding n) ((coordinates n).symm P) := by
  apply (coordinates (n+1)).injective
  rw [AlgEquiv.apply_symm_apply, ← step_coordinates, AlgEquiv.apply_symm_apply]

def encode (n : ℕ) : Test n →ₗ[ℝ] MultivariateFactorialDomain.H (Fin (size n)) :=
  MultivariateFactorialDomain.polynomialMap.comp (coordinates n).symm.toLinearMap

theorem encode_apply (n : ℕ) (P : Test n) : encode n P =
    MultivariateFactorialDomain.polynomial ((coordinates n).symm P) := rfl

theorem encode_injective (n : ℕ) : Function.Injective (encode n) :=
  MultivariateFactorialDomain.polynomial_injective.comp (coordinates n).symm.injective

theorem encode_dense (n : ℕ) : DenseRange (encode n) := by
  have he : Set.range (encode n) = Set.range (MultivariateFactorialDomain.polynomial
      (ι := Fin (size n))) := by
    ext u
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨(coordinates n).symm P, rfl⟩
    · rintro ⟨P, rfl⟩
      exact ⟨coordinates n P, congrArg MultivariateFactorialDomain.polynomial
        ((coordinates n).symm_apply_apply P)⟩
  intro u
  rw [he]
  exact MultivariateFactorialDomain.polynomial_dense u

theorem encode_step (n : ℕ) (P : Test n) :
    encode (n+1) (step n P) =
      MultivariateFactorialRenaming.renameOperator (oldEmbedding n) (encode n P) := by
  rw [encode_apply, inverse_step, encode_apply,
    MultivariateFactorialRenaming.renaming_polynomial]

theorem encode_step_norm (n : ℕ) (P : Test n) : ‖encode (n+1) (step n P)‖ = ‖encode n P‖ := by
  rw [encode_step]
  exact MultivariateFactorialRenaming.renaming_norm _ _

theorem encode_transfer_norm (i j : ℕ) (h : i ≤ j) (P : Test i) :
    ‖encode j (transfer i j h P)‖ = ‖encode i P‖ := by
  induction j, h using Nat.le_induction with
  | base => rw [transfer_self]
  | succ j hj ih => rw [transfer_succ i j hj P, encode_step_norm, ih]

theorem coordinates_path (n : ℕ) (P : Test n) (ω : Path) :
    sampleLift n P ω = MvPolynomial.eval (HigherHeatContinuousCylinders.sample n ω)
      ((coordinates n).symm P) := by
  rw [sampleLift_apply, eval_inverse]
  rfl

end OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialCoordinates
