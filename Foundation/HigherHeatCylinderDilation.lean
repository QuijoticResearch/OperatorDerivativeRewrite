import Foundation.MultivariateFactorialDampedProduct
import Foundation.HigherHeatPolynomialCoordinates

/-! Coordinate dilation on the actual dyadic polynomial cylinder algebra, compatible with refinement. -/
noncomputable section

namespace OperatorDerivativeRewrite.Foundation.HigherHeatCylinderDilation
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatPositionVariation
open MultivariateFactorialSubstitution

theorem dilation_pullback {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ℝ) (f : ι → κ)
    (P : MvPolynomial κ ℝ) :
    polynomialSubstitution id (fun _ => c) (HigherHeatPolynomialRefinement.pullback f P) =
      HigherHeatPolynomialRefinement.pullback f (polynomialSubstitution id (fun _ => c) P) := by
  have he : (polynomialSubstitution (id : ι → ι) (fun _ => c)).comp
      (HigherHeatPolynomialRefinement.pullback f) =
      (HigherHeatPolynomialRefinement.pullback f).comp (polynomialSubstitution id (fun _ => c)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, polynomialSubstitution, HigherHeatPolynomialRefinement.pullback,
      MvPolynomial.aeval_X, HigherHeatPolynomialRefinement.blockVariable, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Finset.mul_sum, id_eq]
  exact AlgHom.congr_fun he P

def gridDilation (c : ℝ) (n : ℕ) : Test n →ₐ[ℝ] Test n := polynomialSubstitution id (fun _ => c)

theorem gridDilation_step (c : ℝ) (n : ℕ) (P : Test n) :
    gridDilation c (n+1) (step n P) = step n (gridDilation c n P) :=
  dilation_pullback c _ P

theorem gridDilation_transfer (c : ℝ) (i j : ℕ) (h : i ≤ j) (P : Test i) :
    gridDilation c j (transfer i j h P) = transfer i j h (gridDilation c i P) := by
  induction j, h using Nat.le_induction with
  | base => rw [transfer_self, transfer_self]
  | succ j hj ih => rw [transfer_succ i j hj, gridDilation_step, ih, transfer_succ i j hj]

def dilation (c : ℝ) : Cylinder →ₐ[ℝ] Cylinder :=
  DirectLimit.Algebra.lift Test transition Cylinder
    (fun n => (cylinderOf n).comp (gridDilation c n))
    (fun i j h P => by
      change cylinderOf j (gridDilation c j (transfer i j h P)) = _
      rw [gridDilation_transfer, cylinder_refinement]
      rfl)

theorem dilation_core (c : ℝ) (n : ℕ) (P : Test n) :
    dilation c (cylinderOf n P) = cylinderOf n (gridDilation c n P) := rfl

theorem coordinates_dilation (c : ℝ) (n : ℕ) (P : Test n) :
    coordinates n (gridDilation c n P) = gridDilation c n (coordinates n P) := by
  apply MvPolynomial.funext
  intro x
  simp only [gridDilation, eval_coordinates, eval_polynomialSubstitution]
  apply congrArg (fun y : Fin (size n) → ℝ => MvPolynomial.eval y P)
  symm
  have hx : (fun i => c*x (id i)) = c • x := rfl
  rw [hx, map_smul]
  rfl

theorem inverse_dilation (c : ℝ) (n : ℕ) (P : Test n) :
    (coordinates n).symm (gridDilation c n P) = gridDilation c n ((coordinates n).symm P) := by
  apply (coordinates n).injective
  rw [AlgEquiv.apply_symm_apply, coordinates_dilation, AlgEquiv.apply_symm_apply]

end OperatorDerivativeRewrite.Foundation.HigherHeatCylinderDilation
