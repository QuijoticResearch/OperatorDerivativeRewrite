import Foundation.HilbertRepresentation

/-! Isometric factors of symmetric operators: adjoint intertwining and exact energy splitting. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.SymmetricFactorEnergy
open HilbertRepresentation
set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem adjoint_intertwining (J : X →ₗᵢ[ℝ] Y) (A : Y →L[ℝ] Y) (B : X →L[ℝ] X)
    (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    (hJ : ∀ x, A (J x) = J (B x)) (y : Y) :
    predictableAdjoint J (A y) = B (predictableAdjoint J y) := by
  apply ext_inner_right ℝ
  intro x
  calc
    inner ℝ (predictableAdjoint J (A y)) x = inner ℝ (A y) (J x) :=
      predictableAdjoint_pairing J (A y) x
    _ = inner ℝ y (A (J x)) := hA y (J x)
    _ = inner ℝ y (J (B x)) := by rw [hJ]
    _ = inner ℝ (predictableAdjoint J y) (B x) :=
      (predictableAdjoint_pairing J y (B x)).symm
    _ = inner ℝ (B (predictableAdjoint J y)) x := (hB _ _).symm

theorem projection_commutes (J : X →ₗᵢ[ℝ] Y) (A : Y →L[ℝ] Y) (B : X →L[ℝ] X)
    (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    (hJ : ∀ x, A (J x) = J (B x)) (y : Y) :
    representationProjection J (A y) = A (representationProjection J y) := by
  change J (predictableAdjoint J (A y)) = A (J (predictableAdjoint J y))
  rw [adjoint_intertwining J A B hA hB hJ, hJ]

theorem adjoint_residual_zero (J : X →ₗᵢ[ℝ] Y) (y : Y) :
    predictableAdjoint J (y - representationProjection J y) = 0 := by
  change predictableAdjoint J (y - J (predictableAdjoint J y)) = 0
  rw [map_sub, predictableAdjoint_isometry_apply, sub_self]

theorem quadratic_energy_split (J : X →ₗᵢ[ℝ] Y)
    (A : Y →L[ℝ] Y) (B : X →L[ℝ] X) (hA : A.toLinearMap.IsSymmetric)
    (hJ : ∀ x, A (J x) = J (B x)) (y : Y) :
    inner ℝ (A y) y =
      inner ℝ (B (predictableAdjoint J y)) (predictableAdjoint J y) +
      inner ℝ (A (y - representationProjection J y))
        (y - representationProjection J y) := by
  let x := predictableAdjoint J y
  let r := y - representationProjection J y
  have hcross : inner ℝ (A (J x)) r = 0 := by
    rw [hJ, real_inner_comm, ← predictableAdjoint_pairing,
      adjoint_residual_zero, inner_zero_left]
  have hcross' : inner ℝ (A r) (J x) = 0 := by
    calc
      inner ℝ (A r) (J x) = inner ℝ r (A (J x)) := hA r (J x)
      _ = inner ℝ (A (J x)) r := real_inner_comm _ _
      _ = 0 := hcross
  have hy : y = J x + r := by
    change y = representationProjection J y + (y - representationProjection J y)
    abel
  calc
    inner ℝ (A y) y = inner ℝ (A (J x + r)) (J x + r) :=
      congrArg (fun z => inner ℝ (A z) z) hy
    _ = inner ℝ (B x) x + inner ℝ (A r) r := by
      rw [map_add, inner_add_left, inner_add_right, inner_add_right,
        hcross, hcross', hJ, J.inner_map_map]
      ring

theorem quadratic_energy_contraction (J : X →ₗᵢ[ℝ] Y)
    (A : Y →L[ℝ] Y) (B : X →L[ℝ] X) (hA : A.toLinearMap.IsSymmetric)
    (hJ : ∀ x, A (J x) = J (B x)) (hpos : ∀ y, 0 ≤ inner ℝ (A y) y) (y : Y) :
    inner ℝ (B (predictableAdjoint J y)) (predictableAdjoint J y) ≤ inner ℝ (A y) y := by
  rw [quadratic_energy_split J A B hA hJ y]
  exact le_add_of_nonneg_right (hpos _)

end OperatorDerivativeRewrite.Foundation.SymmetricFactorEnergy
