import Foundation.HigherHeatCylinderDilation
import Foundation.HigherHeatCompletedSignedMean

/-! Bounded damped multiplication on the common complete analytic cylinder domain. -/
noncomputable section

namespace OperatorDerivativeRewrite.Foundation.HigherHeatCommonDampedProduct
open HigherHeatPolynomialCylinders HigherHeatPolynomialCoordinates HigherHeatAnalyticCylinderDomain
open HigherHeatCylindricalConditioning HigherHeatCylinderDilation
open MultivariateFactorialDomain MultivariateFactorialRenaming MultivariateFactorialDampedProduct
open Classical

theorem embedding_damped_same_grid (n : ℕ) (P Q : Test n) :
    dampedProduct (embedding (cylinderOf n P)) (embedding (cylinderOf n Q)) =
      embedding (dilation (1/2) (cylinderOf n P * cylinderOf n Q)) := by
  have hm : cylinderOf n P * cylinderOf n Q = cylinderOf n (P*Q) := (map_mul (cylinderOf n) P Q).symm
  rw [hm, dilation_core]
  simp only [embedding_apply, gridEmbedding_apply, encode_apply]
  rw [dampedProduct_rename, dampedProduct_polynomial, inverse_dilation]
  have hc : (coordinates n).symm (P*Q) = (coordinates n).symm P * (coordinates n).symm Q :=
    map_mul (coordinates n).symm P Q
  rw [hc]
  rfl

theorem embedding_damped_core (F G : Cylinder) :
    dampedProduct (embedding F) (embedding G) = embedding (dilation (1/2) (F*G)) := by
  induction F using DirectLimit.induction with
  | _ n P =>
    apply tail_induction n (fun G => dampedProduct (embedding (cylinderOf n P)) (embedding G) =
      embedding (dilation (1/2) (cylinderOf n P * G))) _ G
    intro k hnk Q
    rw [← cylinder_refinement n k hnk P]
    exact embedding_damped_same_grid k (transfer n k hnk P) Q

theorem mem_commonClosure (u v : Domain) : dampedProduct u.val v.val ∈ commonClosure := by
  have hc (F G : Cylinder) : dampedProduct (core F).val (core G).val ∈ commonClosure := by
    change dampedProduct (embedding F) (embedding G) ∈ commonClosure
    rw [embedding_damped_core]
    exact embedding.range.le_topologicalClosure ⟨dilation (1/2) (F*G), rfl⟩
  have hl (F : Cylinder) (v : Domain) : dampedProduct (core F).val v.val ∈ commonClosure := by
    exact core_dense.induction_on v
      (commonClosure_closed.preimage (by fun_prop)) (fun G => hc F G)
  exact core_dense.induction_on u
    (commonClosure_closed.preimage (by fun_prop)) (fun F => hl F v)

def rightProduct (u : Domain) : Domain →L[ℝ] Domain :=
  ((dampedProduct u.val).comp commonClosure.subtypeL).codRestrict commonClosure (mem_commonClosure u)

theorem rightProduct_apply (u v : Domain) : (rightProduct u v).val = dampedProduct u.val v.val := rfl

theorem rightProduct_norm (u : Domain) : ‖rightProduct u‖ ≤ ‖u‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u)
  intro v
  exact dampedProduct_bound u.val v.val

def productLinear : Domain →ₗ[ℝ] Domain →L[ℝ] Domain where
  toFun := rightProduct
  map_add' u v := by
    apply ContinuousLinearMap.ext
    intro w
    apply Subtype.ext
    change dampedProduct (u.val+v.val) w.val = dampedProduct u.val w.val + dampedProduct v.val w.val
    rw [map_add, add_apply]
  map_smul' c u := by
    apply ContinuousLinearMap.ext
    intro w
    apply Subtype.ext
    change dampedProduct (c • u.val) w.val = c • dampedProduct u.val w.val
    rw [map_smul, smul_apply]

def product : Domain →L[ℝ] Domain →L[ℝ] Domain :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Domain)
    (F := Domain →L[ℝ] Domain) productLinear 1 (fun u => by
    change ‖rightProduct u‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using rightProduct_norm u)

theorem product_apply (u v : Domain) : (product u v).val = dampedProduct u.val v.val := rfl

theorem product_bound (u v : Domain) : ‖product u v‖ ≤ ‖u‖*‖v‖ :=
  dampedProduct_bound u.val v.val

theorem product_core (F G : Cylinder) : product (core F) (core G) = core (dilation (1/2) (F*G)) := by
  apply Subtype.ext
  exact embedding_damped_core F G

theorem product_comm (u v : Domain) : product u v = product v u := by
  apply Subtype.ext
  exact dampedProduct_comm u.val v.val

end OperatorDerivativeRewrite.Foundation.HigherHeatCommonDampedProduct
