import Foundation.GaussianOrthonormalPolynomialLaw
import Foundation.GaussianObservedRecoveryHarmonicEnergy

/-! Dimension-independent sharp fourth-moment control for actual finite diagonal
quadratics in an arbitrary orthonormal family of Gaussian source directions. -/
noncomputable section
open MeasureTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianDiagonalQuadraticL4
open InfiniteGaussian GaussianTimeSpaceHermite GaussianNumberSectors
open GaussianDiagonalQuadraticMoments GaussianOrthonormalPolynomialLaw GaussianDivergenceRecovery
variable {I : Type*} [Fintype I]

def target (v : I → CoefficientSpace) (a : I → ℝ) : polynomialCylindricalDomain :=
  ∑ i, a i • wick (v i) 2

theorem target_mem_second_chaos (v : I → CoefficientSpace) (a : I → ℝ) :
    (target v a : GaussianL2) ∈ sector 2 := by
  simp only [target, Submodule.coe_sum, Submodule.coe_smul]
  exact (sector 2).sum_mem (fun i _ => (sector 2).smul_mem _ (IBMCubicFirstChaos.wick_mem_sector _ _))

theorem target_eq_cylinder (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (a : I → ℝ) :
    (target v a : GaussianL2) = isonormalCylinderL2 v (quadratic a) := by
  classical
  simp only [target, Submodule.coe_sum, Submodule.coe_smul]
  apply Lp.ext
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => a i • (wick (v i) 2 : GaussianL2)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (wick (v i) 2 : GaussianL2)),
    ae_all_iff.mpr (fun i => core_coeFn (v i) (‖v i‖^2) 2),
    isonormalCylinderL2_coeFn v (quadratic a)] with ω hs hm hw hp
  change (∑ i, a i • (wick (v i) 2 : GaussianL2)) ω = _
  rw [hs, hp]
  simp only [isonormalCylinder, quadratic, map_sum, smul_eval, RingHom.id_apply,
    map_sub, map_pow, eval_X, map_one, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hm i]
  simp only [Pi.smul_apply, smul_eq_mul, wick]
  rw [hw i]
  simp only [hv.norm_eq_one i, one_pow, value_two]

theorem target_variance (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (a : I → ℝ) :
    ‖(target v a : GaussianL2)‖^2 = 2 * ∑ i, (a i)^2 := by
  rw [target_eq_cylinder v hv, polynomial_norm_sq_transport v hv, quadratic_variance]

theorem target_square_eq_cylinder (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (a : I → ℝ) :
    (polynomialProduct (target v a) (target v a) : GaussianL2) =
      isonormalCylinderL2 v ((quadratic a)^2) := by
  have he : target v a = cylinderCore v (quadratic a) := by
    apply Subtype.ext
    exact target_eq_cylinder v hv a
  rw [he, polynomial_square_product_transport]

theorem target_fourth_moment (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (a : I → ℝ) :
    ‖(polynomialProduct (target v a) (target v a) : GaussianL2)‖^2 =
      12 * (∑ i, (a i)^2)^2 + 48 * ∑ i, (a i)^4 := by
  rw [target_square_eq_cylinder v hv, polynomial_norm_sq_transport v hv]
  have he : ((quadratic a)^2)^2 = (quadratic a)^4 := by ring
  rw [he, quadratic_fourth_moment]

theorem target_fourth_upper_bound (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (a : I → ℝ) :
    ‖(polynomialProduct (target v a) (target v a) : GaussianL2)‖^2 ≤
      15 * (‖(target v a : GaussianL2)‖^2)^2 := by
  rw [target_fourth_moment v hv, target_variance v hv]
  nlinarith [sum_fourth_le_sum_square_sq a]

theorem target_fourth_lower_bound (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (a : I → ℝ) :
    3 * (‖(target v a : GaussianL2)‖^2)^2 ≤
      ‖(polynomialProduct (target v a) (target v a) : GaussianL2)‖^2 := by
  rw [target_fourth_moment v hv, target_variance v hv]
  have hp : 0 ≤ ∑ i, (a i)^4 := Finset.sum_nonneg (fun i _ => by positivity)
  nlinarith

theorem target_recovery_energy (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) (a : I → ℝ) :
    ‖recovery (target v a)‖^2 = ∑ i, (a i)^2 := by
  have he := GaussianObservedRecoveryHarmonicEnergy.recovery_sector_energy
    ⟨(target v a : GaussianL2), target_mem_second_chaos v a⟩
  change ‖recovery (target v a)‖^2 = (2 : ℝ)⁻¹ * ‖(target v a : GaussianL2)‖^2 at he
  rw [he, target_variance v hv]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianDiagonalQuadraticL4
