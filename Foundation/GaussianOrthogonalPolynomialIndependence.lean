import Foundation.GaussianDiagonalQuadraticL4
import Foundation.GaussianOrthonormalPolynomialLaw
import Mathlib.MeasureTheory.Constructions.Pi

/-! Actual polynomial observables of finite orthogonal Gaussian families are independent. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianOrthogonalPolynomialIndependence
open InfiniteGaussian FiniteGaussian GaussianOrthonormalPolynomialLaw
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {I J : Type*} [Fintype I] [Fintype J]

theorem sum_sources_orthonormal (u : I → CoefficientSpace) (v : J → CoefficientSpace)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v)
    (huv : ∀ i j, inner ℝ (u i) (v j) = 0) : Orthonormal ℝ (Sum.elim u v) := by
  classical
  rw [orthonormal_iff_ite]
  rintro (i|j) (k|l)
  · simpa using orthonormal_iff_ite.mp hu i k
  · simpa using huv i l
  · change inner ℝ (v j) (u k) = 0
    rw [real_inner_comm (u k) (v j)]
    exact huv k j
  · simpa using orthonormal_iff_ite.mp hv j l

theorem orthogonal_families_joint_law (u : I → CoefficientSpace) (v : J → CoefficientSpace)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v)
    (huv : ∀ i j, inner ℝ (u i) (v j) = 0) :
    HasLaw (fun ω => (firstChaosFamily u ω, firstChaosFamily v ω))
      ((productGaussian I).prod (productGaussian J)) gaussianProduct := by
  have hl := orthonormal_firstChaosFamily_law (Sum.elim u v)
    (sum_sources_orthonormal u v hu hv huv)
  have hm := measurePreserving_sumPiEquivProdPi
    (fun _ : I ⊕ J => GaussianCore.γ)
  convert hm.hasLaw.comp hl using 1
  funext ω
  apply Prod.ext <;> funext i <;> rfl

theorem orthogonal_families_independent (u : I → CoefficientSpace) (v : J → CoefficientSpace)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v)
    (huv : ∀ i j, inner ℝ (u i) (v j) = 0) :
    IndepFun (firstChaosFamily u) (firstChaosFamily v) gaussianProduct := by
  have hz := orthogonal_families_joint_law u v hu hv huv
  have hf : HasLaw (Prod.fst : (I → ℝ) × (J → ℝ) → I → ℝ)
      (productGaussian I) ((productGaussian I).prod (productGaussian J)) :=
    ⟨measurable_fst.aemeasurable, by simp⟩
  have hg : HasLaw (Prod.snd : (I → ℝ) × (J → ℝ) → J → ℝ)
      (productGaussian J) ((productGaussian I).prod (productGaussian J)) :=
    ⟨measurable_snd.aemeasurable, by simp⟩
  exact (indepFun_iff_hasLaw_prodMk_prod (hf.comp hz) (hg.comp hz)).mpr hz

theorem orthogonal_polynomials_independent (u : I → CoefficientSpace) (v : J → CoefficientSpace)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v)
    (huv : ∀ i j, inner ℝ (u i) (v j) = 0)
    (p : MvPolynomial I ℝ) (q : MvPolynomial J ℝ) :
    IndepFun (isonormalCylinderL2 u p) (isonormalCylinderL2 v q) gaussianProduct := by
  have hi := orthogonal_families_independent u v hu hv huv
  have hp : Measurable (fun x : I → ℝ => MvPolynomial.eval x p) := p.continuous_eval.measurable
  have hq : Measurable (fun x : J → ℝ => MvPolynomial.eval x q) := q.continuous_eval.measurable
  exact (hi.comp hp hq).congr (isonormalCylinderL2_coeFn u p).symm
    (isonormalCylinderL2_coeFn v q).symm

theorem orthogonal_diagonal_quadratics_independent
    (u : I → CoefficientSpace) (v : J → CoefficientSpace)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v)
    (huv : ∀ i j, inner ℝ (u i) (v j) = 0) (a : I → ℝ) (b : J → ℝ) :
    IndepFun (GaussianDiagonalQuadraticL4.target u a : GaussianL2)
      (GaussianDiagonalQuadraticL4.target v b : GaussianL2) gaussianProduct := by
  rw [GaussianDiagonalQuadraticL4.target_eq_cylinder u hu,
    GaussianDiagonalQuadraticL4.target_eq_cylinder v hv]
  exact orthogonal_polynomials_independent u v hu hv huv _ _

end OperatorDerivativeRewrite.Foundation.GaussianOrthogonalPolynomialIndependence
