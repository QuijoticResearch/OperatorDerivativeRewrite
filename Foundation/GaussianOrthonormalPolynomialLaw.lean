import Foundation.GaussianDiagonalQuadraticMoments
import Foundation.InfiniteGaussianRepresentation
import Foundation.GaussianChaosCylinders
import Foundation.BochnerL2Dominated
import Mathlib.Probability.HasLaw

/-! Actual finite orthonormal Gaussian source coordinates have the independent
product law. Polynomial moment transport includes all source embeddings. -/
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianOrthonormalPolynomialLaw
open InfiniteGaussian FiniteGaussian GaussianNumberSectors
variable {I : Type*} [Fintype I]

theorem basis_firstChaosFamily_law {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (A : E →ₗᵢ[ℝ] CoefficientSpace) (b : OrthonormalBasis I ℝ E) :
    HasLaw (firstChaosFamily (fun i => A (b i))) (productGaussian I) gaussianProduct := by
  have hY : MeasurePreserving (coordinateFamily b ∘ finiteGaussianPoint A)
      gaussianProduct (productGaussian I) :=
    (orthonormal_coordinates_measurePreserving b).comp
      ⟨finiteGaussianPoint_measurable A, finiteGaussianPoint_law A⟩
  have he : firstChaosFamily (fun i => A (b i)) =ᵐ[gaussianProduct]
      coordinateFamily b ∘ finiteGaussianPoint A := by
    filter_upwards [ae_all_iff.mpr (fun i => finiteGaussianPoint_coordinate A (b i))] with ω hw
    exact funext hw
  refine ⟨(Measurable.of_eval (fun i => (Lp.stronglyMeasurable (firstChaosEmbedding (A (b i)))).measurable)).aemeasurable, ?_⟩
  rw [Measure.map_congr he]
  exact hY.map_eq

theorem orthonormal_firstChaosFamily_law (v : I → CoefficientSpace) (hv : Orthonormal ℝ v) :
    HasLaw (firstChaosFamily v) (productGaussian I) gaussianProduct := by
  classical
  let s : Finset I := Finset.univ
  let S := Submodule.span ℝ (s.image v : Set CoefficientSpace)
  letI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (s.image v).finite_toSet
  letI : MeasurableSpace S := borel S
  letI : BorelSpace S := ⟨rfl⟩
  let e : I ≃ s :=
    { toFun := fun i => ⟨i, Finset.mem_univ i⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun i => by apply Subtype.ext; rfl }
  let b : OrthonormalBasis I ℝ S := (OrthonormalBasis.span hv s).reindex e.symm
  have he : (fun i => S.subtypeₗᵢ (b i)) = v := by
    funext i
    change (((OrthonormalBasis.span hv s).reindex e.symm) i : CoefficientSpace) = v i
    rw [OrthonormalBasis.reindex_apply]
    exact OrthonormalBasis.span_apply hv s (e i)
  have hl := basis_firstChaosFamily_law S.subtypeₗᵢ b
  rwa [he] at hl

theorem polynomial_integral_transport (v : I → CoefficientSpace) (hv : Orthonormal ℝ v)
    (p : MvPolynomial I ℝ) :
    (∫ ω, isonormalCylinder v p ω ∂gaussianProduct) = productPolynomialIntegral p := by
  have hl := orthonormal_firstChaosFamily_law v hv
  have hm : AEStronglyMeasurable (fun x : I → ℝ => eval x p) (productGaussian I) :=
    p.continuous_eval.measurable.aestronglyMeasurable
  convert hl.integral_comp hm using 1 <;> rfl

theorem polynomial_norm_sq_transport (v : I → CoefficientSpace) (hv : Orthonormal ℝ v)
    (p : MvPolynomial I ℝ) :
    ‖isonormalCylinderL2 v p‖^2 = productPolynomialIntegral (p^2) := by
  rw [BochnerL2Dominated.norm_sq_integral]
  have he : (∫ ω, ‖isonormalCylinderL2 v p ω‖^2 ∂gaussianProduct) =
      ∫ ω, isonormalCylinder v (p^2) ω ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [isonormalCylinderL2_coeFn v p] with ω hp
    rw [hp]
    simp only [Real.norm_eq_abs, sq_abs, isonormalCylinder, map_pow]
  rw [he, polynomial_integral_transport v hv]

theorem polynomial_square_product_transport (v : I → CoefficientSpace)
    (p : MvPolynomial I ℝ) :
    (polynomialProduct (cylinderCore v p) (cylinderCore v p) : GaussianL2) =
      isonormalCylinderL2 v (p^2) := by
  apply Lp.ext
  filter_upwards [polynomialProductL2_coeFn (cylinderCore v p) (cylinderCore v p),
    isonormalCylinderL2_coeFn v p, isonormalCylinderL2_coeFn v (p^2)] with ω hs hp h2
  change polynomialProductL2 (cylinderCore v p) (cylinderCore v p) ω = _
  rw [hs]
  change isonormalCylinderL2 v p ω * isonormalCylinderL2 v p ω = _
  rw [hp, h2]
  simp only [isonormalCylinder, map_pow]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianOrthonormalPolynomialLaw
