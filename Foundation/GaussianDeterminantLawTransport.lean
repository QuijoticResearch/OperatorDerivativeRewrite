import Foundation.GaussianDeterminantConditional
import Foundation.GaussianOrthogonalPolynomialIndependence

/-! Transport of the determinant law to actual orthonormal Gaussian coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianDeterminantLawTransport
set_option backward.isDefEq.respectTransparency false
open InfiniteGaussian GaussianQuadraticSourceHodge DoubleSkewGaussianBridge
open GaussianDeterminantConditional GaussianOrthogonalPolynomialIndependence

def rows (h : Fin 2 × Fin 2 → CoefficientSpace) (ω : SampleSpace) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  ((firstChaosEmbedding (h (0,0)) ω, firstChaosEmbedding (h (0,1)) ω),
   (firstChaosEmbedding (h (1,0)) ω, firstChaosEmbedding (h (1,1)) ω))

theorem row_orthonormal (h : Fin 2 × Fin 2 → CoefficientSpace)
    (hh : Orthonormal ℝ h) (a : Fin 2) : Orthonormal ℝ (fun i => h (a,i)) :=
  hh.comp (fun i => (a,i)) (fun _ _ he => congrArg Prod.snd he)

theorem cross_rows_orthogonal (h : Fin 2 × Fin 2 → CoefficientSpace)
    (hh : Orthonormal ℝ h) (i j : Fin 2) : inner ℝ (h (0,i)) (h (1,j)) = 0 := by
  rw [orthonormal_iff_ite.mp hh]
  norm_num

/-- The actual two rows have the four independent standard Gaussian law. -/
theorem rows_hasLaw (h : Fin 2 × Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    HasLaw (rows h) (rowMeasure.prod rowMeasure) gaussianProduct := by
  have hl := orthogonal_families_joint_law (fun i => h (0,i)) (fun i => h (1,i))
    (row_orthonormal h hh 0) (row_orthonormal h hh 1) (cross_rows_orthogonal h hh)
  have hm := (measurePreserving_finTwoArrow (gaussianReal 0 1)).prod
    (measurePreserving_finTwoArrow (gaussianReal 0 1))
  exact hm.hasLaw.comp hl

theorem determinant_ae (h : Fin 2 × Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    quadraticTarget h T =ᵐ[gaussianProduct] fun ω => determinant (rows h ω).1 (rows h ω).2 :=
  gaussian_determinant_ae h hh

/-- Equality of the actual ambient target law with the independently integrated finite law. -/
theorem target_hasLaw (h : Fin 2 × Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h) :
    HasLaw (quadraticTarget h T) determinantLaw gaussianProduct := by
  have hd : HasLaw (fun z : (ℝ × ℝ) × (ℝ × ℝ) => determinant z.1 z.2)
      determinantLaw (rowMeasure.prod rowMeasure) :=
    ⟨(by unfold determinant; fun_prop), rfl⟩
  have hl := hd.comp (rows_hasLaw h hh)
  exact ⟨(Lp.stronglyMeasurable _).aemeasurable,
    (Measure.map_congr (determinant_ae h hh)).trans hl.map_eq⟩

theorem target_charFun (h : Fin 2 × Fin 2 → CoefficientSpace) (hh : Orthonormal ℝ h)
    (t : ℝ) : charFun (gaussianProduct.map (quadraticTarget h T)) t =
      ((1/(1+4*t^2) : ℝ) : ℂ) := by
  rw [(target_hasLaw h hh).map_eq, determinantLaw_charFun]

theorem target_phase_integral (h : Fin 2 × Fin 2 → CoefficientSpace)
    (hh : Orthonormal ℝ h) (t : ℝ) :
    (∫ ω, phase t (quadraticTarget h T ω) ∂gaussianProduct) =
      ((1/(1+4*t^2) : ℝ) : ℂ) := by
  have hl := target_charFun h hh t
  rw [charFun_apply_real,
    integral_map (Lp.stronglyMeasurable _).aemeasurable (by fun_prop)] at hl
  simpa only [phase, Complex.ofReal_mul] using hl

theorem actual_target_charFun (t : ℝ) :
    charFun (gaussianProduct.map (quadraticTarget directions T)) t =
      ((1/(1+4*t^2) : ℝ) : ℂ) := target_charFun directions directions_orthonormal t

theorem target_law_invariant (h k : Fin 2 × Fin 2 → CoefficientSpace)
    (hh : Orthonormal ℝ h) (hk : Orthonormal ℝ k) :
    gaussianProduct.map (quadraticTarget h T) = gaussianProduct.map (quadraticTarget k T) :=
  (target_hasLaw h hh).map_eq.trans (target_hasLaw k hk).map_eq.symm

theorem target_phase_integrable (h : Fin 2 × Fin 2 → CoefficientSpace) (t : ℝ) :
    Integrable (fun ω => phase t (quadraticTarget h T ω)) gaussianProduct := by
  apply Integrable.of_bound (by unfold phase; fun_prop) 1
  exact Filter.Eventually.of_forall fun ω =>
    le_of_eq (Complex.norm_exp_ofReal_mul_I (t * quadraticTarget h T ω))

end OperatorDerivativeRewrite.Foundation.GaussianDeterminantLawTransport
