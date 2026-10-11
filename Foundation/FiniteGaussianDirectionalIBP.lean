import Foundation.FiniteGaussianOperators
import Foundation.FiniteGaussianCylinders

/-! Directional Gaussian Stein identity on a genuine finite Hilbert cylinder. -/
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

/-- Substitute the actual linear coordinates in an orthonormal basis. -/
def basisPolynomialMap (h : ι → E) : MvPolynomial ι ℝ →+*
    MvPolynomial (Fin (Module.finrank ℝ E)) ℝ :=
  eval₂Hom C (fun i => ∑ a, C (inner ℝ (h i) (stdOrthonormalBasis ℝ E a)) * X a)

omit [MeasurableSpace E] [BorelSpace E] [Fintype ι] in
theorem basisPolynomialMap_eval (h : ι → E) (p : MvPolynomial ι ℝ)
    (x : Fin (Module.finrank ℝ E) → ℝ) :
    eval x (basisPolynomialMap h p) =
      cylinder h p (∑ a, x a • stdOrthonormalBasis ℝ E a) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [basisPolynomialMap, cylinder]
  | add p q hp hq => simp [hp, hq, cylinder_add]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, cylinder_mul]
    congr 1
    simp [basisPolynomialMap, cylinder_X, coordinate, mul_comm]

omit [MeasurableSpace E] [BorelSpace E] in
theorem basisPolynomialMap_pderiv_eval (h : ι → E) (p : MvPolynomial ι ℝ)
    (a : Fin (Module.finrank ℝ E)) (x : Fin (Module.finrank ℝ E) → ℝ) :
    eval x (pderiv a (basisPolynomialMap h p)) =
      inner ℝ (cylinderGradient h p (∑ j, x j • stdOrthonormalBasis ℝ E j))
        (stdOrthonormalBasis ℝ E a) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [basisPolynomialMap]
  | add p q hp hq => simp [hp, hq, cylinderGradient_add, inner_add_left]
  | mul_X p i hp =>
    have hl : eval x (pderiv a (basisPolynomialMap h (X i))) =
        inner ℝ (h i) (stdOrthonormalBasis ℝ E a) := by
      simp [basisPolynomialMap, pderiv_X, Pi.single_apply]
    rw [map_mul, pderiv_mul, map_add, map_mul, map_mul, hp, hl,
      basisPolynomialMap_eval, basisPolynomialMap_eval, cylinderGradient_mul,
      cylinderGradient_X, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring

/-- Directional Stein identity for arbitrary finite families, including degenerate ones. -/
theorem cylinder_stein_basis (h : ι → E) (p : MvPolynomial ι ℝ)
    (a : Fin (Module.finrank ℝ E)) :
    (∫ x, inner ℝ (cylinderGradient h p x) (stdOrthonormalBasis ℝ E a)
      ∂gaussianMeasure E) =
    ∫ x, cylinder h p x * inner ℝ (stdOrthonormalBasis ℝ E a) x ∂gaussianMeasure E := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hm : Measurable (fun x : Fin (Module.finrank ℝ E) → ℝ => ∑ i, x i • b i) := by
    fun_prop
  have hg : Continuous (cylinderGradient h p) := by
    unfold cylinderGradient
    exact continuous_finsetSum _ (fun i _ => (cylinder_continuous h (pderiv i p)).smul
      continuous_const)
  have hr : Continuous (fun x : E => cylinder h p x * inner ℝ (b a) x) :=
    (cylinder_continuous h p).mul (continuous_const.inner continuous_id)
  rw [gaussianMeasure_eq_product_map b,
    integral_map hm.aemeasurable (hg.inner continuous_const).aestronglyMeasurable,
    integral_map hm.aemeasurable hr.aestronglyMeasurable]
  have hl := basisPolynomialMap_pderiv_eval h p a
  change (∫ x, inner ℝ (cylinderGradient h p (∑ j, x j • b j)) (b a)
    ∂productGaussian _) = ∫ x, cylinder h p (∑ j, x j • b j) *
      inner ℝ (b a) (∑ j, x j • b j) ∂productGaussian _
  have hx (y : Fin (Module.finrank ℝ E) → ℝ) : inner ℝ (b a) (∑ j, y j • b j) = y a := by
    simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  calc
    _ = ∫ x, eval x (pderiv a (basisPolynomialMap h p)) ∂productGaussian _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => (hl x).symm)
    _ = ∫ x, eval x (basisPolynomialMap h p) * x a ∂productGaussian _ := by
      simpa [mul_comm] using (productPolynomial_stein (basisPolynomialMap h p) a).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by dsimp only; rw [basisPolynomialMap_eval, hx])


/-- Directional Stein for every Hilbert direction, not merely a coordinate unit. -/
theorem cylinder_stein (h : ι → E) (p : MvPolynomial ι ℝ) (v : E) :
    (∫ x, inner ℝ (cylinderGradient h p x) v ∂gaussianMeasure E) =
      ∫ x, cylinder h p x * inner ℝ v x ∂gaussianMeasure E := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hi (w : E) : Integrable (fun x => inner ℝ (cylinderGradient h p x) w)
      (gaussianMeasure E) :=
    (inner_memLp (p := 1) (q := ∞) (r := 1) (cylinderGradient_memLp h p 1 (by simp))
      (memLp_const w : MemLp (fun _ : E => w) ∞ (gaussianMeasure E))).integrable (by simp)
  have hj (w : E) : Integrable (fun x => cylinder h p x * inner ℝ w x)
      (gaussianMeasure E) :=
    mul_L2_integrable (cylinder_memLp h p 2 (by simp)) (coordinate_memLp w 2 (by simp))
  have hl (x : E) : inner ℝ (cylinderGradient h p x) v =
      ∑ a, inner ℝ (b a) v * inner ℝ (cylinderGradient h p x) (b a) := by
    nth_rw 1 [← b.sum_repr' v]
    simp [inner_sum, inner_smul_right, mul_comm]
  have hr (x : E) : cylinder h p x * inner ℝ v x =
      ∑ a, inner ℝ (b a) v * (cylinder h p x * inner ℝ (b a) x) := by
    nth_rw 1 [← b.sum_repr' v]
    simp [sum_inner, real_inner_smul_left, Finset.mul_sum, mul_left_comm]
  simp_rw [hl, hr]
  rw [integral_finsetSum _ (fun a _ => (hi (b a)).const_mul _),
    integral_finsetSum _ (fun a _ => (hj (b a)).const_mul _)]
  simp_rw [integral_const_mul]
  exact Finset.sum_congr rfl (fun a _ => congrArg (inner ℝ (b a) v * ·)
    (cylinder_stein_basis h p a))
end OperatorDerivativeRewrite.Foundation.FiniteGaussian
