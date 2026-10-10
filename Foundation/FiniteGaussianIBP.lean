import Foundation.FiniteGaussianCompleteness

/-! Polynomial Gaussian integration by parts on the independent finite coordinate space. -/
noncomputable section
open MeasureTheory Polynomial Module
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/-- Integration of an actual polynomial is a linear functional; all inputs are integrable. -/
def productPolynomialIntegral : MvPolynomial ι ℝ →ₗ[ℝ] ℝ where
  toFun p := ∫ x, MvPolynomial.eval x p ∂productGaussian ι
  map_add' p q := by
    simp only [map_add]
    exact integral_add ((productPolynomial_memLp p 1 (by simp)).integrable (by simp))
      ((productPolynomial_memLp q 1 (by simp)).integrable (by simp))
  map_smul' c p := by
    simp only [MvPolynomial.smul_eval, RingHom.id_apply, smul_eq_mul]
    exact integral_const_mul c _

omit [Fintype ι] in
/-- Coordinate substitution commutes with actual polynomial evaluation. -/
theorem polynomial_coordinate_eval (p : ℝ[X]) (i : ι) (x : ι → ℝ) :
    MvPolynomial.eval x (Polynomial.aeval (MvPolynomial.X i) p) = p.eval (x i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq]

omit [Fintype ι] in
/-- Differentiate the actual substituted polynomial, not independently assigned data. -/
theorem pderiv_coordinate_polynomial [DecidableEq ι] (i j : ι) (p : ℝ[X]) :
    MvPolynomial.pderiv i (Polynomial.aeval (MvPolynomial.X j : MvPolynomial ι ℝ) p) =
      if i = j then Polynomial.aeval (MvPolynomial.X j : MvPolynomial ι ℝ) p.derivative else 0 := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]; split_ifs <;> simp
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq,
      MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X,
      Polynomial.derivative_monomial, Pi.single_apply]
    by_cases h : i = j
    · subst j; simp [MvPolynomial.C_mul']
    · simp [h, Ne.symm h]

/-- Evaluation of the multilinear polynomial tensor map is the finite product of evaluations. -/
theorem tensorPolynomialMap_eval (p : ι → ℝ[X]) (x : ι → ℝ) :
    MvPolynomial.eval x (tensorPolynomialMap p) = ∏ i, (p i).eval (x i) := by
  simp [tensorPolynomialMap, polynomial_coordinate_eval]

/-- A coordinate derivative differentiates precisely that tensor factor. -/
theorem tensorPolynomialMap_pderiv [DecidableEq ι] (p : ι → ℝ[X]) (i : ι) :
    MvPolynomial.pderiv i (tensorPolynomialMap p) =
      tensorPolynomialMap (Function.update p i (p i).derivative) := by
  classical
  let f (j : ι) := Polynomial.aeval (MvPolynomial.X j : MvPolynomial ι ℝ) (p j)
  have hz (s : Finset ι) (hi : i ∉ s) : MvPolynomial.pderiv i (∏ j ∈ s, f j) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      simp only [Finset.mem_insert, not_or] at hi
      simp [Finset.prod_insert, hj, ih hi.2, f, Ne.symm hi.1]
  change MvPolynomial.pderiv i (∏ j, f j) = _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), MvPolynomial.pderiv_mul,
    hz _ (Finset.notMem_erase _ _)]
  simp only [mul_zero, add_zero, f, pderiv_coordinate_polynomial, ↓reduceIte]
  change _ = ∏ j, Polynomial.aeval (MvPolynomial.X j)
    (Function.update p i (p i).derivative j)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem tensorPolynomialMap_stein (p : ι → ℝ[X]) (i : ι) :
    productPolynomialIntegral (MvPolynomial.X i * tensorPolynomialMap p) =
      productPolynomialIntegral (MvPolynomial.pderiv i (tensorPolynomialMap p)) := by
  classical
  let f (j : ι) (t : ℝ) := (p j).eval t
  have hl (x : ι → ℝ) : x i * ∏ j, f j (x j) =
      ∏ j, (Function.update f i (fun t => t * (p i).eval t) j) (x j) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Function.update_self, f]
    rw [← mul_assoc]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hr (x : ι → ℝ) :
      ∏ j, (Function.update p i (p i).derivative j).eval (x j) =
      ∏ j, (Function.update f i (fun t => (p i).derivative.eval t) j) (x j) := by
    apply Finset.prod_congr rfl
    intro j _
    by_cases h : j = i <;> simp [h, f]
  simp only [productPolynomialIntegral, LinearMap.coe_mk, AddHom.coe_mk,
    map_mul, MvPolynomial.eval_X, tensorPolynomialMap_pderiv, tensorPolynomialMap_eval]
  change (∫ x, x i * ∏ j, f j (x j) ∂productGaussian ι) = _
  rw [funext hl, funext hr]
  rw [integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = i
  · subst j
    simp only [Function.update_self]
    simpa [mul_comm] using GaussianCore.polynomial_stein (p i)
  · simp [Function.update_of_ne h]

/-- Multivariate polynomial Stein identity, proved from finite-product Fubini
and one-dimensional IBP. -/
theorem productPolynomial_stein (p : MvPolynomial ι ℝ) (i : ι) :
    (∫ x, x i * MvPolynomial.eval x p ∂productGaussian ι) =
      ∫ x, MvPolynomial.eval x (MvPolynomial.pderiv i p) ∂productGaussian ι := by
  let L : MvPolynomial ι ℝ →ₗ[ℝ] ℝ :=
    productPolynomialIntegral.comp (LinearMap.mulLeft ℝ (MvPolynomial.X i)) -
      productPolynomialIntegral.comp (MvPolynomial.pderiv i).toLinearMap
  have hs : Submodule.span ℝ (Set.range (tensorHermitePolynomial (ι := ι))) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, rfl⟩
    apply LinearMap.mem_ker.mpr
    exact sub_eq_zero.mpr (tensorPolynomialMap_stein
      (fun j => normalizedHermitePolynomial (α j)) i)
  rw [tensorHermitePolynomial_span] at hs
  have hp : p ∈ L.ker := hs (Submodule.mem_top)
  have he := sub_eq_zero.mp (LinearMap.mem_ker.mp hp)
  simpa [L, productPolynomialIntegral] using he

/-- Gaussian coordinate divergence acting on an actual scalar polynomial. -/
def coordinateDivergencePolynomial (i : ι) (q : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  MvPolynomial.X i * q - MvPolynomial.pderiv i q

/-- Polynomial coordinate integration by parts with all product integrability proved. -/
theorem productPolynomial_integration_by_parts (p q : MvPolynomial ι ℝ) (i : ι) :
    (∫ x, MvPolynomial.eval x (MvPolynomial.pderiv i p) * MvPolynomial.eval x q
      ∂productGaussian ι) =
    ∫ x, MvPolynomial.eval x p * MvPolynomial.eval x (coordinateDivergencePolynomial i q)
      ∂productGaussian ι := by
  have hi (a b : MvPolynomial ι ℝ) : Integrable
      (fun x => MvPolynomial.eval x a * MvPolynomial.eval x b) (productGaussian ι) :=
    mul_L2_integrable (productPolynomial_memLp a 2 (by simp))
      (productPolynomial_memLp b 2 (by simp))
  have h := productPolynomial_stein (p * q) i
  simp only [MvPolynomial.pderiv_mul, map_add, map_mul] at h
  rw [integral_add (hi (MvPolynomial.pderiv i p) q) (hi p (MvPolynomial.pderiv i q))] at h
  simp only [coordinateDivergencePolynomial, map_sub, mul_sub]
  rw [integral_sub (hi p (MvPolynomial.X i * q)) (hi p (MvPolynomial.pderiv i q))]
  have he : (∫ x, x i * (MvPolynomial.eval x p * MvPolynomial.eval x q)
      ∂productGaussian ι) =
      ∫ x, MvPolynomial.eval x p * MvPolynomial.eval x (MvPolynomial.X i * q)
        ∂productGaussian ι := by
    congr 1; funext x; simp; ring
  rw [he] at h
  linarith

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
