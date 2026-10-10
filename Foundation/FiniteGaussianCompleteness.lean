import Foundation.FiniteGaussianDensity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! Algebraic tensor Hermite spanning and Hilbert completeness in every finite dimension. -/
noncomputable section
open MeasureTheory Polynomial Module
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

private def normalizedPolynomialBasis : Basis ℕ ℝ ℝ[X] :=
  Basis.isUnitSMul
    (GaussianCore.hermiteSequence.basis (fun n => by
      simp [GaussianCore.hermiteSequence, (GaussianCore.hermitePolynomial_monic n).leadingCoeff]))
    (w := fun n : ℕ => (Real.sqrt (n.factorial : ℝ))⁻¹)
    (fun n => isUnit_iff_ne_zero.mpr
      (inv_ne_zero (ne_of_gt (GaussianCore.hermite_normalizer_pos n))))

private theorem normalizedPolynomialBasis_apply (n : ℕ) :
    normalizedPolynomialBasis n = normalizedHermitePolynomial n := by
  simp [normalizedPolynomialBasis, Basis.isUnitSMul_apply, normalizedHermitePolynomial,
    GaussianCore.hermiteSequence]

/-- Substitute one actual univariate polynomial into each coordinate,
then multiply the results. -/
def tensorPolynomialMap : MultilinearMap ℝ (fun _ : ι => ℝ[X]) (MvPolynomial ι ℝ) :=
  (MultilinearMap.mkPiAlgebra ℝ ι (MvPolynomial ι ℝ)).compLinearMap
    (fun i => (Polynomial.aeval (MvPolynomial.X i : MvPolynomial ι ℝ)).toLinearMap)

/-- The actual multivariate polynomial representing a normalized Hermite tensor. -/
def tensorHermitePolynomial (α : ι → ℕ) : MvPolynomial ι ℝ :=
  tensorPolynomialMap (fun i => normalizedHermitePolynomial (α i))

/-- Every separable polynomial is a finite linear combination of Hermite tensor polynomials. -/
theorem tensorPolynomialMap_mem_span (p : ι → ℝ[X]) :
    tensorPolynomialMap p ∈ Submodule.span ℝ (Set.range (tensorHermitePolynomial (ι := ι))) := by
  classical
  let b := normalizedPolynomialBasis
  let c (i : ι) := b.repr (p i)
  have he (i : ι) : (∑ n ∈ (c i).support, c i n • normalizedHermitePolynomial n) = p i := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, b, c, normalizedPolynomialBasis_apply]
      using b.linearCombination_repr (p i)
  rw [← show (fun i => ∑ n ∈ (c i).support, c i n • normalizedHermitePolynomial n) = p
    from funext he]
  rw [MultilinearMap.map_sum_finset]
  apply Submodule.sum_mem
  intro α _
  rw [MultilinearMap.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

/-- Tensor Hermite polynomials algebraically span all multivariate polynomials. -/
theorem tensorHermitePolynomial_span :
    Submodule.span ℝ (Set.range (tensorHermitePolynomial (ι := ι))) = ⊤ := by
  classical
  apply eq_top_iff.mpr
  intro p _
  rw [MvPolynomial.as_sum p]
  apply Submodule.sum_mem
  intro v _
  have hm : MvPolynomial.monomial v (p.coeff v) =
      p.coeff v • tensorPolynomialMap (fun i => (Polynomial.X : ℝ[X]) ^ v i) := by
    simp only [tensorPolynomialMap, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, map_pow, Polynomial.aeval_X]
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    · simp [Algebra.smul_def]
    · intro i; simp
  rw [hm]
  exact Submodule.smul_mem _ _ (tensorPolynomialMap_mem_span _)

omit [Fintype ι] in
private theorem coordinate_aeval_eval (p : ℝ[X]) (i : ι) (x : ι → ℝ) :
    MvPolynomial.eval x (Polynomial.aeval (MvPolynomial.X i) p) = p.eval (x i) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [Polynomial.aeval_monomial, MvPolynomial.algebraMap_eq]

/-- The polynomial tensor evaluates to the previously verified tensor function. -/
theorem tensorHermitePolynomial_eval (α : ι → ℕ) (x : ι → ℝ) :
    MvPolynomial.eval x (tensorHermitePolynomial α) = tensorHermiteFunction α x := by
  simp [tensorHermitePolynomial, tensorPolynomialMap, tensorHermiteFunction, coordinate_aeval_eval]

/-- Compatibility in L², with equality of actual almost-everywhere equivalence classes. -/
theorem tensorHermitePolynomial_L2 (α : ι → ℕ) :
    productPolynomialL2 (tensorHermitePolynomial α) = tensorHermite α := by
  apply Lp.ext
  filter_upwards [productPolynomialL2_coeFn (tensorHermitePolynomial α), tensorHermite_coeFn α]
    with x hp ht
  rw [hp, ht, tensorHermitePolynomial_eval]

/-- The algebraic Hermite span is exactly the algebraic polynomial core. -/
theorem tensorHermite_span :
    Submodule.span ℝ (Set.range (tensorHermite (ι := ι))) =
      (productPolynomialEmbedding (ι := ι)).range := by
  have he : Set.range (tensorHermite (ι := ι)) =
      productPolynomialEmbedding '' Set.range (tensorHermitePolynomial (ι := ι)) := by
    ext f
    constructor
    · rintro ⟨α, rfl⟩
      exact ⟨tensorHermitePolynomial α, ⟨α, rfl⟩, tensorHermitePolynomial_L2 α⟩
    · rintro ⟨_, ⟨α, rfl⟩, rfl⟩
      exact ⟨α, (tensorHermitePolynomial_L2 α).symm⟩
  rw [he, ← Submodule.map_span, tensorHermitePolynomial_span, Submodule.map_top]

/-- Completeness follows from independently proved polynomial density. -/
theorem tensorHermite_dense_span :
    Dense (Submodule.span ℝ (Set.range (tensorHermite (ι := ι))) :
      Set (Lp ℝ 2 (productGaussian ι))) := by
  rw [tensorHermite_span]
  exact productPolynomialEmbedding_dense

/-- A complete orthonormal Hilbert basis indexed by all finite multi-indices,
including dimension zero. -/
def tensorHermiteBasis : HilbertBasis (ι → ℕ) ℝ (Lp ℝ 2 (productGaussian ι)) :=
  HilbertBasis.mk tensorHermite_orthonormal (by
    rw [← eq_top_iff]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mp tensorHermite_dense_span)

theorem tensorHermiteBasis_apply (α : ι → ℕ) : tensorHermiteBasis α = tensorHermite α :=
  by rw [tensorHermiteBasis, HilbertBasis.coe_mk]

/-- Every product Gaussian L² vector is the unconditionally convergent series
of its Hermite coefficients. -/
theorem tensorHermiteBasis_hasSum (f : Lp ℝ 2 (productGaussian ι)) :
    HasSum (fun α => inner ℝ (tensorHermite α) f • tensorHermite α) f := by
  simpa only [HilbertBasis.repr_apply_apply, tensorHermiteBasis_apply]
    using (tensorHermiteBasis (ι := ι)).hasSum_repr f

/-- In zero dimensions the sole tensor representative is the constant one. -/
theorem tensorHermiteFunction_empty [IsEmpty ι] (α : ι → ℕ) (x : ι → ℝ) :
    tensorHermiteFunction α x = 1 := by
  simp [tensorHermiteFunction]

/-- The zero-dimensional L² space consists exactly of scalar multiples of its vacuum tensor. -/
theorem tensorHermite_empty_expansion [IsEmpty ι] (f : Lp ℝ 2 (productGaussian ι)) :
    f = inner ℝ (tensorHermite (fun _ : ι => 0)) f •
      tensorHermite (fun _ : ι => 0) := by
  have hh : HasSum (fun _ : ι → ℕ =>
      inner ℝ (tensorHermite (fun _ : ι => 0)) f • tensorHermite (fun _ : ι => 0)) f :=
    (tensorHermiteBasis_hasSum f).congr (fun s => by
      apply Finset.sum_congr rfl
      intro α _
      rw [Subsingleton.elim α (fun _ : ι => (0 : ℕ))])
  have hs := hasSum_fintype (fun _ : ι → ℕ =>
    inner ℝ (tensorHermite (fun _ : ι => 0)) f • tensorHermite (fun _ : ι => 0))
  have he := hh.unique hs
  simpa using he

/-- The one-coordinate construction agrees with the previously verified
complete one-dimensional basis. -/
theorem tensorHermite_unique_coordinate [Unique ι] (n : ℕ) :
    tensorHermite (fun _ : ι => n) =
      Lp.compMeasurePreserving (Function.eval (default : ι))
        (measurePreserving_eval (fun _ : ι => GaussianCore.γ) default)
        (GaussianCore.hermiteBasis n) := by
  apply Lp.ext
  have hm := measurePreserving_eval (fun _ : ι => GaussianCore.γ) (default : ι)
  have ha := hm.quasiMeasurePreserving.ae_eq_comp (GaussianCore.polynomialL2_coeFn
    (normalizedHermitePolynomial n))
  filter_upwards [tensorHermite_coeFn (fun _ : ι => n),
    Lp.coeFn_compMeasurePreserving (GaussianCore.hermiteBasis n) hm, ha] with x ht hc hp
  rw [ht, hc]
  simp only [Function.comp_apply, Function.eval, GaussianCore.hermiteBasis_apply,
    normalizedHermitePolynomial_L2] at hp ⊢
  simpa [tensorHermiteFunction] using hp.symm

section CylindricalCompatibility
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Orthonormal Gaussian coordinates give a genuine measure-preserving pullback. -/
theorem orthonormal_coordinates_measurePreserving (b : OrthonormalBasis ι ℝ E) :
    MeasurePreserving (coordinateFamily b) (gaussianMeasure E) (productGaussian ι) :=
  ⟨by fun_prop, orthonormal_coordinates_joint_law b⟩

/-- Product polynomial classes pull back to the existing actual cylindrical classes. -/
theorem productPolynomialL2_pullback (b : OrthonormalBasis ι ℝ E)
    (p : MvPolynomial ι ℝ) :
    Lp.compMeasurePreserving (coordinateFamily b) (orthonormal_coordinates_measurePreserving b)
      (productPolynomialL2 p) = cylinderL2 b p := by
  apply Lp.ext
  have hm := orthonormal_coordinates_measurePreserving b
  have ha := hm.quasiMeasurePreserving.ae_eq_comp (productPolynomialL2_coeFn p)
  filter_upwards [Lp.coeFn_compMeasurePreserving (productPolynomialL2 p) hm,
    ha, cylinderL2_coeFn b p] with x hc hp ht
  rw [hc, ht, hp]
  rfl

/-- Each tensor basis vector pulls back to its genuine multivariate polynomial cylinder. -/
theorem tensorHermite_pullback (b : OrthonormalBasis ι ℝ E) (α : ι → ℕ) :
    Lp.compMeasurePreserving (coordinateFamily b) (orthonormal_coordinates_measurePreserving b)
      (tensorHermite α) = cylinderL2 b (tensorHermitePolynomial α) := by
  rw [← tensorHermitePolynomial_L2, productPolynomialL2_pullback]

end CylindricalCompatibility
end OperatorDerivativeRewrite.Foundation.FiniteGaussian
