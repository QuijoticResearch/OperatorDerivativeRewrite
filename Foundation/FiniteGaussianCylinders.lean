import Foundation.FiniteGaussianCoordinates
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Actual finite polynomial cylinders and their Hilbert-space gradients. -/
noncomputable section
open MeasureTheory MvPolynomial
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]

/-- Actual polynomial evaluation at the linear coordinates W(hᵢ). No derivative data is stored. -/
def cylinder (h : ι → E) (p : MvPolynomial ι ℝ) (x : E) : ℝ :=
  MvPolynomial.eval (fun i => coordinate (h i) x) p

/-- The candidate gradient, built from actual formal partial derivatives of the polynomial. -/
def cylinderGradient (h : ι → E) (p : MvPolynomial ι ℝ) (x : E) : E :=
  ∑ i, cylinder h (MvPolynomial.pderiv i p) x • h i

omit [Fintype ι] in
@[simp] theorem cylinder_C (h : ι → E) (a : ℝ) : cylinder h (C a) = fun _ => a := by
  funext x; simp [cylinder]

omit [Fintype ι] in
@[simp] theorem cylinder_X (h : ι → E) (i : ι) : cylinder h (X i) = coordinate (h i) := by
  funext x; simp [cylinder]

omit [Fintype ι] in
theorem cylinder_add (h : ι → E) (p q : MvPolynomial ι ℝ) :
    cylinder h (p + q) = cylinder h p + cylinder h q := by
  funext x; simp [cylinder, MvPolynomial.eval_add]

omit [Fintype ι] in
theorem cylinder_mul (h : ι → E) (p q : MvPolynomial ι ℝ) :
    cylinder h (p * q) = cylinder h p * cylinder h q := by
  funext x; simp [cylinder, MvPolynomial.eval_mul]

@[simp] theorem cylinderGradient_C (h : ι → E) (a : ℝ) (x : E) :
    cylinderGradient h (C a) x = 0 := by
  simp [cylinderGradient, cylinder]

@[simp] theorem cylinderGradient_X (h : ι → E) (j : ι) (x : E) :
    cylinderGradient h (X j) x = h j := by
  classical
  simp [cylinderGradient, cylinder, MvPolynomial.pderiv_X, Pi.single_apply]

theorem cylinderGradient_add (h : ι → E) (p q : MvPolynomial ι ℝ) (x : E) :
    cylinderGradient h (p + q) x = cylinderGradient h p x + cylinderGradient h q x := by
  simp [cylinderGradient, map_add, cylinder_add, add_smul, Finset.sum_add_distrib]

/-- Algebraic differentiation of the genuine polynomial expression supplies the product formula. -/
theorem cylinderGradient_mul (h : ι → E) (p q : MvPolynomial ι ℝ) (x : E) :
    cylinderGradient h (p * q) x =
      cylinder h p x • cylinderGradient h q x + cylinder h q x • cylinderGradient h p x := by
  simp only [cylinderGradient, MvPolynomial.pderiv_mul, cylinder_add, cylinder_mul,
    Pi.add_apply, Pi.mul_apply, add_smul, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, mul_comm]

/-- Analytic verification: this vector really represents the Fréchet derivative of the cylinder. -/
theorem cylinder_hasFDerivAt (h : ι → E) (p : MvPolynomial ι ℝ) (x : E) :
    HasFDerivAt (cylinder h p) (innerSL ℝ (cylinderGradient h p x)) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const a x
  | add p q hp hq =>
    rw [cylinder_add, cylinderGradient_add]
    convert hp.add hq using 1
    ext y; simp
  | mul_X p j hp =>
    rw [cylinder_mul, cylinderGradient_mul, cylinder_X, cylinderGradient_X]
    convert hp.mul (coordinate (h j)).hasFDerivAt using 1
    ext y
    simp [coordinate]

/-- The actual analytic derivative is determined by the verified polynomial gradient. -/
theorem cylinder_fderiv (h : ι → E) (p : MvPolynomial ι ℝ) (x : E) :
    fderiv ℝ (cylinder h p) x = innerSL ℝ (cylinderGradient h p x) :=
  (cylinder_hasFDerivAt h p x).fderiv

omit [Fintype ι] in
/-- Polynomial cylinders are actual smooth functions, even when the variable set is infinite. -/
theorem cylinder_smooth (h : ι → E) (p : MvPolynomial ι ℝ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (cylinder h p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [cylinder_C]; exact contDiff_const
  | add p q hp hq => rw [cylinder_add]; exact hp.add hq
  | mul_X p j hp => rw [cylinder_mul, cylinder_X]; exact hp.mul (coordinate (h j)).contDiff

omit [Fintype ι] in
theorem cylinder_continuous (h : ι → E) (p : MvPolynomial ι ℝ) : Continuous (cylinder h p) :=
  (cylinder_smooth h p).continuous

/-- A product rule for the actual Fréchet derivative, not an unfolding of stored values. -/
theorem cylinder_product_rule (h : ι → E) (p q : MvPolynomial ι ℝ) (x : E) :
    fderiv ℝ (fun y => cylinder h p y * cylinder h q y) x =
      innerSL ℝ (cylinder h p x • cylinderGradient h q x +
        cylinder h q x • cylinderGradient h p x) := by
  change fderiv ℝ (cylinder h p * cylinder h q) x = _
  rw [← cylinder_mul, cylinder_fderiv, cylinderGradient_mul]

section GaussianMoments
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Hölder at doubled exponents justifies the multiplication step in the polynomial induction. -/
theorem doubled_holderTriple (r : ℝ≥0∞) : ENNReal.HolderTriple (2 * r) (2 * r) r where
  inv_add_inv_eq_inv := by
    rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl (ENNReal.natCast_ne_top 2)),
      ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero (ENNReal.natCast_ne_top 2),
      one_mul]

omit [Fintype ι] in
/-- All finite moments of every finite polynomial cylinder, including correlated/degenerate ones. -/
theorem cylinder_memLp (h : ι → E) (p : MvPolynomial ι ℝ)
    (r : ℝ≥0∞) (hr : r ≠ ∞) : MemLp (cylinder h p) r (gaussianMeasure E) := by
  induction p using MvPolynomial.induction_on generalizing r with
  | C a => simpa using (memLp_const a : MemLp (fun _ : E => a) r (gaussianMeasure E))
  | add p q hp hq => rw [cylinder_add]; exact (hp r hr).add (hq r hr)
  | mul_X p j hp =>
    have ht : 2 * r ≠ ∞ := ENNReal.mul_ne_top (by simp) hr
    have : ENNReal.HolderTriple (2 * r) (2 * r) r := doubled_holderTriple r
    rw [cylinder_mul, cylinder_X]
    exact (hp (2 * r) ht).mul (coordinate_memLp (h j) (2 * r) ht)

/-- Vector-valued gradient integrability is proved from the scalar partial-derivative moments. -/
theorem cylinderGradient_memLp (h : ι → E) (p : MvPolynomial ι ℝ)
    (r : ℝ≥0∞) (hr : r ≠ ∞) : MemLp (cylinderGradient h p) r (gaussianMeasure E) := by
  apply memLp_finsetSum
  intro i _
  exact smul_memLp (p := r) (q := ∞) (r := r)
    (cylinder_memLp h (MvPolynomial.pderiv i p) r hr) (memLp_const (h i))

/-- Representation independence across different finite coordinate families, even dependent ones.
Equality holds everywhere on the ambient Hilbert space, hence also Gaussian almost everywhere. -/
theorem cylinderGradient_representation_independent {κ : Type*} [Fintype κ]
    (h : ι → E) (k : κ → E) (p : MvPolynomial ι ℝ) (q : MvPolynomial κ ℝ)
    (he : cylinder h p =ᵐ[gaussianMeasure E] cylinder k q) :
    cylinderGradient h p = cylinderGradient k q := by
  have hf := continuous_ae_eq (cylinder_continuous h p) (cylinder_continuous k q) he
  funext x
  apply (InnerProductSpace.toDualMap ℝ E).injective
  change innerSL ℝ (cylinderGradient h p x) = innerSL ℝ (cylinderGradient k q x)
  rw [← cylinder_fderiv, ← cylinder_fderiv, hf]

/-- A genuine scalar Gaussian L² random variable, with integrability already proved. -/
def cylinderL2 (h : ι → E) (p : MvPolynomial ι ℝ) : Lp ℝ 2 (gaussianMeasure E) :=
  (cylinder_memLp h p 2 (by simp)).toLp (cylinder h p)

/-- Its genuine Hilbert-valued L² gradient, rather than separately specified derivative data. -/
def cylinderGradientL2 (h : ι → E) (p : MvPolynomial ι ℝ) : Lp E 2 (gaussianMeasure E) :=
  (cylinderGradient_memLp h p 2 (by simp)).toLp (cylinderGradient h p)

omit [Fintype ι] in
theorem cylinderL2_coeFn (h : ι → E) (p : MvPolynomial ι ℝ) :
    cylinderL2 h p =ᵐ[gaussianMeasure E] cylinder h p := MemLp.coeFn_toLp _

theorem cylinderGradientL2_coeFn (h : ι → E) (p : MvPolynomial ι ℝ) :
    cylinderGradientL2 h p =ᵐ[gaussianMeasure E] cylinderGradient h p := MemLp.coeFn_toLp _

/-- The gradient descends to the actual L² equivalence class across all finite representations. -/
theorem cylinderGradientL2_representation_independent {κ : Type*} [Fintype κ]
    (h : ι → E) (k : κ → E) (p : MvPolynomial ι ℝ) (q : MvPolynomial κ ℝ)
    (he : cylinderL2 h p = cylinderL2 k q) : cylinderGradientL2 h p = cylinderGradientL2 k q := by
  have ha : cylinder h p =ᵐ[gaussianMeasure E] cylinder k q :=
    (cylinderL2_coeFn h p).symm.trans (he ▸ cylinderL2_coeFn k q)
  have hg := cylinderGradient_representation_independent h k p q ha
  apply Lp.ext
  exact (cylinderGradientL2_coeFn h p).trans (hg ▸ (cylinderGradientL2_coeFn k q).symm)

end GaussianMoments
end OperatorDerivativeRewrite.Foundation.FiniteGaussian
