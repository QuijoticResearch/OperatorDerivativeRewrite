import Foundation.InfiniteGaussianDensity
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Actual polynomial cylinders of arbitrary isonormal coordinates and their directional gradients.
No quotient-level Malliavin operator is defined before representation independence is proved. -/
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/-- Actual polynomial random variable built from arbitrary, possibly dependent W(hᵢ). -/
def isonormalCylinder (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ)
    (ω : SampleSpace) : ℝ :=
  MvPolynomial.eval (fun i => firstChaosEmbedding (h i) ω) p

/-- Gradient formula uses actual polynomial partial derivatives, not independent derivative data. -/
def isonormalCylinderGradient (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ)
    (ω : SampleSpace) : CoefficientSpace :=
  ∑ i, isonormalCylinder h (MvPolynomial.pderiv i p) ω • h i

omit [Fintype ι] in
@[simp] theorem isonormalCylinder_C (h : ι → CoefficientSpace) (a : ℝ) :
    isonormalCylinder h (C a) = fun _ => a := by
  funext ω
  simp [isonormalCylinder]

omit [Fintype ι] in
@[simp] theorem isonormalCylinder_X (h : ι → CoefficientSpace) (i : ι) :
    isonormalCylinder h (X i) = (firstChaosEmbedding (h i) : SampleSpace → ℝ) := by
  funext ω
  simp [isonormalCylinder]

omit [Fintype ι] in
theorem isonormalCylinder_add (h : ι → CoefficientSpace) (p q : MvPolynomial ι ℝ) :
    isonormalCylinder h (p + q) = isonormalCylinder h p + isonormalCylinder h q := by
  funext ω
  simp [isonormalCylinder]

omit [Fintype ι] in
theorem isonormalCylinder_mul (h : ι → CoefficientSpace) (p q : MvPolynomial ι ℝ) :
    isonormalCylinder h (p * q) = isonormalCylinder h p * isonormalCylinder h q := by
  funext ω
  simp [isonormalCylinder]

omit [Fintype ι] in
/-- Every finite moment exists, using the proved Gaussian laws and doubled-exponent Hölder. -/
theorem isonormalCylinder_memLp (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ)
    (r : ℝ≥0∞) (hr : r ≠ ∞) : MemLp (isonormalCylinder h p) r gaussianProduct := by
  induction p using MvPolynomial.induction_on generalizing r with
  | C a => simpa using (memLp_const a : MemLp (fun _ : SampleSpace => a) r gaussianProduct)
  | add p q hp hq => rw [isonormalCylinder_add]; exact (hp r hr).add (hq r hr)
  | mul_X p j hp =>
    have ht : 2 * r ≠ ∞ := ENNReal.mul_ne_top (by simp) hr
    have : ENNReal.HolderTriple (2 * r) (2 * r) r := FiniteGaussian.doubled_holderTriple r
    rw [isonormalCylinder_mul, isonormalCylinder_X]
    exact (hp (2 * r) ht).mul ((firstChaos_hasGaussianLaw (h j)).memLp ht)

/-- The genuine ℓ²-valued partial-derivative formula also has all finite moments. -/
theorem isonormalCylinderGradient_memLp (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ)
    (r : ℝ≥0∞) (hr : r ≠ ∞) : MemLp (isonormalCylinderGradient h p) r gaussianProduct := by
  apply memLp_finsetSum
  intro i _
  exact smul_memLp (p := r) (q := ∞) (r := r)
    (isonormalCylinder_memLp h (pderiv i p) r hr) (memLp_const (h i))

/-- Scalar L² class, with integrability proved rather than hypothesized. -/
def isonormalCylinderL2 (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) : GaussianL2 :=
  (isonormalCylinder_memLp h p 2 (by simp)).toLp (isonormalCylinder h p)

/-- Actual ℓ²-valued L² class of the polynomial directional gradient.
Representation independence across different h and p is not asserted here. -/
def isonormalCylinderGradientL2 (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    Lp CoefficientSpace 2 gaussianProduct :=
  (isonormalCylinderGradient_memLp h p 2 (by simp)).toLp (isonormalCylinderGradient h p)

omit [Fintype ι] in
theorem isonormalCylinderL2_coeFn (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    isonormalCylinderL2 h p =ᵐ[gaussianProduct] isonormalCylinder h p := MemLp.coeFn_toLp _

theorem isonormalCylinderGradientL2_coeFn (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    isonormalCylinderGradientL2 h p =ᵐ[gaussianProduct] isonormalCylinderGradient h p :=
  MemLp.coeFn_toLp _

@[simp] theorem isonormalCylinderGradient_C (h : ι → CoefficientSpace) (a : ℝ)
    (ω : SampleSpace) : isonormalCylinderGradient h (C a) ω = 0 := by
  simp [isonormalCylinderGradient, isonormalCylinder]

@[simp] theorem isonormalCylinderGradient_X (h : ι → CoefficientSpace) (j : ι)
    (ω : SampleSpace) : isonormalCylinderGradient h (X j) ω = h j := by
  classical
  simp [isonormalCylinderGradient, isonormalCylinder, pderiv_X, Pi.single_apply]

theorem isonormalCylinderGradient_add (h : ι → CoefficientSpace) (p q : MvPolynomial ι ℝ)
    (ω : SampleSpace) : isonormalCylinderGradient h (p + q) ω =
      isonormalCylinderGradient h p ω + isonormalCylinderGradient h q ω := by
  simp [isonormalCylinderGradient, map_add, isonormalCylinder_add, add_smul,
    Finset.sum_add_distrib]

/-- Product differentiation follows from the true polynomial partial-derivative product rule. -/
theorem isonormalCylinderGradient_mul (h : ι → CoefficientSpace) (p q : MvPolynomial ι ℝ)
    (ω : SampleSpace) : isonormalCylinderGradient h (p * q) ω =
      isonormalCylinder h p ω • isonormalCylinderGradient h q ω +
      isonormalCylinder h q ω • isonormalCylinderGradient h p ω := by
  simp only [isonormalCylinderGradient, pderiv_mul, isonormalCylinder_add,
    isonormalCylinder_mul, Pi.add_apply, Pi.mul_apply, add_smul, Finset.sum_add_distrib]
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

/-- Affine coordinate perturbation along a Hilbert direction v.
This is an actual polynomial function of v; no sample-space translation theorem is assumed. -/
def isonormalCylinderShift (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ)
    (ω : SampleSpace) (v : CoefficientSpace) : ℝ :=
  MvPolynomial.eval (fun i => firstChaosEmbedding (h i) ω + inner ℝ (h i) v) p

/-- Analytic verification: the gradient formula represents the actual Fréchet derivative
of the affine-coordinate polynomial at the zero Hilbert direction. -/
theorem isonormalCylinderShift_hasFDerivAt (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ)
    (ω : SampleSpace) :
    HasFDerivAt (isonormalCylinderShift h p ω)
      (innerSL ℝ (isonormalCylinderGradient h p ω)) (0 : CoefficientSpace) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [isonormalCylinderGradient_C]
    have he : isonormalCylinderShift h (C a) ω = fun _ => a := by
      funext v
      simp [isonormalCylinderShift]
    rw [he]
    simpa using hasFDerivAt_const (𝕜 := ℝ) a (0 : CoefficientSpace)
  | add p q hp hq =>
    rw [isonormalCylinderGradient_add]
    convert hp.add hq using 1
    · ext v
      simp [isonormalCylinderShift]
    · ext v
      simp
  | mul_X p j hp =>
    rw [isonormalCylinderGradient_mul, isonormalCylinderGradient_X]
    have hx := ((innerSL ℝ (h j)).hasFDerivAt (x := (0 : CoefficientSpace))).const_add
      (firstChaosEmbedding (h j) ω)
    convert hp.mul hx using 1
    · ext v
      simp [isonormalCylinderShift]
    · ext v
      simp [isonormalCylinderShift, isonormalCylinder]

/-- The actual analytic derivative is determined by the partial-derivative formula. -/
theorem isonormalCylinderShift_fderiv (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ)
    (ω : SampleSpace) :
    fderiv ℝ (isonormalCylinderShift h p ω) 0 =
      innerSL ℝ (isonormalCylinderGradient h p ω) :=
  (isonormalCylinderShift_hasFDerivAt h p ω).fderiv

/-- A product rule for an actual Fréchet derivative of polynomial coordinate perturbations. -/
theorem isonormalCylinderShift_product_rule (h : ι → CoefficientSpace)
    (p q : MvPolynomial ι ℝ) (ω : SampleSpace) :
    fderiv ℝ (fun v => isonormalCylinderShift h p ω v * isonormalCylinderShift h q ω v) 0 =
      innerSL ℝ (isonormalCylinder h p ω • isonormalCylinderGradient h q ω +
        isonormalCylinder h q ω • isonormalCylinderGradient h p ω) := by
  have he : (fun v => isonormalCylinderShift h p ω v * isonormalCylinderShift h q ω v) =
      isonormalCylinderShift h (p * q) ω := by
    ext v
    simp [isonormalCylinderShift]
  rw [he, isonormalCylinderShift_fderiv, isonormalCylinderGradient_mul]

/-- The product-rule terms are genuinely integrable in every finite Lp, using doubled
input exponents; no global L² multiplication closure is assumed. -/
theorem isonormalCylinder_smulGradient_memLp (h : ι → CoefficientSpace)
    (p q : MvPolynomial ι ℝ) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω => isonormalCylinder h p ω • isonormalCylinderGradient h q ω)
      r gaussianProduct := by
  have ht : 2 * r ≠ ∞ := ENNReal.mul_ne_top (by simp) hr
  have : ENNReal.HolderTriple (2 * r) (2 * r) r := FiniteGaussian.doubled_holderTriple r
  exact smul_memLp (p := 2 * r) (q := 2 * r) (r := r)
    (isonormalCylinder_memLp h p (2 * r) ht)
    (isonormalCylinderGradient_memLp h q (2 * r) ht)

/-- On coordinate unit vectors, the new cylinders retain the existing finite polynomial classes. -/
theorem isonormalCylinderL2_units (s : Finset ℕ) (p : MvPolynomial s ℝ) :
    isonormalCylinderL2 (fun i : s => lp.single 2 i.val (1 : ℝ)) p =
      polynomialCylinderEmbedding s p := by
  have hc (i : s) := coordinateL2_coeFn i.val
  apply Lp.ext
  filter_upwards [isonormalCylinderL2_coeFn
    (fun i : s => lp.single 2 i.val (1 : ℝ)) p,
    polynomialCylinderEmbedding_coeFn s p, ae_all_iff.2 hc] with ω h₁ h₂ hi
  rw [h₁, h₂]
  apply congrArg (fun x : s → ℝ => MvPolynomial.eval x p)
  funext i
  simpa only [firstChaos_unit, finiteProjection, Finset.restrict_def, coordinate] using hi i

/-- Arbitrary finite isonormal polynomial cylinders, with actual L² values.
This is a scalar set of classes, not a derivative operator or prescribed graph. -/
def isonormalPolynomialCore : Set GaussianL2 :=
  {f | ∃ (n : ℕ) (h : Fin n → CoefficientSpace) (p : MvPolynomial (Fin n) ℝ),
    isonormalCylinderL2 h p = f}

/-- Finite-variable renaming agrees with evaluation at the corresponding isonormal units. -/
theorem isonormalCylinderL2_rename_units {n : ℕ} (k : Fin n → ℕ)
    (p : MvPolynomial (Fin n) ℝ) :
    isonormalCylinderL2 (fun i => lp.single 2 (k i) (1 : ℝ)) p =
      coordinatePolynomialL2 (MvPolynomial.rename k p) := by
  apply Lp.ext
  filter_upwards [isonormalCylinderL2_coeFn (fun i => lp.single 2 (k i) (1 : ℝ)) p,
    coordinatePolynomialL2_coeFn (MvPolynomial.rename k p),
    ae_all_iff.2 coordinateL2_coeFn] with ω h₁ h₂ hi
  rw [h₁, h₂]
  simp only [isonormalCylinder, MvPolynomial.eval_rename]
  apply congrArg (fun x : Fin n → ℝ => MvPolynomial.eval x p)
  funext i
  simpa only [firstChaos_unit, coordinate, Function.comp_apply] using hi (k i)

/-- The arbitrary-coordinate isonormal polynomial core is genuinely dense, because it
contains the independently proved dense coordinate polynomial core. -/
theorem isonormalPolynomialCore_dense : Dense isonormalPolynomialCore := by
  apply Dense.mono (s₁ := (coordinatePolynomialEmbedding.range : Set GaussianL2)) ?_
    coordinatePolynomialEmbedding_dense
  rintro f ⟨p, rfl⟩
  obtain ⟨n, k, hk, q, rfl⟩ := MvPolynomial.exists_fin_rename p
  refine ⟨n, (fun i => lp.single 2 (k i) (1 : ℝ)), q, ?_⟩
  exact isonormalCylinderL2_rename_units k q

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
