import Foundation.InfiniteGaussianDerivative

/-! Products and Leibniz on the actual polynomial L² domain, with proved higher moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

/-- Two domain elements always have one common finite polynomial coordinate family. -/
theorem exists_common_polynomial_representation (f g : polynomialCylindricalDomain) :
    ∃ (n : ℕ) (h : Fin n → CoefficientSpace) (p q : MvPolynomial (Fin n) ℝ),
      isonormalCylinderL2 h p = (f : GaussianL2) ∧
      isonormalCylinderL2 h q = (g : GaussianL2) := by
  classical
  let rf := polynomialRepresentation f
  let rg := polynomialRepresentation g
  let I := Fin rf.dimension ⊕ Fin rg.dimension
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I, (Sum.elim rf.directions rg.directions) ∘ e.symm,
    rename (e ∘ Sum.inl) rf.polynomial, rename (e ∘ Sum.inr) rg.polynomial, ?_, ?_⟩
  · rw [isonormalCylinderL2_rename]
    simpa [Function.comp_def] using rf.represents
  · rw [isonormalCylinderL2_rename]
    simpa [Function.comp_def] using rg.represents

/-- Higher moments hold for the actual scalar L² representatives on the domain. -/
theorem polynomialDomain_memLp (f : polynomialCylindricalDomain) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (f : GaussianL2) r gaussianProduct := by
  let a := polynomialRepresentation f
  rw [← a.represents]
  exact (memLp_congr_ae (isonormalCylinderL2_coeFn a.directions a.polynomial)).2
    (isonormalCylinder_memLp a.directions a.polynomial r hr)

/-- The genuine derivative has all finite moments on this polynomial domain. -/
theorem polynomialDerivative_memLp (f : polynomialCylindricalDomain)
    (r : ℝ≥0∞) (hr : r ≠ ∞) : MemLp (polynomialDerivative f) r gaussianProduct := by
  let a := polynomialRepresentation f
  exact (memLp_congr_ae (isonormalCylinderGradientL2_coeFn a.directions a.polynomial)).2
    (isonormalCylinderGradient_memLp a.directions a.polynomial r hr)

theorem polynomialDomain_mul_memLp (f g : polynomialCylindricalDomain)
    (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω => (f : GaussianL2) ω * (g : GaussianL2) ω) r gaussianProduct := by
  have ht : 2 * r ≠ ∞ := ENNReal.mul_ne_top (by simp) hr
  have : ENNReal.HolderTriple (2 * r) (2 * r) r := FiniteGaussian.doubled_holderTriple r
  exact (polynomialDomain_memLp f (2 * r) ht).fun_mul (polynomialDomain_memLp g (2 * r) ht)

/-- Product of actual scalar L² classes, justified here by proved polynomial moments. -/
def polynomialProductL2 (f g : polynomialCylindricalDomain) : GaussianL2 :=
  (polynomialDomain_mul_memLp f g 2 (by simp)).toLp
    (fun ω => (f : GaussianL2) ω * (g : GaussianL2) ω)

theorem polynomialProductL2_coeFn (f g : polynomialCylindricalDomain) :
    polynomialProductL2 f g =ᵐ[gaussianProduct]
      fun ω => (f : GaussianL2) ω * (g : GaussianL2) ω := MemLp.coeFn_toLp _

/-- Polynomial multiplication realizes the actual L² product, not just formal expressions. -/
theorem polynomialProductL2_agrees (f g : polynomialCylindricalDomain)
    {ι : Type*} (h : ι → CoefficientSpace) (p q : MvPolynomial ι ℝ)
    (hp : isonormalCylinderL2 h p = (f : GaussianL2))
    (hq : isonormalCylinderL2 h q = (g : GaussianL2)) :
    polynomialProductL2 f g = isonormalCylinderL2 h (p * q) := by
  apply Lp.ext
  filter_upwards [polynomialProductL2_coeFn f g, isonormalCylinderL2_coeFn h (p * q),
    hp ▸ isonormalCylinderL2_coeFn h p, hq ▸ isonormalCylinderL2_coeFn h q]
      with ω hout hprod hf hg
  simp only [hout, hprod, hf, hg, isonormalCylinder_mul, Pi.mul_apply]

theorem polynomialProductL2_mem_domain (f g : polynomialCylindricalDomain) :
    polynomialProductL2 f g ∈ polynomialCylindricalDomain := by
  obtain ⟨n, h, p, q, hp, hq⟩ := exists_common_polynomial_representation f g
  rw [polynomialProductL2_agrees f g h p q hp hq]
  exact isonormalCylinderL2_mem_core h (p * q)

/-- Intrinsic multiplication on the polynomial cylindrical domain of actual scalar L² classes. -/
def polynomialProduct (f g : polynomialCylindricalDomain) : polynomialCylindricalDomain :=
  ⟨polynomialProductL2 f g, polynomialProductL2_mem_domain f g⟩

/-- Product-rule terms are genuinely in L² because both factors have fourth moments. -/
theorem polynomialDomain_smul_derivative_memLp (f g : polynomialCylindricalDomain)
    (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω => (f : GaussianL2) ω • polynomialDerivative g ω) r gaussianProduct := by
  have ht : 2 * r ≠ ∞ := ENNReal.mul_ne_top (by simp) hr
  have : ENNReal.HolderTriple (2 * r) (2 * r) r := FiniteGaussian.doubled_holderTriple r
  exact smul_memLp (p := 2 * r) (q := 2 * r) (r := r)
    (polynomialDomain_memLp f (2 * r) ht) (polynomialDerivative_memLp g (2 * r) ht)

/-- The actual L² class of f Dg, on the polynomial domain only. -/
def polynomialTimesDerivative (f g : polynomialCylindricalDomain) :
    Lp CoefficientSpace 2 gaussianProduct :=
  (polynomialDomain_smul_derivative_memLp f g 2 (by simp)).toLp
    (fun ω => (f : GaussianL2) ω • polynomialDerivative g ω)

theorem polynomialTimesDerivative_coeFn (f g : polynomialCylindricalDomain) :
    polynomialTimesDerivative f g =ᵐ[gaussianProduct]
      fun ω => (f : GaussianL2) ω • polynomialDerivative g ω := MemLp.coeFn_toLp _

/-- Leibniz for the genuine derivative and multiplication on the actual L² domain. -/
theorem polynomialDerivative_product (f g : polynomialCylindricalDomain) :
    polynomialDerivative (polynomialProduct f g) =
      polynomialTimesDerivative f g + polynomialTimesDerivative g f := by
  obtain ⟨n, h, p, q, hp, hq⟩ := exists_common_polynomial_representation f g
  have hprod : isonormalCylinderL2 h (p * q) = (polynomialProduct f g : GaussianL2) :=
    (polynomialProductL2_agrees f g h p q hp hq).symm
  have hdprod : polynomialDerivative (polynomialProduct f g) =
      isonormalCylinderGradientL2 h (p * q) :=
    polynomialGradient_agrees _ h _ hprod
  have hdf : polynomialDerivative f = isonormalCylinderGradientL2 h p :=
    polynomialGradient_agrees f h p hp
  have hdg : polynomialDerivative g = isonormalCylinderGradientL2 h q :=
    polynomialGradient_agrees g h q hq
  apply Lp.ext
  filter_upwards [hdprod.symm ▸ isonormalCylinderGradientL2_coeFn h (p * q),
    polynomialTimesDerivative_coeFn f g, polynomialTimesDerivative_coeFn g f,
    Lp.coeFn_add (polynomialTimesDerivative f g) (polynomialTimesDerivative g f),
    hp ▸ isonormalCylinderL2_coeFn h p, hq ▸ isonormalCylinderL2_coeFn h q,
    hdf.symm ▸ isonormalCylinderGradientL2_coeFn h p,
    hdg.symm ▸ isonormalCylinderGradientL2_coeFn h q] with ω hd hfg hgf hadd hf hg hDf hDg
  rw [hd, hadd]
  simp only [Pi.add_apply, hfg, hgf, hf, hg, hDf, hDg, isonormalCylinderGradient_mul]

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
