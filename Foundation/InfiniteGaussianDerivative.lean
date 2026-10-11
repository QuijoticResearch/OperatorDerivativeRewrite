import Foundation.InfiniteGaussianRepresentation

/-! The genuine derivative on the polynomial cylindrical subspace of scalar L². -/
noncomputable section
open MeasureTheory ProbabilityTheory MvPolynomial
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] [Fintype κ] in
theorem isonormalCylinderL2_rename (h : κ → CoefficientSpace) (r : ι → κ)
    (p : MvPolynomial ι ℝ) :
    isonormalCylinderL2 h (rename r p) = isonormalCylinderL2 (h ∘ r) p := by
  apply Lp.ext
  filter_upwards [isonormalCylinderL2_coeFn h (rename r p),
    isonormalCylinderL2_coeFn (h ∘ r) p] with ω h₁ h₂
  rw [h₁, h₂]
  simp [isonormalCylinder, MvPolynomial.eval_rename, Function.comp_def]

theorem isonormalCylinderGradientL2_rename (h : κ → CoefficientSpace) (r : ι → κ)
    (p : MvPolynomial ι ℝ) :
    isonormalCylinderGradientL2 h (rename r p) =
      isonormalCylinderGradientL2 (h ∘ r) p :=
  isonormalCylinderGradientL2_representation_independent _ _ _ _
    (isonormalCylinderL2_rename h r p)

omit [Fintype ι] in
theorem isonormalCylinderL2_add (h : ι → CoefficientSpace) (p q : MvPolynomial ι ℝ) :
    isonormalCylinderL2 h (p + q) = isonormalCylinderL2 h p + isonormalCylinderL2 h q := by
  apply Lp.ext
  filter_upwards [isonormalCylinderL2_coeFn h (p + q), isonormalCylinderL2_coeFn h p,
    isonormalCylinderL2_coeFn h q, Lp.coeFn_add (isonormalCylinderL2 h p)
      (isonormalCylinderL2 h q)] with ω hsum hp hq hout
  simp only [hsum, hout, hp, hq, isonormalCylinder_add, Pi.add_apply]

theorem isonormalCylinderGradientL2_add (h : ι → CoefficientSpace)
    (p q : MvPolynomial ι ℝ) :
    isonormalCylinderGradientL2 h (p + q) =
      isonormalCylinderGradientL2 h p + isonormalCylinderGradientL2 h q := by
  apply Lp.ext
  filter_upwards [isonormalCylinderGradientL2_coeFn h (p + q),
    isonormalCylinderGradientL2_coeFn h p, isonormalCylinderGradientL2_coeFn h q,
    Lp.coeFn_add (isonormalCylinderGradientL2 h p) (isonormalCylinderGradientL2 h q)]
      with ω hsum hp hq hout
  simp only [hsum, hout, hp, hq, isonormalCylinderGradient_add, Pi.add_apply]

omit [Fintype ι] in
theorem isonormalCylinderL2_const_mul (h : ι → CoefficientSpace)
    (a : ℝ) (p : MvPolynomial ι ℝ) :
    isonormalCylinderL2 h (C a * p) = a • isonormalCylinderL2 h p := by
  apply Lp.ext
  filter_upwards [isonormalCylinderL2_coeFn h (C a * p), isonormalCylinderL2_coeFn h p,
    Lp.coeFn_smul a (isonormalCylinderL2 h p)] with ω hprod hp hout
  simp only [hprod, hout, hp, isonormalCylinder_mul, isonormalCylinder_C,
    Pi.mul_apply, Pi.smul_apply, smul_eq_mul]

theorem isonormalCylinderGradientL2_const_mul (h : ι → CoefficientSpace)
    (a : ℝ) (p : MvPolynomial ι ℝ) :
    isonormalCylinderGradientL2 h (C a * p) = a • isonormalCylinderGradientL2 h p := by
  apply Lp.ext
  filter_upwards [isonormalCylinderGradientL2_coeFn h (C a * p),
    isonormalCylinderGradientL2_coeFn h p,
    Lp.coeFn_smul a (isonormalCylinderGradientL2 h p)] with ω hprod hp hout
  simp [hprod, hout, hp, isonormalCylinderGradient_mul, isonormalCylinder_C]

omit [Fintype ι] in
/-- Any finite index type represents an element of the original Fin-indexed scalar core. -/
theorem isonormalCylinderL2_mem_core [Finite ι] (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    isonormalCylinderL2 h p ∈ isonormalPolynomialCore := by
  classical
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, h ∘ e.symm, rename e p, ?_⟩
  rw [isonormalCylinderL2_rename]
  congr 1
  ext i
  simp [e, Function.comp_def]

theorem isonormalPolynomialCore_zero : (0 : GaussianL2) ∈ isonormalPolynomialCore := by
  have he : isonormalCylinderL2 (fun _ : Fin 0 => (0 : CoefficientSpace)) (C 0) = 0 := by
    apply Lp.ext
    filter_upwards [isonormalCylinderL2_coeFn (fun _ : Fin 0 => (0 : CoefficientSpace))
      (C 0), Lp.coeFn_zero (E := ℝ) (μ := gaussianProduct) (p := 2)] with ω h₁ h₂
    simp only [h₁, h₂, isonormalCylinder_C, Pi.zero_apply]
  exact he ▸ isonormalCylinderL2_mem_core _ _

theorem isonormalPolynomialCore_add {f g : GaussianL2}
    (hf : f ∈ isonormalPolynomialCore) (hg : g ∈ isonormalPolynomialCore) :
    f + g ∈ isonormalPolynomialCore := by
  rcases hf with ⟨n, h, p, rfl⟩
  rcases hg with ⟨m, k, q, rfl⟩
  have hm := isonormalCylinderL2_mem_core (Sum.elim h k)
    (rename Sum.inl p + rename Sum.inr q)
  simpa only [isonormalCylinderL2_add, isonormalCylinderL2_rename, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr] using hm

theorem isonormalPolynomialCore_smul (a : ℝ) {f : GaussianL2}
    (hf : f ∈ isonormalPolynomialCore) : a • f ∈ isonormalPolynomialCore := by
  rcases hf with ⟨n, h, p, rfl⟩
  rw [← isonormalCylinderL2_const_mul]
  exact isonormalCylinderL2_mem_core _ _

/-- The actual scalar L² polynomial cylindrical subspace; its density was already proved. -/
def polynomialCylindricalDomain : Submodule ℝ GaussianL2 where
  carrier := isonormalPolynomialCore
  zero_mem' := isonormalPolynomialCore_zero
  add_mem' := isonormalPolynomialCore_add
  smul_mem' := isonormalPolynomialCore_smul

/-- Representation data are used only to construct a value whose independence is proved. -/
structure PolynomialRepresentation (f : GaussianL2) where
  dimension : ℕ
  directions : Fin dimension → CoefficientSpace
  polynomial : MvPolynomial (Fin dimension) ℝ
  represents : isonormalCylinderL2 directions polynomial = f

def polynomialRepresentation (f : polynomialCylindricalDomain) : PolynomialRepresentation f :=
  Classical.choice (by
    rcases f.property with ⟨n, h, p, he⟩
    exact ⟨⟨n, h, p, he⟩⟩)

/-- A genuine value on the scalar L² domain, justified by representation independence. -/
def polynomialGradient (f : polynomialCylindricalDomain) : Lp CoefficientSpace 2 gaussianProduct :=
  isonormalCylinderGradientL2 (polynomialRepresentation f).directions
    (polynomialRepresentation f).polynomial

/-- Every representation of a domain element gives precisely its derivative. -/
theorem polynomialGradient_agrees (f : polynomialCylindricalDomain)
    (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ)
    (he : isonormalCylinderL2 h p = (f : GaussianL2)) :
    polynomialGradient f = isonormalCylinderGradientL2 h p :=
  isonormalCylinderGradientL2_representation_independent _ _ _ _
    ((polynomialRepresentation f).represents.trans he.symm)

theorem polynomialGradient_add (f g : polynomialCylindricalDomain) :
    polynomialGradient (f + g) = polynomialGradient f + polynomialGradient g := by
  let rf := polynomialRepresentation f
  let rg := polynomialRepresentation g
  let h := Sum.elim rf.directions rg.directions
  let p : MvPolynomial (Fin rf.dimension ⊕ Fin rg.dimension) ℝ := rename Sum.inl rf.polynomial
  let q : MvPolynomial (Fin rf.dimension ⊕ Fin rg.dimension) ℝ := rename Sum.inr rg.polynomial
  have hp : isonormalCylinderL2 h p = (f : GaussianL2) := by
    simpa only [h, p, isonormalCylinderL2_rename, Function.comp_def, Sum.elim_inl]
      using rf.represents
  have hq : isonormalCylinderL2 h q = (g : GaussianL2) := by
    simpa only [h, q, isonormalCylinderL2_rename, Function.comp_def, Sum.elim_inr]
      using rg.represents
  have he : isonormalCylinderL2 h (p + q) = ((f + g) : GaussianL2) := by
    simpa using (isonormalCylinderL2_add h p q).trans (congrArg₂ (· + ·) hp hq)
  rw [polynomialGradient_agrees (f + g) h (p + q) he,
    isonormalCylinderGradientL2_add, polynomialGradient_agrees f h p hp,
    polynomialGradient_agrees g h q hq]

theorem polynomialGradient_smul (a : ℝ) (f : polynomialCylindricalDomain) :
    polynomialGradient (a • f) = a • polynomialGradient f := by
  let r := polynomialRepresentation f
  have he : isonormalCylinderL2 r.directions (C a * r.polynomial) = ((a • f) : GaussianL2) := by
    simpa using (isonormalCylinderL2_const_mul r.directions a r.polynomial).trans
      (congrArg (a • ·) r.represents)
  rw [polynomialGradient_agrees (a • f) r.directions (C a * r.polynomial) he,
    isonormalCylinderGradientL2_const_mul,
    polynomialGradient_agrees f r.directions r.polynomial r.represents]

/-- The genuine polynomial cylindrical derivative; no closed extension is claimed. -/
def polynomialDerivative : polynomialCylindricalDomain →ₗ[ℝ]
    Lp CoefficientSpace 2 gaussianProduct where
  toFun := polynomialGradient
  map_add' := polynomialGradient_add
  map_smul' := polynomialGradient_smul


/-- This is a densely defined operator on the actual ambient scalar L² space. -/
theorem polynomialCylindricalDomain_dense :
    Dense (polynomialCylindricalDomain : Set GaussianL2) := isonormalPolynomialCore_dense

/-- The quotient-level derivative retains the genuine gradient
on every polynomial representation. -/
theorem polynomialDerivative_on_cylinder (h : ι → CoefficientSpace) (p : MvPolynomial ι ℝ) :
    polynomialDerivative ⟨isonormalCylinderL2 h p, isonormalCylinderL2_mem_core h p⟩ =
      isonormalCylinderGradientL2 h p :=
  polynomialGradient_agrees _ h p rfl

/-- Empty coordinate families have zero derivative, for every polynomial in no variables. -/
theorem polynomialDerivative_empty (h : Fin 0 → CoefficientSpace)
    (p : MvPolynomial (Fin 0) ℝ) :
    polynomialDerivative ⟨isonormalCylinderL2 h p, isonormalCylinderL2_mem_core h p⟩ = 0 := by
  rw [polynomialDerivative_on_cylinder]
  apply Lp.ext
  filter_upwards [isonormalCylinderGradientL2_coeFn h p] with ω hg
  simp [hg, isonormalCylinderGradient]
end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
