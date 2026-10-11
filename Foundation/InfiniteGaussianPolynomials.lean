import Foundation.InfiniteGaussianIsonormal
import Mathlib.Algebra.MvPolynomial.Rename

/-! The genuine algebraic polynomial core on countably many Gaussian coordinates.
Every polynomial uses finitely many variables; no closure of L² multiplication is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

/-- Evaluated countable-variable polynomials have all finite moments, because each has
finite support and the finite Gaussian marginal estimates are already proved. -/
theorem coordinatePolynomial_memLp (p : MvPolynomial ℕ ℝ) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun ω : SampleSpace => MvPolynomial.eval ω p) r gaussianProduct := by
  obtain ⟨s, q, rfl⟩ := MvPolynomial.exists_finset_rename p
  convert polynomialCylinder_memLp s q r hr using 1
  ext ω
  simp [MvPolynomial.eval_rename, polynomialCylinder, finiteProjection,
    Finset.restrict_def, Function.comp_def]

/-- L² class of the actual polynomial evaluation, whose integrability is proved above. -/
def coordinatePolynomialL2 (p : MvPolynomial ℕ ℝ) : GaussianL2 :=
  (coordinatePolynomial_memLp p 2 (by simp)).toLp (fun ω => MvPolynomial.eval ω p)

theorem coordinatePolynomialL2_coeFn (p : MvPolynomial ℕ ℝ) :
    coordinatePolynomialL2 p =ᵐ[gaussianProduct] fun ω => MvPolynomial.eval ω p :=
  MemLp.coeFn_toLp _

/-- Linear evaluation map of finite-support algebraic polynomials. -/
def coordinatePolynomialEmbedding : MvPolynomial ℕ ℝ →ₗ[ℝ] GaussianL2 where
  toFun := coordinatePolynomialL2
  map_add' p q := by
    apply Lp.ext
    filter_upwards [coordinatePolynomialL2_coeFn (p + q), coordinatePolynomialL2_coeFn p,
      coordinatePolynomialL2_coeFn q, Lp.coeFn_add (coordinatePolynomialL2 p)
        (coordinatePolynomialL2 q)] with ω h₁ h₂ h₃ h₄
    rw [h₁, h₄]
    simp [h₂, h₃]
  map_smul' a p := by
    apply Lp.ext
    filter_upwards [coordinatePolynomialL2_coeFn (a • p), coordinatePolynomialL2_coeFn p,
      Lp.coeFn_smul a (coordinatePolynomialL2 p)] with ω h₁ h₂ h₃
    change coordinatePolynomialL2 (a • p) ω = (a • coordinatePolynomialL2 p) ω
    rw [h₁, h₃]
    simp [h₂]

/-- Renaming finite variables into ℕ preserves the actual polynomial random variable. -/
theorem coordinatePolynomialL2_rename (s : Finset ℕ) (p : MvPolynomial s ℝ) :
    coordinatePolynomialL2 (MvPolynomial.rename Subtype.val p) =
      polynomialCylinderEmbedding s p := by
  apply Lp.ext
  filter_upwards [coordinatePolynomialL2_coeFn (MvPolynomial.rename Subtype.val p),
    polynomialCylinderEmbedding_coeFn s p] with ω h₁ h₂
  rw [h₁, h₂]
  simp [MvPolynomial.eval_rename, polynomialCylinder, finiteProjection,
    Finset.restrict_def, Function.comp_def]

/-- The core consists exactly of genuine finite-coordinate polynomial cylinders,
not just their linear span or an assumed completion. -/
theorem coordinatePolynomialEmbedding_range :
    (coordinatePolynomialEmbedding.range : Set GaussianL2) =
      ⋃ s : Finset ℕ, ((polynomialCylinderEmbedding s).range : Set GaussianL2) := by
  ext f
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨s, q, rfl⟩ := MvPolynomial.exists_finset_rename p
    apply Set.mem_iUnion.mpr
    refine ⟨s, q, ?_⟩
    exact (coordinatePolynomialL2_rename s q).symm
  · intro hf
    obtain ⟨s, q, hq⟩ := Set.mem_iUnion.mp hf
    refine ⟨MvPolynomial.rename Subtype.val q, ?_⟩
    exact (coordinatePolynomialL2_rename s q).trans hq

/-- The countable-coordinate polynomial evaluation is faithful on algebraic polynomials. -/
theorem coordinatePolynomialEmbedding_injective :
    Function.Injective coordinatePolynomialEmbedding := by
  intro p q hpq
  obtain ⟨s, p', q', hp, hq⟩ := MvPolynomial.exists_finset_rename₂ p q
  have he : polynomialCylinderEmbedding s p' = polynomialCylinderEmbedding s q' := by
    change coordinatePolynomialL2 p = coordinatePolynomialL2 q at hpq
    rw [hp, hq, coordinatePolynomialL2_rename, coordinatePolynomialL2_rename] at hpq
    exact hpq
  have heq := polynomialCylinderEmbedding_injective s he
  rw [hp, hq, heq]

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
