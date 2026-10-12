import Foundation.GaussianTerminalRepresentation
import Mathlib.LinearAlgebra.Multilinear.Basic

/-! Algebraic tensor Hermite spanning at arbitrary coordinate variances.
Zero variances are allowed; no covariance inverse or independence is assumed. -/
noncomputable section
open MeasureTheory Set MvPolynomial
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianTimeSpaceTensor
open GaussianTimeSpaceHermite
variable {ι : Type*} [Fintype ι]

def tensorMap : MultilinearMap ℝ (fun _ : ι => MvPolynomial Unit ℝ) (MvPolynomial ι ℝ) :=
  (MultilinearMap.mkPiAlgebra ℝ ι (MvPolynomial ι ℝ)).compLinearMap
    (fun i => (rename (fun _ : Unit => i)).toLinearMap)

def tensorPolynomial (t : ι → ℝ) (α : ι → ℕ) : MvPolynomial ι ℝ :=
  tensorMap (fun i => polynomial (t i) (α i))

theorem tensorMap_mem_span (t : ι → ℝ) (p : ι → MvPolynomial Unit ℝ) :
    tensorMap p ∈ Submodule.span ℝ (Set.range (tensorPolynomial t)) := by
  classical
  have h (i : ι) : p i ∈ Submodule.span ℝ (Set.range (polynomial (t i))) := by
    rw [GaussianTerminalRepresentation.polynomial_span]
    trivial
  choose c hc using fun i => Finsupp.mem_span_range_iff_exists_finsupp.mp (h i)
  have he (i : ι) : (∑ n ∈ (c i).support, c i n • polynomial (t i) n) = p i := hc i
  rw [← show (fun i => ∑ n ∈ (c i).support, c i n • polynomial (t i) n) = p from funext he]
  rw [MultilinearMap.map_sum_finset]
  apply Submodule.sum_mem
  intro α _
  rw [MultilinearMap.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

theorem tensorPolynomial_span (t : ι → ℝ) :
    Submodule.span ℝ (Set.range (tensorPolynomial t)) = ⊤ := by
  classical
  apply eq_top_iff.mpr
  intro p _
  rw [MvPolynomial.as_sum p]
  apply Submodule.sum_mem
  intro v _
  have hm : MvPolynomial.monomial v (p.coeff v) =
      p.coeff v • tensorMap (fun i => (X () : MvPolynomial Unit ℝ) ^ v i) := by
    simp only [tensorMap, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      AlgHom.toLinearMap_apply, map_pow, rename_X]
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    · simp [Algebra.smul_def]
    · intro i; simp
  rw [hm]
  exact Submodule.smul_mem _ _ (tensorMap_mem_span t _)

theorem eval_tensorPolynomial (t : ι → ℝ) (α : ι → ℕ) (x : ι → ℝ) :
    eval x (tensorPolynomial t α) = ∏ i, value (α i) (x i) (t i) := by
  simp [tensorPolynomial, tensorMap, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, eval_rename, Function.comp_def, value]

end OperatorDerivativeRewrite.Foundation.GaussianTimeSpaceTensor
