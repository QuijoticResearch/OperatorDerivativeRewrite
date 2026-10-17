import Foundation.PeriodicPathHarmonic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The complete 64-field Walsh basis on the actual side-two coarse periodic lattice. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseWalshBasis
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

abbrev Label := Finset Direction × Direction
abbrev Field := CoarseEdge → ℝ

def characterZ (T : Finset Direction) (q : CoarseVertex) : ℤ :=
  (-1)^(∑ i ∈ T, (q i).val)
def character (T : Finset Direction) (q : CoarseVertex) : ℝ := (characterZ T q : ℝ)
def modeZ (a : Label) (e : CoarseEdge) : ℤ := if e.2 = a.2 then characterZ a.1 e.1 else 0
def mode (a : Label) (e : CoarseEdge) : ℝ := (modeZ a e : ℝ)

theorem label_card : Fintype.card Label = 64 := by decide
theorem edge_card : Fintype.card CoarseEdge = 64 := by decide

theorem int_character_pair : ∀ T U : Finset Direction,
    (∑ q : CoarseVertex, characterZ T q * characterZ U q) = if T = U then 16 else 0 := by decide

theorem int_mode_pair : ∀ a b : Label,
    (∑ e : CoarseEdge, modeZ a e * modeZ b e) = if a = b then 16 else 0 := by
  rintro ⟨T,i⟩ ⟨U,j⟩
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hi (k : Direction) :
      (∑ q : CoarseVertex, modeZ (T,i) (q,k) * modeZ (U,j) (q,k)) =
        if k = i ∧ k = j then (if T = U then 16 else 0) else 0 := by
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [modeZ, hki, hkj, int_character_pair]
  simp_rw [hi]
  by_cases hij : i = j <;> by_cases hTU : T = U <;> simp [hij, hTU, ite_and]

theorem mode_pair (a b : Label) : dotProduct (mode a) (mode b) = if a = b then 16 else 0 := by
  have h := int_mode_pair a b
  unfold dotProduct mode
  exact_mod_cast h

theorem mode_linearIndependent : LinearIndependent ℝ mode := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc a
  have h := congrArg (fun f => dotProduct f (mode a)) hc
  rw [sum_dotProduct] at h
  simp only [smul_dotProduct, mode_pair, smul_eq_mul, zero_dotProduct] at h
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  linarith

def basis : Module.Basis Label ℝ Field :=
  basisOfLinearIndependentOfCardEqFinrank' _ mode_linearIndependent (by
    rw [label_card, Module.finrank_fintype_fun_eq_card, edge_card])

theorem basis_apply (a : Label) : basis a = mode a := by
  rw [basis, coe_basisOfLinearIndependentOfCardEqFinrank']

def coefficient (a : Label) : Field →ₗ[ℝ] ℝ := basis.coord a

theorem coefficient_mode (a b : Label) : coefficient a (mode b) = if b = a then 1 else 0 := by
  rw [← basis_apply b]
  simp [coefficient, Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]

theorem reconstruction (f : Field) : (∑ a : Label, coefficient a f • mode a) = f := by
  simpa only [coefficient, Module.Basis.coord_apply, basis_apply] using basis.sum_repr f

theorem coefficient_dot (a : Label) (f : Field) : dotProduct f (mode a) = 16 * coefficient a f := by
  conv_lhs => rw [← reconstruction f]
  rw [sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul, mode_pair, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseWalshBasis
