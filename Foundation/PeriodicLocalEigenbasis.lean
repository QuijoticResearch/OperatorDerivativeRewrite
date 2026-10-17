import Foundation.PeriodicLocalSpectralSet

/-! A complete eigenbasis of the actual single-block Hessian, with native dual-pair certificates. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalEigenbasis
open PeriodicInteriorGaugeKernel PeriodicSingleBlockCoercivity
  PeriodicSingleBlockDecomposition PeriodicLocalWalshAction PeriodicLocalSpectralSet
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def pivot (a : Label) : Direction := a.val.1.min' ⟨a.val.2, a.property⟩

theorem pivot_mem (a : Label) : pivot a ∈ a.val.1 := Finset.min'_mem _ _

def eigenvalue (a : Label) : ℕ :=
  if a.val.2 = pivot a then 3 else 3+2*a.val.1.card

def mode (a : Label) : Local → ℝ :=
  if a.val.2 = pivot a then walshSum a.val.1
  else walsh a.val.1 a.val.2 - walsh a.val.1 (pivot a)

def intMode (a : Label) (e : Edge) : ℤ :=
  if a.val.2 = pivot a then ∑ i ∈ a.val.1, intWalsh a.val.1 i e
  else intWalsh a.val.1 a.val.2 e - intWalsh a.val.1 (pivot a) e

def intDual (a : Label) (e : Edge) : ℤ :=
  if a.val.2 = pivot a then ∑ i ∈ a.val.1, intWalsh a.val.1 i e
  else (a.val.1.card : ℤ)*intWalsh a.val.1 a.val.2 e -
    ∑ i ∈ a.val.1, intWalsh a.val.1 i e

def dual (a : Label) (e : Local) : ℝ := (intDual a e.val : ℝ)

theorem mode_int (a : Label) (e : Local) : mode a e = (intMode a e.val : ℝ) := by
  by_cases h : a.val.2 = pivot a <;>
    simp [mode, intMode, h, walshSum, walsh, Pi.sub_apply]

set_option maxHeartbeats 256000000 in
/-- A finite integer certificate; no floating arithmetic or external decision oracle. -/
theorem int_dual_pair : ∀ a b : Label,
    (∑ e : Local, intMode a e.val * intDual b e.val) =
      if a=b then 8*(a.val.1.card : ℤ) else 0 := by decide

theorem mode_dual_pair (a b : Label) : dotProduct (mode a) (dual b) =
    if a=b then 8*(a.val.1.card : ℝ) else 0 := by
  have h := int_dual_pair a b
  unfold dotProduct dual
  simp_rw [mode_int]
  exact_mod_cast h

theorem mode_linearIndependent : LinearIndependent ℝ mode := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc a
  have h := congrArg (fun f => dotProduct f (dual a)) hc
  rw [sum_dotProduct] at h
  simp only [smul_dotProduct, mode_dual_pair, smul_eq_mul, zero_dotProduct] at h
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  have hp : 0 < a.val.1.card := Finset.card_pos.mpr ⟨a.val.2, a.property⟩
  have hp' : 0 < (a.val.1.card : ℝ) := by exact_mod_cast hp
  exact (mul_eq_zero.mp h).resolve_right (by positivity)

def eigenBasis : Module.Basis Label ℝ (Local → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ mode_linearIndependent (by
    rw [label_card, Module.finrank_fintype_fun_eq_card, local_card])

theorem eigenBasis_apply (a : Label) : eigenBasis a = mode a := by
  rw [eigenBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

theorem mode_eigen (a : Label) : H (mode a) = (eigenvalue a : ℝ) • mode a := by
  change localHessian.mulVec (mode a) = (eigenvalue a : ℝ) • mode a
  by_cases h : a.val.2 = pivot a
  · simpa [mode, eigenvalue, h] using walshSum_eigenvalue_three a.val.1
  · simpa [mode, eigenvalue, h] using
      walsh_difference_eigenvalue a.val.1 a.val.2 (pivot a) a.property (pivot_mem a)

theorem eigenvalue_counts :
    Fintype.card {a : Label // eigenvalue a = 3} = 15 ∧
    Fintype.card {a : Label // eigenvalue a = 7} = 6 ∧
    Fintype.card {a : Label // eigenvalue a = 9} = 8 ∧
    Fintype.card {a : Label // eigenvalue a = 11} = 3 := by decide

end OperatorDerivativeRewrite.Foundation.PeriodicLocalEigenbasis
